#![allow(clippy::enum_variant_names)]

pub mod trace;

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use crate::cubical::equality::definitionally_equal;
use crate::cubical::interval::{DNF, I, Literal, dnf_bot, dnf_top, eval_interval};
use crate::cubical::syntax::{
    Datatype, ElimCase, Level, Name, System, Tactic, Term, beta, equiv_dom, is_bot_dnf, is_top_dnf,
    max_var, shift, show_term, subst,
};

use crate::cubical::debug;
use trace::record_step;

// Thread-local storage for the current datatype definitions during evaluation.
// This allows `do_papp` to look up square-constructor face terms for boundary reduction
// without threading `dts` through every NbE function signature.
thread_local! {
    static CURRENT_DTS: std::cell::RefCell<Vec<Datatype>> = std::cell::RefCell::new(Vec::new());
    static CURRENT_GLOBALS: std::cell::RefCell<Option<Globals>> = std::cell::RefCell::new(None);
    static NBE_EVAL_CACHE: std::cell::RefCell<HashMap<Term, Term>> = std::cell::RefCell::new(HashMap::new());
    static METAVAR_SOLUTIONS: std::cell::RefCell<Vec<Option<Term>>> = std::cell::RefCell::new(Vec::new());
    static META_NAMES: std::cell::RefCell<Vec<Option<Name>>> = std::cell::RefCell::new(Vec::new());
    static META_EXPECTED: std::cell::RefCell<Vec<Option<Term>>> = std::cell::RefCell::new(Vec::new());
}

/// Set the current datatype definitions for the duration of evaluation.
pub fn set_current_dts(dts: &[Datatype]) {
    CURRENT_DTS.with(|cell| {
        *cell.borrow_mut() = dts.to_vec();
    });
}

/// Get the current datatype definitions. Returns empty vec if not set.
fn current_dts() -> Vec<Datatype> {
    CURRENT_DTS.with(|cell| cell.borrow().clone())
}

/// Set the current global definition values used by `nbe_eval_ctx`.
/// Returns the previously-set value so callers can restore it.
pub fn set_current_globals(globals: Option<Globals>) -> Option<Globals> {
    CURRENT_GLOBALS.with(|cell| {
        let mut slot = cell.borrow_mut();
        let prev = slot.take();
        *slot = globals;
        prev
    })
}

pub type Env = Vec<Value>;

/// A persistent, Rc-linked environment for NbE.
/// Extending is O(1) — existing bindings are shared via Rc rather than deep-copied.
#[derive(Debug, Clone)]
pub struct Scope {
    /// Most recently bound values (innermost at index 0).
    local: Vec<Value>,
    /// Older bindings shared via Rc.
    parent: Option<Rc<Scope>>,
    /// Total number of bindings.
    len: usize,
}

impl Scope {
    pub fn empty() -> Scope {
        Scope {
            local: vec![],
            parent: None,
            len: 0,
        }
    }

    /// Extend with a single innermost binding. O(1).
    pub fn extend(&self, v: Value) -> Scope {
        Scope {
            local: vec![v],
            parent: Some(Rc::new(self.clone())),
            len: self.len + 1,
        }
    }

    /// Chain values as innermost bindings, with self as parent. O(|values|).
    pub fn chain(&self, values: Vec<Value>) -> Scope {
        if values.is_empty() {
            return self.clone();
        }
        let vlen = values.len();
        Scope {
            local: values,
            parent: Some(Rc::new(self.clone())),
            len: self.len + vlen,
        }
    }

    /// Look up the value at de Bruijn index `i` (0 = innermost). O(depth).
    pub fn lookup(&self, i: usize) -> &Value {
        if i < self.local.len() {
            &self.local[i]
        } else {
            self.parent.as_ref().unwrap().lookup(i - self.local.len())
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn to_vec(&self) -> Vec<Value> {
        let mut result = Vec::with_capacity(self.len);
        self.collect_into(&mut result);
        result
    }

    fn collect_into(&self, result: &mut Vec<Value>) {
        if let Some(ref p) = self.parent {
            p.collect_into(result);
        }
        result.extend(self.local.iter().rev().cloned());
    }
}

/// A system at value level: list of (DNF face, value) pairs.
pub type DNFSystem = Vec<(DNF, Value)>;

/// A shared reference to the global definition values.
/// All closures created during evaluation share the same `Globals` so that
/// recursive self-references resolve correctly after placeholder replacement.
pub type Globals = Rc<RefCell<Vec<Value>>>;

fn value_str(globals: &Globals, global_offset: usize, v: &Value) -> String {
    if !debug::is_active() {
        return String::new();
    }
    let term = quote(0, globals, global_offset, v.clone());
    show_term(&[], &term)
}

#[derive(Debug, Clone)]
pub enum Value {
    VNeutral(Neutral),
    VLam(Name, Closure),
    VApp(Box<Value>, Box<Value>),
    VPi(Name, Box<Value>, Closure),
    VSigma(Name, Box<Value>, Closure),
    VPair(Box<Value>, Box<Value>),
    VPath(Box<Value>, Box<Value>, Box<Value>),
    VPLam(Name, IClosure),
    VPApp(Box<Value>, Box<Value>),
    VUniv(Level),
    VProp,
    VSSet,
    VLift(Box<Value>, Level),
    VLower(Box<Value>),
    VIntervalTy,
    VInterval(I),
    VIntervalVar(usize),
    VCube(DNF),
    VData(Name, Vec<Value>),
    VCon(Name, Name, Vec<Value>),
    VPCon(Name, Name, Vec<Value>, Box<Value>),
    VSqCon(Name, Name, Vec<Value>, Box<Value>, Box<Value>),
    /// N-dimensional cell constructor value: `VCellCon(dt, con, args, ivars)`.
    VCellCon(Name, Name, Vec<Value>, Vec<Value>),
    /// Stuck eliminator. The trailing `Scope` is the evaluation environment
    /// at the eliminator's creation site; it is used when re-quoting the
    /// stored raw case bodies (see `quote_case_body`).
    VElim(Box<Value>, Vec<ElimCase>, Box<Value>, Scope, usize),
    VGlue(Box<Value>, DNF, Box<Value>),
    VPartial(Box<Value>, Box<Value>),
    VSystemType(DNFSystem),
    VGlueElem(DNF, Box<Value>, Box<Value>),
    VUnglue(DNF, Box<Value>, Box<Value>),
    VEquiv(Box<Value>, Box<Value>),
    VMkEquiv(
        Box<Value>,
        Box<Value>,
        Box<Value>,
        Box<Value>,
        Box<Value>,
        Box<Value>,
    ),
    VEquivFwd(Box<Value>, Box<Value>),
    VUa(Box<Value>),
    VTransport(Box<Value>, Box<Value>),
    VHComp(Box<Value>, DNFSystem, Box<Value>),
    VComp(Box<Value>, DNFSystem, Box<Value>),
    VFill(Box<Value>, DNFSystem, Box<Value>),
    VHFill(Box<Value>, DNFSystem, Box<Value>),
    VFst(Box<Value>),
    VSnd(Box<Value>),
    VProj(Name, Box<Value>),
    VRecordUpdate(Box<Value>, Vec<(Name, Value)>),
    VDelay(Box<Value>),
    VNext(Box<Value>),
    VForce(Box<Value>),
}

#[derive(Debug, Clone)]
pub struct Closure {
    pub env: Scope,
    pub globals: Globals,
    pub global_offset: usize,
    pub body: Term,
}

#[derive(Debug, Clone)]
pub struct IClosure {
    pub env: Scope,
    pub globals: Globals,
    pub global_offset: usize,
    pub body: Term,
}

#[derive(Debug, Clone)]
pub enum Neutral {
    NVar(usize),
    NApp(Box<Neutral>, Box<Value>),
    NPApp(Box<Neutral>, Box<Value>),
    NSqApp(Box<Neutral>, Box<Value>, Box<Value>),
    /// N-dimensional cell application: `NCellApp(neutral, [r1, r2, ..., rn])`.
    NCellApp(Box<Neutral>, Vec<Value>),
    NFst(Box<Neutral>),
    NSnd(Box<Neutral>),
    NElim(Box<Value>, Vec<ElimCase>, Box<Neutral>, Scope, usize),
    NTransport(Box<Value>, Box<Value>),
    NHComp(Box<Value>, DNFSystem, Box<Value>),
    NComp(Box<Value>, DNFSystem, Box<Value>),
    NFill(Box<Value>, DNFSystem, Box<Value>),
    NHFill(Box<Value>, DNFSystem, Box<Value>),
    NMeta(i32),
    NForce(Box<Neutral>),
    /// Record field projection stuck on a neutral record value.
    NProj(Box<Neutral>, Name),
}

impl Closure {
    pub fn apply(&self, v: Value) -> Value {
        let env = self.env.extend(v);
        eval_nbe(&env, &self.globals, self.global_offset, &self.body)
    }
}

impl IClosure {
    pub fn apply_i(&self, i: I) -> Value {
        self.apply_interval_value(Value::VInterval(i))
    }

    fn apply_i_var(&self, level: usize) -> Value {
        self.apply_interval_value(Value::VIntervalVar(level))
    }

    pub fn apply_interval_value(&self, v: Value) -> Value {
        match &v {
            Value::VInterval(i) => {
                // The closure body references its bound interval variable as
                // `I::Var(0)` (incrementing under nested PLams). Substitute it
                // with the applied interval value *before* evaluating; extending
                // the env is insufficient because eval_nbe's TInterval arm never
                // resolves interval vars against the env.
                //
                // The interval binder occupies a term slot in the parsed body
                // (the parser pushes a dummy binder for `<i>`), so we must push a
                // slot onto the env here as well — matching the `VIntervalVar`
                // and `other` arms below — or term variables inside the body
                // resolve one binder too high.
                let body = subst_interval_var(&self.body, 0, i);
                let env = self.env.extend(Value::VInterval(i.clone()));
                eval_nbe(&env, &self.globals, self.global_offset, &body)
            }
            Value::VIntervalVar(_level) => {
                let env = self.env.extend(v);
                eval_nbe(&env, &self.globals, self.global_offset, &self.body)
            }
            other => {
                let env = self.env.extend(other.clone());
                eval_nbe(&env, &self.globals, self.global_offset, &self.body)
            }
        }
    }
}

/// Structurally substitute interval variable `Var(target)` (the closure's
/// bound interval variable, incremented under nested PLams) with `val` in a
/// term. Pure traversal — no re-normalisation; the caller evaluates the result.
fn subst_interval_var(t: &Term, target: i32, val: &I) -> Term {
    fn go_i(i: &I, target: i32, val: &I) -> I {
        match i {
            I::Var(k) if *k == target => val.clone(),
            I::Meet(a, b) => I::Meet(
                Box::new(go_i(a, target, val)),
                Box::new(go_i(b, target, val)),
            ),
            I::Join(a, b) => I::Join(
                Box::new(go_i(a, target, val)),
                Box::new(go_i(b, target, val)),
            ),
            I::Neg(a) => I::Neg(Box::new(go_i(a, target, val))),
            other => other.clone(),
        }
    }

    fn go(t: &Term, target: i32, val: &I) -> Term {
        match t {
            Term::TInterval(i) => Term::TInterval(go_i(i, target, val)),
            Term::TCube(DNF { cubes }) => {
                let subst_lit = |l: &Literal| -> I {
                    match l {
                        Literal::Pos(k) => go_i(&I::Var(*k), target, val),
                        Literal::NegVar(k) => I::Neg(Box::new(go_i(&I::Var(*k), target, val))),
                    }
                };
                let subst_cube = |c: &BTreeSet<Literal>| -> I {
                    c.iter().fold(I::I1, |acc, l| {
                        I::Meet(Box::new(subst_lit(l)), Box::new(acc))
                    })
                };
                let combined = cubes.iter().fold(I::I0, |acc, c| {
                    I::Join(Box::new(subst_cube(c)), Box::new(acc))
                });
                Term::TInterval(combined)
            }
            Term::TApp(f, a) => {
                Term::TApp(Box::new(go(f, target, val)), Box::new(go(a, target, val)))
            }
            Term::TAbs(x, b) => Term::TAbs(x.clone(), Box::new(go(b, target, val))),
            Term::TPi(x, a, b) => Term::TPi(
                x.clone(),
                Box::new(go(a, target, val)),
                Box::new(go(b, target, val)),
            ),
            Term::TPath(a, u, v) => Term::TPath(
                Box::new(go(a, target, val)),
                Box::new(go(u, target, val)),
                Box::new(go(v, target, val)),
            ),
            Term::PLam(x, b) => Term::PLam(x.clone(), Box::new(go(b, target + 1, val))),
            Term::PApp(p, r) => {
                Term::PApp(Box::new(go(p, target, val)), Box::new(go(r, target, val)))
            }
            Term::THComp(a, sys, base) => Term::THComp(
                Box::new(go(a, target, val)),
                sys.iter()
                    .map(|(phi, t)| (go(phi, target, val), go(t, target, val)))
                    .collect(),
                Box::new(go(base, target, val)),
            ),
            Term::TComp(a, sys, base) => Term::TComp(
                Box::new(go(a, target, val)),
                sys.iter()
                    .map(|(phi, t)| (go(phi, target, val), go(t, target, val)))
                    .collect(),
                Box::new(go(base, target, val)),
            ),
            Term::TFill(a, sys, base) => Term::TFill(
                Box::new(go(a, target, val)),
                sys.iter()
                    .map(|(phi, t)| (go(phi, target, val), go(t, target, val)))
                    .collect(),
                Box::new(go(base, target, val)),
            ),
            Term::THFill(a, sys, base) => Term::THFill(
                Box::new(go(a, target, val)),
                sys.iter()
                    .map(|(phi, t)| (go(phi, target, val), go(t, target, val)))
                    .collect(),
                Box::new(go(base, target, val)),
            ),
            Term::TEquiv(a, b) => {
                Term::TEquiv(Box::new(go(a, target, val)), Box::new(go(b, target, val)))
            }
            Term::TMkEquiv(a, b, f, g, eta, eps) => Term::TMkEquiv(
                Box::new(go(a, target, val)),
                Box::new(go(b, target, val)),
                Box::new(go(f, target, val)),
                Box::new(go(g, target, val)),
                Box::new(go(eta, target, val)),
                Box::new(go(eps, target, val)),
            ),
            Term::TEquivFwd(e, x) => {
                Term::TEquivFwd(Box::new(go(e, target, val)), Box::new(go(x, target, val)))
            }
            Term::TUa(e) => Term::TUa(Box::new(go(e, target, val))),
            Term::TTransport(p, x) => {
                Term::TTransport(Box::new(go(p, target, val)), Box::new(go(x, target, val)))
            }
            Term::TGlue(a, ph, te) => Term::TGlue(
                Box::new(go(a, target, val)),
                Box::new(go(ph, target, val)),
                Box::new(go(te, target, val)),
            ),
            Term::TGlueElem(ph, x, a) => Term::TGlueElem(
                Box::new(go(ph, target, val)),
                Box::new(go(x, target, val)),
                Box::new(go(a, target, val)),
            ),
            Term::TUnglue(ph, te, g) => Term::TUnglue(
                Box::new(go(ph, target, val)),
                Box::new(go(te, target, val)),
                Box::new(go(g, target, val)),
            ),
            Term::TPartial(ph, a) => {
                Term::TPartial(Box::new(go(ph, target, val)), Box::new(go(a, target, val)))
            }
            Term::TSystemType(sys) => Term::TSystemType(
                sys.iter()
                    .map(|(phi, a)| (go(phi, target, val), go(a, target, val)))
                    .collect(),
            ),
            Term::TSigma(x, a, b) => Term::TSigma(
                x.clone(),
                Box::new(go(a, target, val)),
                Box::new(go(b, target, val)),
            ),
            Term::TPair(a, b) => {
                Term::TPair(Box::new(go(a, target, val)), Box::new(go(b, target, val)))
            }
            Term::TFst(p) => Term::TFst(Box::new(go(p, target, val))),
            Term::TSnd(p) => Term::TSnd(Box::new(go(p, target, val))),
            Term::TData(d, params) => Term::TData(
                d.clone(),
                params.iter().map(|a| go(a, target, val)).collect(),
            ),
            Term::TCon(data, con, args) => Term::TCon(
                data.clone(),
                con.clone(),
                args.iter().map(|a| go(a, target, val)).collect(),
            ),
            Term::TPCon(data, con, args, r) => Term::TPCon(
                data.clone(),
                con.clone(),
                args.iter().map(|a| go(a, target, val)).collect(),
                Box::new(go(r, target, val)),
            ),
            Term::TSqCon(data, con, args, r, s) => Term::TSqCon(
                data.clone(),
                con.clone(),
                args.iter().map(|a| go(a, target, val)).collect(),
                Box::new(go(r, target, val)),
                Box::new(go(s, target, val)),
            ),
            Term::TCellCon(data, con, args, ivars) => Term::TCellCon(
                data.clone(),
                con.clone(),
                args.iter().map(|a| go(a, target, val)).collect(),
                ivars.iter().map(|a| go(a, target, val)).collect(),
            ),
            Term::TElim(motive, cases, scrut) => Term::TElim(
                Box::new(go(motive, target, val)),
                cases
                    .iter()
                    .map(|c| ElimCase {
                        con: c.con.clone(),
                        binders: c.binders.clone(),
                        body: Box::new(go(&c.body, target, val)),
                        as_name: c.as_name.clone(),
                        record_bindings: c.record_bindings.clone(),
                    })
                    .collect(),
                Box::new(go(scrut, target, val)),
            ),
            Term::TProj(field, record) => {
                Term::TProj(field.clone(), Box::new(go(record, target, val)))
            }
            Term::TRecordUpdate(record, fields) => Term::TRecordUpdate(
                Box::new(go(record, target, val)),
                fields
                    .iter()
                    .map(|(f, t)| (f.clone(), go(t, target, val)))
                    .collect(),
            ),
            Term::TDelay(a) => Term::TDelay(Box::new(go(a, target, val))),
            Term::TNext(a) => Term::TNext(Box::new(go(a, target, val))),
            Term::TForce(a) => Term::TForce(Box::new(go(a, target, val))),
            Term::TBy(tactics) => Term::TBy(
                tactics
                    .iter()
                    .map(|tac| match tac {
                        Tactic::Exact(t) => Tactic::Exact(go(t, target, val)),
                        other => other.clone(),
                    })
                    .collect(),
            ),
            other => other.clone(),
        }
    }

    go(t, target, val)
}

/// Evaluate a term with local variables in `env` and global definitions in `globals`.
///
/// `global_offset` is the index into `globals` (in env.defs order, most-recent-first)
/// corresponding to the definition whose body is being evaluated.
/// A TVar(k) where k >= env.len() is a global reference:
///   globals[global_offset + (k - env.len())]
/// UNLESS that is also out of bounds — in which case we create a neutral.
///
/// Normalization can diverge on definitions that reference themselves directly
/// (e.g. `def f : Nat -> Nat := fun n => f n`): evaluating the global value
/// re-resolves the self-reference to the same lambda forever, growing the
/// recursion unboundedly. Cap the evaluation depth so such inputs produce a
/// finite (stuck) value instead of overflowing the stack. Every divergent path
/// — direct self-application, mutual recursion, and self-references reached via
/// `Closure::apply` / `IClosure` — recurses through `eval_nbe`, so the single
/// guard below covers them all. Legitimate normal forms stay far below the cap.
const EVAL_NBE_MAX_DEPTH: usize = 200;
thread_local! {
    static EVAL_NBE_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub fn eval_nbe(env: &Scope, globals: &Globals, global_offset: usize, t: &Term) -> Value {
    let depth = EVAL_NBE_DEPTH.with(|c| {
        let d = c.get();
        c.set(d + 1);
        d
    });
    if depth >= EVAL_NBE_MAX_DEPTH {
        EVAL_NBE_DEPTH.with(|c| c.set(depth));
        return Value::VNeutral(Neutral::NVar(depth));
    }
    let result = eval_nbe_inner(env, globals, global_offset, t);
    EVAL_NBE_DEPTH.with(|c| c.set(depth));
    result
}

fn eval_nbe_inner(env: &Scope, globals: &Globals, global_offset: usize, t: &Term) -> Value {
    match t {
        Term::TVar(i) => {
            let i = *i as usize;
            if i < env.len() {
                env.lookup(i).clone()
            } else {
                let g = globals.borrow();
                let global_idx = global_offset + (i - env.len());
                if global_idx < g.len() {
                    g[global_idx].clone()
                } else {
                    Value::VNeutral(Neutral::NVar(global_idx - g.len()))
                }
            }
        }
        Term::TApp(f, a) => do_apply(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, f),
            eval_nbe(env, globals, global_offset, a),
        ),
        Term::TAbs(x, b) => Value::VLam(
            x.clone(),
            Closure {
                env: env.clone(),
                globals: globals.clone(),
                global_offset,
                body: (**b).clone(),
            },
        ),
        Term::TUniv(n) => Value::VUniv(*n),
        Term::TProp => Value::VProp,
        Term::TSSet => Value::VSSet,
        Term::TLift(a, lvl) => {
            Value::VLift(Box::new(eval_nbe(env, globals, global_offset, a)), *lvl)
        }
        Term::TLower(a) => Value::VLower(Box::new(eval_nbe(env, globals, global_offset, a))),
        Term::TIntervalTy => Value::VIntervalTy,
        Term::TPi(x, a, b) => Value::VPi(
            x.clone(),
            Box::new(eval_nbe(env, globals, global_offset, a)),
            Closure {
                env: env.clone(),
                globals: globals.clone(),
                global_offset,
                body: (**b).clone(),
            },
        ),
        Term::TInterval(i) => Value::VInterval(i.clone()),
        Term::TCube(c) => Value::VCube(c.clone()),
        Term::TPath(a, u, v) => Value::VPath(
            Box::new(eval_nbe(env, globals, global_offset, a)),
            Box::new(eval_nbe(env, globals, global_offset, u)),
            Box::new(eval_nbe(env, globals, global_offset, v)),
        ),
        Term::PLam(x, b) => Value::VPLam(
            x.clone(),
            IClosure {
                env: env.clone(),
                globals: globals.clone(),
                global_offset,
                body: (**b).clone(),
            },
        ),
        Term::PApp(p, r) => do_papp(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, p),
            eval_nbe(env, globals, global_offset, r),
        ),
        Term::THComp(a, sys, base) => do_hcomp(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, a),
            eval_system(env, globals, global_offset, sys),
            eval_nbe(env, globals, global_offset, base),
        ),
        Term::TComp(a, sys, base) => do_comp(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, a),
            eval_system(env, globals, global_offset, sys),
            eval_nbe(env, globals, global_offset, base),
        ),
        Term::TFill(a, sys, base) => do_fill(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, a),
            eval_system(env, globals, global_offset, sys),
            eval_nbe(env, globals, global_offset, base),
        ),
        Term::THFill(a, sys, base) => do_hfill(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, a),
            eval_system(env, globals, global_offset, sys),
            eval_nbe(env, globals, global_offset, base),
        ),
        Term::TEquiv(a, b) => Value::VEquiv(
            Box::new(eval_nbe(env, globals, global_offset, a)),
            Box::new(eval_nbe(env, globals, global_offset, b)),
        ),
        Term::TMkEquiv(a, b, f, g, eta, eps) => Value::VMkEquiv(
            Box::new(eval_nbe(env, globals, global_offset, a)),
            Box::new(eval_nbe(env, globals, global_offset, b)),
            Box::new(eval_nbe(env, globals, global_offset, f)),
            Box::new(eval_nbe(env, globals, global_offset, g)),
            Box::new(eval_nbe(env, globals, global_offset, eta)),
            Box::new(eval_nbe(env, globals, global_offset, eps)),
        ),
        Term::TEquivFwd(e, x) => do_equiv_fwd(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, e),
            eval_nbe(env, globals, global_offset, x),
        ),
        Term::TUa(e) => Value::VUa(Box::new(eval_nbe(env, globals, global_offset, e))),
        Term::TTransport(p, x) => {
            let p_val = eval_nbe(env, globals, global_offset, p);
            let x_val = eval_nbe(env, globals, global_offset, x);
            let res = do_transport(env, globals, global_offset, p_val.clone(), x_val.clone());
            match &res {
                Value::VTransport(_, _) | Value::VNeutral(Neutral::NTransport(_, _)) => {
                    let p_term = quote(env.len(), globals, global_offset, p_val);
                    let x_term = quote(env.len(), globals, global_offset, x_val);
                    let reduced = transport_term_fallback(p_term, x_term);
                    match reduced {
                        Term::TTransport(_, _) => res,
                        _ => eval_nbe(env, globals, global_offset, &reduced),
                    }
                }
                _ => res,
            }
        }
        Term::TGlue(a, phi, te) => {
            let phi = value_to_dnf(eval_nbe(env, globals, global_offset, phi));
            let te = eval_nbe(env, globals, global_offset, te);
            if phi == dnf_top() {
                match te {
                    Value::VLam(_, clos) => {
                        let body = clos.apply(Value::VInterval(I::I1));
                        equiv_dom_value(body)
                    }
                    other => equiv_dom_value(other),
                }
            } else if phi == dnf_bot() {
                eval_nbe(env, globals, global_offset, a)
            } else {
                Value::VGlue(
                    Box::new(eval_nbe(env, globals, global_offset, a)),
                    phi,
                    Box::new(te),
                )
            }
        }
        Term::TPartial(phi, a) => {
            let phi_val = eval_nbe(env, globals, global_offset, phi);
            let a_val = eval_nbe(env, globals, global_offset, a);
            let phi_dnf = value_to_dnf(phi_val);
            if phi_dnf == dnf_top() {
                a_val
            } else {
                Value::VPartial(Box::new(a_val), Box::new(Value::VCube(phi_dnf)))
            }
        }
        Term::TSystemType(sys) => {
            let mut entries: DNFSystem = Vec::new();
            for (phi, a) in sys {
                let phi_val = eval_nbe(env, globals, global_offset, phi);
                let a_val = eval_nbe(env, globals, global_offset, a);
                let phi_dnf = value_to_dnf(phi_val);
                entries.push((phi_dnf, a_val));
            }
            Value::VSystemType(entries)
        }
        Term::TGlueElem(phi, t, a) => {
            let phi_dnf = value_to_dnf(eval_nbe(env, globals, global_offset, phi));
            let a_val = eval_nbe(env, globals, global_offset, a);
            if phi_dnf == dnf_top() {
                // phi=1: glue [1, t, a] = t
                // But if t = unglue(te, a), then unglue(glue [1, unglue(te, a), a]) = a
                // (Glue/unglue β for top face).
                eval_nbe(env, globals, global_offset, t)
            } else if phi_dnf == dnf_bot() {
                a_val
            } else {
                Value::VGlueElem(
                    phi_dnf,
                    Box::new(eval_nbe(env, globals, global_offset, t)),
                    Box::new(a_val),
                )
            }
        }
        Term::TUnglue(phi, te, g) => {
            let phi = value_to_dnf(eval_nbe(env, globals, global_offset, phi));
            let te = eval_nbe(env, globals, global_offset, te);
            let g_val = eval_nbe(env, globals, global_offset, g);
            if phi == dnf_top() {
                do_equiv_fwd(globals, global_offset, te, g_val)
            } else if phi == dnf_bot() {
                g_val
            } else {
                match &g_val {
                    Value::VGlueElem(g_phi, _, a) if *g_phi == phi => *a.clone(),
                    _ => Value::VUnglue(phi, Box::new(te), Box::new(g_val)),
                }
            }
        }
        Term::TSigma(x, a, b) => Value::VSigma(
            x.clone(),
            Box::new(eval_nbe(env, globals, global_offset, a)),
            Closure {
                env: env.clone(),
                globals: globals.clone(),
                global_offset,
                body: (**b).clone(),
            },
        ),
        Term::TPair(a, b) => Value::VPair(
            Box::new(eval_nbe(env, globals, global_offset, a)),
            Box::new(eval_nbe(env, globals, global_offset, b)),
        ),
        Term::TFst(p) => do_fst(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, p),
        ),
        Term::TSnd(p) => do_snd(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, p),
        ),
        Term::TProj(field, r) => do_proj(field, eval_nbe(env, globals, global_offset, r)),
        Term::TRecordUpdate(r, updates) => {
            let r_val = eval_nbe(env, globals, global_offset, r);
            let updates_val: Vec<(Name, Value)> = updates
                .iter()
                .map(|(f, e)| (f.clone(), eval_nbe(env, globals, global_offset, e)))
                .collect();
            // Eagerly desugar when the record evaluates to a VCon.
            if let Value::VCon(ref dt, ref con, ref args) = r_val {
                let dts = current_dts();
                if let Some(dt_sig) = dts.iter().find(|d| &d.name == dt) {
                    if let Some(field_names) = &dt_sig.field_names {
                        let mut new_args = args.clone();
                        for (field, val) in &updates_val {
                            if let Some(idx) = field_names.iter().position(|f| f == field) {
                                if idx < new_args.len() {
                                    new_args[idx] = val.clone();
                                }
                            }
                        }
                        return Value::VCon(dt.clone(), con.clone(), new_args);
                    }
                }
            }
            Value::VRecordUpdate(Box::new(r_val), updates_val)
        }
        Term::TData(d, params) => Value::VData(
            d.clone(),
            params
                .iter()
                .map(|p| eval_nbe(env, globals, global_offset, p))
                .collect(),
        ),
        Term::TCon(data, con, args) => Value::VCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| eval_nbe(env, globals, global_offset, a))
                .collect(),
        ),
        Term::TPCon(data, con, args, r) => Value::VPCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| eval_nbe(env, globals, global_offset, a))
                .collect(),
            Box::new(eval_nbe(env, globals, global_offset, r)),
        ),
        Term::TSqCon(data, con, args, r, s) => Value::VSqCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| eval_nbe(env, globals, global_offset, a))
                .collect(),
            Box::new(eval_nbe(env, globals, global_offset, r)),
            Box::new(eval_nbe(env, globals, global_offset, s)),
        ),
        Term::TCellCon(data, con, args, ivars) => Value::VCellCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| eval_nbe(env, globals, global_offset, a))
                .collect(),
            ivars
                .iter()
                .map(|v| eval_nbe(env, globals, global_offset, v))
                .collect(),
        ),
        Term::TElim(motive, cases, scrut) => do_elim(
            eval_nbe(env, globals, global_offset, motive),
            cases,
            eval_nbe(env, globals, global_offset, scrut),
            env,
            globals,
            global_offset,
        ),
        Term::Meta(i) => {
            if *i >= 0 {
                if let Some(solution) = get_meta_solution(*i) {
                    return eval_nbe(env, globals, global_offset, &solution);
                }
            }
            Value::VNeutral(Neutral::NMeta(*i))
        }
        Term::TBy(_) => panic!("TBy should be resolved before NbE"),
        Term::TDelay(a) => Value::VDelay(Box::new(eval_nbe(env, globals, global_offset, a))),
        Term::TNext(a) => Value::VNext(Box::new(eval_nbe(env, globals, global_offset, a))),
        Term::TForce(a) => do_force(
            eval_nbe(env, globals, global_offset, a),
            globals,
            global_offset,
        ),
    }
}

pub fn do_force(v: Value, globals: &Globals, global_offset: usize) -> Value {
    match v {
        Value::VNext(inner) => {
            record_step(
                "force-next".into(),
                "Force (Next _)".into(),
                value_str(globals, global_offset, &inner),
            );
            *inner
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::NForce(Box::new(n))),
        other => Value::VForce(Box::new(other)),
    }
}

pub fn do_apply(globals: &Globals, global_offset: usize, f: Value, a: Value) -> Value {
    match f {
        Value::VLam(ref x, ref clos) => {
            let result = clos.apply(a);
            record_step(
                "beta".into(),
                format!("(λ{}. _) _", x),
                value_str(globals, global_offset, &result),
            );
            result
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::NApp(Box::new(n), Box::new(a))),
        other => Value::VApp(Box::new(other), Box::new(a)),
    }
}

pub fn do_papp(globals: &Globals, global_offset: usize, p: Value, r: Value) -> Value {
    if let Some(i) = value_to_endpoint(&r)
        && let Value::VPLam(_, clos) = p
    {
        let end_lbl = if i == I::I0 { "0" } else { "1" };
        let result = clos.apply_i(i);
        record_step(
            "path-app".into(),
            format!("_ @ {}", end_lbl),
            value_str(globals, global_offset, &result),
        );
        return result;
    }

    match p {
        Value::VPLam(_, clos) => match r {
            Value::VInterval(ref i) => {
                let end_lbl = if *i == I::I0 {
                    "0".to_string()
                } else if *i == I::I1 {
                    "1".to_string()
                } else {
                    format!("{}", i)
                };
                let result = clos.apply_i(i.clone());
                record_step(
                    "path-app".into(),
                    format!("_ @ {}", end_lbl),
                    value_str(globals, global_offset, &result),
                );
                result
            }
            Value::VIntervalVar(level) => clos.apply_i_var(level),
            other => Value::VPApp(
                Box::new(Value::VPLam("_".to_string(), clos)),
                Box::new(other),
            ),
        },
        Value::VNeutral(n) => {
            Value::VNeutral(Neutral::NPApp(Box::new(n.clone()), Box::new(r.clone())))
        }
        // hcomp boundary reduction: (hcomp A sys base) @ 0 = base
        //                           (hcomp A sys base) @ 1 = first tube @ 1
        Value::VHComp(a, sys, base) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                match endpoint {
                    I::I0 => {
                        record_step(
                            "hcomp-papp-0".into(),
                            "hcomp _ _ _ @ 0".into(),
                            value_str(globals, global_offset, &base),
                        );
                        *base
                    }
                    I::I1 => {
                        // At i=1, any tube applied to I1 gives the result
                        // (all tubes agree at endpoints by well-formedness)
                        if let Some((_, first_tube)) = sys.first() {
                            let result = do_papp(
                                globals,
                                global_offset,
                                first_tube.clone(),
                                Value::VInterval(I::I1),
                            );
                            record_step(
                                "hcomp-papp-1".into(),
                                "hcomp _ _ _ @ 1".into(),
                                value_str(globals, global_offset, &result),
                            );
                            result
                        } else {
                            // Empty system: shouldn't happen (filtered earlier), but fallback
                            Value::VPApp(Box::new(Value::VHComp(a, sys, base)), Box::new(r))
                        }
                    }
                    _ => Value::VPApp(Box::new(Value::VHComp(a, sys, base)), Box::new(r)),
                }
            } else {
                Value::VPApp(Box::new(Value::VHComp(a, sys, base)), Box::new(r))
            }
        }
        // fill boundary reduction: (fill A sys base) @ 0 = base
        //                          (fill A sys base) @ 1 = comp A sys base
        Value::VFill(a, sys, base) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                match endpoint {
                    I::I0 => {
                        record_step(
                            "fill-papp-0".into(),
                            "fill _ _ _ @ 0".into(),
                            value_str(globals, global_offset, &base),
                        );
                        *base
                    }
                    I::I1 => {
                        let result = do_comp(globals, global_offset, *a, sys.clone(), *base);
                        record_step(
                            "fill-papp-1".into(),
                            "fill _ _ _ @ 1".into(),
                            value_str(globals, global_offset, &result),
                        );
                        result
                    }
                    _ => Value::VPApp(Box::new(Value::VFill(a, sys, base)), Box::new(r)),
                }
            } else {
                Value::VPApp(Box::new(Value::VFill(a, sys, base)), Box::new(r))
            }
        }
        // hfill boundary reduction: (hfill A sys base) @ 0 = base
        //                           (hfill A sys base) @ 1 = hcomp A sys base
        Value::VHFill(a, sys, base) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                match endpoint {
                    I::I0 => {
                        record_step(
                            "hfill-papp-0".into(),
                            "hfill _ _ _ @ 0".into(),
                            value_str(globals, global_offset, &base),
                        );
                        *base
                    }
                    I::I1 => {
                        let result = do_hcomp(globals, global_offset, *a, sys.clone(), *base);
                        record_step(
                            "hfill-papp-1".into(),
                            "hfill _ _ _ @ 1".into(),
                            value_str(globals, global_offset, &result),
                        );
                        result
                    }
                    _ => Value::VPApp(Box::new(Value::VHFill(a, sys, base)), Box::new(r)),
                }
            } else {
                Value::VPApp(Box::new(Value::VHFill(a, sys, base)), Box::new(r))
            }
        }
        // Square constructor boundary reduction.
        //
        // A square constructor has type:
        //   PathP (<i> PathP (<j> A) face_i0 face_i1) face_j0 face_j1
        //
        // When the first interval is a concrete endpoint:
        //   sq @ 0 @ s  =  face_j0 @ s   (outer path at i=0 gives face_j0)
        //   sq @ 1 @ s  =  face_j1 @ s   (outer path at i=1 gives face_j1)
        Value::VSqCon(ref data, ref con, ref args, ref sq_r, ref sq_s) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                let dts = current_dts();
                if let Some(dt) = dts.iter().find(|dt| &dt.name == data)
                    && let Some(sig) = dt.sqcons.iter().find(|c| &c.name == con)
                {
                    let arity = sig.arity();
                    let face = match endpoint {
                        I::I0 => &sig.face_j0,
                        I::I1 => &sig.face_j1,
                        _ => unreachable!(),
                    };
                    let mut face_inst = face.clone();
                    let arg_terms: Vec<Term> = args
                        .iter()
                        .map(|a| quote(0, globals, global_offset, a.clone()))
                        .collect();
                    for k in (0..arity).rev() {
                        face_inst = subst(k as i32, &arg_terms[arity - 1 - k], &face_inst);
                    }
                    let empty_globals: Globals = Rc::new(RefCell::new(Vec::new()));
                    let face_val = eval_nbe(&Scope::empty(), &empty_globals, 0, &face_inst);
                    record_step(
                        "sqcon-boundary".into(),
                        format!(
                            "{} @ {} @ _",
                            con,
                            if endpoint == I::I0 { "0" } else { "1" }
                        ),
                        value_str(globals, global_offset, &face_val),
                    );
                    return do_papp(globals, global_offset, face_val, (**sq_s).clone());
                }
                Value::VPApp(
                    Box::new(Value::VSqCon(
                        data.clone(),
                        con.clone(),
                        args.clone(),
                        sq_r.clone(),
                        sq_s.clone(),
                    )),
                    Box::new(r),
                )
            } else {
                Value::VPApp(
                    Box::new(Value::VSqCon(
                        data.clone(),
                        con.clone(),
                        args.clone(),
                        sq_r.clone(),
                        sq_s.clone(),
                    )),
                    Box::new(r),
                )
            }
        }
        // N-dimensional cell constructor boundary reduction.
        //
        // A cell constructor with n interval args and faces
        //   faces = [f_0, f_1, ..., f_{2n-2}, f_{2n-1}]
        // has type:
        //   PathP (<i_1> ... PathP (<i_n> A) f_0 f_1) ... f_{2n-2} f_{2n-1})
        //
        // When the first interval arg is a concrete endpoint:
        //   cell @ 0 @ r2 @ ... @ rn  =  (eval f_{2n-2}[args]) @ r2 @ ... @ rn
        //   cell @ 1 @ r2 @ ... @ rn  =  (eval f_{2n-1}[args]) @ r2 @ ... @ rn
        Value::VCellCon(ref data, ref con, ref args, ref ivars) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                let dts = current_dts();
                if let Some(dt) = dts.iter().find(|dt| &dt.name == data)
                    && let Some(sig) = dt.cellcons.iter().find(|c| &c.name == con)
                {
                    let arity = sig.arity();
                    let dim = sig.dimension();
                    // The outermost face pair is the last pair in the faces list.
                    let face = match endpoint {
                        I::I0 => &sig.faces[2 * dim - 2],
                        I::I1 => &sig.faces[2 * dim - 1],
                        _ => unreachable!(),
                    };
                    let mut face_inst = face.clone();
                    let arg_terms: Vec<Term> = args
                        .iter()
                        .map(|a| quote(0, globals, global_offset, a.clone()))
                        .collect();
                    for k in (0..arity).rev() {
                        face_inst = subst(k as i32, &arg_terms[arity - 1 - k], &face_inst);
                    }
                    let empty_globals: Globals = Rc::new(RefCell::new(Vec::new()));
                    let mut face_val = eval_nbe(&Scope::empty(), &empty_globals, 0, &face_inst);
                    record_step(
                        "cellcon-boundary".into(),
                        format!(
                            "{} @ {} @ ...",
                            con,
                            if endpoint == I::I0 { "0" } else { "1" }
                        ),
                        value_str(globals, global_offset, &face_val),
                    );
                    // Apply the face value to the remaining (n-1) interval args.
                    for iv in ivars.iter().rev().skip(1) {
                        face_val = do_papp(globals, global_offset, face_val, iv.clone());
                    }
                    return face_val;
                }
                Value::VPApp(
                    Box::new(Value::VCellCon(
                        data.clone(),
                        con.clone(),
                        args.clone(),
                        ivars.clone(),
                    )),
                    Box::new(r),
                )
            } else {
                // Non-endpoint interval arg: build nested PApp for remaining ivars.
                let result = Value::VPApp(
                    Box::new(Value::VCellCon(
                        data.clone(),
                        con.clone(),
                        args.clone(),
                        ivars.clone(),
                    )),
                    Box::new(r),
                );
                result
            }
        }
        // Zero-arg path constructor: VCon(d, c, []) applied to interval endpoint.
        // A zero-arg path constructor like `line2` has type PathP, so PApp(line2, r)
        // should reduce via the PConSig faces.
        Value::VCon(ref data, ref con, ref args) if args.is_empty() => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                let dts = current_dts();
                if let Some(dt) = dts.iter().find(|dt| &dt.name == data)
                    && let Some(sig) = dt.pcons.iter().find(|c| &c.name == con)
                {
                    let face = match endpoint {
                        I::I0 => &sig.face0,
                        I::I1 => &sig.face1,
                        _ => unreachable!(),
                    };
                    let face_val =
                        eval_nbe(&Scope::empty(), &Rc::new(RefCell::new(Vec::new())), 0, face);
                    record_step(
                        "pcon-zero-arg-boundary".into(),
                        format!("{} @ {}", con, if endpoint == I::I0 { "0" } else { "1" }),
                        value_str(globals, global_offset, &face_val),
                    );
                    return face_val;
                }
            }
            Value::VPApp(
                Box::new(Value::VCon(data.clone(), con.clone(), args.clone())),
                Box::new(r),
            )
        }
        // VGlueElem endpoint reduction:
        //   VGlueElem(phi, t, a) @ 0 = a       (the base A-element)
        //   VGlueElem(phi, t, a) @ 1 = t       (the cap B-element)
        Value::VGlueElem(ref phi, ref t, ref a) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                match endpoint {
                    I::I0 => {
                        record_step(
                            "glue-elem-papp-0".into(),
                            "glue-elem _ _ _ @ 0".into(),
                            value_str(globals, global_offset, a),
                        );
                        (**a).clone()
                    }
                    I::I1 => {
                        record_step(
                            "glue-elem-papp-1".into(),
                            "glue-elem _ _ _ @ 1".into(),
                            value_str(globals, global_offset, t),
                        );
                        (**t).clone()
                    }
                    _ => Value::VPApp(
                        Box::new(Value::VGlueElem(phi.clone(), t.clone(), a.clone())),
                        Box::new(r),
                    ),
                }
            } else {
                Value::VPApp(
                    Box::new(Value::VGlueElem(phi.clone(), t.clone(), a.clone())),
                    Box::new(r),
                )
            }
        }
        other => Value::VPApp(Box::new(other), Box::new(r)),
    }
}

pub fn do_fst(globals: &Globals, global_offset: usize, p: Value) -> Value {
    match p {
        Value::VPair(a, _) => {
            record_step(
                "fst-pair".into(),
                "fst (_, _)".into(),
                value_str(globals, global_offset, &a),
            );
            *a
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::NFst(Box::new(n))),
        other => Value::VFst(Box::new(other)),
    }
}

pub fn do_snd(globals: &Globals, global_offset: usize, p: Value) -> Value {
    match p {
        Value::VPair(_, b) => {
            record_step(
                "snd-pair".into(),
                "snd (_, _)".into(),
                value_str(globals, global_offset, &b),
            );
            *b
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::NSnd(Box::new(n))),
        other => Value::VSnd(Box::new(other)),
    }
}

pub fn do_proj(field: &str, r: Value) -> Value {
    match r {
        // Desugar record update on projection: (r { x = v }).y → r.y when field != x
        Value::VRecordUpdate(r_inner, ref updates) => {
            if let Value::VCon(ref dt, _, ref args) = *r_inner.as_ref() {
                let dts = current_dts();
                if let Some(dt_sig) = dts.iter().find(|d| &d.name == dt) {
                    if let Some(field_names) = &dt_sig.field_names {
                        if let Some((_, val)) = updates.iter().find(|(f, _)| f == field) {
                            return val.clone();
                        }
                        if let Some(idx) = field_names.iter().position(|n| n == field) {
                            if idx < args.len() {
                                return args[idx].clone();
                            }
                        }
                    }
                }
            }
            Value::VProj(
                field.to_string(),
                Box::new(Value::VRecordUpdate(r_inner, updates.clone())),
            )
        }
        Value::VCon(_, _, ref args) => {
            let dts = current_dts();
            if let Some(dt) = dts.iter().find(|dt| {
                dt.cons.len() == 1
                    && dt.pcons.is_empty()
                    && dt.sqcons.is_empty()
                    && dt.cellcons.is_empty()
                    && dt.field_names.is_some()
            }) {
                if let Some(field_names) = &dt.field_names {
                    if let Some(idx) = field_names.iter().position(|n| n == field) {
                        if idx < args.len() {
                            return args[idx].clone();
                        }
                    }
                }
            }
            Value::VProj(field.to_string(), Box::new(r))
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::NProj(Box::new(n), field.to_string())),
        other => Value::VProj(field.to_string(), Box::new(other)),
    }
}

pub fn do_elim(
    motive: Value,
    cases: &[ElimCase],
    scrut: Value,
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
) -> Value {
    match scrut {
        Value::VCon(ref data, ref con, ref args) => {
            match cases.iter().find(|case| case.con == *con) {
                Some(case) => {
                    let mut env2_values: Vec<Value> = args.iter().rev().cloned().collect();
                    if case.as_name.is_some() {
                        env2_values.insert(0, Value::VCon(data.clone(), con.clone(), args.clone()));
                    }
                    let env2 = env.chain(env2_values);
                    let result = eval_nbe(&env2, globals, global_offset, &case.body);
                    record_step(
                        "elim-con".into(),
                        format!("elim _ [{}] ({} {})", con, data, con),
                        value_str(globals, global_offset, &result),
                    );
                    result
                }
                None => Value::VElim(
                    Box::new(motive),
                    cases.to_vec(),
                    Box::new(Value::VCon("".into(), con.clone(), args.clone())),
                    env.clone(),
                    global_offset,
                ),
            }
        }
        Value::VPCon(ref data, ref con, ref args, ref r) => {
            match cases.iter().find(|case| case.con == *con) {
                Some(case) => {
                    let env2 = env.chain(args.iter().rev().cloned().collect());
                    let body = eval_nbe(&env2, globals, global_offset, &case.body);
                    let result = do_papp(globals, global_offset, body, (**r).clone());
                    record_step(
                        "elim-pcon".into(),
                        format!("elim _ [{}] ({} {})", con, data, con),
                        value_str(globals, global_offset, &result),
                    );
                    result
                }
                None => Value::VElim(
                    Box::new(motive),
                    cases.to_vec(),
                    Box::new(Value::VPCon(
                        "".into(),
                        con.clone(),
                        args.clone(),
                        r.clone(),
                    )),
                    env.clone(),
                    global_offset,
                ),
            }
        }
        // Square constructor elimination: body has 2 interval binders.
        // Evaluate body with args in scope, then apply to both interval args.
        Value::VSqCon(ref data, ref con, ref args, ref r, ref s) => {
            match cases.iter().find(|case| case.con == *con) {
                Some(case) => {
                    let env2 = env.chain(args.iter().rev().cloned().collect());
                    let body = eval_nbe(&env2, globals, global_offset, &case.body);
                    // Body is PLam-shaped with 2 interval binders: apply to both r and s.
                    let body_at_r = do_papp(globals, global_offset, body, (**r).clone());
                    let result = do_papp(globals, global_offset, body_at_r, (**s).clone());
                    record_step(
                        "elim-sqcon".into(),
                        format!("elim _ [{}] ({} {})", con, data, con),
                        value_str(globals, global_offset, &result),
                    );
                    result
                }
                None => Value::VElim(
                    Box::new(motive),
                    cases.to_vec(),
                    Box::new(Value::VSqCon(
                        "".into(),
                        con.clone(),
                        args.clone(),
                        r.clone(),
                        s.clone(),
                    )),
                    env.clone(),
                    global_offset,
                ),
            }
        }
        // N-dimensional cell constructor elimination: body has n interval binders.
        // Evaluate body with args in scope, then apply to all interval args.
        Value::VCellCon(ref data, ref con, ref args, ref ivars) => {
            match cases.iter().find(|case| case.con == *con) {
                Some(case) => {
                    let env2 = env.chain(args.iter().rev().cloned().collect());
                    let body = eval_nbe(&env2, globals, global_offset, &case.body);
                    // Apply body to all interval args (innermost first).
                    let mut result = body;
                    for iv in ivars.iter() {
                        result = do_papp(globals, global_offset, result, iv.clone());
                    }
                    record_step(
                        "elim-cellcon".into(),
                        format!("elim _ [{}] ({} {})", con, data, con),
                        value_str(globals, global_offset, &result),
                    );
                    result
                }
                None => Value::VElim(
                    Box::new(motive),
                    cases.to_vec(),
                    Box::new(Value::VCellCon(
                        "".into(),
                        con.clone(),
                        args.clone(),
                        ivars.clone(),
                    )),
                    env.clone(),
                    global_offset,
                ),
            }
        }
        Value::VNeutral(n) => stuck_elim(motive, cases, n, env, global_offset),
        other => Value::VElim(
            Box::new(motive),
            cases.to_vec(),
            Box::new(other),
            env.clone(),
            global_offset,
        ),
    }
}

pub fn do_transport(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    p: Value,
    x: Value,
) -> Value {
    match p {
        Value::VUa(e) => {
            let result = do_equiv_fwd(globals, global_offset, *e, x);
            record_step(
                "transport-ua".into(),
                "transport (ua _) _".into(),
                value_str(globals, global_offset, &result),
            );
            result
        }
        Value::VPLam(ref i_name, ref clos) => {
            let b0 = clos.apply_i(I::I0);
            let b1 = clos.apply_i(I::I1);
            if quote(0, globals, global_offset, b0.clone())
                == quote(0, globals, global_offset, b1.clone())
            {
                record_step(
                    "transport-const".into(),
                    "transport (λi. A) x [A constant]".into(),
                    value_str(globals, global_offset, &x),
                );
                return x;
            }

            match (&b0, &b1) {
                (Value::VUniv(_), Value::VUniv(_)) => {
                    record_step(
                        "transport-univ".into(),
                        "transport (λi. Univ) _".into(),
                        value_str(globals, global_offset, &x),
                    );
                    x
                }

                // Prop/SSet transport (constant type families, same as Univ)
                (Value::VProp, Value::VProp) | (Value::VSSet, Value::VSSet) => {
                    record_step(
                        "transport-prop-ss".into(),
                        "transport (λi. Prop/SSet) _".into(),
                        value_str(globals, global_offset, &x),
                    );
                    x
                }

                // Lift transport: transport (λi. Lift (A i) lvl) x
                (Value::VLift(_, _), Value::VLift(_, _)) => Value::VTransport(
                    Box::new(Value::VPLam(i_name.to_string(), clos.clone())),
                    Box::new(x),
                ),

                // Lower transport: same fallback
                (Value::VLower(_), Value::VLower(_)) => Value::VTransport(
                    Box::new(Value::VPLam(i_name.to_string(), clos.clone())),
                    Box::new(x),
                ),

                // Pi transport (non-dependent codomain only)
                (Value::VPi(arg_name, _, _), Value::VPi(_, _, _)) => {
                    let result =
                        transport_pi(env, globals, global_offset, i_name, clos, arg_name, x);
                    record_step(
                        "transport-pi".into(),
                        "transport (λi. Π _ _) _".into(),
                        value_str(globals, global_offset, &result),
                    );
                    result
                }

                // Path transport
                (Value::VPath(_, _, _), Value::VPath(_, _, _)) => {
                    let result = transport_path(env, globals, global_offset, i_name, clos, x);
                    record_step(
                        "transport-path".into(),
                        "transport (λi. Path _ _ _) _".into(),
                        value_str(globals, global_offset, &result),
                    );
                    result
                }

                // Sigma transport (pair only)
                (Value::VSigma(_, _, _), Value::VSigma(_, _, _)) => match x {
                    Value::VPair(ref a, ref b) => {
                        let result =
                            transport_sigma_pair(env, globals, global_offset, i_name, clos, a, b);
                        record_step(
                            "transport-sigma".into(),
                            "transport (λi. Σ _ _) (_, _)".into(),
                            value_str(globals, global_offset, &result),
                        );
                        result
                    }
                    _ => Value::VTransport(
                        Box::new(Value::VPLam("_".to_string(), clos.clone())),
                        Box::new(x),
                    ),
                },

                // Glue transport (phi=bot or phi=top)
                (Value::VGlue(_, phi0, _), Value::VGlue(_, _, _)) => {
                    let r = transport_glue(env, globals, global_offset, i_name, clos, phi0, &x);
                    r.unwrap_or_else(|| {
                        Value::VTransport(
                            Box::new(Value::VPLam("_".to_string(), clos.clone())),
                            Box::new(x),
                        )
                    })
                }

                // Data type transport: transport through a constant data type family
                // (λi. D params) where D doesn't depend on i.
                // Transport a constructor by transporting each argument through its type.
                (Value::VData(d0, _), Value::VData(d1, _)) if d0 == d1 => match x {
                    Value::VCon(ref d, ref con, ref args) if d == d0 => {
                        let result = transport_data_con(
                            env,
                            globals,
                            global_offset,
                            i_name,
                            clos,
                            con,
                            args,
                        );
                        record_step(
                            "transport-data".into(),
                            format!("transport (λi. {}) ({} ...)", d, con),
                            value_str(globals, global_offset, &result),
                        );
                        result
                    }
                    Value::VPCon(ref d, ref con, ref args, ref r) if d == d0 => {
                        let result = transport_data_pcon(
                            env,
                            globals,
                            global_offset,
                            i_name,
                            clos,
                            con,
                            args,
                            r,
                        );
                        record_step(
                            "transport-data-pcon".into(),
                            format!("transport (λi. {}) ({} ...)", d, con),
                            value_str(globals, global_offset, &result),
                        );
                        result
                    }
                    Value::VSqCon(ref d, ref con, ref args, ref r, ref s) if d == d0 => {
                        let result = transport_data_sqcon(
                            env,
                            globals,
                            global_offset,
                            i_name,
                            clos,
                            con,
                            args,
                            r,
                            s,
                        );
                        record_step(
                            "transport-data-sqcon".into(),
                            format!("transport (λi. {}) ({} ...)", d, con),
                            value_str(globals, global_offset, &result),
                        );
                        result
                    }
                    Value::VCellCon(ref d, ref con, ref args, ref ivars) if d == d0 => {
                        let result = transport_data_cellcon(
                            env,
                            globals,
                            global_offset,
                            i_name,
                            clos,
                            con,
                            args,
                            ivars,
                        );
                        record_step(
                            "transport-data-cellcon".into(),
                            format!("transport (λi. {}) ({} ...)", d, con),
                            value_str(globals, global_offset, &result),
                        );
                        result
                    }
                    _ => Value::VTransport(
                        Box::new(Value::VPLam("_".to_string(), clos.clone())),
                        Box::new(x),
                    ),
                },

                _ => Value::VTransport(
                    Box::new(Value::VPLam("_".to_string(), clos.clone())),
                    Box::new(x),
                ),
            }
        }
        other => Value::VNeutral(Neutral::NTransport(Box::new(other), Box::new(x))),
    }
}

/// Evaluate the body of a PLam at a formal interval variable (TVar(0) in the
/// returned term will be the interval binder).
fn eval_body_at_formal_interval(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    clos: &IClosure,
) -> (Scope, Value) {
    let body_with_var = beta(&shift(1, 0, &clos.body), &Term::TVar(0));
    let formal_env = env.extend(Value::VIntervalVar(env.len()));
    let evaluated = eval_nbe(&formal_env, globals, global_offset, &body_with_var);
    (formal_env, evaluated)
}

/// Apply a Closure with a dummy argument (for non-dependent extraction).
fn apply_non_dep(clos: &Closure) -> Value {
    clos.apply(Value::VInterval(I::I0))
}

/// Check whether a term references de Bruijn variable at the given level,
/// correctly tracking binder depth. Under each binder, the target variable's
/// de Bruijn index increases by 1.
pub fn uses_var_at_level(t: &Term, level: i32) -> bool {
    match t {
        Term::TVar(i) => *i == level,
        Term::TApp(f, a) => uses_var_at_level(f, level) || uses_var_at_level(a, level),
        Term::TAbs(_, b) => uses_var_at_level(b, level + 1),
        Term::TPi(_, a, b) => uses_var_at_level(a, level) || uses_var_at_level(b, level + 1),
        Term::TPath(a, u, v) => {
            uses_var_at_level(a, level)
                || uses_var_at_level(u, level)
                || uses_var_at_level(v, level)
        }
        Term::PLam(_, b) => uses_var_at_level(b, level + 1),
        Term::PApp(p, r) => uses_var_at_level(p, level) || uses_var_at_level(r, level),
        Term::THComp(a, sys, base) => {
            uses_var_at_level(a, level)
                || sys.iter().any(|(phi, tube)| {
                    uses_var_at_level(phi, level) || uses_var_at_level(tube, level)
                })
                || uses_var_at_level(base, level)
        }
        Term::TComp(a, sys, base) => {
            uses_var_at_level(a, level)
                || sys.iter().any(|(phi, tube)| {
                    uses_var_at_level(phi, level) || uses_var_at_level(tube, level)
                })
                || uses_var_at_level(base, level)
        }
        Term::TFill(a, sys, base) => {
            uses_var_at_level(a, level)
                || sys.iter().any(|(phi, tube)| {
                    uses_var_at_level(phi, level) || uses_var_at_level(tube, level)
                })
                || uses_var_at_level(base, level)
        }
        Term::THFill(a, sys, base) => {
            uses_var_at_level(a, level)
                || sys.iter().any(|(phi, tube)| {
                    uses_var_at_level(phi, level) || uses_var_at_level(tube, level)
                })
                || uses_var_at_level(base, level)
        }
        Term::TEquiv(a, b) => uses_var_at_level(a, level) || uses_var_at_level(b, level),
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            uses_var_at_level(a, level)
                || uses_var_at_level(b, level)
                || uses_var_at_level(f, level)
                || uses_var_at_level(g, level)
                || uses_var_at_level(eta, level)
                || uses_var_at_level(eps, level)
        }
        Term::TEquivFwd(e, x) => uses_var_at_level(e, level) || uses_var_at_level(x, level),
        Term::TUa(e) => uses_var_at_level(e, level),
        Term::TTransport(p, x) => uses_var_at_level(p, level) || uses_var_at_level(x, level),
        Term::TGlue(a, phi, te) => {
            uses_var_at_level(a, level)
                || uses_var_at_level(phi, level)
                || uses_var_at_level(te, level)
        }
        Term::TGlueElem(phi, t, a) => {
            uses_var_at_level(phi, level)
                || uses_var_at_level(t, level)
                || uses_var_at_level(a, level)
        }
        Term::TUnglue(phi, te, g) => {
            uses_var_at_level(phi, level)
                || uses_var_at_level(te, level)
                || uses_var_at_level(g, level)
        }
        Term::TPartial(phi, a) => uses_var_at_level(phi, level) || uses_var_at_level(a, level),
        Term::TSystemType(sys) => sys
            .iter()
            .any(|(phi, a)| uses_var_at_level(phi, level) || uses_var_at_level(a, level)),
        Term::TSigma(_, a, b) => uses_var_at_level(a, level) || uses_var_at_level(b, level + 1),
        Term::TPair(a, b) => uses_var_at_level(a, level) || uses_var_at_level(b, level),
        Term::TFst(p) => uses_var_at_level(p, level),
        Term::TSnd(p) => uses_var_at_level(p, level),
        Term::TProj(_, r) => uses_var_at_level(r, level),
        Term::TRecordUpdate(r, updates) => {
            uses_var_at_level(r, level) || updates.iter().any(|(_, e)| uses_var_at_level(e, level))
        }
        Term::TUniv(_)
        | Term::TProp
        | Term::TSSet
        | Term::TIntervalTy
        | Term::TInterval(_)
        | Term::TCube(_) => false,
        Term::TLift(a, _) => uses_var_at_level(a, level),
        Term::TLower(a) => uses_var_at_level(a, level),
        Term::TData(_, params) => params.iter().any(|p| uses_var_at_level(p, level)),
        Term::TCon(_, _, args) => args.iter().any(|a| uses_var_at_level(a, level)),
        Term::TPCon(_, _, args, r) => {
            args.iter().any(|a| uses_var_at_level(a, level)) || uses_var_at_level(r, level)
        }
        Term::TSqCon(_, _, args, r, s) => {
            args.iter().any(|a| uses_var_at_level(a, level))
                || uses_var_at_level(r, level)
                || uses_var_at_level(s, level)
        }
        Term::TCellCon(_, _, args, ivars) => {
            args.iter().any(|a| uses_var_at_level(a, level))
                || ivars.iter().any(|v| uses_var_at_level(v, level))
        }
        Term::TElim(motive, cases, scrut) => {
            uses_var_at_level(motive, level)
                || uses_var_at_level(scrut, level)
                || cases.iter().any(|c| uses_var_at_level(&c.body, level + 1))
        }
        Term::Meta(_) => false,
        Term::TBy(_) => false,
        Term::TDelay(a) | Term::TNext(a) | Term::TForce(a) => uses_var_at_level(a, level),
    }
}

/// Transport through Pi types.
fn transport_pi(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    arg_name: &str,
    x: Value,
) -> Value {
    let (formal_env, pi_at_var) = eval_body_at_formal_interval(env, globals, global_offset, clos);
    let cod_clos = match &pi_at_var {
        Value::VPi(_, _, cod_clos) => cod_clos,
        _ => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(x),
            );
        }
    };

    if !uses_var_at_level(&cod_clos.body, 0i32) {
        let b_val = apply_non_dep(cod_clos);
        let b_body = shift(
            1,
            1,
            &quote(formal_env.len(), globals, global_offset, b_val),
        );
        let b_fam = Term::PLam(i_name.to_string(), Box::new(b_body));
        let x_term = quote(env.len(), globals, global_offset, x);
        let result = Term::TAbs(
            arg_name.to_string(),
            Box::new(Term::TTransport(
                Box::new(b_fam),
                Box::new(Term::TApp(
                    Box::new(shift(1, 0, &x_term)),
                    Box::new(Term::TVar(0)),
                )),
            )),
        );
        eval_nbe(env, globals, global_offset, &result)
    } else {
        let p_term = quote(
            env.len(),
            globals,
            global_offset,
            Value::VPLam(i_name.to_string(), clos.clone()),
        );
        let x_term = quote(env.len(), globals, global_offset, x.clone());
        let reduced = transport_term_fallback(p_term, x_term);
        match reduced {
            Term::TTransport(_, _) => Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(x),
            ),
            _ => eval_nbe(env, globals, global_offset, &reduced),
        }
    }
}

/// Transport through Path types.
fn transport_path(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    x: Value,
) -> Value {
    let (formal_env, path_at_var) = eval_body_at_formal_interval(env, globals, global_offset, clos);
    let a_val = match &path_at_var {
        Value::VPath(a, _, _) => *a.clone(),
        _ => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(x),
            );
        }
    };
    let a_body = shift(
        1,
        1,
        &quote(formal_env.len(), globals, global_offset, a_val),
    );
    let a_fam = Term::PLam(i_name.to_string(), Box::new(a_body));
    let x_term = quote(env.len(), globals, global_offset, x);
    let a_fam_s = shift(1, 0, &a_fam);
    let result = Term::PLam(
        "j".to_string(),
        Box::new(Term::TTransport(
            Box::new(a_fam_s),
            Box::new(Term::PApp(
                Box::new(shift(1, 0, &x_term)),
                Box::new(Term::TVar(0)),
            )),
        )),
    );
    eval_nbe(env, globals, global_offset, &result)
}

/// Transport through Sigma types (pair decomposition).
fn transport_sigma_pair(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    a: &Value,
    b: &Value,
) -> Value {
    let (formal_env, sigma_at_var) =
        eval_body_at_formal_interval(env, globals, global_offset, clos);
    let a_val = match &sigma_at_var {
        Value::VSigma(_, a_val, _) => *a_val.clone(),
        _ => Value::VUniv(0),
    };
    let a_body = shift(
        1,
        1,
        &quote(formal_env.len(), globals, global_offset, a_val),
    );
    let a_fam = Term::PLam(i_name.to_string(), Box::new(a_body));

    let a_prime = eval_nbe(
        env,
        globals,
        global_offset,
        &Term::TTransport(
            Box::new(a_fam.clone()),
            Box::new(quote(env.len(), globals, global_offset, a.clone())),
        ),
    );

    let b_val = match &sigma_at_var {
        Value::VSigma(_, _, cod_clos) => apply_non_dep(cod_clos),
        _ => Value::VUniv(0),
    };
    let b_body = shift(
        1,
        1,
        &quote(formal_env.len(), globals, global_offset, b_val),
    );
    let b_fam = Term::PLam(i_name.to_string(), Box::new(b_body));

    let b_prime = eval_nbe(
        env,
        globals,
        global_offset,
        &Term::TTransport(
            Box::new(b_fam),
            Box::new(quote(env.len(), globals, global_offset, b.clone())),
        ),
    );

    Value::VPair(Box::new(a_prime), Box::new(b_prime))
}

/// Transport a constructor `con c a₁ ... aₙ` through a constant data type family.
///
/// Strategy: build the constructor's full Pi type from the Datatype definition,
/// transport the entire function through the family, then apply to the original
/// arguments. This works because:
///   transport (λi. D) (con c a₁ ... aₙ) = con c (trans₁ a₁) ... (transₙ aₙ)
/// where transₖ transports argument k through its type (instantiated with
/// the already-transported earlier arguments).
fn transport_data_con(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    con_name: &str,
    args: &[Value],
) -> Value {
    let dts = current_dts();
    let d_name = match clos.apply_i(I::I0) {
        Value::VData(name, _) => name,
        _ => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VCon("".into(), con_name.into(), args.to_vec())),
            );
        }
    };
    let dt = match dts.iter().find(|dt| dt.name == d_name) {
        Some(dt) => dt.clone(),
        None => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VCon(d_name.clone(), con_name.into(), args.to_vec())),
            );
        }
    };
    let con_sig = match dt.find_con(con_name) {
        Some(sig) => sig.clone(),
        None => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VCon(d_name.clone(), con_name.into(), args.to_vec())),
            );
        }
    };

    let n = con_sig.arity();
    if n == 0 {
        return Value::VCon(d_name.clone(), con_name.into(), vec![]);
    }

    // Build the constructor's Pi type: Π(a₁:A₁). Π(a₂:A₂(a₁)). ... D
    // Then transport it through the family and apply to original args.
    let mut result_args: Vec<Value> = Vec::new();
    let substed_tys: Vec<Term> = con_sig.arg_tys.clone();

    // We need to transport each argument through its type.
    // The type of argument k may depend on args[0..k].
    // We build the type family (λi. Aₖ) for each k, substituting already-transported args.
    for k in 0..n {
        // Build the k-th type with already-transported args substituted in
        let ty_k = substed_tys[k].clone();
        // Shift to account for the Pi binders we'll abstract over
        let mut ty_shifted = ty_k;
        for j in (0..=k).rev() {
            ty_shifted = shift(1, j as i32, &ty_shifted);
        }
        // Replace bound vars (0..k) with already-transported args as terms
        for j in 0..k {
            let arg_term = quote(env.len(), globals, global_offset, result_args[j].clone());
            ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
        }
        // ty_shifted now has: outermost binder for interval i, then variable 0 is arg k
        // Wrap as (λi. ty_shifted) with var 0 being the interval
        let ty_fam = Term::PLam(i_name.to_string(), Box::new(ty_shifted));
        let transported = eval_nbe(
            env,
            globals,
            global_offset,
            &Term::TTransport(
                Box::new(ty_fam),
                Box::new(quote(env.len(), globals, global_offset, args[k].clone())),
            ),
        );
        result_args.push(transported);
    }

    Value::VCon(d_name.clone(), con_name.into(), result_args)
}

/// Transport a path constructor `pcon c a₁ ... aₙ r` through a constant data type family.
/// Same strategy as transport_data_con, but also keeps the interval argument r unchanged.
fn transport_data_pcon(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    con_name: &str,
    args: &[Value],
    r: &Value,
) -> Value {
    let dts = current_dts();
    let d_name = match clos.apply_i(I::I0) {
        Value::VData(name, _) => name,
        _ => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VPCon(
                    "".into(),
                    con_name.into(),
                    args.to_vec(),
                    Box::new(r.clone()),
                )),
            );
        }
    };
    let dt = match dts.iter().find(|dt| dt.name == d_name) {
        Some(dt) => dt.clone(),
        None => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VPCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    Box::new(r.clone()),
                )),
            );
        }
    };
    let con_sig = match dt.find_pcon(con_name) {
        Some(sig) => sig.clone(),
        None => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VPCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    Box::new(r.clone()),
                )),
            );
        }
    };

    let n = con_sig.arity();
    if n == 0 {
        return Value::VPCon(d_name.clone(), con_name.into(), vec![], Box::new(r.clone()));
    }

    let mut result_args: Vec<Value> = Vec::new();
    let substed_tys: Vec<Term> = con_sig.arg_tys.clone();

    for k in 0..n {
        let ty_k = substed_tys[k].clone();
        let mut ty_shifted = ty_k;
        for j in (0..=k).rev() {
            ty_shifted = shift(1, j as i32, &ty_shifted);
        }
        for j in 0..k {
            let arg_term = quote(env.len(), globals, global_offset, result_args[j].clone());
            ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
        }
        let ty_fam = Term::PLam(i_name.to_string(), Box::new(ty_shifted));
        let transported = eval_nbe(
            env,
            globals,
            global_offset,
            &Term::TTransport(
                Box::new(ty_fam),
                Box::new(quote(env.len(), globals, global_offset, args[k].clone())),
            ),
        );
        result_args.push(transported);
    }

    Value::VPCon(
        d_name.clone(),
        con_name.into(),
        result_args,
        Box::new(r.clone()),
    )
}

/// Transport a square constructor `sqcon c a₁ ... aₙ r s` through a constant data type family.
fn transport_data_sqcon(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    con_name: &str,
    args: &[Value],
    r: &Value,
    s: &Value,
) -> Value {
    let dts = current_dts();
    let d_name = match clos.apply_i(I::I0) {
        Value::VData(name, _) => name,
        _ => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VSqCon(
                    "".into(),
                    con_name.into(),
                    args.to_vec(),
                    Box::new(r.clone()),
                    Box::new(s.clone()),
                )),
            );
        }
    };
    let dt = match dts.iter().find(|dt| dt.name == d_name) {
        Some(dt) => dt.clone(),
        None => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VSqCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    Box::new(r.clone()),
                    Box::new(s.clone()),
                )),
            );
        }
    };
    let con_sig = match dt.find_sqcon(con_name) {
        Some(sig) => sig.clone(),
        None => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VSqCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    Box::new(r.clone()),
                    Box::new(s.clone()),
                )),
            );
        }
    };

    let n = con_sig.arity();
    if n == 0 {
        return Value::VSqCon(
            d_name.clone(),
            con_name.into(),
            vec![],
            Box::new(r.clone()),
            Box::new(s.clone()),
        );
    }

    let mut result_args: Vec<Value> = Vec::new();
    let substed_tys: Vec<Term> = con_sig.arg_tys.clone();

    for k in 0..n {
        let ty_k = substed_tys[k].clone();
        let mut ty_shifted = ty_k;
        for j in (0..=k).rev() {
            ty_shifted = shift(1, j as i32, &ty_shifted);
        }
        for j in 0..k {
            let arg_term = quote(env.len(), globals, global_offset, result_args[j].clone());
            ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
        }
        let ty_fam = Term::PLam(i_name.to_string(), Box::new(ty_shifted));
        let transported = eval_nbe(
            env,
            globals,
            global_offset,
            &Term::TTransport(
                Box::new(ty_fam),
                Box::new(quote(env.len(), globals, global_offset, args[k].clone())),
            ),
        );
        result_args.push(transported);
    }

    Value::VSqCon(
        d_name.clone(),
        con_name.into(),
        result_args,
        Box::new(r.clone()),
        Box::new(s.clone()),
    )
}

/// Transport an n-dimensional cell constructor through a constant data type family.
/// Same strategy as transport_data_pcon/sqcon, but keeps all interval args unchanged.
fn transport_data_cellcon(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    con_name: &str,
    args: &[Value],
    ivars: &[Value],
) -> Value {
    let dts = current_dts();
    let d_name = match clos.apply_i(I::I0) {
        Value::VData(name, _) => name,
        _ => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VCellCon(
                    "".into(),
                    con_name.into(),
                    args.to_vec(),
                    ivars.to_vec(),
                )),
            );
        }
    };
    let dt = match dts.iter().find(|dt| dt.name == d_name) {
        Some(dt) => dt.clone(),
        None => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VCellCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    ivars.to_vec(),
                )),
            );
        }
    };
    let con_sig = match dt.find_cellcon(con_name) {
        Some(sig) => sig.clone(),
        None => {
            return Value::VTransport(
                Box::new(Value::VPLam("_".to_string(), clos.clone())),
                Box::new(Value::VCellCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    ivars.to_vec(),
                )),
            );
        }
    };

    let n = con_sig.arity();
    if n == 0 {
        return Value::VCellCon(d_name.clone(), con_name.into(), vec![], ivars.to_vec());
    }

    let mut result_args: Vec<Value> = Vec::new();
    let substed_tys: Vec<Term> = con_sig.arg_tys.clone();

    for k in 0..n {
        let ty_k = substed_tys[k].clone();
        let mut ty_shifted = ty_k;
        for j in (0..=k).rev() {
            ty_shifted = shift(1, j as i32, &ty_shifted);
        }
        for j in 0..k {
            let arg_term = quote(env.len(), globals, global_offset, result_args[j].clone());
            ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
        }
        let ty_fam = Term::PLam(i_name.to_string(), Box::new(ty_shifted));
        let transported = eval_nbe(
            env,
            globals,
            global_offset,
            &Term::TTransport(
                Box::new(ty_fam),
                Box::new(quote(env.len(), globals, global_offset, args[k].clone())),
            ),
        );
        result_args.push(transported);
    }

    Value::VCellCon(d_name.clone(), con_name.into(), result_args, ivars.to_vec())
}

/// Transport through Glue types.
fn transport_glue(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    phi0: &DNF,
    x: &Value,
) -> Option<Value> {
    if *phi0 == dnf_bot() {
        let (formal_env, glue_at_var) =
            eval_body_at_formal_interval(env, globals, global_offset, clos);
        let a_val = match &glue_at_var {
            Value::VGlue(a, _, _) => *a.clone(),
            _ => return None,
        };
        let a_body = shift(
            1,
            1,
            &quote(formal_env.len(), globals, global_offset, a_val),
        );
        let a_fam = Term::PLam(i_name.to_string(), Box::new(a_body));
        Some(eval_nbe(
            env,
            globals,
            global_offset,
            &Term::TTransport(
                Box::new(a_fam),
                Box::new(quote(env.len(), globals, global_offset, x.clone())),
            ),
        ))
    } else if *phi0 == dnf_top() {
        let (formal_env, glue_at_var) =
            eval_body_at_formal_interval(env, globals, global_offset, clos);
        let te_val = match &glue_at_var {
            Value::VGlue(_, _, te) => *te.clone(),
            _ => return None,
        };
        let dom = equiv_dom_value(te_val);
        let dom_body = shift(1, 1, &quote(formal_env.len(), globals, global_offset, dom));
        let dom_fam = Term::PLam(i_name.to_string(), Box::new(dom_body));
        Some(eval_nbe(
            env,
            globals,
            global_offset,
            &Term::TTransport(
                Box::new(dom_fam),
                Box::new(quote(env.len(), globals, global_offset, x.clone())),
            ),
        ))
    } else {
        // Non-trivial face: decompose glue elements using the cubical Glue transport rule.
        // transp (λi. Glue A [φ] te) (glue [φ] t a)
        //   = glue [φ] t (hcomp A [φ] (λi. t) a)
        // where t stays the same (constant equiv domain) and the base is composed
        // via hcomp to maintain the boundary condition on face φ.
        match x {
            Value::VGlueElem(phi_elem, t, a) if *phi_elem == *phi0 => {
                let (_, glue_at_var) =
                    eval_body_at_formal_interval(env, globals, global_offset, clos);
                let a_ty = match &glue_at_var {
                    Value::VGlue(a, _, _) => *a.clone(),
                    _ => return None,
                };

                // tube = λi. t  (constant tube in hcomp)
                let t_body = shift(1, 0, &quote(env.len(), globals, global_offset, *t.clone()));
                let tube = Term::PLam(i_name.to_string(), Box::new(t_body));
                let tube_val = eval_nbe(env, globals, global_offset, &tube);

                // Wrap as a single-entry system: [(phi, λi. tube)]
                let sys: DNFSystem = vec![(phi0.clone(), tube_val)];
                let hcomp_val = do_hcomp(globals, global_offset, a_ty, sys, *a.clone());

                Some(Value::VGlueElem(
                    phi0.clone(),
                    t.clone(),
                    Box::new(hcomp_val),
                ))
            }
            _ => None,
        }
    }
}

/// Term-level transport reduction.
pub fn transport_term_fallback(p_: Term, x_: Term) -> Term {
    match p_ {
        Term::TUa(ref e) => nbe_eval(&Term::TEquivFwd(e.clone(), Box::new(x_))),

        Term::PLam(ref i_name, ref body) => {
            let b0 = nbe_eval(&beta(body, &Term::TInterval(I::I0)));
            let b1 = nbe_eval(&beta(body, &Term::TInterval(I::I1)));

            if b0 == b1 {
                return x_;
            }

            match (&b0, &b1) {
                (Term::TPi(arg_name, a0, _), Term::TPi(_, a1, _)) => {
                    let arg_name = arg_name.clone();
                    let i_name = i_name.clone();

                    let a0_eval = nbe_eval(a0);
                    let a1_eval = nbe_eval(a1);
                    if a0_eval == a1_eval {
                        let b_fam = Term::PLam(
                            i_name.clone(),
                            Box::new(match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                Term::TPi(_, _, b_i) => {
                                    let max_idx = max_var(&b_i);
                                    let temp = max_idx + 1;
                                    let tmp_var = Term::TVar(temp);
                                    let step1 = subst(0, &tmp_var, &b_i);
                                    let step2 = subst(1, &Term::TVar(0), &step1);
                                    subst(temp, &Term::TVar(1), &step2)
                                }
                                _ => {
                                    let b0_body = match &b0 {
                                        Term::TPi(_, _, b) => (**b).clone(),
                                        _ => b0.clone(),
                                    };
                                    shift(1, 0, &b0_body)
                                }
                            }),
                        );
                        let x_shifted = shift(1, 0, &x_);
                        Term::TAbs(
                            arg_name,
                            Box::new(nbe_eval(&Term::TTransport(
                                Box::new(b_fam),
                                Box::new(nbe_eval(&Term::TApp(
                                    Box::new(x_shifted),
                                    Box::new(Term::TVar(0)),
                                ))),
                            ))),
                        )
                    } else {
                        let b_non_dep = match &b0 {
                            Term::TPi(_, _, b0_body) => {
                                subst(0, &Term::TUniv(0), b0_body) == **b0_body
                            }
                            _ => false,
                        };
                        if b_non_dep {
                            let b0_body = match &b0 {
                                Term::TPi(_, _, b) => (**b).clone(),
                                _ => b0.clone(),
                            };
                            let b_fam = Term::PLam(
                                i_name.clone(),
                                Box::new(
                                    match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                        Term::TPi(_, _, b_i) => *b_i,
                                        _ => shift(1, 0, &b0_body),
                                    },
                                ),
                            );
                            let x_shifted = shift(1, 0, &x_);
                            Term::TAbs(
                                arg_name,
                                Box::new(nbe_eval(&Term::TTransport(
                                    Box::new(b_fam),
                                    Box::new(nbe_eval(&Term::TApp(
                                        Box::new(x_shifted),
                                        Box::new(Term::TVar(0)),
                                    ))),
                                ))),
                            )
                        } else {
                            let arg_name = arg_name.clone();
                            let i_name = i_name.clone();

                            let pi_at_var = nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0)));
                            let a_i = match &pi_at_var {
                                Term::TPi(_, a, _) => (**a).clone(),
                                _ => shift(1, 0, a0),
                            };
                            let b0_body = match &b0 {
                                Term::TPi(_, _, b) => (**b).clone(),
                                _ => b0.clone(),
                            };
                            let b_i = match &pi_at_var {
                                Term::TPi(_, _, b) => (**b).clone(),
                                _ => shift(1, 0, &b0_body),
                            };

                            let a_fam = Term::PLam(i_name.clone(), Box::new(a_i));
                            let a_rev_fam = Term::PLam(
                                "j".to_string(),
                                Box::new(Term::PApp(
                                    Box::new(shift(1, 0, &a_fam)),
                                    Box::new(Term::TInterval(I::Neg(Box::new(I::Var(0))))),
                                )),
                            );

                            let y0_term = Term::TTransport(
                                Box::new(shift(1, 0, &a_rev_fam)),
                                Box::new(Term::TVar(0)),
                            );

                            let b_fam = Term::PLam(
                                i_name.clone(),
                                Box::new({
                                    let max_idx = max_var(&b_i);
                                    let temp = max_idx + 1;
                                    let tmp_var = Term::TVar(temp);
                                    let step1 = subst(0, &tmp_var, &b_i);
                                    let step2 = subst(1, &Term::TVar(0), &step1);
                                    let b_i_swapped = subst(temp, &Term::TVar(1), &step2);

                                    let y0_shifted = shift(1, 0, &y0_term);
                                    let fill_at_i = nbe_eval(&Term::TTransport(
                                        Box::new(Term::PLam(
                                            "j".to_string(),
                                            Box::new(nbe_eval(&Term::PApp(
                                                Box::new(shift(2, 0, &a_fam)),
                                                Box::new(Term::TInterval(I::Meet(
                                                    Box::new(I::Var(1)),
                                                    Box::new(I::Var(0)),
                                                ))),
                                            ))),
                                        )),
                                        Box::new(y0_shifted),
                                    ));
                                    nbe_eval(&subst(1, &fill_at_i, &b_i_swapped))
                                }),
                            );

                            let x_shifted = shift(1, 0, &x_);
                            Term::TAbs(
                                arg_name,
                                Box::new(nbe_eval(&Term::TTransport(
                                    Box::new(b_fam),
                                    Box::new(nbe_eval(&Term::TApp(
                                        Box::new(x_shifted),
                                        Box::new(y0_term),
                                    ))),
                                ))),
                            )
                        }
                    }
                }

                (Term::TPath(ty_a0, _, _), Term::TPath(_, _, _)) => {
                    let i_name = i_name.clone();
                    let ty_a0 = (**ty_a0).clone();

                    let a_fam = Term::PLam(
                        i_name.clone(),
                        Box::new(match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                            Term::TPath(a, _, _) => *a,
                            _ => shift(1, 0, &ty_a0),
                        }),
                    );

                    let a_fam_s = shift(1, 0, &a_fam);
                    let x_shifted = shift(1, 0, &x_);
                    Term::PLam(
                        "j".to_string(),
                        Box::new(nbe_eval(&Term::TTransport(
                            Box::new(a_fam_s),
                            Box::new(Term::PApp(Box::new(x_shifted), Box::new(Term::TVar(0)))),
                        ))),
                    )
                }

                (Term::TSigma(_, _, _), Term::TSigma(_, _, _)) => match x_ {
                    Term::TPair(ref a, ref b) => {
                        let i_name = i_name.clone();

                        let b0_a = match &b0 {
                            Term::TSigma(_, a, _) => (**a).clone(),
                            _ => b0.clone(),
                        };
                        let b0_b = match &b0 {
                            Term::TSigma(_, _, bz) => (**bz).clone(),
                            _ => b0.clone(),
                        };

                        let a_fam = Term::PLam(
                            i_name.clone(),
                            Box::new(match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                Term::TSigma(_, a_i, _) => *a_i,
                                _ => shift(1, 0, &b0_a),
                            }),
                        );

                        let a_prime =
                            nbe_eval(&Term::TTransport(Box::new(a_fam.clone()), a.clone()));

                        let a_clone = (**a).clone();
                        let b_fam = Term::PLam(
                            i_name.clone(),
                            Box::new(match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                Term::TSigma(_, _, b_i) => {
                                    let fill_at_i = nbe_eval(&Term::TTransport(
                                        Box::new(Term::PLam(
                                            "j".to_string(),
                                            Box::new(nbe_eval(&Term::PApp(
                                                Box::new(shift(2, 0, &a_fam)),
                                                Box::new(Term::TInterval(I::Meet(
                                                    Box::new(I::Var(1)),
                                                    Box::new(I::Var(0)),
                                                ))),
                                            ))),
                                        )),
                                        Box::new(shift(1, 0, &a_clone)),
                                    ));
                                    nbe_eval(&beta(&b_i, &fill_at_i))
                                }
                                _ => shift(1, 0, &b0_b),
                            }),
                        );

                        let b_prime = nbe_eval(&Term::TTransport(Box::new(b_fam), b.clone()));
                        Term::TPair(Box::new(a_prime), Box::new(b_prime))
                    }
                    _ => Term::TTransport(
                        Box::new(Term::PLam(i_name.clone(), body.clone())),
                        Box::new(x_),
                    ),
                },

                (Term::TGlue(_, phi0, _), Term::TGlue(_, _, _)) => {
                    let i_name = i_name.clone();
                    if is_bot_dnf(&nbe_eval(phi0)) {
                        nbe_eval(&Term::TTransport(
                            Box::new(Term::PLam(
                                i_name.clone(),
                                Box::new(
                                    match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                        Term::TGlue(a, _, _) => *a,
                                        other => other,
                                    },
                                ),
                            )),
                            Box::new(x_),
                        ))
                    } else if is_top_dnf(&nbe_eval(phi0)) {
                        nbe_eval(&Term::TTransport(
                            Box::new(Term::PLam(
                                i_name.clone(),
                                Box::new(
                                    match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                        Term::TGlue(_, _, te) => equiv_dom(&nbe_eval(&te)),
                                        other => other,
                                    },
                                ),
                            )),
                            Box::new(x_),
                        ))
                    } else {
                        // Non-trivial face: if x_ is a GlueElem with matching face, decompose.
                        match &x_ {
                            Term::TGlueElem(phi_elem, t, a)
                                if nbe_eval(phi0) == nbe_eval(phi_elem) =>
                            {
                                let a_ty = match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0)))
                                {
                                    Term::TGlue(a, _, _) => *a,
                                    other => other,
                                };
                                let tube = Term::PLam(i_name.clone(), Box::new(shift(1, 0, &*t)));
                                let hcomp = Term::THComp(
                                    Box::new(a_ty),
                                    vec![((**phi0).clone(), tube)],
                                    (*a).clone(),
                                );
                                Term::TGlueElem(
                                    Box::new((**phi0).clone()),
                                    t.clone(),
                                    Box::new(hcomp),
                                )
                            }
                            _ => Term::TTransport(
                                Box::new(Term::PLam(i_name, body.clone())),
                                Box::new(x_),
                            ),
                        }
                    }
                }

                // Lift transport: transport (λi. Lift (A i) lvl) (lift v) = lift (transport (λi. A i) v)
                (Term::TLift(_, _), Term::TLift(_, _)) => {
                    let i_name = i_name.clone();
                    match x_ {
                        Term::TLift(v, lvl) => {
                            let a_fam = Term::PLam(
                                i_name.clone(),
                                Box::new(
                                    match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                        Term::TLift(a, _) => *a,
                                        other => other,
                                    },
                                ),
                            );
                            let inner_transport = Term::TTransport(Box::new(a_fam), v);
                            Term::TLift(Box::new(inner_transport), lvl)
                        }
                        _ => Term::TTransport(
                            Box::new(Term::PLam(i_name, body.clone())),
                            Box::new(x_),
                        ),
                    }
                }

                // Lower transport: transport (λi. Lower (A i)) (lower v) = lower (transport (λi. A i) v)
                (Term::TLower(_), Term::TLower(_)) => {
                    let i_name = i_name.clone();
                    match x_ {
                        Term::TLower(v) => {
                            let a_fam = Term::PLam(
                                i_name.clone(),
                                Box::new(
                                    match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                        Term::TLower(a) => *a,
                                        other => other,
                                    },
                                ),
                            );
                            let inner_transport = Term::TTransport(Box::new(a_fam), v);
                            Term::TLower(Box::new(inner_transport))
                        }
                        _ => Term::TTransport(
                            Box::new(Term::PLam(i_name, body.clone())),
                            Box::new(x_),
                        ),
                    }
                }

                _ => Term::TTransport(
                    Box::new(Term::PLam(i_name.clone(), body.clone())),
                    Box::new(x_),
                ),
            }
        }

        p_ => Term::TTransport(Box::new(p_), Box::new(x_)),
    }
}

/// Try to match a constructor value and extract its ordinary + interval args.
/// Returns (con_name, ordinary_args, interval_args) or None.
fn match_ctor_args<'a>(
    v: &'a Value,
    expected_name: &str,
) -> Option<(&'a str, Vec<&'a Value>, Vec<&'a Value>)> {
    match v {
        Value::VCon(_, name, args) if name == expected_name => {
            Some((name.as_str(), args.iter().collect(), vec![]))
        }
        Value::VPCon(_, name, args, r) if name == expected_name => {
            Some((name.as_str(), args.iter().collect(), vec![r.as_ref()]))
        }
        Value::VSqCon(_, name, args, r, s) if name == expected_name => Some((
            name.as_str(),
            args.iter().collect(),
            vec![r.as_ref(), s.as_ref()],
        )),
        Value::VCellCon(_, name, args, ivars) if name == expected_name => {
            Some((name.as_str(), args.iter().collect(), ivars.iter().collect()))
        }
        _ => None,
    }
}

thread_local! {
    static ALL_TUBES_DEPTH: std::cell::Cell<usize> = std::cell::Cell::new(0);
}

/// Check if all tubes in the system are constant (tube @ I0 ≡ tube @ I1)
/// AND coherent with base (tube @ I0 ≡ base). When this holds, the Kan
/// operations degenerate: hcomp/comp → base, fill/hfill → constant path.
fn all_tubes_constant_and_coherent(
    globals: &Globals,
    global_offset: usize,
    sys: &DNFSystem,
    base: &Value,
) -> bool {
    // Guard against re-entrancy. The tube check quotes the base/tubes and
    // compares them with `definitionally_equal`, which re-normalizes via
    // `nbe_eval_ctx` → `quote`. When the quoted body is itself a PLam/VLam
    // whose evaluation contains an hcomp, that re-normalization re-runs this
    // check on the same structure → infinite eval↔quote recursion (see the
    // ring_demo overflow). This check is only an optimization (the
    // constant-tube shortcut); bailing out is safe — the hcomp simply stays
    // stuck instead of reducing to base.
    let depth = ALL_TUBES_DEPTH.with(|d| d.get() + 1);
    ALL_TUBES_DEPTH.with(|d| d.set(depth));
    if depth > 1 {
        ALL_TUBES_DEPTH.with(|d| d.set(depth - 1));
        return false;
    }
    let result = all_tubes_constant_and_coherent_inner(globals, global_offset, sys, base);
    ALL_TUBES_DEPTH.with(|d| d.set(depth - 1));
    result
}

fn all_tubes_constant_and_coherent_inner(
    globals: &Globals,
    global_offset: usize,
    sys: &DNFSystem,
    base: &Value,
) -> bool {
    let base_term = quote(0, globals, global_offset, base.clone());
    for (_phi, tube) in sys {
        let t0 = do_papp(
            globals,
            global_offset,
            tube.clone(),
            Value::VInterval(I::I0),
        );
        let t1 = do_papp(
            globals,
            global_offset,
            tube.clone(),
            Value::VInterval(I::I1),
        );
        let t0_term = quote(0, globals, global_offset, t0);
        let t1_term = quote(0, globals, global_offset, t1);
        // Tube must be constant: t @ I0 ≡ t @ I1
        if !definitionally_equal(&t0_term, &t1_term) {
            return false;
        }
        // Tube must be coherent with base: t @ I0 ≡ base
        if !definitionally_equal(&t0_term, &base_term) {
            return false;
        }
    }
    true
}

pub fn do_hcomp(
    globals: &Globals,
    global_offset: usize,
    a_ty: Value,
    sys: DNFSystem,
    base: Value,
) -> Value {
    // Filter out ⊥ faces
    let sys: DNFSystem = sys
        .into_iter()
        .filter(|(phi, _)| *phi != dnf_bot())
        .collect();

    // Empty system → base
    if sys.is_empty() {
        record_step(
            "hcomp-empty".into(),
            "hcomp A [] base".into(),
            value_str(globals, global_offset, &base),
        );
        return base;
    }

    // Any face = ⊤ → corresponding tube applied at i1
    for (phi, tube) in &sys {
        if *phi == dnf_top() {
            let result = do_papp(
                globals,
                global_offset,
                tube.clone(),
                Value::VInterval(I::I1),
            );
            record_step(
                "hcomp-top-face".into(),
                "hcomp A [⊤ ↦ t, ...] base".into(),
                value_str(globals, global_offset, &result),
            );
            return result;
        }
    }

    // Constant-tube shortcut: when all tubes don't depend on the interval
    // variable (tube @ i0 ≡ tube @ i1) and agree with base, the system
    // imposes no varying constraint and hcomp reduces to base.
    if all_tubes_constant_and_coherent(globals, global_offset, &sys, &base) {
        record_step(
            "hcomp-const-tube".into(),
            "hcomp A [const tubes] base".into(),
            value_str(globals, global_offset, &base),
        );
        return base;
    }

    {
        // ── Deeper hcomp reductions ──
        //
        // 1. Pi decomposition: when the base is a function (VLam) and the
        //    type is a Pi, push hcomp pointwise:
        //    hcomp (Π x:A. B) φ (λi. f i) (λx. b x)
        //    ≡  λx. hcomp (B x) φ (λi. f i x) (b x)
        //
        // 2. Sigma decomposition: when the base is a pair, decompose:
        //    hcomp (Σ x:A. B) φ (p, q) (a, b)
        //    ≡  (hcomp A φ (λi. fst (p i)) a, hcomp (B (fst result)) φ (λi. snd (p i)) b)
        //
        // 3. Constant-tube shortcut: when the tube does not depend on the
        //    interval variable (tube @ 0 ≡ tube @ 1), the hcomp reduces to
        //    tube @ 1 regardless of phi.
        match (&a_ty, &base) {
            // ── Pi decomposition ──
            (Value::VPi(arg_name, _, cod_clos), Value::VLam(_, base_clos)) => {
                let arg_var = Value::VNeutral(Neutral::NVar(0));
                let inner_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let tube_at_arg = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_apply(globals, global_offset, tube_at_i, arg_var.clone())
                            }
                            _ => do_apply(globals, global_offset, tube.clone(), arg_var.clone()),
                        };
                        (phi.clone(), tube_at_arg)
                    })
                    .collect();
                let base_at_arg = base_clos.apply(arg_var.clone());
                let cod_at_arg = cod_clos.apply(arg_var);
                let inner = do_hcomp(globals, global_offset, cod_at_arg, inner_sys, base_at_arg);
                let result = Value::VLam(
                    arg_name.clone(),
                    Closure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: {
                            let inner_term = quote(1, globals, global_offset, inner);
                            Term::TAbs(arg_name.clone(), Box::new(inner_term))
                        },
                    },
                );
                record_step(
                    "hcomp-pi".into(),
                    "hcomp (Π _ _) sys f g".into(),
                    value_str(globals, global_offset, &result),
                );
                result
            }

            // ── Sigma decomposition ──
            (Value::VSigma(_, fst_ty, snd_clos), Value::VPair(fst_base, snd_base)) => {
                let fst_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let fst_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_fst(globals, global_offset, tube_at_i)
                            }
                            _ => do_fst(globals, global_offset, tube.clone()),
                        };
                        let fst_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, fst_tube),
                            },
                        );
                        (phi.clone(), fst_tube_plam)
                    })
                    .collect();
                let fst_result = do_hcomp(
                    globals,
                    global_offset,
                    *fst_ty.clone(),
                    fst_sys,
                    (**fst_base).clone(),
                );

                let snd_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let snd_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_snd(globals, global_offset, tube_at_i)
                            }
                            _ => do_snd(globals, global_offset, tube.clone()),
                        };
                        let snd_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, snd_tube),
                            },
                        );
                        (phi.clone(), snd_tube_plam)
                    })
                    .collect();
                let snd_result = do_hcomp(
                    globals,
                    global_offset,
                    snd_clos.apply((**fst_base).clone()),
                    snd_sys,
                    (**snd_base).clone(),
                );

                let result = Value::VPair(Box::new(fst_result), Box::new(snd_result));
                record_step(
                    "hcomp-sigma".into(),
                    "hcomp (Σ _ _) sys p q".into(),
                    value_str(globals, global_offset, &result),
                );
                result
            }

            // ── Data type decomposition: push hcomp through constructor arguments ──
            (Value::VData(d_name, _), _) => {
                let (base_con, base_args, base_ivars) = match &base {
                    Value::VCon(_, name, args) => (name.clone(), args.clone(), vec![]),
                    Value::VPCon(_, name, args, r) => {
                        (name.clone(), args.clone(), vec![(**r).clone()])
                    }
                    Value::VSqCon(_, name, args, r, s) => (
                        name.clone(),
                        args.clone(),
                        vec![(**r).clone(), (**s).clone()],
                    ),
                    Value::VCellCon(_, name, args, ivars) => {
                        (name.clone(), args.clone(), ivars.clone())
                    }
                    _ => return Value::VHComp(Box::new(a_ty), sys, Box::new(base)),
                };

                let dts = current_dts();
                let dt = match dts.iter().find(|dt| dt.name == *d_name) {
                    Some(dt) => dt.clone(),
                    None => return Value::VHComp(Box::new(a_ty), sys, Box::new(base)),
                };

                let arg_tys = match dt
                    .find_con(&base_con)
                    .map(|s| s.arg_tys.clone())
                    .or_else(|| dt.find_pcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_sqcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_cellcon(&base_con).map(|s| s.arg_tys.clone()))
                {
                    Some(tys) => tys,
                    None => return Value::VHComp(Box::new(a_ty), sys, Box::new(base)),
                };

                let n = arg_tys.len();
                if n == 0 {
                    return base;
                }

                let mut per_arg_tubes: Vec<Vec<(DNF, Value)>> = vec![vec![]; n];
                for (phi, tube) in &sys {
                    let tube_val = match tube {
                        Value::VPLam(_, iclos) => {
                            let formal_i = Value::VIntervalVar(0);
                            iclos.apply_interval_value(formal_i)
                        }
                        _ => tube.clone(),
                    };

                    if let Some((_, tube_args, _)) = match_ctor_args(&tube_val, &base_con) {
                        if tube_args.len() == n {
                            for (k, tube_arg) in tube_args.iter().enumerate() {
                                let tube_arg_plam = Value::VPLam(
                                    "_".to_string(),
                                    IClosure {
                                        env: Scope::empty(),
                                        globals: globals.clone(),
                                        global_offset,
                                        body: quote(1, globals, global_offset, (*tube_arg).clone()),
                                    },
                                );
                                per_arg_tubes[k].push((phi.clone(), tube_arg_plam));
                            }
                        } else {
                            return Value::VHComp(Box::new(a_ty), sys, Box::new(base));
                        }
                    } else {
                        return Value::VHComp(Box::new(a_ty), sys, Box::new(base));
                    }
                }

                let mut result_args: Vec<Value> = Vec::new();
                for k in 0..n {
                    let mut ty_shifted = arg_tys[k].clone();
                    for j in (0..=k).rev() {
                        ty_shifted = shift(1, j as i32, &ty_shifted);
                    }
                    for j in 0..k {
                        let arg_term = quote(0, globals, global_offset, result_args[j].clone());
                        ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
                    }
                    let arg_ty = eval_nbe(&Scope::empty(), globals, global_offset, &ty_shifted);
                    let arg_result = do_hcomp(
                        globals,
                        global_offset,
                        arg_ty,
                        per_arg_tubes[k].clone(),
                        base_args[k].clone(),
                    );
                    result_args.push(arg_result);
                }

                match &base {
                    Value::VCon(_, _, _) => {
                        Value::VCon(d_name.clone(), base_con.clone(), result_args)
                    }
                    Value::VPCon(_, _, _, _) => Value::VPCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_args,
                        Box::new(base_ivars[0].clone()),
                    ),
                    Value::VSqCon(_, _, _, _, _) => Value::VSqCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_args,
                        Box::new(base_ivars[0].clone()),
                        Box::new(base_ivars[1].clone()),
                    ),
                    Value::VCellCon(_, _, _, _) => {
                        Value::VCellCon(d_name.clone(), base_con.clone(), result_args, base_ivars)
                    }
                    _ => unreachable!(),
                }
            }

            // ── Default: stuck hcomp ──
            _ => Value::VHComp(Box::new(a_ty), sys, Box::new(base)),
        }
    }
}

pub fn do_comp(
    globals: &Globals,
    global_offset: usize,
    a_fam: Value,
    sys: DNFSystem,
    base: Value,
) -> Value {
    // Filter out ⊥ faces
    let sys: DNFSystem = sys
        .into_iter()
        .filter(|(phi, _)| *phi != dnf_bot())
        .collect();

    // Empty system → base
    if sys.is_empty() {
        record_step(
            "comp-empty".into(),
            "comp _ [] base".into(),
            value_str(globals, global_offset, &base),
        );
        return base;
    }

    // Any face = ⊤ → corresponding tube applied at i1
    for (phi, tube) in &sys {
        if *phi == dnf_top() {
            let result = do_papp(
                globals,
                global_offset,
                tube.clone(),
                Value::VInterval(I::I1),
            );
            record_step(
                "comp-top-face".into(),
                "comp _ [⊤ ↦ t, ...] base".into(),
                value_str(globals, global_offset, &result),
            );
            return result;
        }
    }

    // Constant-tube shortcut
    if all_tubes_constant_and_coherent(globals, global_offset, &sys, &base) {
        record_step(
            "comp-const-tube".into(),
            "comp A [const tubes] base".into(),
            value_str(globals, global_offset, &base),
        );
        return base;
    }

    {
        match (&a_fam, &base) {
            // ── Pi decomposition ──
            (Value::VPi(arg_name, _, cod_clos), Value::VLam(_, base_clos)) => {
                let arg_var = Value::VNeutral(Neutral::NVar(0));
                let inner_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let tube_at_arg = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_apply(globals, global_offset, tube_at_i, arg_var.clone())
                            }
                            _ => do_apply(globals, global_offset, tube.clone(), arg_var.clone()),
                        };
                        (phi.clone(), tube_at_arg)
                    })
                    .collect();
                let base_at_arg = base_clos.apply(arg_var.clone());
                let cod_at_arg = cod_clos.apply(arg_var);
                let inner = do_comp(globals, global_offset, cod_at_arg, inner_sys, base_at_arg);
                let result = Value::VLam(
                    arg_name.clone(),
                    Closure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: {
                            let inner_term = quote(1, globals, global_offset, inner);
                            Term::TAbs(arg_name.clone(), Box::new(inner_term))
                        },
                    },
                );
                record_step(
                    "comp-pi".into(),
                    "comp (Π _ _) sys f g".into(),
                    value_str(globals, global_offset, &result),
                );
                result
            }

            // ── Sigma decomposition ──
            (Value::VSigma(_, fst_ty, snd_clos), Value::VPair(fst_base, snd_base)) => {
                let fst_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let fst_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_fst(globals, global_offset, tube_at_i)
                            }
                            _ => do_fst(globals, global_offset, tube.clone()),
                        };
                        let fst_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, fst_tube),
                            },
                        );
                        (phi.clone(), fst_tube_plam)
                    })
                    .collect();
                let fst_result = do_comp(
                    globals,
                    global_offset,
                    *fst_ty.clone(),
                    fst_sys,
                    (**fst_base).clone(),
                );

                let snd_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let snd_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_snd(globals, global_offset, tube_at_i)
                            }
                            _ => do_snd(globals, global_offset, tube.clone()),
                        };
                        let snd_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, snd_tube),
                            },
                        );
                        (phi.clone(), snd_tube_plam)
                    })
                    .collect();
                let snd_result = do_comp(
                    globals,
                    global_offset,
                    snd_clos.apply((**fst_base).clone()),
                    snd_sys,
                    (**snd_base).clone(),
                );

                let result = Value::VPair(Box::new(fst_result), Box::new(snd_result));
                record_step(
                    "comp-sigma".into(),
                    "comp (Σ _ _) sys p q".into(),
                    value_str(globals, global_offset, &result),
                );
                result
            }

            // ── Data type decomposition: push comp through constructor arguments ──
            (Value::VData(d_name, _), _) => {
                let (base_con, base_args, base_ivars) = match &base {
                    Value::VCon(_, name, args) => (name.clone(), args.clone(), vec![]),
                    Value::VPCon(_, name, args, r) => {
                        (name.clone(), args.clone(), vec![(**r).clone()])
                    }
                    Value::VSqCon(_, name, args, r, s) => (
                        name.clone(),
                        args.clone(),
                        vec![(**r).clone(), (**s).clone()],
                    ),
                    Value::VCellCon(_, name, args, ivars) => {
                        (name.clone(), args.clone(), ivars.clone())
                    }
                    _ => {
                        let result = Value::VComp(Box::new(a_fam), sys, Box::new(base));
                        record_step(
                            "comp-stuck".into(),
                            "comp _ _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                };

                let dts = current_dts();
                let dt = match dts.iter().find(|dt| dt.name == *d_name) {
                    Some(dt) => dt.clone(),
                    None => {
                        let result = Value::VComp(Box::new(a_fam), sys, Box::new(base));
                        record_step(
                            "comp-stuck".into(),
                            "comp _ _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                };

                let arg_tys = dt
                    .find_con(&base_con)
                    .map(|s| s.arg_tys.clone())
                    .or_else(|| dt.find_pcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_sqcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_cellcon(&base_con).map(|s| s.arg_tys.clone()));
                let arg_tys = match arg_tys {
                    Some(tys) => tys,
                    None => {
                        let result = Value::VComp(Box::new(a_fam), sys, Box::new(base));
                        record_step(
                            "comp-stuck".into(),
                            "comp _ _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                };

                let n = arg_tys.len();
                if n == 0 {
                    return base;
                }

                let mut per_arg_tubes: Vec<Vec<(DNF, Value)>> = vec![vec![]; n];
                for (phi, tube) in &sys {
                    let tube_val = match tube {
                        Value::VPLam(_, iclos) => {
                            let formal_i = Value::VIntervalVar(0);
                            iclos.apply_interval_value(formal_i)
                        }
                        _ => tube.clone(),
                    };

                    if let Some((_, tube_args, _)) = match_ctor_args(&tube_val, &base_con) {
                        if tube_args.len() == n {
                            for (k, tube_arg) in tube_args.iter().enumerate() {
                                let tube_arg_plam = Value::VPLam(
                                    "_".to_string(),
                                    IClosure {
                                        env: Scope::empty(),
                                        globals: globals.clone(),
                                        global_offset,
                                        body: quote(1, globals, global_offset, (*tube_arg).clone()),
                                    },
                                );
                                per_arg_tubes[k].push((phi.clone(), tube_arg_plam));
                            }
                        } else {
                            let result = Value::VComp(Box::new(a_fam), sys, Box::new(base));
                            record_step(
                                "comp-stuck".into(),
                                "comp _ _ _ _".into(),
                                value_str(globals, global_offset, &result),
                            );
                            return result;
                        }
                    } else {
                        let result = Value::VComp(Box::new(a_fam), sys, Box::new(base));
                        record_step(
                            "comp-stuck".into(),
                            "comp _ _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                }

                let mut result_args: Vec<Value> = Vec::new();
                for k in 0..n {
                    let mut ty_shifted = arg_tys[k].clone();
                    for j in (0..=k).rev() {
                        ty_shifted = shift(1, j as i32, &ty_shifted);
                    }
                    for j in 0..k {
                        let arg_term = quote(0, globals, global_offset, result_args[j].clone());
                        ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
                    }
                    let arg_ty = eval_nbe(&Scope::empty(), globals, global_offset, &ty_shifted);
                    let arg_result = do_comp(
                        globals,
                        global_offset,
                        arg_ty,
                        per_arg_tubes[k].clone(),
                        base_args[k].clone(),
                    );
                    result_args.push(arg_result);
                }

                let result = match &base {
                    Value::VCon(_, _, _) => {
                        Value::VCon(d_name.clone(), base_con.clone(), result_args)
                    }
                    Value::VPCon(_, _, _, _) => Value::VPCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_args,
                        Box::new(base_ivars[0].clone()),
                    ),
                    Value::VSqCon(_, _, _, _, _) => Value::VSqCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_args,
                        Box::new(base_ivars[0].clone()),
                        Box::new(base_ivars[1].clone()),
                    ),
                    Value::VCellCon(_, _, _, _) => {
                        Value::VCellCon(d_name.clone(), base_con.clone(), result_args, base_ivars)
                    }
                    _ => unreachable!(),
                };
                record_step(
                    "comp-data".into(),
                    format!("comp (λi. {}) ({} ...)", d_name, base_con),
                    value_str(globals, global_offset, &result),
                );
                result
            }

            _ => {
                let result = Value::VComp(Box::new(a_fam), sys, Box::new(base));
                record_step(
                    "comp-stuck".into(),
                    "comp _ _ _ _".into(),
                    value_str(globals, global_offset, &result),
                );
                result
            }
        }
    }
}

pub fn do_fill(
    globals: &Globals,
    global_offset: usize,
    a_fam: Value,
    sys: DNFSystem,
    base: Value,
) -> Value {
    // Filter out ⊥ faces
    let sys: DNFSystem = sys
        .into_iter()
        .filter(|(phi, _)| *phi != dnf_bot())
        .collect();

    // Empty system → constant path
    if sys.is_empty() {
        let result = Value::VPLam(
            "j".to_string(),
            IClosure {
                env: Scope::empty(),
                globals: globals.clone(),
                global_offset,
                body: quote(1, globals, global_offset, base.clone()),
            },
        );
        record_step(
            "fill-empty".into(),
            "fill _ [] base".into(),
            value_str(globals, global_offset, &result),
        );
        return result;
    }

    // Any face = ⊤ → corresponding tube
    for (phi, tube) in &sys {
        if *phi == dnf_top() {
            let result = tube.clone();
            record_step(
                "fill-top-face".into(),
                "fill _ [⊤ ↦ t, ...] base".into(),
                value_str(globals, global_offset, &result),
            );
            return result;
        }
    }

    // Constant-tube shortcut: fill produces a constant path when tubes don't vary
    if all_tubes_constant_and_coherent(globals, global_offset, &sys, &base) {
        let result = Value::VPLam(
            "j".to_string(),
            IClosure {
                env: Scope::empty(),
                globals: globals.clone(),
                global_offset,
                body: quote(1, globals, global_offset, base.clone()),
            },
        );
        record_step(
            "fill-const-tube".into(),
            "fill A [const tubes] base".into(),
            value_str(globals, global_offset, &result),
        );
        return result;
    }

    // ── Decompose fill for Pi/Sigma/Data types ──
    // fill returns a PATH, so decomposition wraps inner fills with PApp at interval variable j.
    // The IClosure body binds j at level 0; inside TAbs, j is at TV(1).
    {
        match (&a_fam, &base) {
            // ── Pi decomposition ──
            // fill (Π x:A. B) sys (λx. f x) = λj. λx. fill B [sys x] (f x) @ j
            (Value::VPi(arg_name, _, cod_clos), Value::VLam(_, base_clos)) => {
                let arg_var = Value::VNeutral(Neutral::NVar(0));
                let inner_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let tube_at_arg = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_apply(globals, global_offset, tube_at_i, arg_var.clone())
                            }
                            _ => do_apply(globals, global_offset, tube.clone(), arg_var.clone()),
                        };
                        (phi.clone(), tube_at_arg)
                    })
                    .collect();
                let base_at_arg = base_clos.apply(arg_var.clone());
                let cod_at_arg = cod_clos.apply(arg_var);
                let inner = do_fill(globals, global_offset, cod_at_arg, inner_sys, base_at_arg);
                let inner_term = quote(1, globals, global_offset, inner);
                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: Term::TAbs(
                            arg_name.clone(),
                            Box::new(Term::PApp(Box::new(inner_term), Box::new(Term::TVar(1)))),
                        ),
                    },
                );
                record_step(
                    "fill-pi".into(),
                    "fill (Π _ _) sys f".into(),
                    value_str(globals, global_offset, &result),
                );
                result
            }

            // ── Sigma decomposition ──
            // fill (Σ x:A. B) sys (a, b) = λj. (fill A [fst_sys] a @ j, fill B [snd_sys] b @ j)
            (Value::VSigma(_, fst_ty, snd_clos), Value::VPair(fst_base, snd_base)) => {
                let fst_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let fst_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_fst(globals, global_offset, tube_at_i)
                            }
                            _ => do_fst(globals, global_offset, tube.clone()),
                        };
                        let fst_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, fst_tube),
                            },
                        );
                        (phi.clone(), fst_tube_plam)
                    })
                    .collect();
                let fst_fill = do_fill(
                    globals,
                    global_offset,
                    *fst_ty.clone(),
                    fst_sys,
                    (**fst_base).clone(),
                );

                let snd_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let snd_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_snd(globals, global_offset, tube_at_i)
                            }
                            _ => do_snd(globals, global_offset, tube.clone()),
                        };
                        let snd_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, snd_tube),
                            },
                        );
                        (phi.clone(), snd_tube_plam)
                    })
                    .collect();
                let snd_fill = do_fill(
                    globals,
                    global_offset,
                    snd_clos.apply((**fst_base).clone()),
                    snd_sys,
                    (**snd_base).clone(),
                );

                let fst_fill_term = quote(1, globals, global_offset, fst_fill);
                let snd_fill_term = quote(1, globals, global_offset, snd_fill);
                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: Term::TPair(
                            Box::new(Term::PApp(Box::new(fst_fill_term), Box::new(Term::TVar(1)))),
                            Box::new(Term::PApp(Box::new(snd_fill_term), Box::new(Term::TVar(1)))),
                        ),
                    },
                );
                record_step(
                    "fill-sigma".into(),
                    "fill (Σ _ _) sys p".into(),
                    value_str(globals, global_offset, &result),
                );
                result
            }

            // ── Data type decomposition: push fill through constructor arguments ──
            (Value::VData(d_name, _), _) => {
                let (base_con, base_args, base_ivars) = match &base {
                    Value::VCon(_, name, args) => (name.clone(), args.clone(), vec![]),
                    Value::VPCon(_, name, args, r) => {
                        (name.clone(), args.clone(), vec![(**r).clone()])
                    }
                    Value::VSqCon(_, name, args, r, s) => (
                        name.clone(),
                        args.clone(),
                        vec![(**r).clone(), (**s).clone()],
                    ),
                    Value::VCellCon(_, name, args, ivars) => {
                        (name.clone(), args.clone(), ivars.clone())
                    }
                    _ => {
                        let result = Value::VFill(Box::new(a_fam), sys, Box::new(base));
                        record_step(
                            "fill-stuck".into(),
                            "fill _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                };

                let dts = current_dts();
                let dt = match dts.iter().find(|dt| dt.name == *d_name) {
                    Some(dt) => dt.clone(),
                    None => {
                        let result = Value::VFill(Box::new(a_fam), sys, Box::new(base));
                        record_step(
                            "fill-stuck".into(),
                            "fill _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                };

                let arg_tys = match dt
                    .find_con(&base_con)
                    .map(|s| s.arg_tys.clone())
                    .or_else(|| dt.find_pcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_sqcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_cellcon(&base_con).map(|s| s.arg_tys.clone()))
                {
                    Some(tys) => tys,
                    None => {
                        let result = Value::VFill(Box::new(a_fam), sys, Box::new(base));
                        record_step(
                            "fill-stuck".into(),
                            "fill _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                };

                let n = arg_tys.len();
                if n == 0 {
                    // No arguments: fill is a constant path
                    let result = Value::VPLam(
                        "j".to_string(),
                        IClosure {
                            env: Scope::empty(),
                            globals: globals.clone(),
                            global_offset,
                            body: quote(1, globals, global_offset, base.clone()),
                        },
                    );
                    record_step(
                        "fill-data-empty".into(),
                        "fill D [] c".into(),
                        value_str(globals, global_offset, &result),
                    );
                    return result;
                }

                let mut per_arg_tubes: Vec<Vec<(DNF, Value)>> = vec![vec![]; n];
                for (phi, tube) in &sys {
                    let tube_val = match tube {
                        Value::VPLam(_, iclos) => {
                            let formal_i = Value::VIntervalVar(0);
                            iclos.apply_interval_value(formal_i)
                        }
                        _ => tube.clone(),
                    };

                    if let Some((_, tube_args, _)) = match_ctor_args(&tube_val, &base_con) {
                        if tube_args.len() == n {
                            for (k, tube_arg) in tube_args.iter().enumerate() {
                                let tube_arg_plam = Value::VPLam(
                                    "_".to_string(),
                                    IClosure {
                                        env: Scope::empty(),
                                        globals: globals.clone(),
                                        global_offset,
                                        body: quote(1, globals, global_offset, (*tube_arg).clone()),
                                    },
                                );
                                per_arg_tubes[k].push((phi.clone(), tube_arg_plam));
                            }
                        } else {
                            let result = Value::VFill(Box::new(a_fam), sys, Box::new(base));
                            record_step(
                                "fill-stuck".into(),
                                "fill _ _ _".into(),
                                value_str(globals, global_offset, &result),
                            );
                            return result;
                        }
                    } else {
                        let result = Value::VFill(Box::new(a_fam), sys, Box::new(base));
                        record_step(
                            "fill-stuck".into(),
                            "fill _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                }

                let mut result_arg_terms: Vec<Term> = Vec::new();
                for k in 0..n {
                    let mut ty_shifted = arg_tys[k].clone();
                    for j in (0..=k).rev() {
                        ty_shifted = shift(1, j as i32, &ty_shifted);
                    }
                    for j in 0..k {
                        let arg_term = quote(0, globals, global_offset, base_args[j].clone());
                        ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
                    }
                    let arg_ty = eval_nbe(&Scope::empty(), globals, global_offset, &ty_shifted);
                    let arg_fill = do_fill(
                        globals,
                        global_offset,
                        arg_ty,
                        per_arg_tubes[k].clone(),
                        base_args[k].clone(),
                    );
                    let arg_fill_term = quote(1, globals, global_offset, arg_fill);
                    result_arg_terms
                        .push(Term::PApp(Box::new(arg_fill_term), Box::new(Term::TVar(1))));
                }

                let con_term = match &base {
                    Value::VCon(_, _, _) => {
                        Term::TCon(d_name.clone(), base_con.clone(), result_arg_terms)
                    }
                    Value::VPCon(_, _, _, _) => Term::TPCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_arg_terms,
                        Box::new(quote(1, globals, global_offset, base_ivars[0].clone())),
                    ),
                    Value::VSqCon(_, _, _, _, _) => Term::TSqCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_arg_terms,
                        Box::new(quote(1, globals, global_offset, base_ivars[0].clone())),
                        Box::new(quote(1, globals, global_offset, base_ivars[1].clone())),
                    ),
                    Value::VCellCon(_, _, _, _) => {
                        let ivar_terms: Vec<Term> = base_ivars
                            .iter()
                            .map(|v| quote(1, globals, global_offset, v.clone()))
                            .collect();
                        Term::TCellCon(
                            d_name.clone(),
                            base_con.clone(),
                            result_arg_terms,
                            ivar_terms,
                        )
                    }
                    _ => unreachable!(),
                };

                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: con_term,
                    },
                );
                record_step(
                    "fill-data".into(),
                    format!("fill (λi. {}) ({} ...)", d_name, base_con),
                    value_str(globals, global_offset, &result),
                );
                result
            }

            // ── Default: stuck fill ──
            _ => {
                let result = Value::VFill(Box::new(a_fam), sys, Box::new(base));
                record_step(
                    "fill-stuck".into(),
                    "fill _ _ _".into(),
                    value_str(globals, global_offset, &result),
                );
                result
            }
        }
    }
}

pub fn do_hfill(
    globals: &Globals,
    global_offset: usize,
    a_ty: Value,
    sys: DNFSystem,
    base: Value,
) -> Value {
    // Filter out ⊥ faces
    let sys: DNFSystem = sys
        .into_iter()
        .filter(|(phi, _)| *phi != dnf_bot())
        .collect();

    // Empty system → constant path
    if sys.is_empty() {
        let result = Value::VPLam(
            "j".to_string(),
            IClosure {
                env: Scope::empty(),
                globals: globals.clone(),
                global_offset,
                body: quote(1, globals, global_offset, base.clone()),
            },
        );
        record_step(
            "hfill-empty".into(),
            "hfill _ [] base".into(),
            value_str(globals, global_offset, &result),
        );
        return result;
    }

    // Any face = ⊤ → corresponding tube
    for (phi, tube) in &sys {
        if *phi == dnf_top() {
            let result = tube.clone();
            record_step(
                "hfill-top-face".into(),
                "hfill _ [⊤ ↦ t, ...] base".into(),
                value_str(globals, global_offset, &result),
            );
            return result;
        }
    }

    // Constant-tube shortcut: hfill produces a constant path when tubes don't vary
    if all_tubes_constant_and_coherent(globals, global_offset, &sys, &base) {
        let result = Value::VPLam(
            "j".to_string(),
            IClosure {
                env: Scope::empty(),
                globals: globals.clone(),
                global_offset,
                body: quote(1, globals, global_offset, base.clone()),
            },
        );
        record_step(
            "hfill-const-tube".into(),
            "hfill A [const tubes] base".into(),
            value_str(globals, global_offset, &result),
        );
        return result;
    }

    // ── Decompose hfill for Pi/Sigma/Data types ──
    // hfill returns a PATH, so decomposition wraps inner hfills with PApp at interval variable j.
    {
        match (&a_ty, &base) {
            // ── Pi decomposition ──
            // hfill (Π x:A. B) sys (λx. f x) = λj. λx. hfill B [sys x] (f x) @ j
            (Value::VPi(arg_name, _, cod_clos), Value::VLam(_, base_clos)) => {
                let arg_var = Value::VNeutral(Neutral::NVar(0));
                let inner_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let tube_at_arg = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_apply(globals, global_offset, tube_at_i, arg_var.clone())
                            }
                            _ => do_apply(globals, global_offset, tube.clone(), arg_var.clone()),
                        };
                        (phi.clone(), tube_at_arg)
                    })
                    .collect();
                let base_at_arg = base_clos.apply(arg_var.clone());
                let cod_at_arg = cod_clos.apply(arg_var);
                let inner = do_hfill(globals, global_offset, cod_at_arg, inner_sys, base_at_arg);
                let inner_term = quote(1, globals, global_offset, inner);
                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: Term::TAbs(
                            arg_name.clone(),
                            Box::new(Term::PApp(Box::new(inner_term), Box::new(Term::TVar(1)))),
                        ),
                    },
                );
                record_step(
                    "hfill-pi".into(),
                    "hfill (Π _ _) sys f".into(),
                    value_str(globals, global_offset, &result),
                );
                result
            }

            // ── Sigma decomposition ──
            // hfill (Σ x:A. B) sys (a, b) = λj. (hfill A [fst_sys] a @ j, hfill B [snd_sys] b @ j)
            (Value::VSigma(_, fst_ty, snd_clos), Value::VPair(fst_base, snd_base)) => {
                let fst_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let fst_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_fst(globals, global_offset, tube_at_i)
                            }
                            _ => do_fst(globals, global_offset, tube.clone()),
                        };
                        let fst_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, fst_tube),
                            },
                        );
                        (phi.clone(), fst_tube_plam)
                    })
                    .collect();
                let fst_fill = do_hfill(
                    globals,
                    global_offset,
                    *fst_ty.clone(),
                    fst_sys,
                    (**fst_base).clone(),
                );

                let snd_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let snd_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i);
                                do_snd(globals, global_offset, tube_at_i)
                            }
                            _ => do_snd(globals, global_offset, tube.clone()),
                        };
                        let snd_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, snd_tube),
                            },
                        );
                        (phi.clone(), snd_tube_plam)
                    })
                    .collect();
                let snd_fill = do_hfill(
                    globals,
                    global_offset,
                    snd_clos.apply((**fst_base).clone()),
                    snd_sys,
                    (**snd_base).clone(),
                );

                let fst_fill_term = quote(1, globals, global_offset, fst_fill);
                let snd_fill_term = quote(1, globals, global_offset, snd_fill);
                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: Term::TPair(
                            Box::new(Term::PApp(Box::new(fst_fill_term), Box::new(Term::TVar(1)))),
                            Box::new(Term::PApp(Box::new(snd_fill_term), Box::new(Term::TVar(1)))),
                        ),
                    },
                );
                record_step(
                    "hfill-sigma".into(),
                    "hfill (Σ _ _) sys p".into(),
                    value_str(globals, global_offset, &result),
                );
                result
            }

            // ── Data type decomposition: push hfill through constructor arguments ──
            (Value::VData(d_name, _), _) => {
                let (base_con, base_args, base_ivars) = match &base {
                    Value::VCon(_, name, args) => (name.clone(), args.clone(), vec![]),
                    Value::VPCon(_, name, args, r) => {
                        (name.clone(), args.clone(), vec![(**r).clone()])
                    }
                    Value::VSqCon(_, name, args, r, s) => (
                        name.clone(),
                        args.clone(),
                        vec![(**r).clone(), (**s).clone()],
                    ),
                    Value::VCellCon(_, name, args, ivars) => {
                        (name.clone(), args.clone(), ivars.clone())
                    }
                    _ => {
                        let result = Value::VHFill(Box::new(a_ty), sys, Box::new(base));
                        record_step(
                            "hfill-stuck".into(),
                            "hfill _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                };

                let dts = current_dts();
                let dt = match dts.iter().find(|dt| dt.name == *d_name) {
                    Some(dt) => dt.clone(),
                    None => {
                        let result = Value::VHFill(Box::new(a_ty), sys, Box::new(base));
                        record_step(
                            "hfill-stuck".into(),
                            "hfill _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                };

                let arg_tys = match dt
                    .find_con(&base_con)
                    .map(|s| s.arg_tys.clone())
                    .or_else(|| dt.find_pcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_sqcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_cellcon(&base_con).map(|s| s.arg_tys.clone()))
                {
                    Some(tys) => tys,
                    None => {
                        let result = Value::VHFill(Box::new(a_ty), sys, Box::new(base));
                        record_step(
                            "hfill-stuck".into(),
                            "hfill _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                };

                let n = arg_tys.len();
                if n == 0 {
                    let result = Value::VPLam(
                        "j".to_string(),
                        IClosure {
                            env: Scope::empty(),
                            globals: globals.clone(),
                            global_offset,
                            body: quote(1, globals, global_offset, base.clone()),
                        },
                    );
                    record_step(
                        "hfill-data-empty".into(),
                        "hfill D [] c".into(),
                        value_str(globals, global_offset, &result),
                    );
                    return result;
                }

                let mut per_arg_tubes: Vec<Vec<(DNF, Value)>> = vec![vec![]; n];
                for (phi, tube) in &sys {
                    let tube_val = match tube {
                        Value::VPLam(_, iclos) => {
                            let formal_i = Value::VIntervalVar(0);
                            iclos.apply_interval_value(formal_i)
                        }
                        _ => tube.clone(),
                    };

                    if let Some((_, tube_args, _)) = match_ctor_args(&tube_val, &base_con) {
                        if tube_args.len() == n {
                            for (k, tube_arg) in tube_args.iter().enumerate() {
                                let tube_arg_plam = Value::VPLam(
                                    "_".to_string(),
                                    IClosure {
                                        env: Scope::empty(),
                                        globals: globals.clone(),
                                        global_offset,
                                        body: quote(1, globals, global_offset, (*tube_arg).clone()),
                                    },
                                );
                                per_arg_tubes[k].push((phi.clone(), tube_arg_plam));
                            }
                        } else {
                            let result = Value::VHFill(Box::new(a_ty), sys, Box::new(base));
                            record_step(
                                "hfill-stuck".into(),
                                "hfill _ _ _".into(),
                                value_str(globals, global_offset, &result),
                            );
                            return result;
                        }
                    } else {
                        let result = Value::VHFill(Box::new(a_ty), sys, Box::new(base));
                        record_step(
                            "hfill-stuck".into(),
                            "hfill _ _ _".into(),
                            value_str(globals, global_offset, &result),
                        );
                        return result;
                    }
                }

                let mut result_arg_terms: Vec<Term> = Vec::new();
                for k in 0..n {
                    let mut ty_shifted = arg_tys[k].clone();
                    for j in (0..=k).rev() {
                        ty_shifted = shift(1, j as i32, &ty_shifted);
                    }
                    for j in 0..k {
                        let arg_term = quote(0, globals, global_offset, base_args[j].clone());
                        ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
                    }
                    let arg_ty = eval_nbe(&Scope::empty(), globals, global_offset, &ty_shifted);
                    let arg_fill = do_hfill(
                        globals,
                        global_offset,
                        arg_ty,
                        per_arg_tubes[k].clone(),
                        base_args[k].clone(),
                    );
                    let arg_fill_term = quote(1, globals, global_offset, arg_fill);
                    result_arg_terms
                        .push(Term::PApp(Box::new(arg_fill_term), Box::new(Term::TVar(1))));
                }

                let con_term = match &base {
                    Value::VCon(_, _, _) => {
                        Term::TCon(d_name.clone(), base_con.clone(), result_arg_terms)
                    }
                    Value::VPCon(_, _, _, _) => Term::TPCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_arg_terms,
                        Box::new(quote(1, globals, global_offset, base_ivars[0].clone())),
                    ),
                    Value::VSqCon(_, _, _, _, _) => Term::TSqCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_arg_terms,
                        Box::new(quote(1, globals, global_offset, base_ivars[0].clone())),
                        Box::new(quote(1, globals, global_offset, base_ivars[1].clone())),
                    ),
                    Value::VCellCon(_, _, _, _) => {
                        let ivar_terms: Vec<Term> = base_ivars
                            .iter()
                            .map(|v| quote(1, globals, global_offset, v.clone()))
                            .collect();
                        Term::TCellCon(
                            d_name.clone(),
                            base_con.clone(),
                            result_arg_terms,
                            ivar_terms,
                        )
                    }
                    _ => unreachable!(),
                };

                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: con_term,
                    },
                );
                record_step(
                    "hfill-data".into(),
                    format!("hfill (λi. {}) ({} ...)", d_name, base_con),
                    value_str(globals, global_offset, &result),
                );
                result
            }

            // ── Default: stuck hfill ──
            _ => {
                let result = Value::VHFill(Box::new(a_ty), sys, Box::new(base));
                record_step(
                    "hfill-stuck".into(),
                    "hfill _ _ _".into(),
                    value_str(globals, global_offset, &result),
                );
                result
            }
        }
    }
}

thread_local! {
    static QUOTE_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Quoting can also diverge independently of `eval_nbe`: re-quoting a lambda
/// whose body re-references the same global value grows the quote recursion one
/// `TAbs` layer per cycle (`quote` -> `Closure::apply` -> `eval_nbe` -> `quote`),
/// while each `eval_nbe` call returns immediately. Cap the quote depth so such
/// values produce a finite (stuck) term instead of overflowing the stack. The
/// placeholder is an unbound `TVar(size)` (far beyond any real context), which
/// surfaces as an error downstream rather than silently passing. The cap must be
/// low enough to fit the debug-build stack frames on the smallest thread stack
/// the normalizer may run on (test threads default to 2 MiB).
const QUOTE_MAX_DEPTH: usize = 200;

pub fn quote(size: usize, globals: &Globals, global_offset: usize, v: Value) -> Term {
    let n = QUOTE_DEPTH.with(|c| {
        let d = c.get() + 1;
        c.set(d);
        d
    });
    if n > QUOTE_MAX_DEPTH {
        QUOTE_DEPTH.with(|c| c.set(n - 1));
        return Term::TVar(size as i32);
    }
    let r = quote_inner(size, globals, global_offset, v);
    QUOTE_DEPTH.with(|c| c.set(n - 1));
    r
}

fn quote_inner(size: usize, globals: &Globals, global_offset: usize, v: Value) -> Term {
    match v {
        Value::VNeutral(n) => quote_neutral(size, globals, global_offset, n),
        Value::VLam(x, clos) => Term::TAbs(
            x,
            Box::new(quote(
                size + 1,
                globals,
                global_offset,
                clos.apply(Value::VNeutral(Neutral::NVar(size))),
            )),
        ),
        Value::VApp(f, a) => Term::TApp(
            Box::new(quote(size, globals, global_offset, *f)),
            Box::new(quote(size, globals, global_offset, *a)),
        ),
        Value::VPi(x, a, b) => Term::TPi(
            x,
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(quote(
                size + 1,
                globals,
                global_offset,
                b.apply(Value::VNeutral(Neutral::NVar(size))),
            )),
        ),
        Value::VSigma(x, a, b) => Term::TSigma(
            x,
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(quote(
                size + 1,
                globals,
                global_offset,
                b.apply(Value::VNeutral(Neutral::NVar(size))),
            )),
        ),
        Value::VPair(a, b) => Term::TPair(
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(quote(size, globals, global_offset, *b)),
        ),
        Value::VFst(p) => Term::TFst(Box::new(quote(size, globals, global_offset, *p))),
        Value::VSnd(p) => Term::TSnd(Box::new(quote(size, globals, global_offset, *p))),
        Value::VProj(field, r) => {
            Term::TProj(field, Box::new(quote(size, globals, global_offset, *r)))
        }
        Value::VRecordUpdate(r, updates) => Term::TRecordUpdate(
            Box::new(quote(size, globals, global_offset, *r)),
            updates
                .iter()
                .map(|(f, e)| (f.clone(), quote(size, globals, global_offset, e.clone())))
                .collect(),
        ),
        Value::VPath(a, u, v) => Term::TPath(
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(quote(size, globals, global_offset, *u)),
            Box::new(quote(size, globals, global_offset, *v)),
        ),
        Value::VPLam(x, clos) => Term::PLam(
            x,
            Box::new(quote(
                size + 1,
                globals,
                global_offset,
                clos.apply_i_var(size),
            )),
        ),
        Value::VPApp(p, r) => Term::PApp(
            Box::new(quote(size, globals, global_offset, *p)),
            Box::new(quote(size, globals, global_offset, *r)),
        ),
        Value::VUniv(n) => Term::TUniv(n),
        Value::VProp => Term::TProp,
        Value::VSSet => Term::TSSet,
        Value::VLift(a, lvl) => Term::TLift(Box::new(quote(size, globals, global_offset, *a)), lvl),
        Value::VLower(a) => Term::TLower(Box::new(quote(size, globals, global_offset, *a))),
        Value::VIntervalTy => Term::TIntervalTy,
        Value::VInterval(i) => Term::TInterval(i),
        Value::VIntervalVar(level) => level_to_var(size, level),
        Value::VCube(c) => Term::TCube(c),
        Value::VData(d, params) => Term::TData(
            d,
            params
                .into_iter()
                .map(|p| quote(size, globals, global_offset, p))
                .collect(),
        ),
        Value::VCon(d, c, args) => Term::TCon(
            d,
            c,
            args.into_iter()
                .map(|a| quote(size, globals, global_offset, a))
                .collect(),
        ),
        Value::VPCon(d, c, args, r) => Term::TPCon(
            d,
            c,
            args.into_iter()
                .map(|a| quote(size, globals, global_offset, a))
                .collect(),
            Box::new(quote(size, globals, global_offset, *r)),
        ),
        Value::VSqCon(d, c, args, r, s) => Term::TSqCon(
            d,
            c,
            args.into_iter()
                .map(|a| quote(size, globals, global_offset, a))
                .collect(),
            Box::new(quote(size, globals, global_offset, *r)),
            Box::new(quote(size, globals, global_offset, *s)),
        ),
        Value::VCellCon(d, c, args, ivars) => Term::TCellCon(
            d,
            c,
            args.into_iter()
                .map(|a| quote(size, globals, global_offset, a))
                .collect(),
            ivars
                .into_iter()
                .map(|v| quote(size, globals, global_offset, v))
                .collect(),
        ),
        Value::VElim(motive, cases, scrut, env, go) => Term::TElim(
            Box::new(quote(size, globals, global_offset, *motive)),
            quote_cases(size, globals, global_offset, &env, go, cases),
            Box::new(quote(size, globals, global_offset, *scrut)),
        ),
        Value::VGlue(a, phi, te) => Term::TGlue(
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(Term::TCube(phi)),
            Box::new(quote(size, globals, global_offset, *te)),
        ),
        Value::VPartial(a, phi) => Term::TPartial(
            Box::new(quote(size, globals, global_offset, *phi)),
            Box::new(quote(size, globals, global_offset, *a)),
        ),
        Value::VSystemType(sys) => Term::TSystemType(
            sys.into_iter()
                .map(|(phi, a)| (Term::TCube(phi), quote(size, globals, global_offset, a)))
                .collect(),
        ),
        Value::VGlueElem(phi, t, a) => Term::TGlueElem(
            Box::new(Term::TCube(phi)),
            Box::new(quote(size, globals, global_offset, *t)),
            Box::new(quote(size, globals, global_offset, *a)),
        ),
        Value::VUnglue(phi, te, g) => Term::TUnglue(
            Box::new(Term::TCube(phi)),
            Box::new(quote(size, globals, global_offset, *te)),
            Box::new(quote(size, globals, global_offset, *g)),
        ),
        Value::VEquiv(a, b) => Term::TEquiv(
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(quote(size, globals, global_offset, *b)),
        ),
        Value::VMkEquiv(a, b, f, g, eta, eps) => Term::TMkEquiv(
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(quote(size, globals, global_offset, *b)),
            Box::new(quote(size, globals, global_offset, *f)),
            Box::new(quote(size, globals, global_offset, *g)),
            Box::new(quote(size, globals, global_offset, *eta)),
            Box::new(quote(size, globals, global_offset, *eps)),
        ),
        Value::VEquivFwd(e, x) => Term::TEquivFwd(
            Box::new(quote(size, globals, global_offset, *e)),
            Box::new(quote(size, globals, global_offset, *x)),
        ),
        Value::VUa(e) => Term::TUa(Box::new(quote(size, globals, global_offset, *e))),
        Value::VTransport(p, x) => Term::TTransport(
            Box::new(quote(size, globals, global_offset, *p)),
            Box::new(quote(size, globals, global_offset, *x)),
        ),
        Value::VHComp(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone()),
                    )
                })
                .collect();
            Term::THComp(
                Box::new(quote(size, globals, global_offset, *a)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base)),
            )
        }
        Value::VComp(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone()),
                    )
                })
                .collect();
            Term::TComp(
                Box::new(quote(size, globals, global_offset, *a)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base)),
            )
        }
        Value::VFill(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone()),
                    )
                })
                .collect();
            Term::TFill(
                Box::new(quote(size, globals, global_offset, *a)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base)),
            )
        }
        Value::VHFill(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone()),
                    )
                })
                .collect();
            Term::THFill(
                Box::new(quote(size, globals, global_offset, *a)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base)),
            )
        }
        Value::VDelay(a) => Term::TDelay(Box::new(quote(size, globals, global_offset, *a))),
        Value::VNext(a) => Term::TNext(Box::new(quote(size, globals, global_offset, *a))),
        Value::VForce(a) => Term::TForce(Box::new(quote(size, globals, global_offset, *a))),
    }
}

fn quote_neutral(size: usize, globals: &Globals, global_offset: usize, n: Neutral) -> Term {
    match n {
        Neutral::NVar(level) => level_to_var(size, level),
        Neutral::NApp(f, a) => Term::TApp(
            Box::new(quote_neutral(size, globals, global_offset, *f)),
            Box::new(quote(size, globals, global_offset, *a)),
        ),
        Neutral::NPApp(p, r) => Term::PApp(
            Box::new(quote_neutral(size, globals, global_offset, *p)),
            Box::new(quote(size, globals, global_offset, *r)),
        ),
        Neutral::NSqApp(p, r, s) => {
            let pq = quote_neutral(size, globals, global_offset, *p);
            let rq = quote(size, globals, global_offset, *r);
            let sq = quote(size, globals, global_offset, *s);
            Term::PApp(
                Box::new(Term::PApp(Box::new(pq), Box::new(rq))),
                Box::new(sq),
            )
        }
        Neutral::NCellApp(p, ivars) => {
            let mut result = quote_neutral(size, globals, global_offset, *p);
            for iv in ivars.into_iter().rev() {
                result = Term::PApp(
                    Box::new(result),
                    Box::new(quote(size, globals, global_offset, iv)),
                );
            }
            result
        }
        Neutral::NFst(p) => Term::TFst(Box::new(quote_neutral(size, globals, global_offset, *p))),
        Neutral::NSnd(p) => Term::TSnd(Box::new(quote_neutral(size, globals, global_offset, *p))),
        Neutral::NElim(motive, cases, scrut, env, go) => Term::TElim(
            Box::new(quote(size, globals, global_offset, *motive)),
            quote_cases(size, globals, global_offset, &env, go, cases),
            Box::new(quote_neutral(size, globals, global_offset, *scrut)),
        ),
        Neutral::NTransport(p, x) => Term::TTransport(
            Box::new(quote(size, globals, global_offset, *p)),
            Box::new(quote(size, globals, global_offset, *x)),
        ),
        Neutral::NHComp(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone()),
                    )
                })
                .collect();
            Term::THComp(
                Box::new(quote(size, globals, global_offset, *a)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base)),
            )
        }
        Neutral::NComp(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone()),
                    )
                })
                .collect();
            Term::TComp(
                Box::new(quote(size, globals, global_offset, *a)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base)),
            )
        }
        Neutral::NFill(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone()),
                    )
                })
                .collect();
            Term::TFill(
                Box::new(quote(size, globals, global_offset, *a)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base)),
            )
        }
        Neutral::NHFill(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone()),
                    )
                })
                .collect();
            Term::THFill(
                Box::new(quote(size, globals, global_offset, *a)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base)),
            )
        }
        Neutral::NMeta(i) => Term::Meta(i),
        Neutral::NForce(n) => {
            Term::TForce(Box::new(quote_neutral(size, globals, global_offset, *n)))
        }
        Neutral::NProj(n, field) => Term::TProj(
            field,
            Box::new(quote_neutral(size, globals, global_offset, *n)),
        ),
    }
}

/// Re-anchor a stored elim case body for quotation.
///
/// A stuck elim stores the *raw source* case bodies. Those bodies reference
/// (in de Bruijn order): the case's own binders (TVar 0..nb), the enclosing
/// locals captured in the elim's creation `env`, and below-frame globals.
/// Re-evaluating the body under fresh binders would re-trigger recursive
/// definitions (e.g. `add`'s `suc` case body calls `add` on the pattern
/// variable), producing a fresh stuck elim every level — a non-terminating
/// growth. So we re-anchor *structurally*: local references are replaced by
/// the re-quoted captured values, binder references round-trip unchanged, and
/// global references are moved to below the quoting frame. Nothing is
/// re-evaluated, so recursion terminates.
fn quote_case_body(
    size: usize,
    globals: &Globals,
    global_offset: usize,
    env: &Scope,
    go: usize,
    t: &Term,
) -> Term {
    match t {
        Term::TVar(i) => {
            let i = *i as usize;
            if i < env.len() {
                let v = env.lookup(i).clone();
                match &v {
                    // Captured closures must be re-anchored structurally, not
                    // re-quoted via general `quote`: `quote` on a VLam applies
                    // the closure (`clos.apply`), which re-evaluates the body.
                    // Inside a stuck elim that body can reference recursive
                    // definitions (e.g. `add_comm m' n`), so re-evaluating it
                    // re-unfolds the definition one level per pass and never
                    // terminates. Re-anchoring the raw body under the
                    // closure's env keeps quoting evaluation-free (see the
                    // comment on `quote_case_body`).
                    Value::VLam(x, clos) => Term::TAbs(
                        x.clone(),
                        Box::new(quote_case_body(
                            size + 1,
                            globals,
                            global_offset,
                            &clos.env.extend(Value::VNeutral(Neutral::NVar(size))),
                            clos.global_offset,
                            &clos.body,
                        )),
                    ),
                    Value::VPLam(x, clos) => Term::PLam(
                        x.clone(),
                        Box::new(quote_case_body(
                            size + 1,
                            globals,
                            global_offset,
                            &clos.env.extend(Value::VIntervalVar(size)),
                            clos.global_offset,
                            &clos.body,
                        )),
                    ),
                    _ => quote(size, globals, global_offset, v.clone()),
                }
            } else {
                Term::TVar((size + go + i - env.len()) as i32)
            }
        }
        Term::TApp(f, a) => Term::TApp(
            Box::new(quote_case_body(size, globals, global_offset, env, go, f)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
        ),
        Term::TAbs(x, b) => Term::TAbs(
            x.clone(),
            Box::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::NVar(size))),
                go,
                b,
            )),
        ),
        Term::TUniv(n) => Term::TUniv(*n),
        Term::TProp => Term::TProp,
        Term::TSSet => Term::TSSet,
        Term::TLift(a, lvl) => Term::TLift(
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            *lvl,
        ),
        Term::TLower(a) => Term::TLower(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
        ))),
        Term::TIntervalTy => Term::TIntervalTy,
        Term::TPi(x, a, b) => Term::TPi(
            x.clone(),
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            Box::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::NVar(size))),
                go,
                b,
            )),
        ),
        Term::TInterval(i) => Term::TInterval(i.clone()),
        Term::TCube(c) => Term::TCube(c.clone()),
        Term::TPath(a, u, v) => Term::TPath(
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, u)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, v)),
        ),
        Term::PLam(x, b) => Term::PLam(
            x.clone(),
            Box::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::NVar(size))),
                go,
                b,
            )),
        ),
        Term::PApp(p, r) => Term::PApp(
            Box::new(quote_case_body(size, globals, global_offset, env, go, p)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, r)),
        ),
        Term::THComp(a, sys, u0) => Term::THComp(
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        quote_case_body(size, globals, global_offset, env, go, phi),
                        quote_case_body(size, globals, global_offset, env, go, t),
                    )
                })
                .collect(),
            Box::new(quote_case_body(size, globals, global_offset, env, go, u0)),
        ),
        Term::TComp(a, sys, u0) => Term::TComp(
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        quote_case_body(size, globals, global_offset, env, go, phi),
                        quote_case_body(size, globals, global_offset, env, go, t),
                    )
                })
                .collect(),
            Box::new(quote_case_body(size, globals, global_offset, env, go, u0)),
        ),
        Term::TFill(a, sys, u0) => Term::TFill(
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        quote_case_body(size, globals, global_offset, env, go, phi),
                        quote_case_body(size, globals, global_offset, env, go, t),
                    )
                })
                .collect(),
            Box::new(quote_case_body(size, globals, global_offset, env, go, u0)),
        ),
        Term::THFill(a, sys, u0) => Term::THFill(
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        quote_case_body(size, globals, global_offset, env, go, phi),
                        quote_case_body(size, globals, global_offset, env, go, t),
                    )
                })
                .collect(),
            Box::new(quote_case_body(size, globals, global_offset, env, go, u0)),
        ),
        Term::TEquiv(a, b) => Term::TEquiv(
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, b)),
        ),
        Term::TMkEquiv(a, b, f, g, eta, eps) => Term::TMkEquiv(
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, b)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, f)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, g)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, eta)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, eps)),
        ),
        Term::TEquivFwd(e, x) => Term::TEquivFwd(
            Box::new(quote_case_body(size, globals, global_offset, env, go, e)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, x)),
        ),
        Term::TUa(e) => Term::TUa(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            e,
        ))),
        Term::TTransport(p, x) => Term::TTransport(
            Box::new(quote_case_body(size, globals, global_offset, env, go, p)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, x)),
        ),
        Term::TGlue(a, phi, te) => Term::TGlue(
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, phi)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, te)),
        ),
        Term::TGlueElem(phi, t, a) => Term::TGlueElem(
            Box::new(quote_case_body(size, globals, global_offset, env, go, phi)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, t)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
        ),
        Term::TUnglue(phi, te, g) => Term::TUnglue(
            Box::new(quote_case_body(size, globals, global_offset, env, go, phi)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, te)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, g)),
        ),
        Term::TPartial(phi, a) => Term::TPartial(
            Box::new(quote_case_body(size, globals, global_offset, env, go, phi)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
        ),
        Term::TSystemType(sys) => Term::TSystemType(
            sys.iter()
                .map(|(phi, a)| {
                    (
                        quote_case_body(size, globals, global_offset, env, go, phi),
                        quote_case_body(size, globals, global_offset, env, go, a),
                    )
                })
                .collect(),
        ),
        Term::TSigma(x, a, b) => Term::TSigma(
            x.clone(),
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            Box::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::NVar(size))),
                go,
                b,
            )),
        ),
        Term::TPair(a, b) => Term::TPair(
            Box::new(quote_case_body(size, globals, global_offset, env, go, a)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, b)),
        ),
        Term::TFst(p) => Term::TFst(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            p,
        ))),
        Term::TSnd(p) => Term::TSnd(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            p,
        ))),
        Term::TData(name, params) => Term::TData(
            name.clone(),
            params
                .iter()
                .map(|p| quote_case_body(size, globals, global_offset, env, go, p))
                .collect(),
        ),
        Term::TCon(data, con, args) => Term::TCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| quote_case_body(size, globals, global_offset, env, go, a))
                .collect(),
        ),
        Term::TPCon(data, con, args, r) => Term::TPCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| quote_case_body(size, globals, global_offset, env, go, a))
                .collect(),
            Box::new(quote_case_body(size, globals, global_offset, env, go, r)),
        ),
        Term::TSqCon(data, con, args, r, s) => Term::TSqCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| quote_case_body(size, globals, global_offset, env, go, a))
                .collect(),
            Box::new(quote_case_body(size, globals, global_offset, env, go, r)),
            Box::new(quote_case_body(size, globals, global_offset, env, go, s)),
        ),
        Term::TCellCon(data, con, args, ivars) => Term::TCellCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| quote_case_body(size, globals, global_offset, env, go, a))
                .collect(),
            ivars
                .iter()
                .map(|v| quote_case_body(size, globals, global_offset, env, go, v))
                .collect(),
        ),
        Term::TElim(motive, cases, scrut) => {
            let mut new_cases = Vec::with_capacity(cases.len());
            for case in cases {
                let extra = if case.as_name.is_some() { 1 } else { 0 };
                let nb = case.binders.len() + extra;
                let mut env2 = env.clone();
                for j in (0..nb).rev() {
                    env2 = env2.extend(Value::VNeutral(Neutral::NVar(size + j)));
                }
                new_cases.push(ElimCase {
                    con: case.con.clone(),
                    binders: case.binders.clone(),
                    body: Box::new(quote_case_body(
                        size + nb,
                        globals,
                        global_offset,
                        &env2,
                        go,
                        &case.body,
                    )),
                    as_name: case.as_name.clone(),
                    record_bindings: case.record_bindings.clone(),
                });
            }
            Term::TElim(
                Box::new(quote_case_body(
                    size,
                    globals,
                    global_offset,
                    env,
                    go,
                    motive,
                )),
                new_cases,
                Box::new(quote_case_body(
                    size,
                    globals,
                    global_offset,
                    env,
                    go,
                    scrut,
                )),
            )
        }
        Term::Meta(i) => Term::Meta(*i),
        Term::TBy(_) => panic!("TBy should be resolved before NbE"),
        Term::TDelay(a) => Term::TDelay(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
        ))),
        Term::TNext(a) => Term::TNext(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
        ))),
        Term::TForce(a) => Term::TForce(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
        ))),
        Term::TProj(field, r) => Term::TProj(
            field.clone(),
            Box::new(quote_case_body(size, globals, global_offset, env, go, r)),
        ),
        Term::TRecordUpdate(r, updates) => Term::TRecordUpdate(
            Box::new(quote_case_body(size, globals, global_offset, env, go, r)),
            updates
                .iter()
                .map(|(f, e)| {
                    (
                        f.clone(),
                        quote_case_body(size, globals, global_offset, env, go, e),
                    )
                })
                .collect(),
        ),
    }
}

fn quote_cases(
    size: usize,
    globals: &Globals,
    global_offset: usize,
    env: &Scope,
    go: usize,
    cases: Vec<ElimCase>,
) -> Vec<ElimCase> {
    cases
        .into_iter()
        .map(|case| {
            let extra = if case.as_name.is_some() { 1 } else { 0 };
            let nb = case.binders.len() + extra;
            let mut env2 = env.clone();
            for j in (0..nb).rev() {
                env2 = env2.extend(Value::VNeutral(Neutral::NVar(size + j)));
            }
            ElimCase {
                con: case.con,
                binders: case.binders.clone(),
                body: Box::new(quote_case_body(
                    size + nb,
                    globals,
                    global_offset,
                    &env2,
                    go,
                    &case.body,
                )),
                as_name: case.as_name,
                record_bindings: case.record_bindings,
            }
        })
        .collect()
}

pub fn normalize(env: &Scope, globals: &Globals, global_offset: usize, t: &Term) -> Term {
    quote(
        env.len(),
        globals,
        global_offset,
        eval_nbe(env, globals, global_offset, t),
    )
}

/// Evaluate a term-level system into a DNFSystem.
pub fn eval_system(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    sys: &System,
) -> DNFSystem {
    sys.iter()
        .map(|(phi, t)| {
            let phi_val = eval_nbe(env, globals, global_offset, phi);
            let phi_dnf = value_to_dnf(phi_val);
            let t_val = eval_nbe(env, globals, global_offset, t);
            (phi_dnf, t_val)
        })
        .collect()
}

/// Evaluate a closed term without global definitions (original behavior).
pub fn nbe_eval(t: &Term) -> Term {
    if !has_meta_in_term(t) {
        let cached = NBE_EVAL_CACHE.with(|cache| cache.borrow().get(t).cloned());
        if let Some(result) = cached {
            return result;
        }
    }
    let result = {
        let empty_globals: Globals = Rc::new(RefCell::new(Vec::new()));
        let mv = max_var(t);
        if mv < 0 {
            normalize(&Scope::empty(), &empty_globals, 0, t)
        } else {
            let size = (mv + 1) as usize;
            let mut env = Scope::empty();
            for level in 0..size {
                env = env.extend(Value::VNeutral(Neutral::NVar(level)));
            }
            normalize(&env, &empty_globals, 0, t)
        }
    };
    if !has_meta_in_term(t) {
        NBE_EVAL_CACHE.with(|cache| cache.borrow_mut().insert(t.clone(), result.clone()));
    }
    result
}

/// Evaluate a term with access to global definition values.
///
/// `globals` should be ordered most-recent-first (same as `env.defs`).
/// `global_offset` is the index into `globals` where the evaluated term's
/// own definition lives (0 = most recent, the typical case for evaluating
/// the target expression).
pub fn nbe_eval_with_globals(t: &Term, globals: &Globals, global_offset: usize) -> Term {
    // The env starts empty — all TVars resolve to globals.
    // Lambdas push binders onto the env during evaluation via do_apply.
    normalize(&Scope::empty(), globals, global_offset, t)
}

/// Evaluate a term with access to the thread-local global definition values
/// (set via `set_current_globals`). The first `ctx_len` de Bruijn indices are
/// treated as local binders and the remainder as global references, matching
/// the typechecker convention that global definitions sit at the bottom of the
/// context. Falls back to `nbe_eval` (no globals) when none are set.
pub fn nbe_eval_ctx(ctx_len: usize, t: &Term) -> Term {
    let Some(globals) = CURRENT_GLOBALS.with(|cell| cell.borrow().clone()) else {
        return nbe_eval(t);
    };
    let n_globals = globals.borrow().len();
    let n_local = ctx_len.saturating_sub(n_globals);
    // Build the eval env with ONLY the local binders (as neutral variables).
    // Global references are left outside the env so they resolve through the
    // `globals` vec in `eval_nbe_inner` (`global_offset + (i - env.len())`).
    // Keeping globals out of the env is load-bearing: any stuck elim created
    // during this evaluation captures `env`, and `quote_case_body` re-anchors
    // a raw case-body global ref as a *reference below the frame* precisely
    // when the ref lands beyond `env.len()`. If globals were in the env, those
    // refs would land inside `env.len()` and get inlined, which re-evaluates
    // recursive definitions (e.g. `add`'s case body calling `add`) on every
    // normalization pass — the non-terminating growth documented at
    // `quote_case_body`. With a locals-only env, normalization is idempotent.
    let mut env = Scope::empty();
    for level in 0..n_local {
        env = env.extend(Value::VNeutral(Neutral::NVar(level)));
    }
    quote(n_local, &globals, 0, eval_nbe(&env, &globals, 0, t))
}

fn do_equiv_fwd(globals: &Globals, global_offset: usize, e: Value, x: Value) -> Value {
    match e {
        Value::VMkEquiv(_, _, f, _, _, _) => {
            let result = do_apply(globals, global_offset, *f, x);
            record_step(
                "equiv-fwd".into(),
                "equivFwd (mkEquiv _ _ f _ _ _) _".into(),
                value_str(globals, global_offset, &result),
            );
            result
        }
        other => Value::VEquivFwd(Box::new(other), Box::new(x)),
    }
}

fn equiv_dom_value(v: Value) -> Value {
    match v {
        Value::VMkEquiv(a, _, _, _, _, _) | Value::VEquiv(a, _) => *a,
        Value::VPair(a, _) => *a,
        other => other,
    }
}

fn stuck_elim(
    motive: Value,
    cases: &[ElimCase],
    n: Neutral,
    env: &Scope,
    global_offset: usize,
) -> Value {
    Value::VNeutral(Neutral::NElim(
        Box::new(motive),
        cases.to_vec(),
        Box::new(n),
        env.clone(),
        global_offset,
    ))
}

fn value_to_dnf(v: Value) -> DNF {
    match v {
        Value::VCube(d) => d,
        Value::VInterval(i) => eval_interval(&i),
        Value::VIntervalVar(level) => eval_interval(&I::Var(level as i32)),
        other => match quote(0, &Rc::new(RefCell::new(Vec::new())), 0, other) {
            Term::TCube(d) => d,
            Term::TInterval(i) => eval_interval(&i),
            _ => dnf_bot(),
        },
    }
}

fn value_to_endpoint(v: &Value) -> Option<I> {
    match v {
        Value::VInterval(i) => {
            let d = eval_interval(i);
            if d == dnf_bot() {
                Some(I::I0)
            } else if d == dnf_top() {
                Some(I::I1)
            } else {
                None
            }
        }
        Value::VCube(d) if *d == dnf_bot() => Some(I::I0),
        Value::VCube(d) if *d == dnf_top() => Some(I::I1),
        _ => None,
    }
}

/// Find the tube value from a system whose face holds at a specific interval endpoint.
/// Returns Some(tube_value) if a face evaluates to true at the endpoint, None otherwise.
fn find_system_entry_at_endpoint(sys: &DNFSystem, endpoint: &I) -> Option<Value> {
    let endpoint_subst = eval_interval(endpoint);
    for (face, tube) in sys {
        if *face == endpoint_subst {
            return Some(tube.clone());
        }
    }
    None
}

fn level_to_var(size: usize, level: usize) -> Term {
    if level < size {
        Term::TVar((size - level - 1) as i32)
    } else {
        Term::TVar(level.saturating_sub(size) as i32)
    }
}

// ---------------------------------------------------------------------------
// Metavariable store and helpers
// ---------------------------------------------------------------------------

pub fn fresh_meta_id() -> i32 {
    METAVAR_SOLUTIONS.with(|s| {
        let mut store = s.borrow_mut();
        let id = store.len() as i32;
        store.push(None);
        META_NAMES.with(|n| n.borrow_mut().push(None));
        META_EXPECTED.with(|e| e.borrow_mut().push(None));
        id
    })
}

/// Register a display name for a hole (from `?name` syntax).
/// Anonymous holes (`_`, `?`) have no name.
pub fn set_meta_name(id: i32, name: Name) {
    META_NAMES.with(|n| {
        if id >= 0 && (id as usize) < n.borrow().len() {
            n.borrow_mut()[id as usize] = Some(name);
        }
    });
}

pub fn get_meta_name(id: i32) -> Option<Name> {
    if id < 0 {
        return None;
    }
    META_NAMES.with(|n| n.borrow().get(id as usize).and_then(|o| o.clone()))
}

/// Record the expected type of a hole as discovered by `check_dt`.
/// Only meaningful while the hole is unsolved.
pub fn set_meta_expected(id: i32, ty: Term) {
    META_EXPECTED.with(|e| {
        if id >= 0 && (id as usize) < e.borrow().len() {
            let mut store = e.borrow_mut();
            if store[id as usize].is_none() {
                store[id as usize] = Some(ty);
            }
        }
    });
}

pub fn get_meta_expected(id: i32) -> Option<Term> {
    if id < 0 {
        return None;
    }
    META_EXPECTED.with(|e| e.borrow().get(id as usize).and_then(|o| o.clone()))
}

pub fn solve_meta(id: i32, solution: Term) {
    METAVAR_SOLUTIONS.with(|s| {
        if id >= 0 && (id as usize) < s.borrow().len() {
            s.borrow_mut()[id as usize] = Some(solution);
        }
    });
}

pub fn get_meta_solution(id: i32) -> Option<Term> {
    if id < 0 {
        return None;
    }
    METAVAR_SOLUTIONS.with(|s| s.borrow().get(id as usize).and_then(|opt| opt.clone()))
}

pub fn clear_metavars() {
    METAVAR_SOLUTIONS.with(|s| s.borrow_mut().clear());
    META_NAMES.with(|n| n.borrow_mut().clear());
    META_EXPECTED.with(|e| e.borrow_mut().clear());
}

pub fn clear_nbe_cache() {
    NBE_EVAL_CACHE.with(|cache| cache.borrow_mut().clear());
}

pub fn clear_all_caches() {
    clear_nbe_cache();
    clear_metavars();
}

pub fn meta_mentions(id: i32, t: &Term) -> bool {
    match t {
        Term::Meta(j) => *j == id,
        Term::TVar(_)
        | Term::TUniv(_)
        | Term::TProp
        | Term::TSSet
        | Term::TIntervalTy
        | Term::TInterval(_)
        | Term::TCube(_) => false,
        Term::TApp(f, a) => meta_mentions(id, f) || meta_mentions(id, a),
        Term::TAbs(_, b) | Term::PLam(_, b) => meta_mentions(id, b),
        Term::TPi(_, a, b) | Term::TSigma(_, a, b) => meta_mentions(id, a) || meta_mentions(id, b),
        Term::TPath(a, u, v) => {
            meta_mentions(id, a) || meta_mentions(id, u) || meta_mentions(id, v)
        }
        Term::PApp(p, r) => meta_mentions(id, p) || meta_mentions(id, r),
        Term::THComp(a, sys, base)
        | Term::TComp(a, sys, base)
        | Term::TFill(a, sys, base)
        | Term::THFill(a, sys, base) => {
            meta_mentions(id, a)
                || meta_mentions(id, base)
                || sys
                    .iter()
                    .any(|(phi, tube)| meta_mentions(id, phi) || meta_mentions(id, tube))
        }
        Term::TEquiv(a, b) => meta_mentions(id, a) || meta_mentions(id, b),
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            meta_mentions(id, a)
                || meta_mentions(id, b)
                || meta_mentions(id, f)
                || meta_mentions(id, g)
                || meta_mentions(id, eta)
                || meta_mentions(id, eps)
        }
        Term::TEquivFwd(e, x) | Term::TTransport(e, x) => {
            meta_mentions(id, e) || meta_mentions(id, x)
        }
        Term::TUa(e) => meta_mentions(id, e),
        Term::TGlue(a, phi, te) => {
            meta_mentions(id, a) || meta_mentions(id, phi) || meta_mentions(id, te)
        }
        Term::TGlueElem(phi, t, a) => {
            meta_mentions(id, phi) || meta_mentions(id, t) || meta_mentions(id, a)
        }
        Term::TUnglue(phi, te, g) => {
            meta_mentions(id, phi) || meta_mentions(id, te) || meta_mentions(id, g)
        }
        Term::TPartial(phi, a) => meta_mentions(id, phi) || meta_mentions(id, a),
        Term::TSystemType(sys) => sys
            .iter()
            .any(|(phi, a)| meta_mentions(id, phi) || meta_mentions(id, a)),
        Term::TPair(a, b) => meta_mentions(id, a) || meta_mentions(id, b),
        Term::TFst(p)
        | Term::TSnd(p)
        | Term::TProj(_, p)
        | Term::TLift(p, _)
        | Term::TLower(p)
        | Term::TDelay(p)
        | Term::TNext(p)
        | Term::TForce(p) => meta_mentions(id, p),
        Term::TRecordUpdate(r, updates) => {
            meta_mentions(id, r) || updates.iter().any(|(_, e)| meta_mentions(id, e))
        }
        Term::TData(_, params) => params.iter().any(|p| meta_mentions(id, p)),
        Term::TCon(_, _, args) => args.iter().any(|a| meta_mentions(id, a)),
        Term::TPCon(_, _, args, r) => {
            args.iter().any(|a| meta_mentions(id, a)) || meta_mentions(id, r)
        }
        Term::TSqCon(_, _, args, r, s) => {
            args.iter().any(|a| meta_mentions(id, a))
                || meta_mentions(id, r)
                || meta_mentions(id, s)
        }
        Term::TCellCon(_, _, args, ivars) => {
            args.iter().any(|a| meta_mentions(id, a)) || ivars.iter().any(|v| meta_mentions(id, v))
        }
        Term::TElim(motive, cases, scrut) => {
            meta_mentions(id, motive)
                || meta_mentions(id, scrut)
                || cases.iter().any(|c| meta_mentions(id, &c.body))
        }
        Term::TBy(_) => false,
    }
}

pub fn try_solve_meta(id: i32, rhs: &Term) -> bool {
    if id < 0 {
        return false;
    }
    if get_meta_solution(id).is_some() {
        return true;
    }
    if meta_mentions(id, rhs) {
        return false;
    }
    solve_meta(id, rhs.clone());
    true
}

pub fn zonk(t: &Term) -> Term {
    match t {
        Term::Meta(i) => {
            if let Some(solution) = get_meta_solution(*i) {
                solution
            } else {
                t.clone()
            }
        }
        _ => {
            let mut cloned = t.clone();
            fn zonk_sub(term: &mut Term) {
                match term {
                    Term::Meta(i) => {
                        if let Some(solution) = get_meta_solution(*i) {
                            *term = solution;
                        }
                    }
                    _ => {
                        let children = term_children_mut(term);
                        for child in children {
                            zonk_sub(child);
                        }
                    }
                }
            }
            zonk_sub(&mut cloned);
            cloned
        }
    }
}

fn term_children_mut(t: &mut Term) -> Vec<&mut Term> {
    match t {
        Term::TVar(_)
        | Term::TUniv(_)
        | Term::TProp
        | Term::TSSet
        | Term::TIntervalTy
        | Term::TInterval(_)
        | Term::TCube(_)
        | Term::Meta(_) => vec![],
        Term::TApp(f, a) => vec![f.as_mut(), a.as_mut()],
        Term::TAbs(_, b) | Term::PLam(_, b) => vec![b.as_mut()],
        Term::TPi(_, a, b) | Term::TSigma(_, a, b) => vec![a.as_mut(), b.as_mut()],
        Term::TPath(a, u, v) => vec![a.as_mut(), u.as_mut(), v.as_mut()],
        Term::PApp(p, r) => vec![p.as_mut(), r.as_mut()],
        Term::THComp(a, sys, base)
        | Term::TComp(a, sys, base)
        | Term::TFill(a, sys, base)
        | Term::THFill(a, sys, base) => {
            let mut children = vec![a.as_mut(), base.as_mut()];
            for (phi, tube) in sys.iter_mut() {
                children.push(phi);
                children.push(tube);
            }
            children
        }
        Term::TEquiv(a, b) => vec![a.as_mut(), b.as_mut()],
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            vec![
                a.as_mut(),
                b.as_mut(),
                f.as_mut(),
                g.as_mut(),
                eta.as_mut(),
                eps.as_mut(),
            ]
        }
        Term::TEquivFwd(e, x) | Term::TTransport(e, x) => vec![e.as_mut(), x.as_mut()],
        Term::TUa(e) => vec![e.as_mut()],
        Term::TGlue(a, phi, te) => vec![a.as_mut(), phi.as_mut(), te.as_mut()],
        Term::TGlueElem(phi, t, a) => vec![phi.as_mut(), t.as_mut(), a.as_mut()],
        Term::TUnglue(phi, te, g) => vec![phi.as_mut(), te.as_mut(), g.as_mut()],
        Term::TPartial(phi, a) => vec![phi.as_mut(), a.as_mut()],
        Term::TSystemType(sys) => sys
            .iter_mut()
            .flat_map(|(phi, a)| vec![phi as &mut Term, a as &mut Term])
            .collect(),
        Term::TPair(a, b) => vec![a.as_mut(), b.as_mut()],
        Term::TFst(p)
        | Term::TSnd(p)
        | Term::TLift(p, _)
        | Term::TLower(p)
        | Term::TDelay(p)
        | Term::TNext(p)
        | Term::TForce(p) => vec![p.as_mut()],
        Term::TProj(_, p) => vec![p.as_mut()],
        Term::TRecordUpdate(r, updates) => {
            let mut children: Vec<&mut Term> = vec![r.as_mut()];
            for (_, e) in updates.iter_mut() {
                children.push(e);
            }
            children
        }
        Term::TData(_, params) => params.iter_mut().collect(),
        Term::TCon(_, _, args) => args.iter_mut().collect(),
        Term::TPCon(_, _, args, r) => {
            let mut children: Vec<&mut Term> = args.iter_mut().collect();
            children.push(r.as_mut());
            children
        }
        Term::TSqCon(_, _, args, r, s) => {
            let mut children: Vec<&mut Term> = args.iter_mut().collect();
            children.push(r.as_mut());
            children.push(s.as_mut());
            children
        }
        Term::TCellCon(_, _, args, ivars) => {
            let mut children: Vec<&mut Term> = args.iter_mut().collect();
            children.extend(ivars.iter_mut());
            children
        }
        Term::TElim(motive, cases, scrut) => {
            let mut children = vec![motive.as_mut(), scrut.as_mut()];
            for case in cases.iter_mut() {
                children.push(case.body.as_mut());
            }
            children
        }
        Term::TBy(_) => vec![],
    }
}

fn has_meta_in_term(t: &Term) -> bool {
    match t {
        Term::Meta(_) => true,
        _ => {
            let children = term_children_ref(t);
            children.into_iter().any(has_meta_in_term)
        }
    }
}

fn term_children_ref(t: &Term) -> Vec<&Term> {
    match t {
        Term::TVar(_)
        | Term::TUniv(_)
        | Term::TProp
        | Term::TSSet
        | Term::TIntervalTy
        | Term::TInterval(_)
        | Term::TCube(_)
        | Term::Meta(_) => vec![],
        Term::TApp(f, a) => vec![f.as_ref(), a.as_ref()],
        Term::TAbs(_, b) | Term::PLam(_, b) => vec![b.as_ref()],
        Term::TPi(_, a, b) | Term::TSigma(_, a, b) => vec![a.as_ref(), b.as_ref()],
        Term::TPath(a, u, v) => vec![a.as_ref(), u.as_ref(), v.as_ref()],
        Term::PApp(p, r) => vec![p.as_ref(), r.as_ref()],
        Term::THComp(a, sys, base)
        | Term::TComp(a, sys, base)
        | Term::TFill(a, sys, base)
        | Term::THFill(a, sys, base) => {
            let mut children = vec![a.as_ref(), base.as_ref()];
            for (phi, tube) in sys {
                children.push(phi);
                children.push(tube);
            }
            children
        }
        Term::TEquiv(a, b) => vec![a.as_ref(), b.as_ref()],
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            vec![
                a.as_ref(),
                b.as_ref(),
                f.as_ref(),
                g.as_ref(),
                eta.as_ref(),
                eps.as_ref(),
            ]
        }
        Term::TEquivFwd(e, x) | Term::TTransport(e, x) => vec![e.as_ref(), x.as_ref()],
        Term::TUa(e) => vec![e.as_ref()],
        Term::TGlue(a, phi, te) => vec![a.as_ref(), phi.as_ref(), te.as_ref()],
        Term::TGlueElem(phi, t, a) => vec![phi.as_ref(), t.as_ref(), a.as_ref()],
        Term::TUnglue(phi, te, g) => vec![phi.as_ref(), te.as_ref(), g.as_ref()],
        Term::TPartial(phi, a) => vec![phi.as_ref(), a.as_ref()],
        Term::TSystemType(sys) => sys
            .iter()
            .flat_map(|(phi, a)| vec![phi as &Term, a as &Term])
            .collect(),
        Term::TPair(a, b) => vec![a.as_ref(), b.as_ref()],
        Term::TFst(p)
        | Term::TSnd(p)
        | Term::TProj(_, p)
        | Term::TLift(p, _)
        | Term::TLower(p)
        | Term::TDelay(p)
        | Term::TNext(p)
        | Term::TForce(p) => vec![p.as_ref()],
        Term::TRecordUpdate(r, updates) => {
            let mut children: Vec<&Term> = vec![r.as_ref()];
            for (_, e) in updates.iter() {
                children.push(e);
            }
            children
        }
        Term::TData(_, params) => params.iter().collect(),
        Term::TCon(_, _, args) => args.iter().collect(),
        Term::TPCon(_, _, args, r) => {
            let mut children: Vec<&Term> = args.iter().collect();
            children.push(r.as_ref());
            children
        }
        Term::TSqCon(_, _, args, r, s) => {
            let mut children: Vec<&Term> = args.iter().collect();
            children.push(r.as_ref());
            children.push(s.as_ref());
            children
        }
        Term::TCellCon(_, _, args, ivars) => {
            let mut children: Vec<&Term> = args.iter().collect();
            children.extend(ivars.iter());
            children
        }
        Term::TElim(motive, cases, scrut) => {
            let mut children = vec![motive.as_ref(), scrut.as_ref()];
            for case in cases {
                children.push(case.body.as_ref());
            }
            children
        }
        Term::TBy(_) => vec![],
    }
}

/// Collect the ids of every unsolved hole (`Term::Meta` with no solution)
/// appearing in `t`.
pub fn collect_unsolved_metas(t: &Term) -> Vec<i32> {
    fn walk(t: &Term, out: &mut Vec<i32>) {
        match t {
            Term::Meta(i) => {
                if get_meta_solution(*i).is_none() && !out.contains(i) {
                    out.push(*i);
                }
            }
            _ => {
                for child in term_children_ref(t) {
                    walk(child, out);
                }
            }
        }
    }
    let mut out = Vec::new();
    walk(t, &mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cubical::interval::Literal;
    use std::collections::BTreeSet;

    fn b(t: Term) -> Box<Term> {
        Box::new(t)
    }

    #[test]
    fn identity_function_normalizes_to_itself() {
        let id = Term::TAbs("x".to_string(), b(Term::TVar(0)));
        assert_eq!(nbe_eval(&id), id);
    }

    #[test]
    fn beta_reduces_identity_application() {
        let term = Term::TApp(
            b(Term::TAbs("x".to_string(), b(Term::TVar(0)))),
            b(Term::TUniv(0)),
        );
        assert_eq!(nbe_eval(&term), Term::TUniv(0));
    }

    #[test]
    fn fst_of_pair_reduces() {
        let term = Term::TFst(b(Term::TPair(b(Term::TUniv(0)), b(Term::TUniv(1)))));
        assert_eq!(nbe_eval(&term), Term::TUniv(0));
    }

    #[test]
    fn transport_over_constant_family_is_identity() {
        let family = Term::PLam("i".to_string(), b(Term::TUniv(0)));
        let term = Term::TTransport(b(family), b(Term::TUniv(1)));
        assert_eq!(nbe_eval(&term), Term::TUniv(1));
    }

    #[test]
    fn transport_over_nonconstant_pi_produces_lambda() {
        let body = Term::TPi(
            "x".to_string(),
            b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
            b(Term::TUniv(0)),
        );
        let fam = Term::PLam("i".to_string(), b(body));
        let arg = Term::TAbs("x".to_string(), b(Term::TUniv(0)));
        let term = Term::TTransport(b(fam), b(arg));
        let result = nbe_eval(&term);
        assert!(
            matches!(&result, Term::TAbs(_, _)),
            "expected TAbs, got: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    }

    #[test]
    fn deep_transport_fallback_unsticks_pi() {
        let body = Term::TPi(
            "x".to_string(),
            b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
            b(Term::TUniv(0)),
        );
        let fam = Term::PLam("i".to_string(), b(body));
        let arg = Term::TAbs("x".to_string(), b(Term::TUniv(0)));
        let term = Term::TTransport(b(fam), b(arg));
        let result = nbe_eval(&term);
        assert!(
            !matches!(result, Term::TTransport(_, _)),
            "transport should not be stuck: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    }

    #[test]
    fn sigma_transport_on_pair_reduces() {
        let sigma = Term::TSigma("x".to_string(), b(Term::TUniv(0)), b(Term::TUniv(1)));
        let fam = Term::PLam("i".to_string(), b(sigma));
        let pair = Term::TPair(b(Term::TUniv(0)), b(Term::TUniv(1)));
        let term = Term::TTransport(b(fam), b(pair.clone()));
        let result = nbe_eval(&term);
        assert_eq!(result, pair);
    }

    #[test]
    fn path_transport_produces_plam() {
        let path = Term::TPath(
            b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
            b(Term::TUniv(0)),
            b(Term::TUniv(0)),
        );
        let fam = Term::PLam("i".to_string(), b(path));
        let arg = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let term = Term::TTransport(b(fam), b(arg));
        let result = nbe_eval(&term);
        assert!(
            matches!(&result, Term::PLam(_, _)),
            "expected PLam, got: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    }

    #[test]
    fn native_pi_transport_no_deep_fallback() {
        let body = Term::TPi(
            "x".to_string(),
            b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
            b(Term::TUniv(0)),
        );
        let fam = Term::PLam("i".to_string(), b(body));
        let arg = Term::TAbs("x".to_string(), b(Term::TUniv(0)));
        let term = Term::TTransport(b(fam), b(arg));
        let result = nbe_eval(&term);
        assert!(
            matches!(&result, Term::TAbs(_, _)),
            "expected TAbs (native Pi transport), got: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    }

    #[test]
    fn dependent_codomain_pi_transport_reduces() {
        // Family: λi. (x : i x) → (y : U) → x
        // The codomain (y:U) → x depends on x (the Pi argument), so this
        // exercises the dependent Pi transport code path.
        let body = Term::TPi(
            "x".to_string(),
            b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
            b(Term::TPi(
                "y".to_string(),
                b(Term::TUniv(0)),
                b(Term::TVar(1)),
            )),
        );
        let fam = Term::PLam("i".to_string(), b(body));
        let arg = Term::TAbs(
            "x".to_string(),
            b(Term::TAbs("y".to_string(), b(Term::TVar(1)))),
        );
        let term = Term::TTransport(b(fam), b(arg));
        let result = nbe_eval(&term);
        assert!(
            !matches!(&result, Term::TTransport(_, _)),
            "dependent Pi transport should reduce, got stuck: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
        assert!(
            matches!(&result, Term::TAbs(_, _)),
            "expected TAbs, got: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    }

    #[test]
    fn hcomp_papp_at_zero_reduces_to_base() {
        // hcomp A [(i0, tube)] base @ 0 should reduce to base
        // (non-trivial face keeps hcomp stuck until papp)
        let tube = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let hcomp = Term::THComp(
            b(Term::TUniv(0)),
            vec![(Term::TInterval(I::Var(0)), tube)],
            b(Term::TUniv(1)),
        );
        let term = Term::PApp(b(hcomp), b(Term::TInterval(I::I0)));
        let result = nbe_eval(&term);
        assert_eq!(result, Term::TUniv(1));
    }

    #[test]
    fn hcomp_papp_at_one_reduces_to_tube_at_one() {
        // hcomp A [(i0, tube)] base @ 1 should reduce to tube @ 1
        let tube = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let hcomp = Term::THComp(
            b(Term::TUniv(0)),
            vec![(Term::TInterval(I::Var(0)), tube)],
            b(Term::TUniv(1)),
        );
        let term = Term::PApp(b(hcomp), b(Term::TInterval(I::I1)));
        let result = nbe_eval(&term);
        assert_eq!(result, Term::TUniv(0));
    }

    #[test]
    fn hcomp_const_tube_coherent_reduces_to_base() {
        // hcomp U [i1 => λj. U0] U0 should reduce to U0 (constant-tube shortcut)
        // Tube PLam("j", U0) is constant (U0 at both I0 and I1) and equals base U0.
        let tube = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let hcomp = Term::THComp(
            b(Term::TUniv(0)),
            vec![(Term::TInterval(I::I1), tube)],
            b(Term::TUniv(0)),
        );
        let result = nbe_eval(&hcomp);
        assert_eq!(
            result,
            Term::TUniv(0),
            "constant-tube hcomp should reduce to base"
        );
    }

    #[test]
    fn fill_const_tube_coherent_reduces_to_const_path() {
        // fill U [i1 => λj. U0] U0 should reduce to λj. U0 (constant-tube shortcut)
        let tube = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let fill = Term::TFill(
            b(Term::TUniv(0)),
            vec![(Term::TInterval(I::I1), tube)],
            b(Term::TUniv(0)),
        );
        let result = nbe_eval(&fill);
        assert!(
            matches!(&result, Term::PLam(_, _)),
            "constant-tube fill should reduce to VPLam (constant path), got: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    }

    #[test]
    fn glue_transport_on_glue_elem_decomposes() {
        // transport (λi. Glue (TVar(i)) [phi] te) (glue [phi] cap base)
        // where phi is non-trivial constant (Pos(1) — different from transport var)
        // A = TVar(0) varies with i (VInterval(I::I0) at i=0, VInterval(I::I1) at i=1)
        // so the family is non-constant and transport_glue is reached.
        //
        // Result: glue [phi] cap (hcomp A_type [phi] (λi. cap) base)
        let non_trivial_phi = Term::TCube(DNF {
            cubes: BTreeSet::from([BTreeSet::from([Literal::Pos(1)])]),
        });
        let glue_ty = Term::TGlue(
            b(Term::TVar(0)), // A varies with i → makes family non-constant
            b(non_trivial_phi.clone()),
            b(Term::TUniv(0)), // te
        );
        let fam = Term::PLam("i".to_string(), b(glue_ty));
        let cap = Term::TUniv(1);
        let base = Term::TUniv(2);
        let glue_elem = Term::TGlueElem(b(non_trivial_phi.clone()), b(cap), b(base));
        let transport = Term::TTransport(b(fam), b(glue_elem));
        let globals: Globals = Rc::new(RefCell::new(Vec::new()));
        let result = eval_nbe(&Scope::empty(), &globals, 0, &transport);
        let phi_dnf = DNF {
            cubes: BTreeSet::from([BTreeSet::from([Literal::Pos(1)])]),
        };
        match result {
            Value::VGlueElem(phi, t, a) => {
                assert_eq!(phi, phi_dnf, "face should be the non-trivial phi");
                match *t {
                    Value::VUniv(n) => assert_eq!(n, 1, "cap should be U1"),
                    other => panic!("expected VUniv(1) for cap, got: {:?}", other),
                }
                match *a {
                    Value::VHComp(_, h_sys, h_base) => {
                        // Single-entry system with the expected face
                        assert_eq!(h_sys.len(), 1, "hcomp system should have 1 entry");
                        assert_eq!(h_sys[0].0, phi_dnf, "hcomp face should match");
                        match *h_base {
                            Value::VUniv(n) => assert_eq!(n, 2, "hcomp base should be U2"),
                            other => panic!("expected VUniv(2) for hcomp base, got: {:?}", other),
                        }
                    }
                    other => panic!("expected VHComp, got: {:?}", other),
                }
            }
            other => panic!("expected VGlueElem, got: {:?}", other),
        }
    }

    #[test]
    fn glue_transport_on_non_glue_elem_stays_stuck() {
        // transport (λi. Glue (TVar(i)) [phi] te) U0
        // A varies → family non-constant, but input is not GlueElem → stuck
        let non_trivial_phi = Term::TCube(DNF {
            cubes: BTreeSet::from([BTreeSet::from([Literal::Pos(1)])]),
        });
        let glue_ty = Term::TGlue(b(Term::TVar(0)), b(non_trivial_phi), b(Term::TUniv(0)));
        let fam = Term::PLam("i".to_string(), b(glue_ty));
        let transport = Term::TTransport(b(fam), b(Term::TUniv(0)));
        let globals: Globals = Rc::new(RefCell::new(Vec::new()));
        let result = eval_nbe(&Scope::empty(), &globals, 0, &transport);
        match result {
            Value::VTransport(_, _) => {}
            other => panic!("expected stuck VTransport, got: {:?}", other),
        }
    }

    #[test]
    fn glue_transport_face_mismatch_stays_stuck() {
        // transport (λi. Glue (TVar(i)) [phi1] te) (glue [phi2] cap base)
        // phi1 != phi2 → decomposition fails → stuck
        let phi1 = Term::TCube(DNF {
            cubes: BTreeSet::from([BTreeSet::from([Literal::Pos(1)])]),
        });
        let phi2 = Term::TCube(DNF {
            cubes: BTreeSet::from([BTreeSet::from([Literal::NegVar(1)])]),
        });
        let glue_ty = Term::TGlue(b(Term::TVar(0)), b(phi1), b(Term::TUniv(0)));
        let fam = Term::PLam("i".to_string(), b(glue_ty));
        let glue_elem = Term::TGlueElem(b(phi2), b(Term::TUniv(1)), b(Term::TUniv(2)));
        let transport = Term::TTransport(b(fam), b(glue_elem));
        let globals: Globals = Rc::new(RefCell::new(Vec::new()));
        let result = eval_nbe(&Scope::empty(), &globals, 0, &transport);
        match result {
            Value::VTransport(_, _) => {}
            other => panic!(
                "expected stuck VTransport on face mismatch, got: {:?}",
                other
            ),
        }
    }
}
