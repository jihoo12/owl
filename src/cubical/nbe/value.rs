//! Core NbE runtime types: scopes, values, neutrals and closures.
//!
//! Split out of the former monolithic `nbe/mod.rs`; the module tree is
//! documented in `mod.rs`.
#![allow(clippy::enum_variant_names)]

use std::cell::RefCell;
use std::rc::Rc;

use super::eval::{eval_nbe, subst_interval_var};
use super::quote::quote;
use crate::cubical::debug;
use crate::cubical::interval::{DNF, I};
use crate::cubical::session::Session;
use crate::cubical::syntax::{ElimCase, Level, Name, Term, show_term};

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

pub(super) fn value_str(
    globals: &Globals,
    global_offset: usize,
    v: &Value,
    session: &mut Session,
) -> String {
    if !debug::is_active() {
        return String::new();
    }
    let term = quote(0, globals, global_offset, v.clone(), session);
    show_term(&[], &term)
}

#[derive(Debug, Clone)]
pub enum Value {
    VNeutral(Neutral),
    VLam(Name, Closure),
    VApp(Box<Value>, Box<Value>),
    VPi(Name, Box<Value>, Closure, bool),
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
    pub fn apply(&self, v: Value, session: &mut Session) -> Value {
        let env = self.env.extend(v);
        eval_nbe(&env, &self.globals, self.global_offset, &self.body, session)
    }
}

impl IClosure {
    pub fn apply_i(&self, i: I, session: &mut Session) -> Value {
        self.apply_interval_value(Value::VInterval(i), session)
    }

    pub(super) fn apply_i_var(&self, level: usize, session: &mut Session) -> Value {
        self.apply_interval_value(Value::VIntervalVar(level), session)
    }

    pub fn apply_interval_value(&self, v: Value, session: &mut Session) -> Value {
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
                eval_nbe(&env, &self.globals, self.global_offset, &body, session)
            }
            Value::VIntervalVar(_level) => {
                let env = self.env.extend(v);
                eval_nbe(&env, &self.globals, self.global_offset, &self.body, session)
            }
            other => {
                let env = self.env.extend(other.clone());
                eval_nbe(&env, &self.globals, self.global_offset, &self.body, session)
            }
        }
    }
}
