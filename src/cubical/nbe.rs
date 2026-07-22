#![allow(dead_code)]
#![allow(clippy::enum_variant_names)]

use std::cell::RefCell;
use std::rc::Rc;

use crate::cubical::interval::{DNF, I, dnf_bot, dnf_top, eval_interval};
use crate::cubical::syntax::{ElimCase, Level, Name, Term, beta, equiv_dom, is_bot_dnf, is_top_dnf, max_var, shift, show_term, subst};

pub type Env = Vec<Value>;

/// A shared reference to the global definition values.
/// All closures created during evaluation share the same `Globals` so that
/// recursive self-references resolve correctly after placeholder replacement.
pub type Globals = Rc<RefCell<Vec<Value>>>;

// ── Reduction trace infrastructure ──

/// A single reduction step recorded during normalization.
#[derive(Debug, Clone)]
pub struct ReductionStep {
    pub rule: String,
    pub input: String,
    pub output: String,
}

thread_local! {
    static REDUCTION_TRACE: std::cell::RefCell<Vec<ReductionStep>> = std::cell::RefCell::new(Vec::new());
}

pub static TRACE_ACTIVE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

pub fn start_trace() {
    TRACE_ACTIVE.store(true, std::sync::atomic::Ordering::Release);
    REDUCTION_TRACE.with(|t| t.borrow_mut().clear());
}

pub fn stop_trace() -> Vec<ReductionStep> {
    TRACE_ACTIVE.store(false, std::sync::atomic::Ordering::Release);
    REDUCTION_TRACE.with(|t| t.borrow_mut().split_off(0))
}

fn record_step(rule: String, input: String, output: String) {
    if TRACE_ACTIVE.load(std::sync::atomic::Ordering::Acquire) {
        REDUCTION_TRACE.with(|t| t.borrow_mut().push(ReductionStep { rule, input, output }));
    }
}

fn value_str(globals: &Globals, global_offset: usize, v: &Value) -> String {
    if !TRACE_ACTIVE.load(std::sync::atomic::Ordering::Acquire) {
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
    VIntervalTy,
    VInterval(I),
    VIntervalVar(usize),
    VCube(DNF),
    VData(Name),
    VCon(Name, Name, Vec<Value>),
    VPCon(Name, Name, Vec<Value>, Box<Value>),
    VElim(Box<Value>, Vec<ElimCase>, Box<Value>),
    VGlue(Box<Value>, DNF, Box<Value>),
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
    VHComp(Box<Value>, DNF, Box<Value>, Box<Value>),
    VFst(Box<Value>),
    VSnd(Box<Value>),
}

#[derive(Debug, Clone)]
pub struct Closure {
    pub env: Env,
    pub globals: Globals,
    pub global_offset: usize,
    pub body: Term,
}

#[derive(Debug, Clone)]
pub struct IClosure {
    pub env: Env,
    pub globals: Globals,
    pub global_offset: usize,
    pub body: Term,
}

#[derive(Debug, Clone)]
pub enum Neutral {
    NVar(usize),
    NApp(Box<Neutral>, Box<Value>),
    NPApp(Box<Neutral>, Box<Value>),
    NFst(Box<Neutral>),
    NSnd(Box<Neutral>),
    NElim(Box<Value>, Vec<ElimCase>, Box<Neutral>),
    NTransport(Box<Value>, Box<Value>),
    NHComp(Box<Value>, DNF, Box<Value>, Box<Value>),
}

impl Closure {
    pub fn apply(&self, v: Value) -> Value {
        let mut env = vec![v];
        env.extend_from_slice(&self.env);
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
        let mut env = vec![v];
        env.extend_from_slice(&self.env);
        eval_nbe(&env, &self.globals, self.global_offset, &self.body)
    }
}

/// Evaluate a term with local variables in `env` and global definitions in `globals`.
///
/// `global_offset` is the index into `globals` (in env.defs order, most-recent-first)
/// corresponding to the definition whose body is being evaluated.
/// A TVar(k) where k >= env.len() is a global reference:
///   globals[global_offset + (k - env.len())]
/// UNLESS that is also out of bounds — in which case we create a neutral.
pub fn eval_nbe(env: &[Value], globals: &Globals, global_offset: usize, t: &Term) -> Value {
    match t {
        Term::TVar(i) => {
            let i = *i as usize;
            if i < env.len() {
                env[i].clone()
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
            globals, global_offset,
            eval_nbe(env, globals, global_offset, f),
            eval_nbe(env, globals, global_offset, a),
        ),
        Term::TAbs(x, b) => Value::VLam(
            x.clone(),
            Closure {
                env: env.to_vec(),
                globals: globals.clone(),
                global_offset,
                body: (**b).clone(),
            },
        ),
        Term::TUniv(n) => Value::VUniv(*n),
        Term::TIntervalTy => Value::VIntervalTy,
        Term::TPi(x, a, b) => Value::VPi(
            x.clone(),
            Box::new(eval_nbe(env, globals, global_offset, a)),
            Closure {
                env: env.to_vec(),
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
                env: env.to_vec(),
                globals: globals.clone(),
                global_offset,
                body: (**b).clone(),
            },
        ),
        Term::PApp(p, r) => do_papp(
            globals, global_offset,
            eval_nbe(env, globals, global_offset, p),
            eval_nbe(env, globals, global_offset, r),
        ),
        Term::THComp(a, phi, tube, base) => do_hcomp(
            globals, global_offset,
            eval_nbe(env, globals, global_offset, a),
            value_to_dnf(eval_nbe(env, globals, global_offset, phi)),
            eval_nbe(env, globals, global_offset, tube),
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
            globals, global_offset,
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
                Value::VGlue(Box::new(eval_nbe(env, globals, global_offset, a)), phi, Box::new(te))
            }
        }
        Term::TGlueElem(phi, t, a) => {
            let phi = value_to_dnf(eval_nbe(env, globals, global_offset, phi));
            if phi == dnf_top() {
                eval_nbe(env, globals, global_offset, t)
            } else if phi == dnf_bot() {
                eval_nbe(env, globals, global_offset, a)
            } else {
                Value::VGlueElem(phi, Box::new(eval_nbe(env, globals, global_offset, t)), Box::new(eval_nbe(env, globals, global_offset, a)))
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
                env: env.to_vec(),
                globals: globals.clone(),
                global_offset,
                body: (**b).clone(),
            },
        ),
        Term::TPair(a, b) => Value::VPair(
            Box::new(eval_nbe(env, globals, global_offset, a)),
            Box::new(eval_nbe(env, globals, global_offset, b)),
        ),
        Term::TFst(p) => do_fst(globals, global_offset, eval_nbe(env, globals, global_offset, p)),
        Term::TSnd(p) => do_snd(globals, global_offset, eval_nbe(env, globals, global_offset, p)),
        Term::TData(d) => Value::VData(d.clone()),
        Term::TCon(data, con, args) => Value::VCon(
            data.clone(),
            con.clone(),
            args.iter().map(|a| eval_nbe(env, globals, global_offset, a)).collect(),
        ),
        Term::TPCon(data, con, args, r) => Value::VPCon(
            data.clone(),
            con.clone(),
            args.iter().map(|a| eval_nbe(env, globals, global_offset, a)).collect(),
            Box::new(eval_nbe(env, globals, global_offset, r)),
        ),
        Term::TElim(motive, cases, scrut) => {
            do_elim(
                eval_nbe(env, globals, global_offset, motive),
                cases,
                eval_nbe(env, globals, global_offset, scrut),
                env,
                globals,
                global_offset,
            )
        }
    }
}

pub fn do_apply(globals: &Globals, global_offset: usize, f: Value, a: Value) -> Value {
    match f {
        Value::VLam(ref x, ref clos) => {
            let result = clos.apply(a);
            record_step("beta".into(), format!("(λ{}. _) _", x), value_str(globals, global_offset, &result));
            result
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::NApp(Box::new(n), Box::new(a))),
        other => Value::VApp(Box::new(other), Box::new(a)),
    }
}

pub fn do_papp(globals: &Globals, global_offset: usize, p: Value, r: Value) -> Value {
    if let Some(i) = value_to_endpoint(&r)
        && let Value::VPLam(_, clos) = p {
            let end_lbl = if i == I::I0 { "0" } else { "1" };
            let result = clos.apply_i(i);
            record_step("path-app".into(), format!("_ @ {}", end_lbl), value_str(globals, global_offset, &result));
            return result;
        }

    match p {
        Value::VPLam(_, clos) => match r {
            Value::VInterval(ref i) => {
                let end_lbl = if *i == I::I0 { "0".to_string() } else if *i == I::I1 { "1".to_string() } else { format!("{}", i) };
                let result = clos.apply_i(i.clone());
                record_step("path-app".into(), format!("_ @ {}", end_lbl), value_str(globals, global_offset, &result));
                result
            }
            Value::VIntervalVar(level) => clos.apply_i_var(level),
            other => Value::VPApp(
                Box::new(Value::VPLam("_".to_string(), clos)),
                Box::new(other),
            ),
        },
        Value::VNeutral(n) => Value::VNeutral(Neutral::NPApp(Box::new(n), Box::new(r))),
        // hcomp boundary reduction: (hcomp A φ tube base) @ 0 = base
        //                           (hcomp A φ tube base) @ 1 = tube @ 1
        Value::VHComp(a, phi, tube, base) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                match endpoint {
                    I::I0 => {
                        record_step("hcomp-papp-0".into(), "hcomp _ _ _ _ @ 0".into(), value_str(globals, global_offset, &base));
                        *base
                    }
                    I::I1 => {
                        let result = do_papp(globals, global_offset, *tube, Value::VInterval(I::I1));
                        record_step("hcomp-papp-1".into(), "hcomp _ _ _ _ @ 1".into(), value_str(globals, global_offset, &result));
                        result
                    }
                    _ => Value::VPApp(Box::new(Value::VHComp(a, phi, tube, base)), Box::new(r)),
                }
            } else {
                Value::VPApp(Box::new(Value::VHComp(a, phi, tube, base)), Box::new(r))
            }
        },
        other => Value::VPApp(Box::new(other), Box::new(r)),
    }
}

pub fn do_fst(globals: &Globals, global_offset: usize, p: Value) -> Value {
    match p {
        Value::VPair(a, _) => {
            record_step("fst-pair".into(), "fst (_, _)".into(), value_str(globals, global_offset, &a));
            *a
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::NFst(Box::new(n))),
        other => Value::VFst(Box::new(other)),
    }
}

pub fn do_snd(globals: &Globals, global_offset: usize, p: Value) -> Value {
    match p {
        Value::VPair(_, b) => {
            record_step("snd-pair".into(), "snd (_, _)".into(), value_str(globals, global_offset, &b));
            *b
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::NSnd(Box::new(n))),
        other => Value::VSnd(Box::new(other)),
    }
}

pub fn do_elim(motive: Value, cases: &[ElimCase], scrut: Value, env: &[Value], globals: &Globals, global_offset: usize) -> Value {
    match scrut {
        Value::VCon(ref data, ref con, ref args) => match cases.iter().find(|case| case.con == *con) {
            Some(case) => {
                let mut env2: Env = args.iter().rev().cloned().collect();
                env2.extend_from_slice(env);
                let result = eval_nbe(&env2, globals, global_offset, &case.body);
                record_step("elim-con".into(), format!("elim _ [{}] ({} {})", con, data, con), value_str(globals, global_offset, &result));
                result
            }
            None => Value::VElim(
                Box::new(motive),
                cases.to_vec(),
                Box::new(Value::VCon("".into(), con.clone(), args.clone())),
            ),
        },
        Value::VPCon(ref data, ref con, ref args, ref r) => match cases.iter().find(|case| case.con == *con) {
            Some(case) => {
                let mut env2: Env = args.iter().rev().cloned().collect();
                env2.extend_from_slice(env);
                let body = eval_nbe(&env2, globals, global_offset, &case.body);
                let result = do_papp(globals, global_offset, body, (**r).clone());
                record_step("elim-pcon".into(), format!("elim _ [{}] ({} {})", con, data, con), value_str(globals, global_offset, &result));
                result
            }
            None => Value::VElim(
                Box::new(motive),
                cases.to_vec(),
                Box::new(Value::VPCon("".into(), con.clone(), args.clone(), r.clone())),
            ),
        },
        Value::VNeutral(n) => stuck_elim(motive, cases, n),
        other => Value::VElim(Box::new(motive), cases.to_vec(), Box::new(other)),
    }
}

pub fn do_transport(env: &[Value], globals: &Globals, global_offset: usize, p: Value, x: Value) -> Value {
    match p {
        Value::VUa(e) => {
            let result = do_equiv_fwd(globals, global_offset, *e, x);
            record_step("transport-ua".into(), "transport (ua _) _".into(), value_str(globals, global_offset, &result));
            result
        }
        Value::VPLam(ref i_name, ref clos) => {
            let b0 = clos.apply_i(I::I0);
            let b1 = clos.apply_i(I::I1);
            if quote(0, globals, global_offset, b0.clone()) == quote(0, globals, global_offset, b1.clone()) {
                record_step("transport-const".into(), "transport (λi. A) x [A constant]".into(), value_str(globals, global_offset, &x));
                return x;
            }


            match (&b0, &b1) {
                (Value::VUniv(_), Value::VUniv(_)) => {
                    record_step("transport-univ".into(), "transport (λi. Univ) _".into(), value_str(globals, global_offset, &x));
                    x
                }

                // Pi transport (non-dependent codomain only)
                (Value::VPi(arg_name, _, _), Value::VPi(_, _, _)) => {
                    let result = transport_pi(env, globals, global_offset, i_name, clos, arg_name, x);
                    record_step("transport-pi".into(), "transport (λi. Π _ _) _".into(), value_str(globals, global_offset, &result));
                    result
                }

                // Path transport
                (Value::VPath(_, _, _), Value::VPath(_, _, _)) => {
                    let result = transport_path(env, globals, global_offset, i_name, clos, x);
                    record_step("transport-path".into(), "transport (λi. Path _ _ _) _".into(), value_str(globals, global_offset, &result));
                    result
                }

                // Sigma transport (pair only)
                (Value::VSigma(_, _, _), Value::VSigma(_, _, _)) => {
                    match x {
                        Value::VPair(ref a, ref b) => {
                            let result = transport_sigma_pair(env, globals, global_offset, i_name, clos, a, b);
                            record_step("transport-sigma".into(), "transport (λi. Σ _ _) (_, _)".into(), value_str(globals, global_offset, &result));
                            result
                        }
                        _ => Value::VTransport(Box::new(Value::VPLam("_".to_string(), clos.clone())), Box::new(x)),
                    }
                }

                // Glue transport (phi=bot or phi=top)
                (Value::VGlue(_, phi0, _), Value::VGlue(_, _, _)) => {
                    let r = transport_glue(env, globals, global_offset, i_name, clos, phi0, &x);
                    r.unwrap_or_else(|| {
                        Value::VTransport(Box::new(Value::VPLam("_".to_string(), clos.clone())), Box::new(x))
                    })
                }

                _ => Value::VTransport(Box::new(Value::VPLam("_".to_string(), clos.clone())), Box::new(x)),
            }
        }
        other => Value::VNeutral(Neutral::NTransport(Box::new(other), Box::new(x))),
    }
}

/// Evaluate the body of a PLam at a formal interval variable (TVar(0) in the
/// returned term will be the interval binder).
fn eval_body_at_formal_interval(env: &[Value], globals: &Globals, global_offset: usize, clos: &IClosure) -> (Vec<Value>, Value) {
    let body_with_var = beta(
        &shift(1, 0, &clos.body),
        &Term::TVar(0),
    );
    let mut formal_env = vec![Value::VIntervalVar(env.len())];
    formal_env.extend_from_slice(env);
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
        Term::TPath(a, u, v) => uses_var_at_level(a, level) || uses_var_at_level(u, level) || uses_var_at_level(v, level),
        Term::PLam(_, b) => uses_var_at_level(b, level + 1),
        Term::PApp(p, r) => uses_var_at_level(p, level) || uses_var_at_level(r, level),
        Term::THComp(a, phi, u, u0) => uses_var_at_level(a, level) || uses_var_at_level(phi, level) || uses_var_at_level(u, level) || uses_var_at_level(u0, level),
        Term::TEquiv(a, b) => uses_var_at_level(a, level) || uses_var_at_level(b, level),
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            uses_var_at_level(a, level) || uses_var_at_level(b, level) || uses_var_at_level(f, level) || uses_var_at_level(g, level) || uses_var_at_level(eta, level) || uses_var_at_level(eps, level)
        }
        Term::TEquivFwd(e, x) => uses_var_at_level(e, level) || uses_var_at_level(x, level),
        Term::TUa(e) => uses_var_at_level(e, level),
        Term::TTransport(p, x) => uses_var_at_level(p, level) || uses_var_at_level(x, level),
        Term::TGlue(a, phi, te) => uses_var_at_level(a, level) || uses_var_at_level(phi, level) || uses_var_at_level(te, level),
        Term::TGlueElem(phi, t, a) => uses_var_at_level(phi, level) || uses_var_at_level(t, level) || uses_var_at_level(a, level),
        Term::TUnglue(phi, te, g) => uses_var_at_level(phi, level) || uses_var_at_level(te, level) || uses_var_at_level(g, level),
        Term::TSigma(_, a, b) => uses_var_at_level(a, level) || uses_var_at_level(b, level + 1),
        Term::TPair(a, b) => uses_var_at_level(a, level) || uses_var_at_level(b, level),
        Term::TFst(p) => uses_var_at_level(p, level),
        Term::TSnd(p) => uses_var_at_level(p, level),
        Term::TUniv(_) | Term::TIntervalTy | Term::TInterval(_) | Term::TCube(_) | Term::TData(_) => false,
        Term::TCon(_, _, args) => args.iter().any(|a| uses_var_at_level(a, level)),
        Term::TPCon(_, _, args, r) => args.iter().any(|a| uses_var_at_level(a, level)) || uses_var_at_level(r, level),
        Term::TElim(motive, cases, scrut) => {
            uses_var_at_level(motive, level) || uses_var_at_level(scrut, level) || cases.iter().any(|c| uses_var_at_level(&c.body, level + 1))
        }
    }
}

/// Transport through Pi types.
fn transport_pi(env: &[Value], globals: &Globals, global_offset: usize, i_name: &str, clos: &IClosure, arg_name: &str, x: Value) -> Value {
    let (formal_env, pi_at_var) = eval_body_at_formal_interval(env, globals, global_offset, clos);
    let cod_clos = match &pi_at_var {
        Value::VPi(_, _, cod_clos) => cod_clos,
        _ => return Value::VTransport(
            Box::new(Value::VPLam("_".to_string(), clos.clone())),
            Box::new(x),
        ),
    };

    if !uses_var_at_level(&cod_clos.body, 0i32) {
        let b_val = apply_non_dep(cod_clos);
        let b_body = shift(1, 1, &quote(formal_env.len(), globals, global_offset, b_val));
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
        let p_term = quote(env.len(), globals, global_offset, Value::VPLam(i_name.to_string(), clos.clone()));
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
fn transport_path(env: &[Value], globals: &Globals, global_offset: usize, i_name: &str, clos: &IClosure, x: Value) -> Value {
    let (formal_env, path_at_var) = eval_body_at_formal_interval(env, globals, global_offset, clos);
    let a_val = match &path_at_var {
        Value::VPath(a, _, _) => *a.clone(),
        _ => return Value::VTransport(
            Box::new(Value::VPLam("_".to_string(), clos.clone())),
            Box::new(x),
        ),
    };
    let a_body = shift(1, 1, &quote(formal_env.len(), globals, global_offset, a_val));
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
    env: &[Value],
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    a: &Value,
    b: &Value,
) -> Value {
    let (formal_env, sigma_at_var) = eval_body_at_formal_interval(env, globals, global_offset, clos);
    let a_val = match &sigma_at_var {
        Value::VSigma(_, a_val, _) => *a_val.clone(),
        _ => Value::VUniv(0),
    };
    let a_body = shift(1, 1, &quote(formal_env.len(), globals, global_offset, a_val));
    let a_fam = Term::PLam(i_name.to_string(), Box::new(a_body));

    let a_prime = eval_nbe(env, globals, global_offset, &Term::TTransport(
        Box::new(a_fam.clone()),
        Box::new(quote(env.len(), globals, global_offset, a.clone())),
    ));

    let b_val = match &sigma_at_var {
        Value::VSigma(_, _, cod_clos) => apply_non_dep(cod_clos),
        _ => Value::VUniv(0),
    };
    let b_body = shift(1, 1, &quote(formal_env.len(), globals, global_offset, b_val));
    let b_fam = Term::PLam(i_name.to_string(), Box::new(b_body));

    let b_prime = eval_nbe(env, globals, global_offset, &Term::TTransport(
        Box::new(b_fam),
        Box::new(quote(env.len(), globals, global_offset, b.clone())),
    ));

    Value::VPair(Box::new(a_prime), Box::new(b_prime))
}

/// Transport through Glue types.
fn transport_glue(
    env: &[Value],
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    phi0: &DNF,
    x: &Value,
) -> Option<Value> {
    if *phi0 == dnf_bot() {
        let (formal_env, glue_at_var) = eval_body_at_formal_interval(env, globals, global_offset, clos);
        let a_val = match &glue_at_var {
            Value::VGlue(a, _, _) => *a.clone(),
            _ => return None,
        };
        let a_body = shift(1, 1, &quote(formal_env.len(), globals, global_offset, a_val));
        let a_fam = Term::PLam(i_name.to_string(), Box::new(a_body));
        Some(eval_nbe(env, globals, global_offset, &Term::TTransport(
            Box::new(a_fam),
            Box::new(quote(env.len(), globals, global_offset, x.clone())),
        )))
    } else if *phi0 == dnf_top() {
        let (formal_env, glue_at_var) = eval_body_at_formal_interval(env, globals, global_offset, clos);
        let te_val = match &glue_at_var {
            Value::VGlue(_, _, te) => *te.clone(),
            _ => return None,
        };
        let dom = equiv_dom_value(te_val);
        let dom_body = shift(1, 1, &quote(formal_env.len(), globals, global_offset, dom));
        let dom_fam = Term::PLam(i_name.to_string(), Box::new(dom_body));
        Some(eval_nbe(env, globals, global_offset, &Term::TTransport(
            Box::new(dom_fam),
            Box::new(quote(env.len(), globals, global_offset, x.clone())),
        )))
    } else {
        // Non-trivial face: decompose glue elements using the cubical Glue transport rule.
        // transp (λi. Glue A [φ] te) (glue [φ] t a)
        //   = glue [φ] t (hcomp A [φ] (λi. t) a)
        // where t stays the same (constant equiv domain) and the base is composed
        // via hcomp to maintain the boundary condition on face φ.
        match x {
            Value::VGlueElem(phi_elem, t, a) if *phi_elem == *phi0 => {
                let (_, glue_at_var) = eval_body_at_formal_interval(env, globals, global_offset, clos);
                let a_ty = match &glue_at_var {
                    Value::VGlue(a, _, _) => *a.clone(),
                    _ => return None,
                };

                // tube = λi. t  (constant tube in hcomp)
                let t_body = shift(1, 0, &quote(env.len(), globals, global_offset, *t.clone()));
                let tube = Term::PLam(i_name.to_string(), Box::new(t_body));
                let tube_val = eval_nbe(env, globals, global_offset, &tube);

                let hcomp_val = do_hcomp(globals, global_offset, a_ty, phi0.clone(), tube_val, *a.clone());

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
                                Box::new(nbe_eval(&Term::TApp(Box::new(x_shifted), Box::new(Term::TVar(0))))),
                            ))),
                        )
                    } else {
                        let b_non_dep = match &b0 {
                            Term::TPi(_, _, b0_body) => subst(0, &Term::TUniv(0), b0_body) == **b0_body,
                            _ => false,
                        };
                        if b_non_dep {
                            let b0_body = match &b0 {
                                Term::TPi(_, _, b) => (**b).clone(),
                                _ => b0.clone(),
                            };
                            let b_fam = Term::PLam(
                                i_name.clone(),
                                Box::new(match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                    Term::TPi(_, _, b_i) => *b_i,
                                    _ => shift(1, 0, &b0_body),
                                }),
                            );
                            let x_shifted = shift(1, 0, &x_);
                            Term::TAbs(
                                arg_name,
                                Box::new(nbe_eval(&Term::TTransport(
                                    Box::new(b_fam),
                                    Box::new(nbe_eval(&Term::TApp(Box::new(x_shifted), Box::new(Term::TVar(0))))),
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

                (Term::TSigma(_, _, _), Term::TSigma(_, _, _)) => {
                    match x_ {
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
                    }
                }

                (Term::TGlue(_, phi0, _), Term::TGlue(_, _, _)) => {
                    let i_name = i_name.clone();
                    if is_bot_dnf(&nbe_eval(phi0)) {
                        nbe_eval(&Term::TTransport(
                            Box::new(Term::PLam(
                                i_name.clone(),
                                Box::new(match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                    Term::TGlue(a, _, _) => *a,
                                    other => other,
                                }),
                            )),
                            Box::new(x_),
                        ))
                    } else if is_top_dnf(&nbe_eval(phi0)) {
                        nbe_eval(&Term::TTransport(
                            Box::new(Term::PLam(
                                i_name.clone(),
                                Box::new(match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                    Term::TGlue(_, _, te) => equiv_dom(&nbe_eval(&te)),
                                    other => other,
                                }),
                            )),
                            Box::new(x_),
                        ))
                    } else {
                        // Non-trivial face: if x_ is a GlueElem with matching face, decompose.
                        match &x_ {
                            Term::TGlueElem(phi_elem, t, a) if nbe_eval(phi0) == nbe_eval(phi_elem) => {
                                let a_ty = match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0))) {
                                    Term::TGlue(a, _, _) => *a,
                                    other => other,
                                };
                                let tube = Term::PLam(
                                    i_name.clone(),
                                    Box::new(shift(1, 0, &*t)),
                                );
                                let hcomp = Term::THComp(
                                    Box::new(a_ty),
                                    phi0.clone(),
                                    Box::new(tube),
                                    (*a).clone(),
                                );
                                Term::TGlueElem(phi0.clone(), t.clone(), Box::new(hcomp))
                            }
                            _ => Term::TTransport(Box::new(Term::PLam(i_name, body.clone())), Box::new(x_)),
                        }
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

pub fn do_hcomp(globals: &Globals, global_offset: usize, a_ty: Value, phi: DNF, tube: Value, base: Value) -> Value {
    if phi == dnf_top() {
        let result = do_papp(globals, global_offset, tube, Value::VInterval(I::I1));
        record_step("hcomp-top".into(), "hcomp A ⊤ tube base".into(), value_str(globals, global_offset, &result));
        result
    } else if phi == dnf_bot() {
        record_step("hcomp-bot".into(), "hcomp A ⊥ tube base".into(), value_str(globals, global_offset, &base));
        base
    } else {
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
                // Evaluate tube and base at a fresh argument variable
                let tube_at_arg = match &tube {
                    Value::VPLam(_, iclos) => {
                        let formal_i = Value::VIntervalVar(0);
                        let tube_at_i = iclos.apply_interval_value(formal_i);
                        do_apply(globals, global_offset, tube_at_i, arg_var.clone())
                    }
                    _ => do_apply(globals, global_offset, tube.clone(), arg_var.clone()),
                };
                let base_at_arg = base_clos.apply(arg_var.clone());
                let cod_at_arg = cod_clos.apply(arg_var);
                let inner = do_hcomp(globals, global_offset, cod_at_arg, phi.clone(), tube_at_arg, base_at_arg);
                let result = Value::VLam(arg_name.clone(), Closure {
                    env: vec![],
                    globals: globals.clone(),
                    global_offset,
                    body: {
                        let inner_term = quote(1, globals, global_offset, inner);
                        Term::TAbs(arg_name.clone(), Box::new(inner_term))
                    },
                });
                record_step("hcomp-pi".into(), "hcomp (Π _ _) φ f g".into(), value_str(globals, global_offset, &result));
                result
            }

            // ── Sigma decomposition ──
            (Value::VSigma(_, fst_ty, snd_clos), Value::VPair(fst_base, snd_base)) => {
                let fst_tube = match &tube {
                    Value::VPLam(_, iclos) => {
                        let formal_i = Value::VIntervalVar(0);
                        let tube_at_i = iclos.apply_interval_value(formal_i);
                        do_fst(globals, global_offset, tube_at_i)
                    }
                    _ => Value::VPApp(Box::new(tube.clone()), Box::new(Value::VIntervalVar(0))),
                };
                let fst_tube_plam = Value::VPLam("_".to_string(), IClosure {
                    env: vec![],
                    globals: globals.clone(),
                    global_offset,
                    body: quote(1, globals, global_offset, fst_tube),
                });
                let fst_result = do_hcomp(globals, global_offset, *fst_ty.clone(), phi.clone(), fst_tube_plam, (**fst_base).clone());

                let snd_tube = match &tube {
                    Value::VPLam(_, iclos) => {
                        let formal_i = Value::VIntervalVar(0);
                        let tube_at_i = iclos.apply_interval_value(formal_i);
                        do_snd(globals, global_offset, tube_at_i)
                    }
                    _ => Value::VPApp(Box::new(tube.clone()), Box::new(Value::VIntervalVar(0))),
                };
                let snd_tube_plam = Value::VPLam("_".to_string(), IClosure {
                    env: vec![],
                    globals: globals.clone(),
                    global_offset,
                    body: quote(1, globals, global_offset, snd_tube),
                });
                let snd_result = do_hcomp(globals, global_offset,
                    snd_clos.apply((**fst_base).clone()), phi.clone(), snd_tube_plam, (**snd_base).clone());

                let result = Value::VPair(Box::new(fst_result), Box::new(snd_result));
                record_step("hcomp-sigma".into(), "hcomp (Σ _ _) φ p q".into(), value_str(globals, global_offset, &result));
                result
            }

            // ── Default: stuck hcomp ──
            _ => Value::VHComp(Box::new(a_ty), phi, Box::new(tube), Box::new(base)),
        }
    }
}

pub fn quote(size: usize, globals: &Globals, global_offset: usize, v: Value) -> Term {
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
        Value::VApp(f, a) => Term::TApp(Box::new(quote(size, globals, global_offset, *f)), Box::new(quote(size, globals, global_offset, *a))),
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
        Value::VPair(a, b) => Term::TPair(Box::new(quote(size, globals, global_offset, *a)), Box::new(quote(size, globals, global_offset, *b))),
        Value::VFst(p) => Term::TFst(Box::new(quote(size, globals, global_offset, *p))),
        Value::VSnd(p) => Term::TSnd(Box::new(quote(size, globals, global_offset, *p))),
        Value::VPath(a, u, v) => Term::TPath(
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(quote(size, globals, global_offset, *u)),
            Box::new(quote(size, globals, global_offset, *v)),
        ),
        Value::VPLam(x, clos) => Term::PLam(x, Box::new(quote(size + 1, globals, global_offset, clos.apply_i_var(size)))),
        Value::VPApp(p, r) => Term::PApp(Box::new(quote(size, globals, global_offset, *p)), Box::new(quote(size, globals, global_offset, *r))),
        Value::VUniv(n) => Term::TUniv(n),
        Value::VIntervalTy => Term::TIntervalTy,
        Value::VInterval(i) => Term::TInterval(i),
        Value::VIntervalVar(level) => level_to_var(size, level),
        Value::VCube(c) => Term::TCube(c),
        Value::VData(d) => Term::TData(d),
        Value::VCon(d, c, args) => {
            Term::TCon(d, c, args.into_iter().map(|a| quote(size, globals, global_offset, a)).collect())
        }
        Value::VPCon(d, c, args, r) => Term::TPCon(
            d,
            c,
            args.into_iter().map(|a| quote(size, globals, global_offset, a)).collect(),
            Box::new(quote(size, globals, global_offset, *r)),
        ),
        Value::VElim(motive, cases, scrut) => Term::TElim(
            Box::new(quote(size, globals, global_offset, *motive)),
            quote_cases(size, globals, global_offset, cases),
            Box::new(quote(size, globals, global_offset, *scrut)),
        ),
        Value::VGlue(a, phi, te) => Term::TGlue(
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(Term::TCube(phi)),
            Box::new(quote(size, globals, global_offset, *te)),
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
        Value::VEquiv(a, b) => Term::TEquiv(Box::new(quote(size, globals, global_offset, *a)), Box::new(quote(size, globals, global_offset, *b))),
        Value::VMkEquiv(a, b, f, g, eta, eps) => Term::TMkEquiv(
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(quote(size, globals, global_offset, *b)),
            Box::new(quote(size, globals, global_offset, *f)),
            Box::new(quote(size, globals, global_offset, *g)),
            Box::new(quote(size, globals, global_offset, *eta)),
            Box::new(quote(size, globals, global_offset, *eps)),
        ),
        Value::VEquivFwd(e, x) => {
            Term::TEquivFwd(Box::new(quote(size, globals, global_offset, *e)), Box::new(quote(size, globals, global_offset, *x)))
        }
        Value::VUa(e) => Term::TUa(Box::new(quote(size, globals, global_offset, *e))),
        Value::VTransport(p, x) => {
            Term::TTransport(Box::new(quote(size, globals, global_offset, *p)), Box::new(quote(size, globals, global_offset, *x)))
        }
        Value::VHComp(a, phi, tube, base) => Term::THComp(
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(Term::TCube(phi)),
            Box::new(quote(size, globals, global_offset, *tube)),
            Box::new(quote(size, globals, global_offset, *base)),
        ),
    }
}

fn quote_neutral(size: usize, globals: &Globals, global_offset: usize, n: Neutral) -> Term {
    match n {
        Neutral::NVar(level) => level_to_var(size, level),
        Neutral::NApp(f, a) => {
            Term::TApp(Box::new(quote_neutral(size, globals, global_offset, *f)), Box::new(quote(size, globals, global_offset, *a)))
        }
        Neutral::NPApp(p, r) => {
            Term::PApp(Box::new(quote_neutral(size, globals, global_offset, *p)), Box::new(quote(size, globals, global_offset, *r)))
        }
        Neutral::NFst(p) => Term::TFst(Box::new(quote_neutral(size, globals, global_offset, *p))),
        Neutral::NSnd(p) => Term::TSnd(Box::new(quote_neutral(size, globals, global_offset, *p))),
        Neutral::NElim(motive, cases, scrut) => Term::TElim(
            Box::new(quote(size, globals, global_offset, *motive)),
            quote_cases(size, globals, global_offset, cases),
            Box::new(quote_neutral(size, globals, global_offset, *scrut)),
        ),
        Neutral::NTransport(p, x) => {
            Term::TTransport(Box::new(quote(size, globals, global_offset, *p)), Box::new(quote(size, globals, global_offset, *x)))
        }
        Neutral::NHComp(a, phi, tube, base) => Term::THComp(
            Box::new(quote(size, globals, global_offset, *a)),
            Box::new(Term::TCube(phi)),
            Box::new(quote(size, globals, global_offset, *tube)),
            Box::new(quote(size, globals, global_offset, *base)),
        ),
    }
}

fn quote_cases(size: usize, globals: &Globals, global_offset: usize, cases: Vec<ElimCase>) -> Vec<ElimCase> {
    cases
        .into_iter()
        .map(|case| ElimCase {
            con: case.con,
            binders: case.binders.clone(),
            body: Box::new(normalize_under_binders(
                size,
                case.binders.len(),
                globals,
                global_offset,
                &case.body,
            )),
        })
        .collect()
}

fn normalize_under_binders(size: usize, binders: usize, globals: &Globals, global_offset: usize, body: &Term) -> Term {
    let mut env = Vec::new();
    for level in (size..size + binders).rev() {
        env.push(Value::VNeutral(Neutral::NVar(level)));
    }
    quote(size + binders, globals, global_offset, eval_nbe(&env, globals, global_offset, body))
}

pub fn normalize(env: &[Value], globals: &Globals, global_offset: usize, t: &Term) -> Term {
    quote(env.len(), globals, global_offset, eval_nbe(env, globals, global_offset, t))
}

/// Evaluate a closed term without global definitions (original behavior).
pub fn nbe_eval(t: &Term) -> Term {
    let empty_globals: Globals = Rc::new(RefCell::new(Vec::new()));
    let mv = max_var(t);
    if mv < 0 {
        normalize(&[], &empty_globals, 0, t)
    } else {
        let size = (mv + 1) as usize;
        let mut env = Vec::with_capacity(size);
        for level in (0..size).rev() {
            env.push(Value::VNeutral(Neutral::NVar(level)));
        }
        normalize(&env, &empty_globals, 0, t)
    }
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
    normalize(&[], globals, global_offset, t)
}

fn do_equiv_fwd(globals: &Globals, global_offset: usize, e: Value, x: Value) -> Value {
    match e {
        Value::VMkEquiv(_, _, f, _, _, _) => {
            let result = do_apply(globals, global_offset, *f, x);
            record_step("equiv-fwd".into(), "equivFwd (mkEquiv _ _ f _ _ _) _".into(), value_str(globals, global_offset, &result));
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

fn stuck_elim(motive: Value, cases: &[ElimCase], n: Neutral) -> Value {
    Value::VNeutral(Neutral::NElim(
        Box::new(motive),
        cases.to_vec(),
        Box::new(n),
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

fn level_to_var(size: usize, level: usize) -> Term {
    if level < size {
        Term::TVar((size - level - 1) as i32)
    } else {
        Term::TVar(level.saturating_sub(size) as i32)
    }
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
        let sigma = Term::TSigma(
            "x".to_string(),
            b(Term::TUniv(0)),
            b(Term::TUniv(1)),
        );
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
        // hcomp A (i0) tube base @ 0 should reduce to base
        // (non-trivial face keeps hcomp stuck until papp)
        let tube = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let hcomp = Term::THComp(
            b(Term::TUniv(0)),
            b(Term::TInterval(I::Var(0))),
            b(tube),
            b(Term::TUniv(1)),
        );
        let term = Term::PApp(b(hcomp), b(Term::TInterval(I::I0)));
        let result = nbe_eval(&term);
        assert_eq!(result, Term::TUniv(1));
    }

    #[test]
    fn hcomp_papp_at_one_reduces_to_tube_at_one() {
        // hcomp A (i0) tube base @ 1 should reduce to tube @ 1
        let tube = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let hcomp = Term::THComp(
            b(Term::TUniv(0)),
            b(Term::TInterval(I::Var(0))),
            b(tube),
            b(Term::TUniv(1)),
        );
        let term = Term::PApp(b(hcomp), b(Term::TInterval(I::I1)));
        let result = nbe_eval(&term);
        assert_eq!(result, Term::TUniv(0));
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
            b(Term::TVar(0)),         // A varies with i → makes family non-constant
            b(non_trivial_phi.clone()),
            b(Term::TUniv(0)),        // te
        );
        let fam = Term::PLam("i".to_string(), b(glue_ty));
        let cap = Term::TUniv(1);
        let base = Term::TUniv(2);
        let glue_elem = Term::TGlueElem(
            b(non_trivial_phi.clone()),
            b(cap),
            b(base),
        );
        let transport = Term::TTransport(b(fam), b(glue_elem));
        let globals: Globals = Rc::new(RefCell::new(Vec::new()));
        let result = eval_nbe(&[], &globals, 0, &transport);
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
                    Value::VHComp(_, h_phi, _, h_base) => {
                        assert_eq!(h_phi, phi_dnf, "hcomp face should match");
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
        let glue_ty = Term::TGlue(
            b(Term::TVar(0)),
            b(non_trivial_phi),
            b(Term::TUniv(0)),
        );
        let fam = Term::PLam("i".to_string(), b(glue_ty));
        let transport = Term::TTransport(b(fam), b(Term::TUniv(0)));
        let globals: Globals = Rc::new(RefCell::new(Vec::new()));
        let result = eval_nbe(&[], &globals, 0, &transport);
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
        let glue_ty = Term::TGlue(
            b(Term::TVar(0)),
            b(phi1),
            b(Term::TUniv(0)),
        );
        let fam = Term::PLam("i".to_string(), b(glue_ty));
        let glue_elem = Term::TGlueElem(
            b(phi2),
            b(Term::TUniv(1)),
            b(Term::TUniv(2)),
        );
        let transport = Term::TTransport(b(fam), b(glue_elem));
        let globals: Globals = Rc::new(RefCell::new(Vec::new()));
        let result = eval_nbe(&[], &globals, 0, &transport);
        match result {
            Value::VTransport(_, _) => {}
            other => panic!("expected stuck VTransport on face mismatch, got: {:?}", other),
        }
    }
}
