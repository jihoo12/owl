//! Small helpers shared across the nbe submodules.

use std::sync::{Arc, Mutex};

use super::elim::do_apply;
use super::quote::quote;
use super::trace::record_step;
use super::value::{Globals, Value, value_str};
use crate::cubical::interval::{DNF, I, dnf_bot, dnf_top, eval_interval};
use crate::cubical::session::Session;
use crate::cubical::syntax::Term;

// -- util: do_equiv_fwd -----------------------------------------------------

pub(super) fn do_equiv_fwd(
    globals: &Globals,
    global_offset: usize,
    e: Value,
    x: Value,
    session: &mut Session,
) -> Value {
    match e {
        Value::VMkEquiv(_, _, f, _, _, _) => {
            let result = do_apply(globals, global_offset, f.as_ref().clone(), x, session);
            record_step(
                "equiv-fwd".into(),
                "equivFwd (mkEquiv _ _ f _ _ _) _".into(),
                value_str(globals, global_offset, &result, session),
            );
            result
        }
        other => Value::VEquivFwd(Arc::new(other), Arc::new(x)),
    }
}

// -- util: equiv_dom_value --------------------------------------------------

pub(super) fn equiv_dom_value(v: Value) -> Value {
    match v {
        Value::VMkEquiv(a, _, _, _, _, _) | Value::VEquiv(a, _) => a.as_ref().clone(),
        Value::VPair(a, _) => a.as_ref().clone(),
        other => other,
    }
}

pub(super) fn equiv_cod_value(v: Value) -> Value {
    match v {
        Value::VMkEquiv(_, b, _, _, _, _) | Value::VEquiv(_, b) => b.as_ref().clone(),
        Value::VPair(_, b) => b.as_ref().clone(),
        other => other,
    }
}

// -- util: value_to_dnf ------------------------------------------------------

pub(super) fn value_to_dnf(v: Value, session: &mut Session) -> DNF {
    match v {
        Value::VCube(d) => d,
        Value::VInterval(i) => eval_interval(&i),
        Value::VIntervalVar(level) => eval_interval(&I::Var(level as i32)),
        other => match quote(0, &Arc::new(Mutex::new(Vec::new())), 0, other, session) {
            Term::TCube(d) => d,
            Term::TInterval(i) => eval_interval(&i),
            _ => dnf_bot(),
        },
    }
}

// -- util: value_to_endpoint -------------------------------------------------

pub(super) fn value_to_endpoint(v: &Value) -> Option<I> {
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
