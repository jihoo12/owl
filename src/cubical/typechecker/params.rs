// Parameter inference and argument checking for parameterized constructors.
//
// Shared by TCon/TPCon/TSqCon/TCellCon.

use crate::cubical::nbe::nbe_eval;
use crate::cubical::session::Session;
use crate::cubical::syntax::{Datatype, Term, subst_params};

use super::context::Ctx;
use super::errors::TypeError;
use super::{check_dt, infer_dt};

/// Two-phase helper for parameterized constructor checking:
///
/// 1. **Phase 1 — Infer params:** Walk the argument list; when the
///    (partially-substituted) expected type for an argument is a bare
///    `TVar(k)` with `k < num_params`, the argument *is* the parameter
///    value — infer its type from the context.
///
/// 2. **Phase 2 — Check args:** Walk again with fully-substituted arg_tys,
///    checking each argument against its expected type.
///
/// `initial_params` optionally pre-seeds some parameters (e.g. from an
/// expected type in bidirectional checking).  Its length must equal
/// `num_params`.
///
/// Returns `(param_terms, checked_args)` where `param_terms[i]` is
/// `Some(term)` if parameter `i` was inferred, `None` otherwise.
pub fn infer_and_check_params(
    dts: &[Datatype],
    ctx: &Ctx,
    sig_arg_tys: &[Term],
    args: &[Term],
    num_params: usize,
    session: &mut Session,
) -> Result<(Vec<Option<Term>>, Vec<Term>), TypeError> {
    infer_and_check_params_seeded(dts, ctx, sig_arg_tys, args, num_params, &[], session)
}

/// Like `infer_and_check_params` but accepts pre-seeded parameter values.
pub fn infer_and_check_params_seeded(
    dts: &[Datatype],
    ctx: &Ctx,
    sig_arg_tys: &[Term],
    args: &[Term],
    num_params: usize,
    initial_params: &[Option<Term>],
    session: &mut Session,
) -> Result<(Vec<Option<Term>>, Vec<Term>), TypeError> {
    debug_assert!(initial_params.len() <= num_params);
    // Phase 1: Infer parameter values from argument types.
    let mut param_terms: Vec<Option<Term>> = initial_params.to_vec();
    param_terms.resize(num_params, None);
    {
        let mut prev_args: Vec<Term> = Vec::new();
        for (k, arg) in args.iter().enumerate() {
            let mut arg_ty = sig_arg_tys[k].clone();
            // Use parallel substitution to avoid sequential subst interference:
            // when param values contain TVar(0) (e.g. inside `fun X => mkR ...`),
            // sequential subst calls corrupt each other's de Bruijn indices.
            arg_ty = subst_params(num_params, &param_terms, &arg_ty);
            if let Term::TVar(idx) = &arg_ty {
                let i = *idx as usize;
                if i < num_params && param_terms[i].is_none() {
                    param_terms[i] = Some(infer_dt(dts, ctx, arg, session)?);
                    continue;
                }
            }
            prev_args.push(nbe_eval(arg, session));
        }
    }
    // Phase 2: Check args with fully-substituted arg_tys.
    let mut checked_args: Vec<Term> = Vec::with_capacity(args.len());
    for (k, arg) in args.iter().enumerate() {
        let arg_ty = subst_params(num_params, &param_terms, &sig_arg_tys[k]);
        // NOTE: We intentionally do NOT apply previous-arg substitution here.
        // The arg_tys telescope references only datatype parameters (via de Bruijn
        // indices), not previous constructor arguments.  Using `beta` would
        // incorrectly shift(-1,0,...) all free variables after substitution,
        // corrupting indices.  Dependent record fields (where a field type
        // references a previous field) are not yet supported.
        check_dt(dts, ctx, arg, &nbe_eval(&arg_ty, session), session)?;
        checked_args.push(nbe_eval(arg, session));
    }
    Ok((param_terms, checked_args))
}

/// Build the parameter list for a return type from inferred param terms.
/// Uninferred params default to `TVar(i)`.
pub fn build_params(param_terms: &[Option<Term>]) -> Vec<Term> {
    param_terms
        .iter()
        .enumerate()
        .map(|(i, p)| p.clone().unwrap_or_else(|| Term::TVar(i as i32)))
        .collect()
}
