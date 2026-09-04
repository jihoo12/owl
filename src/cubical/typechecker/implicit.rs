// Implicit argument resolution for the typechecker.
//
// When a function type has implicit Pi binders `{x : A}`, we search the
// context for a term of type `A` and apply it automatically.

use std::sync::Arc;

use crate::cubical::equality::{EtaResult, definitionally_equal_ctx_r};
use crate::cubical::nbe::nbe_eval_ctx;
use crate::cubical::session::Session;
use crate::cubical::syntax::{Datatype, Term, beta, shift};

use super::context::Ctx;

/// Try to find a term in the context that matches the given type.
/// This is used for implicit argument resolution - when we have an implicit
/// binder `{x : A}`, we search the context for a term of type `A`.
pub fn find_implicit_arg(
    _dts: &[Datatype],
    ctx: &Ctx,
    target_ty: &Term,
    session: &mut Session,
) -> Option<Term> {
    let target_nf = nbe_eval_ctx(ctx.len(), target_ty, session);
    for (i, (_name, ty)) in ctx.iter().enumerate() {
        // Stored binder types are recorded relative to the binder's own frame
        // (binder at index 0); re-anchor with the same shift `lookup_ctx`
        // applies before comparing against the target.
        let ty_shifted = shift(i as i32 + 1, 0, ty);
        let ty_nf = nbe_eval_ctx(ctx.len(), &ty_shifted, session);
        if definitionally_equal_ctx_r(ctx, &ty_nf, &target_nf, session) == EtaResult::Equal {
            return Some(Term::TVar(i as i32));
        }
    }
    None
}

/// Fill in implicit Pi arguments in a function type.
/// Given a function type like `Π {x : A} (y : B) {z : C}. D`,
/// and a context, this searches for implicit arguments and applies them.
/// Returns the updated function term with implicit args applied, and the
/// remaining type after implicit args are filled.
pub fn fill_implicit_args(
    _dts: &[Datatype],
    ctx: &Ctx,
    mut f: Term,
    mut f_ty: Term,
    session: &mut Session,
) -> Result<(Term, Term), crate::cubical::typechecker::errors::TypeError> {
    loop {
        let f_ty_nf = nbe_eval_ctx(ctx.len(), &f_ty, session);
        match f_ty_nf {
            Term::TPi(_x, a, b, implicit) if implicit => {
                // Search for an implicit argument of type `a`
                if let Some(arg) = find_implicit_arg(_dts, ctx, &a, session) {
                    let arg_clone = arg.clone();
                    // Apply the implicit argument
                    f = Term::TApp(Arc::new(f), Arc::new(arg));
                    // Update the type to the codomain with the argument substituted
                    f_ty = beta(&b, &arg_clone);
                    // Continue the loop in case there are more implicit args
                    continue;
                }
                // No implicit arg found - we'll need the user to provide it explicitly
                break;
            }
            _ => break,
        }
    }
    Ok((f, f_ty))
}
