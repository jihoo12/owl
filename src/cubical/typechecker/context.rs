// Context type and basic context operations for the typechecker.

use crate::cubical::syntax::{Name, Term, shift};

use super::errors::TypeError;

pub type Ctx = Vec<(Name, Term)>;

pub fn err_names(ctx: &Ctx) -> Vec<Name> {
    ctx.iter().map(|(n, _)| n.clone()).collect()
}

pub fn interval_ty() -> Term {
    Term::TIntervalTy
}

pub fn extend_ctx(x: Name, ty: Term, ctx: &Ctx) -> Ctx {
    let mut ctx2 = vec![(x, ty)];
    ctx2.extend_from_slice(ctx);
    ctx2
}

pub fn lookup_ctx(i: i32, ctx: &Ctx) -> Result<Term, TypeError> {
    if i < 0 || i as usize >= ctx.len() {
        Err(TypeError::UnboundVariable(format!("#{}", i)))
    } else {
        // Return the declared type unnormalized. Normalizing here bakes
        // quoted elim case bodies (whose global refs are re-anchored to
        // absolute frame positions) into the type; beta-substituting
        // arguments into that quoted normal form then leaves stale
        // re-anchored references that never re-resolve on the second pass.
        // Consumers normalize at the point of comparison, so a single
        // normalization pass from the raw type keeps both sides consistent.
        Ok(shift(i + 1, 0, &ctx[i as usize].1))
    }
}
