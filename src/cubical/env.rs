// Cubical Env — Rust port of Env.hs
//
// Depends on:
//   crate::syntax::{Name, Term, Datatype, shift, subst}
//   crate::typechecker::{Ctx, TypeError, infer, check, infer_dt, check_dt}

use crate::cubical::syntax::{Datatype, Name, Term, shift, subst};
use crate::cubical::typechecker::{Ctx, TypeError, check, check_dt, infer, infer_dt};

// ---------------------------------------------------------------------------
// Global Named Environment
// ---------------------------------------------------------------------------

/// A global definition: `(name, type, value)`.
/// Stored most-recent first.
pub type GlobalEnv = Vec<(Name, Term, Term)>;

/// A full top-level environment: named definitions plus datatype declarations.
///
/// `defs` mirrors `GlobalEnv` — a list of `(name, type, value)` triples,
/// most-recent first, whose de Bruijn indices are assigned by declaration
/// order (most-recent = index 0 at the point of reference).
///
/// `datatypes` is a flat list of all declared datatypes, in declaration order.
/// Order doesn't affect typechecking (datatype lookup is by name), but
/// most-recent-first matches the `defs` convention so the parser can push
/// uniformly.
#[derive(Debug, Clone, Default)]
pub struct Env {
    pub defs: GlobalEnv,
    pub datatypes: Vec<Datatype>,
}

impl Env {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a definition `name : ty = val` to the front of the env.
    /// The caller is responsible for ensuring `val` and `ty` are already
    /// closed/resolved with respect to existing globals (i.e. `apply_globals`
    /// has been called on them if they contain global references).
    pub fn define(&mut self, name: Name, ty: Term, val: Term) {
        self.defs.insert(0, (name, ty, val));
    }

    /// Register a datatype declaration.
    pub fn declare_datatype(&mut self, dt: Datatype) {
        self.datatypes.push(dt);
    }

    /// Look up a datatype by name.
    #[allow(dead_code)]
    pub fn find_datatype(&self, name: &str) -> Option<&Datatype> {
        self.datatypes.iter().find(|dt| dt.name == name)
    }
}

// ---------------------------------------------------------------------------
// Context / substitution helpers (unchanged from GlobalEnv era)
// ---------------------------------------------------------------------------

/// Build a `Ctx` from the definitions in an `Env` (or a bare `GlobalEnv`).
/// Variables are ordered innermost-first, matching `GlobalEnv`'s
/// most-recent-first order (most-recent global = de Bruijn index 0).
pub fn global_ctx(genv: &GlobalEnv) -> Ctx {
    genv.iter()
        .map(|(name, ty, _)| (name.clone(), ty.clone()))
        .collect()
}

/// Substitute all global definitions into a term directly via de Bruijn
/// substitution, rather than wrapping in `TApp`/`TAbs` chains.
///
/// The parser assigns globals indices starting at `length localEnv`.
/// At the top level `localEnv` is empty, so globals occupy indices `0..n-1`
/// with the most-recent global at index 0.
///
/// We substitute one global at a time, outermost (highest index) first,
/// so that earlier substitutions don't disturb the indices of later ones.
/// After substituting index `k`, we shift the term down by 1 to close the gap.
pub fn apply_globals(genv: &GlobalEnv, t: &Term) -> Term {
    // Remove globals from the outside in: the oldest definition has the
    // highest de Bruijn index, so substituting it first cannot disturb the
    // indices of newer globals that still need to be substituted.
    let n = genv.len();
    (0..n).rev().fold(t.clone(), |body, k| {
        let (_, _, v) = &genv[k];
        subst_global(k as i32, v, &body)
    })
}

/// Substitute the global at de Bruijn index `k` with its value `v`,
/// then shift the whole term down by 1 to account for the removed binding.
fn subst_global(k: i32, v: &Term, body: &Term) -> Term {
    shift(-1, k, &subst(k, &shift(k, 0, v), body))
}

// ---------------------------------------------------------------------------
// Typing with GlobalEnv (backward-compatible, no datatypes)
// ---------------------------------------------------------------------------

/// Infer the type of a term in the context of a `GlobalEnv` (no datatypes).
#[allow(dead_code)]
pub fn infer_with_env(genv: &GlobalEnv, t: &Term) -> Result<Term, TypeError> {
    infer(&global_ctx(genv), t)
}

/// Check a term against a type in the context of a `GlobalEnv` (no datatypes).
#[allow(dead_code)]
pub fn check_with_env(genv: &GlobalEnv, t: &Term, ty: &Term) -> Result<(), TypeError> {
    check(&global_ctx(genv), t, ty)
}

// ---------------------------------------------------------------------------
// Typing with full Env (definitions + datatypes)
// ---------------------------------------------------------------------------

/// Infer the type of a term in a full `Env`.
pub fn infer_with_full_env(env: &Env, t: &Term) -> Result<Term, TypeError> {
    infer_dt(&env.datatypes, &global_ctx(&env.defs), t)
}

/// Check a term against a type in a full `Env`.
pub fn check_with_full_env(env: &Env, t: &Term, ty: &Term) -> Result<(), TypeError> {
    check_dt(&env.datatypes, &global_ctx(&env.defs), t, ty)
}