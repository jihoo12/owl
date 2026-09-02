// Cubical Env — Rust port of Env.hs
//
// Depends on:
//   crate::syntax::{Name, Term, Datatype, shift, subst}
//   crate::typechecker::{Ctx, TypeError, infer, check, infer_dt, check_dt}

use crate::cubical::nbe::value::NeutralInner;
use crate::cubical::nbe::{Globals, Neutral, Scope, Value, eval_nbe};
use crate::cubical::session::Session;
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
    /// Global instance database for implicit argument resolution.
    /// Each entry is (instance_name, instance_type, instance_value).
    /// The instance_type should be a TData applied to parameters, e.g.,
    /// `CommRing A add mul zero one`.
    pub instances: Vec<(Name, Term, Term)>,
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

    /// Declare a postulate (axiom): `name : ty` with no body.
    /// The value is a neutral variable referencing the definition's own slot,
    /// so it never reduces — exactly the semantics of an opaque axiom.
    pub fn postulate(&mut self, name: Name, ty: Term) {
        self.defs.insert(0, (name, ty, Term::TVar(0)));
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

    /// Register an instance for implicit argument resolution.
    /// `instance_ty` should be the type of the instance (e.g., `CommRing A add mul zero one`).
    /// `instance_val` is the instance term itself.
    pub fn register_instance(&mut self, name: Name, instance_ty: Term, instance_val: Term) {
        self.instances.push((name, instance_ty, instance_val));
    }

    /// Find an instance matching the given target type.
    /// Searches the instance database for an instance whose type matches `target_ty`.
    pub fn find_instance(&self, target_ty: &Term, session: &mut Session) -> Option<Term> {
        let target_nf = crate::cubical::nbe::nbe_eval_ctx(0, target_ty, session);
        let empty_ctx: Ctx = Vec::new();
        for (_name, inst_ty, inst_val) in &self.instances {
            let inst_ty_nf = crate::cubical::nbe::nbe_eval_ctx(0, inst_ty, session);
            if crate::cubical::equality::definitionally_equal_ctx_r(
                &empty_ctx,
                &inst_ty_nf,
                &target_nf,
                session,
            ) == crate::cubical::equality::EtaResult::Equal
            {
                return Some(inst_val.clone());
            }
        }
        None
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
#[allow(dead_code)]
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
#[allow(dead_code)]
fn subst_global(k: i32, v: &Term, body: &Term) -> Term {
    shift(-1, k, &subst(k, &shift(k, 0, v), body))
}

// ---------------------------------------------------------------------------
// Typing with GlobalEnv (backward-compatible, no datatypes)
// ---------------------------------------------------------------------------

/// Infer the type of a term in the context of a `GlobalEnv` (no datatypes).
#[allow(dead_code)]
pub fn infer_with_env(
    genv: &GlobalEnv,
    t: &Term,
    session: &mut Session,
) -> Result<Term, TypeError> {
    infer(&global_ctx(genv), t, session)
}

/// Check a term against a type in the context of a `GlobalEnv` (no datatypes).
#[allow(dead_code)]
pub fn check_with_env(
    genv: &GlobalEnv,
    t: &Term,
    ty: &Term,
    session: &mut Session,
) -> Result<(), TypeError> {
    check(&global_ctx(genv), t, ty, session)
}

// ---------------------------------------------------------------------------
// Typing with full Env (definitions + datatypes)
// ---------------------------------------------------------------------------

/// Build the shared vector of global definition values for an environment.
///
/// Definitions are stored newest-first, so we evaluate oldest-first; the
/// shared vector lets closures see their recursive definition once its
/// placeholder has been replaced.
pub fn build_definition_values(env: &Env, session: &mut Session) -> Globals {
    let placeholder = Value::VNeutral(Neutral::nvar(0));
    let globals = std::sync::Arc::new(std::sync::Mutex::new(vec![placeholder; env.defs.len()]));
    for index in (0..env.defs.len()).rev() {
        let (_, _, value) = &env.defs[index];
        globals.lock().unwrap()[index] = eval_nbe(&Scope::empty(), &globals, index, value, session);
    }
    // Postulates (and self-referential stuck defs) evaluate to VNeutral(NVar(0))
    // because globals[index] is still the placeholder at eval time. Fix up the
    // NVar level so quoting produces the correct global de Bruijn index: NVar(0)
    // → NVar(index). Without this, the neutral would be misinterpreted as a local
    // variable when quoted in contexts with >0 local binders.
    {
        let mut g = globals.lock().unwrap();
        for i in 0..g.len() {
            if let Value::VNeutral(n) = &g[i] {
                if matches!(n.inner(), NeutralInner::NVar(0)) {
                    g[i] = Value::VNeutral(Neutral::nvar(i));
                }
            }
        }
    }
    globals
}

/// Infer the type of a term in a full `Env`.
pub fn infer_with_full_env(env: &Env, t: &Term, session: &mut Session) -> Result<Term, TypeError> {
    let globals = build_definition_values(env, session);
    let prev = session.set_current_globals(Some(globals));
    let result = infer_dt(&env.datatypes, &global_ctx(&env.defs), t, session);
    session.set_current_globals(prev);
    result
}

/// Check a term against a type in a full `Env`.
pub fn check_with_full_env(
    env: &Env,
    t: &Term,
    ty: &Term,
    session: &mut Session,
) -> Result<(), TypeError> {
    let globals = build_definition_values(env, session);
    let prev = session.set_current_globals(Some(globals));
    let result = check_dt(&env.datatypes, &global_ctx(&env.defs), t, ty, session);
    session.set_current_globals(prev);
    result
}
