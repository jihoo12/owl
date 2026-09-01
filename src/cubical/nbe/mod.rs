#![allow(clippy::enum_variant_names)]

//! NbE (normalisation by evaluation) for Owl.
//!
//! The implementation is split across sibling submodules:
//!
//! | module        | contents                                                       |
//! |---------------|----------------------------------------------------------------|
//! | [`value`]     | runtime types: `Scope`, `Value`, `Neutral`, closures            |
//! | [`eval`]      | term evaluation (`Term` -> `Value`)                             |
//! | [`elim`]      | eliminators on values (apply, papp, projections, elim, force)   |
//! | [`transport`] | cubical transport and its per-shape specialisations             |
//! | [`hcomp`]     | composition operations: hcomp / comp / fill / hfill             |
//! | [`quote`]     | quoting values back to normalised terms                         |
//! | [`meta`]      | metavariable helpers over terms                                 |
//! | [`util`]      | small helpers shared across submodules                          |
//! | [`trace`]     | reduction-step tracing support                                  |
//!
//! This file re-exports the historical flat API so that external callers
//! (`crate::cubical::{env, equality, driver, tactics, typechecker, ...}`)
//! keep importing from `crate::cubical::nbe::*` unchanged, and hosts the
//! top-level entry points that tie evaluation and quoting together.

pub mod elim;
pub mod eval;
pub mod hcomp;
pub mod meta;
pub mod quote;
pub mod trace;
pub mod transport;
pub mod util;
pub mod value;

#[cfg(test)]
mod tests;

// ---------------------------------------------------------------------------
// Flat re-exports — preserve the pre-split public surface of this module.
// Some of these are part of the external/test-only API and have no internal
// callers; in a binary crate rustc would flag them as unused imports.
// ---------------------------------------------------------------------------
#[allow(unused_imports)]
pub use elim::{do_apply, do_elim, do_force, do_fst, do_papp, do_proj, do_snd};
#[allow(unused_imports)]
pub use eval::{eval_nbe, eval_system};
#[allow(unused_imports)]
pub use hcomp::{do_comp, do_fill, do_hcomp, do_hfill};
#[allow(unused_imports)]
pub use meta::{collect_unsolved_metas, meta_mentions, try_solve_meta, zonk};
pub use quote::quote;
#[allow(unused_imports)]
pub use transport::{do_transport, transport_term_fallback, uses_var_at_level};
#[allow(unused_imports)]
pub use value::{Closure, DNFSystem, Env, Globals, IClosure, Neutral, Scope, Value};

/// Metavariable lookup, delegated to the session module.
#[allow(unused_imports)]
pub use crate::cubical::session::get_meta_solution;

use std::sync::{Arc, Mutex};

use crate::cubical::session::Session;
use crate::cubical::syntax::{Term, max_var};

use meta::has_meta_in_term;

pub fn normalize(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    t: &Term,
    session: &mut Session,
) -> Term {
    quote(
        env.len(),
        globals,
        global_offset,
        eval_nbe(env, globals, global_offset, t, session),
        session,
    )
}

/// Evaluate a closed term without global definitions (original behavior).
pub fn nbe_eval(t: &Term, session: &mut Session) -> Term {
    if !has_meta_in_term(t) {
        let cached = session.eval_cache_get(t);
        if let Some(result) = cached {
            return result;
        }
    }
    let result = {
        let empty_globals: Globals = Arc::new(Mutex::new(Vec::new()));
        let mv = max_var(t);
        if mv < 0 {
            normalize(&Scope::empty(), &empty_globals, 0, t, session)
        } else {
            let size = (mv + 1) as usize;
            let mut env = Scope::empty();
            for level in 0..size {
                env = env.extend(Value::VNeutral(Neutral::nvar(level)));
            }
            normalize(&env, &empty_globals, 0, t, session)
        }
    };
    if !has_meta_in_term(t) {
        session.eval_cache_insert(t.clone(), result.clone());
    }
    result
}

/// Evaluate a term with access to global definition values.
///
/// `globals` should be ordered most-recent-first (same as `env.defs`).
/// `global_offset` is the index into `globals` where the evaluated term's
/// own definition lives (0 = most recent, the typical case for evaluating
/// the target expression).
pub fn nbe_eval_with_globals(
    t: &Term,
    globals: &Globals,
    global_offset: usize,
    session: &mut Session,
) -> Term {
    // The env starts empty — all TVars resolve to globals.
    // Lambdas push binders onto the env during evaluation via do_apply.
    normalize(&Scope::empty(), globals, global_offset, t, session)
}

/// Evaluate a term with access to the thread-local global definition values
/// (set via `set_current_globals`). The first `ctx_len` de Bruijn indices are
/// treated as local binders and the remainder as global references, matching
/// the typechecker convention that global definitions sit at the bottom of the
/// context. Falls back to `nbe_eval` (no globals) when none are set.
pub fn nbe_eval_ctx(ctx_len: usize, t: &Term, session: &mut Session) -> Term {
    let Some(globals) = session.get_current_globals() else {
        return nbe_eval(t, session);
    };
    let n_globals = globals.lock().unwrap().len();
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
        env = env.extend(Value::VNeutral(Neutral::nvar(level)));
    }
    quote(
        n_local,
        &globals,
        0,
        eval_nbe(&env, &globals, 0, t, session),
        session,
    )
}
