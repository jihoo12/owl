//! Tactic resolver trait — decouples the kernel from the tactic engine.
//!
//! The kernel defines a trait for resolving tactics. The frontend implements
//! this trait with the actual tactic engine. The kernel's typechecker calls
//! the trait method when it encounters a `TBy` term.

use crate::session::Session;
use crate::syntax::{Datatype, Tactic, Term};
use crate::typechecker::{Ctx, TypeError};
use std::sync::OnceLock;

use std::fmt;

/// Trait for resolving tactics into proof terms.
///
/// The kernel calls this trait when it encounters a `TBy` block in a definition.
/// The frontend implements this trait with the actual tactic engine.
pub trait TacticResolver: Send + Sync + fmt::Debug {
    /// Resolve a list of tactics into a proof term.
    ///
    /// # Arguments
    /// * `dts` - All known datatypes
    /// * `ctx` - The current typing context
    /// * `goal_ty` - The goal type (normalized)
    /// * `raw_goal_ty` - The goal type (unnormalized, as written by the user)
    /// * `tactics` - The list of tactics to execute
    /// * `session` - The current session state
    ///
    /// # Returns
    /// The proof term, or a type error if tactic resolution fails.
    fn resolve_tactics(
        &self,
        dts: &[Datatype],
        ctx: &Ctx,
        goal_ty: &Term,
        raw_goal_ty: &Term,
        tactics: &[Tactic],
        session: &mut Session,
    ) -> Result<Term, TypeError>;
}

/// Global tactic resolver, set by the frontend.
static TACTIC_RESOLVER: OnceLock<Box<dyn TacticResolver>> = OnceLock::new();

/// Set the global tactic resolver.
///
/// This must be called before any typechecking occurs.
pub fn set_tactic_resolver(resolver: Box<dyn TacticResolver>) {
    TACTIC_RESOLVER
        .set(resolver)
        .expect("Tactic resolver already set");
}

/// Get a reference to the global tactic resolver.
pub fn tactic_resolver() -> Option<&'static dyn TacticResolver> {
    TACTIC_RESOLVER.get().map(|b| b.as_ref())
}
