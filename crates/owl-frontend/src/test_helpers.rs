//! Shared test helpers for the frontend module.
//!
//! Re-exports common utilities so that individual test modules don't need
//! to duplicate boilerplate.

use owl_kernel::syntax::Term;
use std::sync::Arc;

/// Shorthand for `Arc::new(t)`.
pub fn b(t: Term) -> Arc<Term> {
    Arc::new(t)
}

/// Create an empty `Globals` value for tests that don't need global definitions.
pub fn empty_globals() -> owl_kernel::nbe::Globals {
    Arc::new(std::sync::Mutex::new(Vec::new()))
}

/// Run a closure with a fresh `Session`.
pub fn with_session<R>(f: impl FnOnce(&mut owl_kernel::session::Session) -> R) -> R {
    owl_kernel::session::with_session_mut(f)
}

/// Parse + typecheck + evaluate an Owl source string.
pub fn run_str_test(src: &str) -> Result<crate::driver::RunOutput, crate::driver::RunError> {
    with_session(|session| crate::driver::run_str(src, session))
}
