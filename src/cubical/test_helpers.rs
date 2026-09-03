//! Shared test helpers for the cubical module.
//!
//! Re-exports common utilities so that individual test modules don't need
//! to duplicate boilerplate (`b()`, `empty_globals()`, `with_session()`, etc.).

use crate::cubical::syntax::Term;
use std::sync::Arc;

/// Shorthand for `Arc::new(t)`.
pub fn b(t: Term) -> Arc<Term> {
    Arc::new(t)
}

/// Create an empty `Globals` value for tests that don't need global definitions.
pub fn empty_globals() -> crate::cubical::nbe::Globals {
    Arc::new(std::sync::Mutex::new(Vec::new()))
}

/// Run a closure with a fresh `Session`.
pub fn with_session<R>(f: impl FnOnce(&mut crate::cubical::session::Session) -> R) -> R {
    crate::cubical::session::with_session_mut(f)
}

/// Parse + typecheck + evaluate an Owl source string.
pub fn run_str_test(
    src: &str,
) -> Result<crate::cubical::driver::RunOutput, crate::cubical::driver::RunError> {
    with_session(|session| crate::cubical::driver::run_str(src, session))
}
