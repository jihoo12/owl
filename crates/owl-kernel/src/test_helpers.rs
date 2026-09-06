//! Shared test helpers for the kernel module.

use crate::syntax::Term;
use std::sync::Arc;

/// Shorthand for `Arc::new(t)`.
pub fn b(t: Term) -> Arc<Term> {
    Arc::new(t)
}
