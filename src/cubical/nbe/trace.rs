//! Reduction trace infrastructure for debugging NbE.
//!
//! Trace recording is gated on the global debug flag in `cubical::debug`.

use crate::cubical::debug;
use crate::cubical::session;

/// A single reduction step recorded during normalization.
#[derive(Debug, Clone)]
pub struct ReductionStep {
    pub rule: String,
    pub input: String,
    pub output: String,
}

/// Start recording reduction steps.
pub fn start_trace() {
    debug::enable();
    session::with_session_mut(|s| s.reduction_trace.clear());
}

/// Stop recording and return all accumulated steps.
pub fn stop_trace() -> Vec<ReductionStep> {
    session::with_session_mut(|s| std::mem::take(&mut s.reduction_trace))
}

/// Record a single reduction step (no-op when debug is inactive).
pub fn record_step(rule: String, input: String, output: String) {
    if debug::is_active() {
        session::with_session_mut(|s| {
            s.reduction_trace.push(ReductionStep {
                rule,
                input,
                output,
            })
        });
    }
}

/// Drain all recorded steps (for printing without stopping).
pub fn drain_trace() -> Vec<ReductionStep> {
    session::with_session_mut(|s| std::mem::take(&mut s.reduction_trace))
}
