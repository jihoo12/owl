//! Reduction trace infrastructure for debugging NbE.
//!
//! Trace recording is gated on the global debug flag in `cubical::debug`.

use std::cell::RefCell;

use crate::cubical::debug;

thread_local! {
    static REDUCTION_TRACE: RefCell<Vec<ReductionStep>> = RefCell::new(Vec::new());
}

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
    REDUCTION_TRACE.with(|c| c.borrow_mut().clear());
}

/// Stop recording and return all accumulated steps.
pub fn stop_trace() -> Vec<ReductionStep> {
    REDUCTION_TRACE.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

/// Record a single reduction step (no-op when debug is inactive).
pub fn record_step(rule: String, input: String, output: String) {
    if debug::is_active() {
        REDUCTION_TRACE.with(|c| {
            c.borrow_mut().push(ReductionStep {
                rule,
                input,
                output,
            })
        });
    }
}

/// Drain all recorded steps (for printing without stopping).
pub fn drain_trace() -> Vec<ReductionStep> {
    REDUCTION_TRACE.with(|c| std::mem::take(&mut *c.borrow_mut()))
}
