//! Reduction trace infrastructure for debugging NbE.

/// A single reduction step recorded during normalization.
#[derive(Debug, Clone)]
pub struct ReductionStep {
    pub rule: String,
    pub input: String,
    pub output: String,
}

thread_local! {
    static REDUCTION_TRACE: std::cell::RefCell<Vec<ReductionStep>> = const { std::cell::RefCell::new(Vec::new()) };
}

pub static TRACE_ACTIVE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

pub fn start_trace() {
    TRACE_ACTIVE.store(true, std::sync::atomic::Ordering::Release);
    REDUCTION_TRACE.with(|t| t.borrow_mut().clear());
}

pub fn stop_trace() -> Vec<ReductionStep> {
    TRACE_ACTIVE.store(false, std::sync::atomic::Ordering::Release);
    REDUCTION_TRACE.with(|t| t.borrow_mut().split_off(0))
}

pub fn record_step(rule: String, input: String, output: String) {
    if TRACE_ACTIVE.load(std::sync::atomic::Ordering::Acquire) {
        REDUCTION_TRACE.with(|t| t.borrow_mut().push(ReductionStep { rule, input, output }));
    }
}
