//! Global debug logging infrastructure for Owl.
//!
//! Activated via `--debug` flag or `OWL_DEBUG=1` environment variable.
//! When active, the typechecker and NbE engine emit detailed trace logs
//! to stderr.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

/// Global flag: is debug logging active?
static DEBUG_ACTIVE: AtomicBool = AtomicBool::new(false);

/// Indentation depth for nested log messages.
static DEBUG_DEPTH: AtomicUsize = AtomicUsize::new(0);

/// Enable debug logging. Called once at startup.
pub fn enable() {
    DEBUG_ACTIVE.store(true, Ordering::Release);
}

/// Check if debug logging is active.
#[inline]
pub fn is_active() -> bool {
    DEBUG_ACTIVE.load(Ordering::Acquire)
}

/// Increment indent (call on function entry).
pub fn indent() {
    DEBUG_DEPTH.fetch_add(1, Ordering::Relaxed);
}

/// Decrement indent (call on function exit).
pub fn dedent() {
    DEBUG_DEPTH.fetch_sub(1, Ordering::Relaxed);
}

/// Get current indentation as a prefix string.
pub fn indent_str() -> &'static str {
    // We can't dynamically build a string in a static context,
    // so we use a fixed set of indent levels.
    static INDENTS: [&str; 16] = [
        "",
        "  ",
        "    ",
        "      ",
        "        ",
        "          ",
        "            ",
        "              ",
        "                ",
        "                  ",
        "                    ",
        "                      ",
        "                        ",
        "                          ",
        "                            ",
        "                              ",
    ];
    let depth = DEBUG_DEPTH.load(Ordering::Relaxed);
    INDENTS[depth.min(INDENTS.len() - 1)]
}

/// Log a message to stderr if debug is active.
#[macro_export]
macro_rules! debug_log {
    ($($arg:tt)*) => {
        if $crate::cubical::debug::is_active() {
            eprintln!("{}{}", $crate::cubical::debug::indent_str(), format!($($arg)*));
        }
    };
}

/// RAII guard that increments indent on creation and decrements on drop.
pub struct DebugScope;

impl DebugScope {
    pub fn new(label: &str) -> Self {
        if is_active() {
            eprintln!("{}>> {}", indent_str(), label);
            indent();
        }
        DebugScope
    }
}

impl Drop for DebugScope {
    fn drop(&mut self) {
        if is_active() {
            dedent();
            eprintln!("{}<<", indent_str());
        }
    }
}

/// Convenience macro for scoped debug logging.
///
/// Usage:
/// ```ignore
/// fn my_function(x: i32) -> i32 {
///     debug_scope!("my_function({})", x);
///     // ... body ...
/// }
/// ```
#[macro_export]
macro_rules! debug_scope {
    ($($arg:tt)*) => {
        let _debug_scope = $crate::cubical::debug::DebugScope::new(&format!($($arg)*));
    };
}
