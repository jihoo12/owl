//! Owl Frontend — Parser, tactics, and driver.
//!
//! This crate contains the untrusted frontend components:
//! - Surface language parser
//! - Tactic engine and solvers (omega, ring, field, group)
//! - File I/O driver

pub mod driver;
pub mod eq;
pub mod field;
pub mod group;
pub mod omega;
pub mod parser;
pub mod ring;
pub mod tactics;

#[cfg(test)]
pub mod cumulativity_tests;

#[cfg(test)]
pub mod test_helpers;

// Re-export debug_log! macro from kernel for use in frontend code
pub use owl_kernel::debug_log;

// Re-exports for convenience
pub use driver::{RunError, RunOutput, check, check_str, check_str_with_holes, run, run_str};
