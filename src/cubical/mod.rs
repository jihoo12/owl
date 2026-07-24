pub mod driver;
pub mod env;
pub mod equality;
pub mod interval;
#[allow(dead_code)]
pub mod nbe;
pub mod parser;
pub mod syntax;
pub mod tactics;
pub mod typechecker;
pub mod debug;

#[cfg(test)]
pub mod dependent_pi_transport_test;

pub use driver::{RunError, check, check_str, run, run_str};
