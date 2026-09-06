//! Owl Kernel — Trusted core for the cubical type theory proof assistant.
//!
//! This crate contains the minimal trusted computing base (TCB) for Owl:
//! - Core syntax and de Bruijn operations
//! - Normalization by evaluation (NbE)
//! - Bidirectional typechecker
//! - Definitional equality
//! - Cubical interval algebra
//! - Session state management
//! - Global environment

pub mod debug;
pub mod env;
pub mod equality;
pub mod interval;
pub mod nbe;
pub mod session;
pub mod syntax;
pub mod tactics;
pub mod typechecker;

#[cfg(test)]
pub mod test_helpers;
pub use session::Session;
pub use syntax::{Ctx, Name, Pos, Term};
