use super::*;
use std::fs;
use std::path::Path;

pub(super) fn run(path: impl AsRef<Path>) -> Result<RunOutput, RunError> {
    crate::cubical::session::with_session_mut(|session| super::run(path, session))
}

pub(super) fn check(path: impl AsRef<Path>) -> Result<(), RunError> {
    crate::cubical::session::with_session_mut(|session| super::check(path, session))
}

pub(super) fn run_str(source: &str) -> Result<RunOutput, RunError> {
    crate::cubical::session::with_session_mut(|session| super::run_str(source, session))
}

pub(super) fn check_str(source: &str) -> Result<(), RunError> {
    crate::cubical::session::with_session_mut(|session| super::check_str(source, session))
}

pub(super) fn temp_dir(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("{}_{}", name, std::process::id()))
}

pub(super) fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

mod computation;
mod example_guards;
mod holes;
mod imports;
mod tactics;
