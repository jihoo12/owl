pub mod env;
pub mod equality;
pub mod ffi;
pub mod interval;
pub mod json;
pub mod nbe;
pub mod parser;
pub mod syntax;
pub mod typechecker;

#[cfg(test)]
pub mod dependent_pi_transport_test;

use std::collections::HashSet;
use std::fmt;
use std::path::{Path, PathBuf};

use self::env::{Env, apply_globals, check_with_full_env, infer_with_full_env};
use self::nbe::nbe_eval;
use self::parser::{Decl, ParseError, ProgramParser};
use self::syntax::{Name, Term};
use self::typechecker::{TypeError, check_closed_dt};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunOutput {
    pub name: Name,
    pub ty: Term,
    pub value: Term,
    pub global_names: Vec<Name>,
}

impl fmt::Display for RunOutput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} : {} = {}",
            self.name,
            syntax::show_term(&self.global_names, &self.ty),
            syntax::show_term(&self.global_names, &self.value),
        )
    }
}

#[derive(Debug)]
pub enum RunError {
    Io(std::io::Error),
    Parse(ParseError),
    Type(Box<TypeError>),
    Import(String),
    NoEntryPoint,
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RunError::Io(err) => write!(f, "I/O error: {}", err),
            RunError::Parse(err) => write!(f, "parse error: {}", err),
            RunError::Type(err) => write!(f, "type error:\n{}", err),
            RunError::Import(msg) => write!(f, "import error: {}", msg),
            RunError::NoEntryPoint => write!(f, "program has no definition to run"),
        }
    }
}

impl std::error::Error for RunError {}

impl From<std::io::Error> for RunError {
    fn from(err: std::io::Error) -> Self {
        RunError::Io(err)
    }
}

impl From<ParseError> for RunError {
    fn from(err: ParseError) -> Self {
        RunError::Parse(err)
    }
}

impl From<TypeError> for RunError {
    fn from(err: TypeError) -> Self {
        RunError::Type(Box::new(err))
    }
}

/// Read, typecheck, and evaluate a cubical source file.
///
/// Top-level declarations are processed in order. Datatypes are registered in
/// the environment, definitions are checked against their annotations, and the
/// `main` definition (or the last definition if no `main` exists) is normalized
/// and returned as the program result.
pub fn run(path: impl AsRef<Path>) -> Result<RunOutput, RunError> {
    let path = path.as_ref();
    let source = std::fs::read_to_string(path)?;
    run_source(path, &source)
}

/// Typecheck and evaluate cubical source from a string, using the current
/// directory for import resolution.
pub fn run_str(source: &str) -> Result<RunOutput, RunError> {
    run_source(Path::new("."), source)
}

fn run_source(root_path: &Path, source: &str) -> Result<RunOutput, RunError> {
    let mut env = Env::new();
    let mut loaded = HashSet::new();
    let import_base = root_path.parent().unwrap_or_else(|| Path::new("."));
    let mut last_def = None;

    process_file_source(
        source,
        import_base,
        &mut env,
        &mut loaded,
        &mut HashSet::new(),
        &mut last_def,
    )?;

    // Prefer `main` over the last definition when both exist.
    if let Some(main_entry) = env.defs.iter().find(|(name, _, _)| name == "main") {
        let (name, ty, val) = main_entry;
        Ok(RunOutput {
            name: name.clone(),
            ty: ty.clone(),
            value: nbe_eval(val),
            global_names: env.defs.iter().map(|(n, _, _)| n.clone()).collect(),
        })
    } else {
        last_def.ok_or(RunError::NoEntryPoint)
    }
}

fn resolve_import_path(base: &Path, path: &str) -> PathBuf {
    let requested = Path::new(path);
    if requested.is_absolute() {
        requested.to_path_buf()
    } else {
        base.join(requested)
    }
}

fn canonical_import_path(path: &Path) -> PathBuf {
    std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

fn process_file_source(
    source: &str,
    import_base: &Path,
    env: &mut Env,
    loaded: &mut HashSet<PathBuf>,
    loading: &mut HashSet<PathBuf>,
    last_def: &mut Option<RunOutput>,
) -> Result<(), RunError> {
    let mut parser = ProgramParser::new(source)?;
    while let Some(decl) = parser.next_decl()? {
        match decl {
            Decl::Import { path } => {
                load_import(&path, env, loaded, loading, import_base, last_def)?;
                parser.sync_from_env(env);
            }
            Decl::Data(dt) => {
                process_data(&dt, env)?;
            }
            Decl::Def { name, ty, val } => {
                *last_def = Some(process_def(&name, &ty, &val, env)?);
            }
        }
    }
    Ok(())
}

fn load_import(
    path: &str,
    env: &mut Env,
    loaded: &mut HashSet<PathBuf>,
    loading: &mut HashSet<PathBuf>,
    import_base: &Path,
    last_def: &mut Option<RunOutput>,
) -> Result<(), RunError> {
    let resolved = resolve_import_path(import_base, path);
    let canonical = canonical_import_path(&resolved);

    if loaded.contains(&canonical) {
        return Ok(());
    }
    if !loading.insert(canonical.clone()) {
        return Err(RunError::Import(format!(
            "circular import involving '{}'",
            resolved.display()
        )));
    }

    let source = std::fs::read_to_string(&resolved).map_err(|err| {
        RunError::Import(format!("cannot read '{}': {}", resolved.display(), err))
    })?;

    let nested_base = resolved.parent().unwrap_or(import_base);
    process_file_source(&source, nested_base, env, loaded, loading, last_def)?;

    loading.remove(&canonical);
    loaded.insert(canonical);
    Ok(())
}

fn process_data(dt: &crate::cubical::syntax::Datatype, env: &mut Env) -> Result<(), RunError> {
    // Check positivity before registering the datatype.
    crate::cubical::syntax::check_datatype_positivity(dt)
        .map_err(|e| RunError::Type(Box::new(crate::cubical::typechecker::TypeError::Other(
            format!("{}", e),
        ))))?;
    env.declare_datatype(dt.clone());
    for con in &dt.cons {
        for arg_ty in &con.arg_tys {
            check_closed_dt(&env.datatypes, arg_ty, &Term::TUniv(0)).map_err(|e| RunError::Type(Box::new(e)))?;
        }
    }
    Ok(())
}

fn process_def(name: &Name, ty: &Term, val: &Term, env: &mut Env) -> Result<RunOutput, RunError> {
    println!("{}: ✓", name);
    let closed_ty_globals = apply_globals(&env.defs, ty);
    let closed_val = val.clone();

    // Normalize only for the universe-level check; keep the original
    // structure (e.g., Glue types) intact for body checking.
    let closed_ty_nf = nbe_eval(&closed_ty_globals);
    match nbe_eval(&infer_with_full_env(env, &closed_ty_nf)?) {
        Term::TUniv(_) => {}
        other => return Err(TypeError::ExpectedUniverse(other).into()),
    }
    // Register before checking the body so recursive calls resolve.
    env.define(name.clone(), closed_ty_globals.clone(), closed_val.clone());
    check_with_full_env(env, &closed_val, &closed_ty_globals)?;
    let output = RunOutput {
        name: name.clone(),
        ty: closed_ty_globals.clone(),
        value: nbe_eval(&closed_val),
        global_names: env.defs.iter().map(|(n, _, _)| n.clone()).collect(),
    };

    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::io::Write;

    #[test]
    fn run_with_import_merges_declarations() {
        let dir = std::env::temp_dir().join(format!("cubical_import_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let nat_path = dir.join("nat.uwuc");
        let main_path = dir.join("main.uwuc");

        fs::write(&nat_path, "data Nat = | zero : Nat | suc : Nat -> Nat\n").unwrap();
        fs::write(
            &main_path,
            "import \"nat.uwuc\"\n\ndef main : Nat -> Nat = \\n. n\n",
        )
        .unwrap();

        let output = run(&main_path).expect("imported program should run");
        assert_eq!(output.name, "main");

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_reports_circular_import() {
        let dir = std::env::temp_dir().join(format!("cubical_cycle_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let a_path = dir.join("a.uwuc");
        let b_path = dir.join("b.uwuc");

        let mut a_file = fs::File::create(&a_path).unwrap();
        writeln!(a_file, "import \"b.uwuc\"").unwrap();
        writeln!(a_file, "def a : U0 = U0").unwrap();

        let mut b_file = fs::File::create(&b_path).unwrap();
        writeln!(b_file, "import \"a.uwuc\"").unwrap();
        writeln!(b_file, "def b : U0 = U0").unwrap();

        let err = run(&a_path).unwrap_err();
        assert!(matches!(err, RunError::Import(_)));

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_plus_on_nat() {
        let src = "data Nat = | zero : Nat | suc : Nat -> Nat\n\
                   def plus : Nat -> Nat -> Nat = \\m n. elim (\\_. Nat) \
                   { | zero => n | suc m' => suc (plus m' n) } m\n\
                   def four : Nat = plus (suc (suc zero)) (suc (suc zero))";
        let dir = std::env::temp_dir().join(format!("cubical_plus_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join("main.uwuc");
        fs::write(&path, src).unwrap();
        let output = run(&path).expect("plus should typecheck");
        assert_eq!(output.name, "four");
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn transport_over_ua_still_works() {
        let src = "\
def id : (A : U0) -> A -> A = \\A x. x\n\
def transportExample : (A B : U0) -> Equiv A B -> A -> B =\n\
  \\A B e a. transport (<i> ua e @ i) a\n\
def main : (A B : U0) -> Equiv A B -> A -> B = transportExample\n";
        let dir = std::env::temp_dir().join(format!("cubical_transport_ua_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join("main.uwuc");
        fs::write(&path, src).unwrap();
        let output = run(&path).expect("transport over ua should typecheck");
        // `run()` prefers `main` over earlier definitions
        assert_eq!(output.name, "main");
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_mul_via_run_path() {
        let src = "data Nat = | zero : Nat | suc : Nat -> Nat\n\
                   def add : Nat -> Nat -> Nat = \\m n. elim (\\_. Nat) { \
                   | zero => n | suc k => suc (add k n) } m\n\
                   def mul : Nat -> Nat -> Nat = \\m n. elim (\\_. Nat) { \
                   | zero => zero | suc k => add n (mul k n) } m\n\
                   def main : Nat = mul (suc (suc zero)) (suc (suc (suc zero)))";
        let dir = std::env::temp_dir().join(format!("cubical_mul_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join("main.uwuc");
        fs::write(&path, src).unwrap();
        let output = run(&path).expect("mul should compute");
        eprintln!("mul result: {}", output);
        let _ = fs::remove_dir_all(&dir);
    }
}
