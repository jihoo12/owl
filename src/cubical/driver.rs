//! File I/O pipeline: read, parse, typecheck, and evaluate cubical source files.

use std::collections::HashSet;
use std::fmt;
use std::path::{Path, PathBuf};

use crate::cubical::env::{Env, check_with_full_env, infer_with_full_env};
use crate::cubical::nbe::{nbe_eval, nbe_eval_with_globals, zonk};
use crate::cubical::parser::{Decl, ProgramParser};
use crate::cubical::syntax::{Name, Term};
use crate::cubical::typechecker::errors::ContextualError;
use crate::cubical::typechecker::{Ctx, TypeError};

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
            crate::cubical::syntax::show_term(&self.global_names, &self.ty),
            crate::cubical::syntax::show_term(&self.global_names, &self.value),
        )
    }
}

#[derive(Debug)]
pub enum RunError {
    Io(std::io::Error),
    Parse(crate::cubical::parser::ParseError),
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

impl From<crate::cubical::parser::ParseError> for RunError {
    fn from(err: crate::cubical::parser::ParseError) -> Self {
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

/// Read and typecheck a cubical source file without evaluating an entry point.
///
/// This accepts libraries containing only datatype declarations, which makes it
/// suitable for the `owl check` command and for checking imported modules.
pub fn check(path: impl AsRef<Path>) -> Result<(), RunError> {
    let path = path.as_ref();
    let source = std::fs::read_to_string(path)?;
    check_source(path, &source)
}

/// Typecheck and evaluate cubical source from a string, using the current
/// directory for import resolution.
pub fn run_str(source: &str) -> Result<RunOutput, RunError> {
    run_source(Path::new("."), source)
}

/// Typecheck cubical source from a string, without requiring a `main`
/// definition. Imports are resolved relative to the current directory.
pub fn check_str(source: &str) -> Result<(), RunError> {
    check_source(Path::new("."), source)
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
    if let Some((name, _, _)) = env.defs.iter().find(|(name, _, _)| name == "main") {
        Ok(normalize_definition(&env, name))
    } else {
        last_def
            .map(|output| normalize_definition(&env, &output.name))
            .ok_or(RunError::NoEntryPoint)
    }
}

fn normalize_definition(env: &Env, name: &str) -> RunOutput {
    let index = env
        .defs
        .iter()
        .position(|(candidate, _, _)| candidate == name)
        .expect("definition selected from environment must exist");
    let (name, ty, value) = &env.defs[index];
    let globals = crate::cubical::env::build_definition_values(env);
    RunOutput {
        name: name.clone(),
        ty: zonk(ty),
        value: zonk(&nbe_eval_with_globals(value, &globals, index)),
        global_names: env.defs.iter().map(|(name, _, _)| name.clone()).collect(),
    }
}

fn check_source(root_path: &Path, source: &str) -> Result<(), RunError> {
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
    )
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
    crate::cubical::nbe::clear_nbe_cache();
    // Accumulate name positions across the whole program so globals from
    // earlier declarations (which may only surface as inferred types) resolve
    // to a position. Reverse lookup prefers the most recent occurrence.
    let mut decl_positions = Vec::new();
    while let Some(decl) = parser.next_decl()? {
        decl_positions.extend(parser.take_decl_positions());
        crate::cubical::typechecker::errors::set_decl_name_positions(decl_positions.clone());
        let result: Result<(), RunError> = (|| {
            match decl {
                Decl::Import { path } => {
                    load_import(&path, env, loaded, loading, import_base, last_def)?;
                    parser.sync_from_env(env);
                }
                Decl::Data(dt) => {
                    process_data(&dt, env)?;
                }
                Decl::DataMutual(dts) => {
                    process_data_mutual(&dts, env)?;
                }
                Decl::Record(dt) => {
                    process_data(&dt, env)?;
                }
                Decl::DataWithFunc {
                    dt,
                    func_name,
                    func_ty,
                    func_val,
                } => {
                    process_data_with_func(&dt, &func_name, &func_ty, &func_val, env)?;
                }
                Decl::Def {
                    name,
                    ty,
                    val,
                    by_wf,
                } => {
                    *last_def = Some(process_def(&name, &ty, &val, env, by_wf)?);
                }
            }
            Ok(())
        })();
        result?;
        crate::cubical::nbe::clear_nbe_cache();
    }
    crate::cubical::typechecker::errors::clear_decl_name_positions();
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
    crate::cubical::syntax::check_datatype_positivity(dt).map_err(|e| {
        RunError::Type(Box::new(crate::cubical::typechecker::TypeError::Other(
            format!("{}", e),
        )))
    })?;
    env.declare_datatype(dt.clone());
    // Build a context with the parameter types so that arg_tys which
    // reference parameters via de Bruijn indices (e.g. TVar(0) for the
    // first parameter) can be checked.
    let param_ctx: crate::cubical::typechecker::Ctx = dt
        .params
        .iter()
        .rev()
        .map(|(pname, pty)| {
            // Keep each param type's de Bruijn indices UNCHANGED.  Params are
            // inserted into the parser's `term_env` front-first, so `params`
            // is stored in parse order while the runtime context stores them
            // innermost-first (last param at position 0).  The reversed
            // iteration reproduces exactly the parse-time layout, so a param
            // type's original indices already resolve to the correct slots
            // (verified: `lookup_ctx` shifts a stored type by `i+1`, which
            // lands on the same param a reference `j-1-k` targeted at parse
            // time).  Shifting here breaks params whose types reference
            // earlier params (e.g. `add : R -> R -> R` in a record, where the
            // field type references `add`), producing wrong de Bruijn indices.
            (pname.clone(), pty.clone())
        })
        .collect();
    for con in &dt.cons {
        for arg_ty in &con.arg_tys {
            crate::cubical::typechecker::check_dt(
                &env.datatypes,
                &param_ctx,
                arg_ty,
                &Term::TUniv(0),
            )
            .map_err(|e| RunError::Type(Box::new(e)))?;
        }
    }
    // Check boundary coherence for square constructors.
    crate::cubical::typechecker::check_sqcon_coherence(&env.datatypes, dt)
        .map_err(|e| RunError::Type(Box::new(e)))?;
    Ok(())
}

/// Process a mutual inductive declaration: register all datatypes first,
/// then typecheck each constructor against the full mutual environment.
fn process_data_mutual(
    dts: &[crate::cubical::syntax::Datatype],
    env: &mut Env,
) -> Result<(), RunError> {
    // Phase 1: Register all datatypes so they can reference each other.
    for dt in dts {
        crate::cubical::syntax::check_datatype_positivity(dt).map_err(|e| {
            RunError::Type(Box::new(crate::cubical::typechecker::TypeError::Other(
                format!("{}", e),
            )))
        })?;
        env.declare_datatype(dt.clone());
    }
    // Phase 2: Typecheck constructor argument types against the full mutual environment.
    for dt in dts {
        let param_ctx: crate::cubical::typechecker::Ctx = dt
            .params
            .iter()
            .rev()
            .map(|(pname, pty)| {
                // See `process_data`: param types keep their original
                // (parse-time) de Bruijn indices; shifting breaks params whose
                // types reference earlier params.
                (pname.clone(), pty.clone())
            })
            .collect();
        for con in &dt.cons {
            for arg_ty in &con.arg_tys {
                crate::cubical::typechecker::check_dt(
                    &env.datatypes,
                    &param_ctx,
                    arg_ty,
                    &Term::TUniv(0),
                )
                .map_err(|e| RunError::Type(Box::new(e)))?;
            }
        }
        crate::cubical::typechecker::check_sqcon_coherence(&env.datatypes, dt)
            .map_err(|e| RunError::Type(Box::new(e)))?;
    }
    Ok(())
}

/// Process an induction-recursion declaration: register the datatype,
/// then typecheck and register the function definition.
fn process_data_with_func(
    dt: &crate::cubical::syntax::Datatype,
    func_name: &Name,
    func_ty: &Term,
    func_val: &Term,
    env: &mut Env,
) -> Result<RunOutput, RunError> {
    // First, process the datatype (positivity check + register).
    process_data(dt, env)?;
    // Then, process the function definition with the datatype in scope.
    process_def(func_name, func_ty, func_val, env, false)
}

/// Collect the unsolved holes (with names and expected types) in `t`.
fn unsolved_hole_report(t: &Term) -> Vec<(i32, Name, Option<Term>)> {
    crate::cubical::nbe::collect_unsolved_metas(t)
        .into_iter()
        .map(|id| {
            let name = crate::cubical::nbe::get_meta_name(id).unwrap_or_default();
            let expected = crate::cubical::nbe::get_meta_expected(id);
            (id, name, expected)
        })
        .collect()
}

fn process_def(
    name: &Name,
    ty: &Term,
    val: &Term,
    env: &mut Env,
    by_wf: bool,
) -> Result<RunOutput, RunError> {
    crate::cubical::nbe::clear_nbe_cache();
    crate::debug_log!("process_def '{}':", name);
    if by_wf {
        crate::cubical::typechecker::termination::set_skip_guard(true);
    }
    crate::debug_log!(
        "process_def '{}' raw_ty: {}",
        name,
        crate::cubical::syntax::pretty::show_term(&[], ty)
    );
    // Rebase the raw annotation into the body-check context (own definition
    // at de Bruijn index 0, older definitions at j+1). We deliberately do NOT
    // close the annotation by evaluating it against the current definitions'
    // values: inlining a definition body and re-quoting it re-anchors the
    // references inside stuck elim case bodies onto the wrong slots (e.g.
    // `cong_suc`'s body materialized inside `add`'s elim cases). Keeping the
    // raw references means they are resolved lazily by `nbe_eval_ctx` against
    // the thread-local globals, where the layout matches.
    let check_ty = crate::cubical::syntax::shift(1, 0, ty);

    // If the type annotation is a `_` hole, skip the universe-level check;
    // it will be solved during body typechecking.
    if !matches!(ty, Term::Meta(_)) {
        match nbe_eval(&infer_with_full_env(env, ty)?) {
            Term::TUniv(_) => {}
            other => {
                return Err(RunError::Type(Box::new(TypeError::ExpectedUniverse {
                    ty: other,
                    names: vec![],
                    pos: None,
                })));
            }
        }
    }

    // Resolve any tactic blocks in the value before typechecking.
    // Build the global context so tactic blocks can reference previously
    // defined names (and the current definition for recursive references).
    let mut global_ctx: Ctx = env
        .defs
        .iter()
        .map(|(n, ty, _)| (n.clone(), ty.clone()))
        .collect();
    // The parser inserts the current definition's name at global_env[0]
    // before parsing the value, so it is available for self-reference.
    // Mirror that here by pushing the current name+type at the front.
    global_ctx.insert(0, (name.clone(), check_ty.clone()));
    // Tactic resolution may need to reduce global definitions (e.g. `add`
    // applied to constructors), so expose the definition values via the
    // thread-local globals exactly like `check_with_full_env` does. The
    // current definition itself is not yet in `env.defs`, so its reference
    // (de Bruijn index 0 of the goal scope) stays neutral.
    let globals = crate::cubical::env::build_definition_values(env);
    let prev_globals = crate::cubical::nbe::set_current_globals(Some(globals));
    let resolved_val =
        crate::cubical::tactics::resolve_tactics(&env.datatypes, val, &check_ty, &global_ctx)
            .map_err(|e| RunError::Type(Box::new(ContextualError::with_def(name, e).inner)));
    crate::cubical::nbe::set_current_globals(prev_globals);
    let resolved_val = resolved_val?;

    // Register before checking the body so recursive calls resolve.
    // Store the RAW annotation so that consumers resolving this definition's
    // type via the stored-ref convention
    // (`nbe_eval_ctx(ctx.len(), shift(j+1, 0, annotation))`) see a clean,
    // non-inlined annotation.
    env.define(name.clone(), ty.clone(), resolved_val.clone());
    let prev_def = crate::cubical::typechecker::termination::set_current_def(Some(name.clone()));
    let result = check_with_full_env(env, &resolved_val, &check_ty)
        .map_err(|e| RunError::Type(Box::new(ContextualError::with_def(name, e).inner)));
    crate::cubical::typechecker::termination::set_current_def(prev_def);
    if by_wf {
        crate::cubical::typechecker::termination::set_skip_guard(false);
    }
    result?;

    // Unsolved-hole check: a definition may not leave `?` / `_` holes open.
    let mut metas = unsolved_hole_report(&zonk(&resolved_val));
    metas.extend(unsolved_hole_report(&zonk(ty)));
    if !metas.is_empty() {
        let names: Vec<Name> = env.defs.iter().map(|(n, _, _)| n.clone()).collect();
        return Err(RunError::Type(Box::new(
            ContextualError::with_def(name, TypeError::UnsolvedHoles { metas, names }).inner,
        )));
    }

    let output = RunOutput {
        name: name.clone(),
        ty: zonk(ty),
        value: zonk(&nbe_eval(&resolved_val)),
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

        let nat_path = dir.join("nat.owl");
        let main_path = dir.join("main.owl");

        fs::write(
            &nat_path,
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n",
        )
        .unwrap();
        fs::write(
            &main_path,
            "import \"nat.owl\"\n\ndef main : Nat -> Nat := fun n => n\n",
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

        let a_path = dir.join("a.owl");
        let b_path = dir.join("b.owl");

        let mut a_file = fs::File::create(&a_path).unwrap();
        writeln!(a_file, "import \"b.owl\"").unwrap();
        writeln!(a_file, "def a : U0 := U0").unwrap();

        let mut b_file = fs::File::create(&b_path).unwrap();
        writeln!(b_file, "import \"a.owl\"").unwrap();
        writeln!(b_file, "def b : U0 := U0").unwrap();

        let err = run(&a_path).unwrap_err();
        assert!(matches!(err, RunError::Import(_)));

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_plus_on_nat() {
        let src = "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
                   def plus : Nat -> Nat -> Nat := fun m n => match m return Nat with \
                   | zero => n | suc m' => suc (plus m' n)\n\
                   def four : Nat := plus (suc (suc zero)) (suc (suc zero))";
        let dir = std::env::temp_dir().join(format!("cubical_plus_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join("main.owl");
        fs::write(&path, src).unwrap();
        let output = run(&path).expect("plus should typecheck");
        assert_eq!(output.name, "four");
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn transport_over_ua_still_works() {
        let src = "\
def id : forall (A : U0), A -> A := fun A x => x\n\
def transportExample : forall (A : U0), forall (B : U0), Equiv A B -> A -> B :=\n\
  fun A B e a => transport (<i> ua e @ i) a\n\
def main : forall (A : U0), forall (B : U0), Equiv A B -> A -> B := transportExample\n";
        let dir = std::env::temp_dir().join(format!("cubical_transport_ua_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join("main.owl");
        fs::write(&path, src).unwrap();
        let output = run(&path).expect("transport over ua should typecheck");
        // `run()` prefers `main` over earlier definitions
        assert_eq!(output.name, "main");
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_mul_via_run_path() {
        let src = "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
                   def add : Nat -> Nat -> Nat := fun m n => match m return Nat with \
                   | zero => n | suc k => suc (add k n)\n\
                   def mul : Nat -> Nat -> Nat := fun m n => match m return Nat with \
                   | zero => zero | suc k => add n (mul k n)\n\
                   def main : Nat := mul (suc (suc zero)) (suc (suc (suc zero)))";
        let dir = std::env::temp_dir().join(format!("cubical_mul_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join("main.owl");
        fs::write(&path, src).unwrap();
        let output = run(&path).expect("mul should compute");
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_normalizes_global_definitions() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def add : Nat -> Nat -> Nat := fun m n => match m return Nat with | zero => n | suc k => suc (add k n)\n\
             def main : Nat := add (suc (suc zero)) (suc (suc zero))",
        )
        .expect("program should evaluate");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(4)
        );
    }

    #[test]
    fn check_accepts_library_without_definition() {
        let dir = std::env::temp_dir().join(format!("cubical_check_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join("nat.owl");
        fs::write(
            &path,
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n",
        )
        .unwrap();

        check(&path).expect("a datatype-only library should check");
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn tactic_id_typechecks() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def id : forall (A : U0), A -> A := by intro A x; exact x\n\
             def main : Nat := id Nat zero",
        )
        .expect("tactic id should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(0)
        );
    }

    #[test]
    fn tactic_assumption_typechecks() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def id_nat : Nat -> Nat := by intro x; assumption\n\
             def main : Nat := id_nat (suc zero)",
        )
        .expect("tactic assumption should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(1)
        );
    }

    #[test]
    fn tactic_apply_typechecks() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def id_nat : Nat -> Nat := fun x => x\n\
             def apply_test : Nat -> Nat := by intro x; apply id_nat; exact x\n\
             def main : Nat := apply_test (suc (suc zero))",
        )
        .expect("tactic apply should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(2)
        );
    }

    #[test]
    fn tactic_apply_then_exact_typechecks() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def add_one : Nat -> Nat := fun n => suc n\n\
             def apply_chain_test : Nat -> Nat := by intro x; apply add_one; apply add_one; exact x\n\
             def main : Nat := apply_chain_test (suc zero)",
        )
        .expect("tactic chained apply should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(3)
        );
    }

    #[test]
    fn tactic_exact_nat_typechecks() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def const_zero : Nat := by exact zero\n\
             def main : Nat := const_zero",
        )
        .expect("tactic exact should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(0)
        );
    }

    #[test]
    fn tactic_reflexivity_typechecks() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def refl_zero : Path Nat zero zero := by reflexivity\n\
             def main : Nat := zero",
        )
        .expect("tactic reflexivity should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(0)
        );
    }

    #[test]
    fn tactic_symmetry_typechecks() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def sym_test : Path Nat zero zero := by symmetry; reflexivity\n\
             def main : Nat := zero",
        )
        .expect("tactic symmetry + reflexivity should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(0)
        );
    }

    #[test]
    fn tactic_split_typechecks() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def pair_test : Nat * Nat := by split; exact zero; exact (suc zero)\n\
             def main : Nat := fst pair_test",
        )
        .expect("tactic split should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(0)
        );
    }

    #[test]
    fn tactic_split_snd_typechecks() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def pair_test2 : Nat * Nat := by split; exact (suc zero); exact (suc (suc zero))\n\
             def main : Nat := snd pair_test2",
        )
        .expect("tactic split snd should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(2)
        );
    }

    #[test]
    fn tactic_constructor_zero_args() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def my_zero : Nat := by constructor\n\
             def main : Nat := my_zero",
        )
        .expect("tactic constructor (zero args) should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(0)
        );
    }

    #[test]
    fn tactic_constructor_one_arg() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def my_suc : Nat := by constructor suc; exact zero\n\
             def main : Nat := my_suc",
        )
        .expect("tactic constructor (one arg) should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(1)
        );
    }

    #[test]
    fn tactic_constructor_named() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def my_two : Nat := by constructor suc; exact (suc zero)\n\
             def main : Nat := my_two",
        )
        .expect("tactic constructor (named) should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(2)
        );
    }

    #[test]
    fn tactic_constructor_chain() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def three : Nat := by constructor suc; exact (suc (suc zero))\n\
             def main : Nat := three",
        )
        .expect("tactic constructor chain should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(3)
        );
    }

    #[test]
    fn tactic_trivial_path() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def trivial_path : Path Nat zero zero := by trivial\n\
             def main : Nat := zero",
        )
        .expect("tactic trivial on reflexive path should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(0)
        );
    }

    #[test]
    fn tactic_trivial_datatype() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def trivial_nat : Nat := by trivial\n\
             def main : Nat := trivial_nat",
        )
        .expect("tactic trivial on zero-arg constructor should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(0)
        );
    }

    #[test]
    fn tactic_compute_simplifies() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def id : Nat -> Nat := fun x => x\n\
             def compute_test : Nat := by compute; exact (id zero)\n\
             def main : Nat := compute_test",
        )
        .expect("tactic compute should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(0)
        );
    }

    #[test]
    fn tactic_transitivity_typechecks() {
        // transitivity is hard to test with Nat since we don't have
        // path constructors.  Test that it at least parses and gives
        // a meaningful error when the goal isn't a path.
        let err = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def bad : Nat := by transitivity",
        );
        assert!(err.is_err());
    }

    #[test]
    fn unsolved_named_hole_is_reported() {
        let err = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def x : Nat := ?hole",
        )
        .unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("Unsolved holes"), "msg: {}", msg);
        assert!(msg.contains("?hole"), "msg: {}", msg);
        assert!(msg.contains("Nat"), "msg: {}", msg);
    }

    #[test]
    fn unsolved_underscore_hole_is_reported() {
        let err = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def x : Nat := _",
        )
        .unwrap_err();
        assert!(err.to_string().contains("Unsolved holes"));
    }

    #[test]
    fn hole_inside_term_is_reported() {
        let err = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def x : Nat := suc ?n",
        )
        .unwrap_err();
        assert!(err.to_string().contains("?n"));
    }

    #[test]
    fn type_hole_solved_by_unification() {
        let output = run_str(
            "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
             def x : ?ty := zero\n\
             def main : Nat := x",
        )
        .expect("type hole should be solved by unification");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(0)
        );
    }

    #[test]
    fn mutual_inductive_even_odd() {
        // Even/Odd as mutually-defined inductive types.
        // even zero, even (suc (suc n)) when even n
        // odd (suc zero), odd (suc (suc n)) when odd n
        let output = run_str(
            "inductive even where \
             | even_zero : even \
             | even_suc : even -> even \
             with inductive odd where \
             | odd_one : odd \
             | odd_suc : odd -> odd\n\
             def main : even := even_zero",
        )
        .expect("mutual inductive even/odd should typecheck");
        assert_eq!(output.name, "main");
    }

    #[test]
    fn mutual_inductive_forward_reference() {
        // B references A's constructors (forward reference).
        let output = run_str(
            "inductive A where \
             | a1 : A \
             | a2 : A \
             with inductive B where \
             | b1 : A -> B \
             | b2 : B\n\
             def main : B := b2",
        )
        .expect("mutual inductive with forward reference should typecheck");
        assert_eq!(output.name, "main");
    }

    #[test]
    fn induction_recursion_basic() {
        // Induction-recursion: define a datatype and a function simultaneously.
        let output = run_str(
            "inductive Nat where \
             | zero : Nat \
             | suc : Nat -> Nat \
             with isZero : Nat -> Nat := fun n => match n return Nat with \
             | zero => suc zero \
             | suc _ => zero\n\
             def main : Nat := isZero zero",
        )
        .expect("induction-recursion should typecheck");
        assert_eq!(
            crate::cubical::syntax::pretty::nat_to_int(&output.value),
            Some(1)
        );
    }

    #[test]
    fn nat_path_algebra_example_checks() {
        // Guard against regressions in the verified path-algebra example:
        // congruence, symmetry, transitivity and the additive laws over Nat.
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("nat_path_algebra.owl");
        check(&path).expect("examples/nat_path_algebra.owl should typecheck");
    }

    #[test]
    fn record_examples_check() {
        // Guard against regressions in record support: minimal records,
        // dependent record params, record update, and record-with-stress
        // patterns. The `record` declaration desugars to a single-constructor
        // inductive, so these exercise the constructor-arg (field-type)
        // checking path.
        for name in [
            "record_minimal.owl",
            "record_types.owl",
            "stress_record_types.owl",
            "stress_update_or_patterns.owl",
        ] {
            let path = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("examples")
                .join(name);
            check(&path).unwrap_or_else(|e| panic!("examples/{name} should typecheck: {e}"));
        }
    }

    #[test]
    fn nested_patterns_example_checks() {
        // Guard against regressions in the parser-side compilation of nested
        // constructor patterns (`suc (suc m)`, `cons x (cons y zs)`, `as` and
        // or-patterns combined with nesting). Deep nested-eliminator chains
        // need a bigger stack than the default 2 MiB test-thread stack.
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("stress_nested_patterns.owl");
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .expect("spawn nested patterns check thread");
        handle
            .join()
            .expect("nested patterns check thread panicked")
            .expect("examples/stress_nested_patterns.owl should typecheck");
    }

    #[test]
    fn nested_patterns_reject_mixed_columns() {
        // A variable pattern and a constructor pattern in the same column
        // cannot be compiled into the kernel's first-matching-case eliminator
        // (the variable arm would silently shadow the constructor arms).
        let source = "inductive Nat where\n\
             | zero : Nat\n\
             | suc : Nat -> Nat\n\
             def bad : Nat -> Nat := fun n =>\n\
               match n return Nat with\n\
               | zero        => zero\n\
               | suc (suc m) => m\n\
               | suc m       => m\n\
             def main : Nat := bad (suc zero)";
        let err = run_str(source).expect_err("mixed columns must be rejected");
        assert!(
            err.to_string()
                .contains("mixed variable and constructor patterns")
        );
    }

    #[test]
    fn nested_patterns_reject_incomplete_match() {
        // Phase 1.3 completeness check: an open match must cover every
        // constructor of the scrutinee datatype.
        let source = "inductive Nat where\n\
             | zero : Nat\n\
             | suc : Nat -> Nat\n\
             def bad : Nat -> Nat := fun n =>\n\
               match n return Nat with\n\
               | zero => zero\n\
             def main : Nat := bad (suc zero)";
        let err = run_str(source).expect_err("incomplete matches must be rejected");
        assert!(err.to_string().contains("incomplete pattern match"));
    }

    #[test]
    fn omega_demo_example_checks() {
        // Guard against regressions in `by omega`: definitional reflexivity
        // (unfolding `add` on constructor-headed arguments) and direct
        // application of a previously verified global lemma.
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("omega_demo.owl");
        check(&path).expect("examples/omega_demo.owl should typecheck");
    }

    #[test]
    fn ring_demo_example_checks() {
        // Guard against regressions in `by ring`: polynomial normalization
        // over the commutative semiring on Nat plus the law-application tree
        // the kernel re-checks (add_comm/mul_comm/distributivity demos).
        // The large law-application proofs need a bigger stack than the
        // default 2 MiB test-thread stack.
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("ring_demo.owl");
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .expect("spawn ring check thread");
        handle
            .join()
            .expect("ring check thread panicked")
            .expect("examples/ring_demo.owl should typecheck");
    }

    #[test]
    fn ring_laws_lib_checks() {
        // The ring-law library is imported by the demos and resolved by name
        // by `by ring`; it must typecheck standalone as a library. Its large
        // law-application normal forms need a bigger stack than the default
        // 2 MiB test-thread stack.
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("lib")
            .join("ring_laws.owl");
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .expect("spawn ring laws check thread");
        handle
            .join()
            .expect("ring laws check thread panicked")
            .expect("lib/ring_laws.owl should typecheck");
    }

    #[test]
    fn comm_ring_demo_example_checks() {
        // Guard against regressions in `by ring with C`: polynomial
        // normalization over an abstract `CommRing` record plus the
        // law-application tree the kernel re-checks.  The large proofs need a
        // bigger stack than the default 2 MiB test-thread stack.
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("comm_ring_demo.owl");
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .expect("spawn comm ring check thread");
        handle
            .join()
            .expect("comm ring check thread panicked")
            .expect("examples/comm_ring_demo.owl should typecheck");
    }

    #[test]
    fn stress_mul_algebra_example_checks() {
        // Full multiplicative algebra: assoc/comm/distributive laws over Nat
        // as cubical paths, ending with the double-double lemma. Guards the
        // suspended-elim case-body normalization fix in the equality checker.
        // The deeply nested elim/hcomp normal forms need a larger stack than
        // the default 2 MiB test-thread stack.
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("stress_mul_algebra.owl");
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .expect("spawn stress check thread");
        handle
            .join()
            .expect("stress check thread panicked")
            .expect("examples/stress_mul_algebra.owl should typecheck");
    }

    #[test]
    fn field_demo_example_checks() {
        // Guard against regressions in `by field with F`: the fraction
        // reification/inverse machinery over an abstract `Field` record plus
        // the law-application tree the kernel re-checks (frac mul/add/div,
        // inv inv/mul, mul inv). The large proofs need a bigger stack than
        // the default 2 MiB test-thread stack; the kernel re-check is also
        // slow in debug builds (the biggest theorem takes ~1 min per pass).
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("field_demo.owl");
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .expect("spawn field check thread");
        handle
            .join()
            .expect("field check thread panicked")
            .expect("examples/field_demo.owl should typecheck");
    }

    #[test]
    fn field_laws_lib_checks() {
        // The field-law library is imported by the demos and resolved by name
        // by `by field with F`; it must typecheck standalone as a library.
        // Its large law-application normal forms need a bigger stack than the
        // default 2 MiB test-thread stack.
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("lib")
            .join("field_laws.owl");
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .expect("spawn field laws check thread");
        handle
            .join()
            .expect("field laws check thread panicked")
            .expect("lib/field_laws.owl should typecheck");
    }

    #[test]
    fn all_example_files_check() {
        // Sweep every examples/*.owl file not already covered by a dedicated
        // test above (cubical/HIT/path/param/quotient/tactics/record demos and
        // the remaining stress files), so nothing in examples/ can silently
        // regress. Each file is checked on a 64 MiB stack thread so large
        // proof trees don't overflow the default 2 MiB test-thread stack.
        let covered = [
            "nat_path_algebra.owl",
            "record_minimal.owl",
            "record_types.owl",
            "stress_record_types.owl",
            "stress_update_or_patterns.owl",
            "omega_demo.owl",
            "ring_demo.owl",
            "comm_ring_demo.owl",
            "stress_mul_algebra.owl",
            "field_demo.owl",
        ];
        let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
        let mut files: Vec<_> = std::fs::read_dir(&examples)
            .expect("examples/ should exist")
            .map(|e| {
                e.expect("read dir entry")
                    .file_name()
                    .to_string_lossy()
                    .into_owned()
            })
            .filter(|n| n.ends_with(".owl") && !covered.contains(&n.as_str()))
            .collect();
        files.sort();
        assert!(
            !files.is_empty(),
            "expected at least one uncovered example file"
        );
        let handles: Vec<_> = files
            .iter()
            .cloned()
            .map(|name| {
                let path = examples.join(&name);
                std::thread::Builder::new()
                    .stack_size(64 * 1024 * 1024)
                    .spawn(move || {
                        check(&path)
                            .unwrap_or_else(|e| panic!("examples/{name} should typecheck: {e}"))
                    })
                    .expect("spawn example check thread")
            })
            .collect();
        for (name, handle) in files.iter().zip(handles) {
            handle
                .join()
                .unwrap_or_else(|e| panic!("examples/{name} thread panicked: {e:?}"));
        }
    }

    #[test]
    fn omega_rejects_unproved_comm() {
        // Without a pre-proved comm lemma omega cannot synthesize induction
        // yet; it must fail with a clear error rather than accept a circular
        // proof.
        let source = "inductive Nat where\n\
             | zero : Nat\n\
             | suc : Nat -> Nat\n\
             def add : Nat -> Nat -> Nat := fun m n =>\n\
               match m return Nat with\n\
               | zero => n\n\
               | suc m' => suc (add m' n)\n\
             def bad : forall (m : Nat), forall (n : Nat), Path Nat (add m n) (add n m) := by intro m n; omega";
        let err = run_str(source).expect_err("omega should reject an unproved comm goal");
        assert!(err.to_string().contains("omega: unable to solve goal"));
    }
}
