//! File I/O pipeline: read, parse, typecheck, and evaluate cubical source files.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::cubical::env::{Env, check_with_full_env, infer_with_full_env};
use crate::cubical::nbe::{nbe_eval, nbe_eval_with_globals, zonk};
use crate::cubical::parser::{Decl, ProgramParser};
use crate::cubical::session::Session;
use crate::cubical::syntax::{LevelExpr, Name, Term};
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
pub fn run(path: impl AsRef<Path>, session: &mut Session) -> Result<RunOutput, RunError> {
    let path = path.as_ref();
    let source = std::fs::read_to_string(path)?;
    run_source(path, &source, session)
}

/// Read and typecheck a cubical source file without evaluating an entry point.
///
/// This accepts libraries containing only datatype declarations, which makes it
/// suitable for the `owl check` command and for checking imported modules.
pub fn check(path: impl AsRef<Path>, session: &mut Session) -> Result<(), RunError> {
    let path = path.as_ref();
    let source = std::fs::read_to_string(path)?;
    check_source(path, &source, session)
}

/// Typecheck and evaluate cubical source from a string, using the current
/// directory for import resolution.
pub fn run_str(source: &str, session: &mut Session) -> Result<RunOutput, RunError> {
    run_source(Path::new("."), source, session)
}

/// Typecheck cubical source from a string, without requiring a `main`
/// definition. Imports are resolved relative to the current directory.
pub fn check_str(source: &str, session: &mut Session) -> Result<(), RunError> {
    check_source(Path::new("."), source, session)
}

fn run_source(
    root_path: &Path,
    source: &str,
    session: &mut Session,
) -> Result<RunOutput, RunError> {
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
        &mut HashMap::new(),
        &mut HashMap::new(),
        None,
        &mut last_def,
        None,
        None,
        session,
    )?;

    // Prefer `main` over the last definition when both exist.
    if let Some((name, _, _)) = env.defs.iter().find(|(name, _, _)| name == "main") {
        Ok(normalize_definition(&env, name, session))
    } else {
        last_def
            .map(|output| normalize_definition(&env, &output.name, session))
            .ok_or(RunError::NoEntryPoint)
    }
}

fn normalize_definition(env: &Env, name: &str, session: &mut Session) -> RunOutput {
    let index = env
        .defs
        .iter()
        .position(|(candidate, _, _)| candidate == name)
        .expect("definition selected from environment must exist");
    let (name, ty, value) = &env.defs[index];
    let globals = crate::cubical::env::build_definition_values(env, session);
    RunOutput {
        name: name.clone(),
        ty: zonk(ty, session),
        value: zonk(
            &nbe_eval_with_globals(value, &globals, index, session),
            session,
        ),
        global_names: env.defs.iter().map(|(name, _, _)| name.clone()).collect(),
    }
}

fn check_source(root_path: &Path, source: &str, session: &mut Session) -> Result<(), RunError> {
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
        &mut HashMap::new(),
        &mut HashMap::new(),
        None,
        &mut last_def,
        None,
        None,
        session,
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
    loaded: &mut HashSet<LoadedKey>,
    loading: &mut HashSet<PathBuf>,
    def_sources: &mut HashMap<Name, PathBuf>,
    dt_sources: &mut HashMap<Name, PathBuf>,
    origin: Option<&Path>,
    last_def: &mut Option<RunOutput>,
    forced_prefix: Option<&str>,
    only: Option<&[Name]>,
    session: &mut Session,
) -> Result<(), RunError> {
    let mut parser = ProgramParser::new_with_prefix(source, forced_prefix, session)?;
    session.clear_nbe_cache();
    session.clear_reflection_results();
    // Accumulate name positions across the whole program so globals from
    // earlier declarations (which may only surface as inferred types) resolve
    // to a position. Reverse lookup prefers the most recent occurrence.
    let mut decl_positions = Vec::new();
    while let Some(decl) = parser.next_decl()? {
        decl_positions.extend(parser.take_decl_positions());
        session.set_decl_name_positions(decl_positions.clone());
        let result: Result<(), RunError> = (|| {
            match decl {
                Decl::Import {
                    path,
                    alias,
                    only: nested_only,
                } => {
                    load_import(
                        &path,
                        &alias,
                        &nested_only,
                        env,
                        loaded,
                        loading,
                        def_sources,
                        dt_sources,
                        import_base,
                        last_def,
                        session,
                    )?;
                    parser.sync_from_env(env);
                }
                Decl::Module { .. } | Decl::ModuleEnd => {
                    // The parser already updated its module scope.
                }
                Decl::ModuleInst { name, source, args } => {
                    instantiate_module(&name, &source, &args, env, session)?;
                    // Instantiated members must resolve in later declarations.
                    parser.sync_from_env(env);
                }
                Decl::Data(dt) => {
                    process_data(&dt, env, session)?;
                    if import_selection_active(&dt.name, only, forced_prefix) {
                        if let Some(p) = origin {
                            note_imported_dt(&dt.name, p, dt_sources)?;
                        }
                    }
                    prune_datatypes(env, only, forced_prefix, 1);
                }
                Decl::DataMutual(dts) => {
                    process_data_mutual(&dts, env, session)?;
                    for dt in &dts {
                        if import_selection_active(&dt.name, only, forced_prefix) {
                            if let Some(p) = origin {
                                note_imported_dt(&dt.name, p, dt_sources)?;
                            }
                        }
                    }
                    prune_datatypes(env, only, forced_prefix, dts.len());
                }
                Decl::Record(dt) => {
                    process_data(&dt, env, session)?;
                    if import_selection_active(&dt.name, only, forced_prefix) {
                        if let Some(p) = origin {
                            note_imported_dt(&dt.name, p, dt_sources)?;
                        }
                    }
                    prune_datatypes(env, only, forced_prefix, 1);
                }
                Decl::DataWithFunc {
                    dt,
                    func_name,
                    func_ty,
                    func_val,
                } => {
                    process_data_with_func(&dt, &func_name, &func_ty, &func_val, env, session)?;
                    if import_selection_active(&func_name, only, forced_prefix) {
                        if let Some(p) = origin {
                            note_imported_def(&func_name, p, def_sources)?;
                        }
                    } else {
                        hide_front_def(env);
                    }
                    if import_selection_active(&dt.name, only, forced_prefix) {
                        if let Some(p) = origin {
                            note_imported_dt(&dt.name, p, dt_sources)?;
                        }
                    }
                    prune_datatypes(env, only, forced_prefix, 1);
                }
                Decl::Def {
                    name,
                    ty,
                    val,
                    by_wf,
                } => {
                    *last_def = Some(process_def(&name, &ty, &val, env, by_wf, session)?);
                    if import_selection_active(&name, only, forced_prefix) {
                        if let Some(p) = origin {
                            note_imported_def(&name, p, def_sources)?;
                        }
                    } else {
                        hide_front_def(env);
                    }
                }
                Decl::Postulate { name, ty } => {
                    process_postulate(&name, &ty, env, session)?;
                    if import_selection_active(&name, only, forced_prefix) {
                        if let Some(p) = origin {
                            note_imported_def(&name, p, def_sources)?;
                        }
                    } else {
                        hide_front_def(env);
                    }
                    parser.sync_from_env(env);
                }
            }
            Ok(())
        })();
        result?;
        session.clear_nbe_cache();
        session.clear_reflection_results();
    }
    session.clear_decl_name_positions();
    Ok(())
}

/// The dedup key for an imported file: its canonical path plus the forced
/// module prefix (an aliased file may be imported under several aliases, in
/// which case each alias is a distinct namespace).
type LoadedKey = (PathBuf, String);
fn load_import(
    path: &str,
    alias: &Option<String>,
    only: &Option<Vec<Name>>,
    env: &mut Env,
    loaded: &mut HashSet<LoadedKey>,
    loading: &mut HashSet<PathBuf>,
    def_sources: &mut HashMap<Name, PathBuf>,
    dt_sources: &mut HashMap<Name, PathBuf>,
    import_base: &Path,
    last_def: &mut Option<RunOutput>,
    session: &mut Session,
) -> Result<(), RunError> {
    let resolved = resolve_import_path(import_base, path);
    let canonical = canonical_import_path(&resolved);
    let key: LoadedKey = (canonical.clone(), loaded_tag(alias, only));
    if loaded.contains(&key) {
        return Ok(());
    }
    // Cycle detection is per canonical path: loading a file twice in a cycle
    // recurses forever regardless of alias or selection.
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
    process_file_source(
        &source,
        nested_base,
        env,
        loaded,
        loading,
        def_sources,
        dt_sources,
        Some(&canonical),
        last_def,
        alias.as_deref(),
        only.as_deref(),
        session,
    )?;
    loading.remove(&canonical);
    loaded.insert(key);
    Ok(())
}

/// Namespace tag for the dedup key: the forced alias, then the sorted,
/// deduplicated `only` entries so `only [x, y]` and `only [y, x]` share one
/// load. No selection contributes nothing.
fn loaded_tag(alias: &Option<String>, only: &Option<Vec<Name>>) -> String {
    let mut tag = alias.clone().unwrap_or_default();
    if let Some(items) = only {
        tag.push('\u{1}');
        let mut sorted: Vec<&str> = items.iter().map(|s| s.as_str()).collect();
        sorted.sort();
        sorted.dedup();
        tag.push_str(&sorted.join(","));
    }
    tag
}
/// Register an imported definition, rejecting collisions with definitions
/// from a different import.
fn note_imported_def(
    name: &Name,
    origin: &Path,
    def_sources: &mut HashMap<Name, PathBuf>,
) -> Result<(), RunError> {
    if let Some(prev) = def_sources.get(name) {
        if prev != origin {
            return Err(RunError::Import(format!(
                "conflicting definitions for '{}': imported from '{}' and '{}'; \
                 disambiguate with 'import ... as <alias>' or 'only [...]' selections",
                name,
                prev.display(),
                origin.display()
            )));
        }
    }
    def_sources.insert(name.clone(), origin.to_path_buf());
    Ok(())
}
/// Register an imported datatype, rejecting cross-file collisions (datatype
/// lookup is by name, so two different declarations under one name would make
/// eliminators ambiguous).
fn note_imported_dt(
    name: &Name,
    origin: &Path,
    dt_sources: &mut HashMap<Name, PathBuf>,
) -> Result<(), RunError> {
    if let Some(prev) = dt_sources.get(name) {
        if prev != origin {
            return Err(RunError::Import(format!(
                "conflicting datatype '{}': imported from '{}' and '{}'; \
                 disambiguate with 'import ... as <alias>' or 'only [...]' selections",
                name,
                prev.display(),
                origin.display()
            )));
        }
    }
    dt_sources.insert(name.clone(), origin.to_path_buf());
    Ok(())
}
/// Whether a declaration survives the active `only [...]` clause at all
/// (no clause = everything is selected).
fn import_selection_active(name: &str, only: Option<&[Name]>, forced_prefix: Option<&str>) -> bool {
    match only {
        None => true,
        Some(list) => import_selection_selected(name, list, forced_prefix),
    }
}
/// Expand a module instantiation `module N = M (e1) ... (en)` into ordinary
/// definitions: every def `M.x` of the source module becomes a fresh global
/// `N.x : M.x e1 ... en := M.x e1 ... en`, fed through the standard
/// `process_def` path so the kernel re-checks each expansion.
///
/// The annotation instantiates the member's stored Pi-type through NbE
/// (term-level application cannot apply to an embedded Pi term); the value
/// is an application spine over a *global reference* to the member (never
/// over its unfolded lambda — that redex cannot be inferred). The reference
/// index is resolved immediately before definition as `idx + 1`: this very
/// member is front-inserted before its body check, shifting the source down.
/// Members expand oldest-first; nested members (`M.N.x`) are rejected in v1.
fn instantiate_module(
    name: &Name,
    source: &Name,
    args: &[Term],
    env: &mut Env,
    session: &mut Session,
) -> Result<(), RunError> {
    let src_prefix = format!("{source}.");
    let mut members: Vec<Name> = Vec::new();
    for (n, _, _) in env.defs.iter() {
        if let Some(rest) = n.strip_prefix(&src_prefix) {
            if rest.contains('.') {
                return Err(RunError::Type(Box::new(TypeError::Other(format!(
                    "module instantiation of '{source}' with nested members is not supported \
                     (found '{}')",
                    n
                )))));
            }
            members.push(rest.to_string());
        }
    }
    for m in members.into_iter().rev() {
        let src_full = format!("{source}.{m}");
        let dst_full = format!("{name}.{m}");
        let idx = env
            .defs
            .iter()
            .position(|(n, _, _)| *n == src_full)
            .ok_or_else(|| {
                RunError::Type(Box::new(TypeError::Other(format!(
                    "unknown module member '{}' during instantiation",
                    src_full
                ))))
            })?;
        // Annotation: instantiate the source member's stored Pi-type by
        // asking the typechecker to INFER the applied spine (pre-insert
        // layout). Inference both validates every argument against the
        // corresponding domain and returns the concrete instantiated type,
        // which is a proper type expression and therefore passes
        // `process_def`'s universe check. Term-level application cannot
        // express this instantiation directly, and NbE cannot either —
        // `do_apply` intentionally blocks on `VPi`.
        //
        // Value: the same application spine but over a reference anchored at
        // `idx + 1`, because `process_def` inserts this very member at the
        // front before checking its body, shifting the source member down.
        // The syntactic spine only needs to be valid for that immediate
        // check; afterwards the member lives as an evaluated value.
        let gref_now = Term::TVar(idx as i32);
        let probe = args.iter().fold(gref_now, |acc, a| {
            Term::TApp(Arc::new(acc), Arc::new(a.clone()))
        });
        let ann = zonk(&infer_with_full_env(env, &probe, session)?, session);
        let gref = Term::TVar((idx + 1) as i32);
        let spine = args.iter().fold(gref, |acc, a| {
            Term::TApp(Arc::new(acc), Arc::new(a.clone()))
        });
        process_def(&dst_full, &ann, &spine, env, false, session)?;
    }
    Ok(())
}

/// Selection test for an `import ... only [...]` clause. A declaration whose
/// fully qualified name (forced import alias included) is `name` stays
/// visible iff, after stripping the alias prefix, some selection entry equals
/// it or is a module-path prefix of it — selecting `M` keeps everything
/// inside module `M`.
fn import_selection_selected(name: &str, only: &[Name], forced_prefix: Option<&str>) -> bool {
    let stripped = match forced_prefix {
        Some(prefix) => name.strip_prefix(&format!("{prefix}.")).unwrap_or(name),
        None => name,
    };
    only.iter()
        .any(|entry| stripped == entry.as_str() || stripped.starts_with(&format!("{entry}.")))
}
/// Hide the definition most recently added at the front of `env.defs`.
///
/// Hiding is rename-only on purpose: de Bruijn indices were assigned from
/// declaration order at parse time, so removing the entry would corrupt every
/// later reference into the file; names are cosmetic labels and safe to
/// rewrite. The replacement name starts with NUL so it can never appear in
/// source text and never matches a resolution candidate.
fn hide_front_def(env: &mut Env) {
    if let Some((name, _, _)) = env.defs.first_mut() {
        *name = format!("\u{0}hidden::{}", name);
    }
}
/// Drop the last `count` registered datatypes that are not selected by an
/// active `only` clause (`None` keeps everything). Datatype lookup is by name
/// rather than position, so removal cannot corrupt references; a kept
/// declaration that mentions a dropped one fails loudly at its point of use.
/// That is the documented semantics of selective imports: list what you use.
fn prune_datatypes(
    env: &mut Env,
    only: Option<&[Name]>,
    forced_prefix: Option<&str>,
    count: usize,
) {
    let Some(only) = only else { return };
    let start = env.datatypes.len().saturating_sub(count);
    let kept: Vec<crate::cubical::syntax::Datatype> = env.datatypes[start..]
        .iter()
        .filter(|dt| import_selection_selected(&dt.name, only, forced_prefix))
        .cloned()
        .collect();
    env.datatypes.truncate(start);
    env.datatypes.extend(kept);
}

fn process_data(
    dt: &crate::cubical::syntax::Datatype,
    env: &mut Env,
    session: &mut Session,
) -> Result<(), RunError> {
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
                &Term::TUniv(LevelExpr::LConst(0)),
                session,
            )
            .map_err(|e| RunError::Type(Box::new(e)))?;
        }
    }
    // Check boundary coherence for square constructors.
    crate::cubical::typechecker::check_sqcon_coherence(&env.datatypes, dt, session)
        .map_err(|e| RunError::Type(Box::new(e)))?;
    Ok(())
}

/// Process a mutual inductive declaration: register all datatypes first,
/// then typecheck each constructor against the full mutual environment.
fn process_data_mutual(
    dts: &[crate::cubical::syntax::Datatype],
    env: &mut Env,
    session: &mut Session,
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
                    &Term::TUniv(LevelExpr::LConst(0)),
                    session,
                )
                .map_err(|e| RunError::Type(Box::new(e)))?;
            }
        }
        crate::cubical::typechecker::check_sqcon_coherence(&env.datatypes, dt, session)
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
    session: &mut Session,
) -> Result<RunOutput, RunError> {
    // First, process the datatype (positivity check + register).
    process_data(dt, env, session)?;
    // Then, process the function definition with the datatype in scope.
    process_def(func_name, func_ty, func_val, env, false, session)
}

/// Collect the unsolved holes (with names and expected types) in `t`.
fn unsolved_hole_report(t: &Term, session: &Session) -> Vec<(i32, Name, Option<Term>)> {
    let mut ids = Vec::new();
    collect_meta_ids(t, &mut ids);
    ids.into_iter()
        .filter(|id| session.get_meta_solution(*id).is_none())
        .map(|id| {
            let name = session.get_meta_name(id).unwrap_or_default();
            let expected = session.get_meta_expected(id);
            (id, name, expected)
        })
        .collect()
}

fn collect_meta_ids(t: &Term, out: &mut Vec<i32>) {
    match t {
        Term::Meta(i) => {
            if !out.contains(i) {
                out.push(*i);
            }
        }
        Term::TApp(a, b) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
        }
        Term::TAbs(_, b) => {
            collect_meta_ids(b, out);
        }
        Term::TLift(a, _) | Term::TLower(a) => {
            collect_meta_ids(a, out);
        }
        Term::TLevelTy => {}
        Term::TPi(_, a, b, _) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
        }
        Term::TPath(a, b, c) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
            collect_meta_ids(c, out);
        }
        Term::PLam(_, b) => {
            collect_meta_ids(b, out);
        }
        Term::PApp(a, b) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
        }
        Term::THComp(a, faces, c) => {
            collect_meta_ids(a, out);
            for f in faces {
                collect_meta_ids(&f.1, out);
            }
            collect_meta_ids(c, out);
        }
        Term::TComp(a, faces, c) => {
            collect_meta_ids(a, out);
            for f in faces {
                collect_meta_ids(&f.1, out);
            }
            collect_meta_ids(c, out);
        }
        Term::TFill(a, faces, c) => {
            collect_meta_ids(a, out);
            for f in faces {
                collect_meta_ids(&f.1, out);
            }
            collect_meta_ids(c, out);
        }
        Term::THFill(a, faces, c) => {
            collect_meta_ids(a, out);
            for f in faces {
                collect_meta_ids(&f.1, out);
            }
            collect_meta_ids(c, out);
        }
        Term::TTransport(a, b) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
        }
        Term::TGlue(a, b, c) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
            collect_meta_ids(c, out);
        }
        Term::TGlueElem(a, b, c) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
            collect_meta_ids(c, out);
        }
        Term::TUnglue(a, b, c) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
            collect_meta_ids(c, out);
        }
        Term::TPartial(a, b) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
        }
        Term::TEquiv(a, b) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
        }
        Term::TMkEquiv(a, b, c, d, e, f) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
            collect_meta_ids(c, out);
            collect_meta_ids(d, out);
            collect_meta_ids(e, out);
            collect_meta_ids(f, out);
        }
        Term::TEquivFwd(a, b) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
        }
        Term::TUa(a) => {
            collect_meta_ids(a, out);
        }
        Term::TSigma(_, a, b) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
        }
        Term::TPair(a, b) => {
            collect_meta_ids(a, out);
            collect_meta_ids(b, out);
        }
        Term::TFst(a) | Term::TSnd(a) => {
            collect_meta_ids(a, out);
        }
        Term::TData(_, args) | Term::TCon(_, _, args) => {
            for a in args {
                collect_meta_ids(a, out);
            }
        }
        Term::TPCon(_, _, args, r) => {
            for a in args {
                collect_meta_ids(a, out);
            }
            collect_meta_ids(r, out);
        }
        Term::TSqCon(_, _, args, r, s) => {
            for a in args {
                collect_meta_ids(a, out);
            }
            collect_meta_ids(r, out);
            collect_meta_ids(s, out);
        }
        Term::TCellCon(_, _, args, ivars) => {
            for a in args {
                collect_meta_ids(a, out);
            }
            for a in ivars {
                collect_meta_ids(a, out);
            }
        }
        Term::TElim(motive, cases, scrut) => {
            collect_meta_ids(motive, out);
            for c in cases {
                collect_meta_ids(&c.body, out);
            }
            collect_meta_ids(scrut, out);
        }
        Term::TProj(_, a) => {
            collect_meta_ids(a, out);
        }
        Term::TRecordUpdate(a, fields) => {
            collect_meta_ids(a, out);
            for (_, v) in fields {
                collect_meta_ids(v, out);
            }
        }
        _ => {}
    }
}

/// Phase timer for the per-definition pipeline, reported to stderr when
/// `OWL_TIMINGS=1`. Zero cost otherwise (one env lookup per report call,
/// which itself is gated).
struct PhaseTiming<'a>(&'a str, std::time::Instant);

impl<'a> PhaseTiming<'a> {
    fn start(def: &'a str) -> Self {
        Self(def, std::time::Instant::now())
    }
    fn report(&self, phase: &str) {
        if std::env::var_os("OWL_TIMINGS").is_some() {
            eprintln!(
                "[timing] {:<28} {:<14} {:>10.2?}",
                self.0,
                phase,
                self.1.elapsed()
            );
        }
    }
}

fn process_postulate(
    name: &Name,
    ty: &Term,
    env: &mut Env,
    session: &mut Session,
) -> Result<(), RunError> {
    session.clear_nbe_cache();
    session.clear_reflection_results();
    crate::debug_log!("process_postulate '{}':", name);

    // Verify the type is in a universe.
    if !matches!(ty, Term::Meta(_)) {
        match nbe_eval(&infer_with_full_env(env, ty, session)?, session) {
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

    // Register as a postulate — no body, opaque neutral value.
    env.postulate(name.clone(), ty.clone());
    Ok(())
}

pub(crate) fn process_def(
    name: &Name,
    ty: &Term,
    val: &Term,
    env: &mut Env,
    by_wf: bool,
    session: &mut Session,
) -> Result<RunOutput, RunError> {
    session.clear_nbe_cache();
    session.clear_reflection_results();
    crate::debug_log!("process_def '{}':", name);
    if by_wf {
        crate::cubical::typechecker::termination::set_skip_guard(true, session);
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
        match nbe_eval(&infer_with_full_env(env, ty, session)?, session) {
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
    let globals = crate::cubical::env::build_definition_values(env, session);
    let prev_globals = session.set_current_globals(Some(globals));
    let tm_resolve = PhaseTiming::start(name.as_str());
    let resolved_val = crate::cubical::tactics::resolve_tactics(
        &env.datatypes,
        val,
        &check_ty,
        &global_ctx,
        session,
    )
    .map_err(|e| RunError::Type(Box::new(ContextualError::with_def(name, e).inner)));
    session.set_current_globals(prev_globals);
    let resolved_val = resolved_val?;
    tm_resolve.report("tactic-resolve");

    // Register before checking the body so recursive calls resolve.
    // Store the RAW annotation so that consumers resolving this definition's
    // type via the stored-ref convention
    // (`nbe_eval_ctx(ctx.len(), shift(j+1, 0, annotation))`) see a clean,
    // non-inlined annotation.
    env.define(name.clone(), ty.clone(), resolved_val.clone());
    // Register as an instance if the type is a known instance class
    if let Term::TData(dname, _params) = ty {
        if matches!(dname.as_str(), "CommRing" | "Field" | "Group" | "Module") {
            env.register_instance(name.clone(), ty.clone(), resolved_val.clone());
        }
    }
    let prev_def =
        crate::cubical::typechecker::termination::set_current_def(Some(name.clone()), session);
    let tm_check = PhaseTiming::start(name.as_str());
    let from_tactic = matches!(val, Term::TBy(_));

    // Set the reflection context so getContext can access it during NbE.
    // Encode context as nested pairs: ((name1, type1), ((name2, type2), ...)).
    let ctx_term = global_ctx.iter().rfold(
        Term::TCon("Unit".to_string(), "tt".to_string(), Vec::new()),
        |acc, (n, t)| {
            Term::TPair(
                Arc::new(Term::TPair(
                    Arc::new(Term::TData("String".to_string(), vec![Term::TVar(0)])),
                    Arc::new(t.clone()),
                )),
                Arc::new(acc),
            )
        },
    );
    let prev_ctx = session.reflection_ctx().cloned();
    session.set_reflection_ctx(Some(ctx_term));

    let result = check_with_full_env(env, &resolved_val, &check_ty, session).map_err(|e| {
        let err = ContextualError::with_def(name, e);
        if from_tactic && !crate::cubical::debug::is_active() {
            RunError::Type(Box::new(TypeError::Other(format!(
                "{err}\n  (the body was produced by a tactic block; re-run with --debug for \
                 the solver's own diagnostic)"
            ))))
        } else {
            RunError::Type(Box::new(err.inner))
        }
    });
    tm_check.report("kernel-recheck");
    crate::cubical::typechecker::termination::set_current_def(prev_def, session);
    session.set_reflection_ctx(prev_ctx);
    if by_wf {
        crate::cubical::typechecker::termination::set_skip_guard(false, session);
    }
    result?;

    // Unsolved-hole check: a definition may not leave `?` / `_` holes open.
    let mut metas = unsolved_hole_report(&zonk(&resolved_val, session), session);
    metas.extend(unsolved_hole_report(&zonk(ty, session), session));
    if !metas.is_empty() {
        let names: Vec<Name> = env.defs.iter().map(|(n, _, _)| n.clone()).collect();
        return Err(RunError::Type(Box::new(
            ContextualError::with_def(name, TypeError::UnsolvedHoles { metas, names }).inner,
        )));
    }

    let tm_norm = PhaseTiming::start(name.as_str());
    let output = RunOutput {
        name: name.clone(),
        ty: zonk(ty, session),
        value: zonk(&nbe_eval(&resolved_val, session), session),
        global_names: env.defs.iter().map(|(n, _, _)| n.clone()).collect(),
    };
    tm_norm.report("output-norm");

    Ok(output)
}

#[cfg(test)]
mod tests;
