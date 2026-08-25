//! File I/O pipeline: read, parse, typecheck, and evaluate cubical source files.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::path::{Path, PathBuf};

use crate::cubical::env::{Env, check_with_full_env, infer_with_full_env};
use crate::cubical::nbe::{nbe_eval, nbe_eval_with_globals, zonk};
use crate::cubical::parser::{Decl, ProgramParser};
use crate::cubical::session::Session;
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
            }
            Ok(())
        })();
        result?;
        session.clear_nbe_cache();
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
            Term::TApp(Box::new(acc), Box::new(a.clone()))
        });
        let ann = zonk(&infer_with_full_env(env, &probe, session)?, session);
        let gref = Term::TVar((idx + 1) as i32);
        let spine = args.iter().fold(gref, |acc, a| {
            Term::TApp(Box::new(acc), Box::new(a.clone()))
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
                &Term::TUniv(0),
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
                    &Term::TUniv(0),
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
        Term::TPi(_, a, b) => {
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

fn process_def(
    name: &Name,
    ty: &Term,
    val: &Term,
    env: &mut Env,
    by_wf: bool,
    session: &mut Session,
) -> Result<RunOutput, RunError> {
    session.clear_nbe_cache();
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

    // Register before checking the body so recursive calls resolve.
    // Store the RAW annotation so that consumers resolving this definition's
    // type via the stored-ref convention
    // (`nbe_eval_ctx(ctx.len(), shift(j+1, 0, annotation))`) see a clean,
    // non-inlined annotation.
    env.define(name.clone(), ty.clone(), resolved_val.clone());
    let prev_def =
        crate::cubical::typechecker::termination::set_current_def(Some(name.clone()), session);
    let result = check_with_full_env(env, &resolved_val, &check_ty, session)
        .map_err(|e| RunError::Type(Box::new(ContextualError::with_def(name, e).inner)));
    crate::cubical::typechecker::termination::set_current_def(prev_def, session);
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

    let output = RunOutput {
        name: name.clone(),
        ty: zonk(ty, session),
        value: zonk(&nbe_eval(&resolved_val, session), session),
        global_names: env.defs.iter().map(|(n, _, _)| n.clone()).collect(),
    };

    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::io::Write;

    fn run(path: impl AsRef<Path>) -> Result<RunOutput, RunError> {
        crate::cubical::session::with_session_mut(|session| super::run(path, session))
    }

    fn check(path: impl AsRef<Path>) -> Result<(), RunError> {
        crate::cubical::session::with_session_mut(|session| super::check(path, session))
    }

    fn run_str(source: &str) -> Result<RunOutput, RunError> {
        crate::cubical::session::with_session_mut(|session| super::run_str(source, session))
    }

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
    fn run_aliased_import_qualifies_names() {
        let dir = std::env::temp_dir().join(format!("cubical_alias_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let arith_path = dir.join("arith.owl");
        let main_path = dir.join("main.owl");

        fs::write(
            &arith_path,
            "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
             def add : Nat -> Nat -> Nat := fun m n => match m return Nat with\n\
             \x20 | zero => n\n  | suc m' => suc (add m' n)\n",
        )
        .unwrap();
        fs::write(
            &main_path,
            "import \"arith.owl\" as A\n\
             def four : A.Nat := A.add (A.suc (A.suc A.zero)) (A.suc (A.suc A.zero))\n",
        )
        .unwrap();

        let output = run(&main_path).expect("aliased import should run");
        assert_eq!(output.name, "four");

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_nested_modules_and_aliased_folding() {
        let dir = std::env::temp_dir().join(format!("cubical_module_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let outer_path = dir.join("outer.owl");
        let plain_path = dir.join("plain.owl");
        let aliased_path = dir.join("aliased.owl");

        // Library with nested modules; self-references are unqualified so the
        // file works both plainly imported and folded under an alias.
        fs::write(
            &outer_path,
            "module Outer where\n\
             \x20 module Inner where\n\
             \x20   inductive T where\n\
             \x20     | mk : T\n\
             \x20 end\n\
             \x20 def get : T := mk\n\
             end\n",
        )
        .unwrap();
        // Plain import keeps the file's own module names.
        fs::write(
            &plain_path,
            "import \"outer.owl\"\n\
             def v : Outer.Inner.T := Outer.Inner.mk\n\
             def w : Outer.Inner.T := Outer.get\n",
        )
        .unwrap();
        // Aliased import folds the file's modules into the alias, so nested
        // datatypes become `O.T` (flattened) — visible unqualified as `T`.
        fs::write(
            &aliased_path,
            "import \"outer.owl\" as O\n\
             def v : O.T := O.mk\n\
             def w : O.T := O.get\n",
        )
        .unwrap();

        let plain = run(&plain_path).expect("plain nested import should run");
        assert_eq!(plain.name, "w");
        let aliased = run(&aliased_path).expect("aliased nested import should run");
        assert_eq!(aliased.name, "w");

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_selective_import_keeps_selected_names() {
        let dir = std::env::temp_dir().join(format!("cubical_only_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let arith_path = dir.join("arith.owl");
        let main_path = dir.join("main.owl");

        fs::write(
            &arith_path,
            "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
             def add : Nat -> Nat -> Nat := fun m n => match m return Nat with\n\
             \x20 | zero => n\n  | suc m' => suc (add m' n)\n\
             def sub : Nat -> Nat -> Nat := fun m n => m\n",
        )
        .unwrap();
        // `Nat` and `add` are listed (dependencies included); `sub` is not
        // selected and must be invisible afterwards.
        fs::write(
            &main_path,
            "import \"arith.owl\" only [Nat, add]\n\
             def two : Nat := add (suc zero) (suc zero)\n",
        )
        .unwrap();

        let output = run(&main_path).expect("selective import should run");
        assert_eq!(output.name, "two");

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_selective_import_hides_unselected_names() {
        let dir =
            std::env::temp_dir().join(format!("cubical_only_hide_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let arith_path = dir.join("arith.owl");
        let main_path = dir.join("main.owl");

        fs::write(
            &arith_path,
            "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
             def add : Nat -> Nat -> Nat := fun m n => match m return Nat with\n\
             \x20 | zero => n\n  | suc m' => suc (add m' n)\n",
        )
        .unwrap();
        // `zero`/`suc` are not in the selection, so referencing them must fail.
        fs::write(
            &main_path,
            "import \"arith.owl\" only [add]\n\
             def bad : U0 := zero\n",
        )
        .unwrap();

        assert!(
            run(&main_path).is_err(),
            "unselected imported name should not resolve"
        );

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_selective_import_module_member_selection() {
        let dir =
            std::env::temp_dir().join(format!("cubical_only_module_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let lib_path = dir.join("lib.owl");
        let member_path = dir.join("member.owl");
        let module_path = dir.join("module_sel.owl");

        fs::write(
            &lib_path,
            "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
             module M where\n\
             \x20 def one : Nat := suc zero\n\
             end\n",
        )
        .unwrap();
        // Selecting a dotted member path keeps just that declaration.
        fs::write(
            &member_path,
            "import \"lib.owl\" only [Nat, M.one]\n\
             def v : Nat := M.one\n",
        )
        .unwrap();
        // Selecting the whole module keeps everything inside it.
        fs::write(
            &module_path,
            "import \"lib.owl\" only [Nat, M]\n\
             def v : Nat := M.one\n",
        )
        .unwrap();

        let out1 = run(&member_path).expect("dotted member selection should run");
        assert_eq!(out1.name, "v");
        let out2 = run(&module_path).expect("whole-module selection should run");
        assert_eq!(out2.name, "v");

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_selective_import_avoids_name_collisions() {
        let dir = std::env::temp_dir().join(format!(
            "cubical_only_collision_test_{}",
            std::process::id()
        ));
        fs::create_dir_all(&dir).unwrap();

        // Two libraries exposing a same-named `helper`; selective imports pull
        // disjoint members from each so both coexist.
        let a_path = dir.join("liba.owl");
        let b_path = dir.join("libb.owl");
        let main_path = dir.join("main.owl");

        fs::write(
            &a_path,
            "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
             def helper : Nat -> Nat := fun n => suc n\n\
             def from_a : Nat -> Nat := fun n => helper n\n",
        )
        .unwrap();
        fs::write(
            &b_path,
            "inductive Bool where | true : Bool | false : Bool\n\
             def helper : Bool -> Bool := fun b => b\n\
             def from_b : Bool -> Bool := fun b => helper b\n",
        )
        .unwrap();
        fs::write(
            &main_path,
            "import \"liba.owl\" only [Nat, suc, zero, from_a]\n\
             import \"libb.owl\" only [Bool, false, from_b]\n\
             def va : Nat := from_a (suc zero)\n\
             def vb : Bool := from_b false\n",
        )
        .unwrap();

        // The collision-prone `helper` names are never both exposed: each
        // import only merges its selected (visible) members.
        let output = run(&main_path).expect("disjoint selective imports should run");
        assert_eq!(output.name, "vb");

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_same_name_imports_from_different_files_rejected() {
        // Even byte-identical content conflicts when two different files
        // claim the same name: provenance is the disambiguation criterion,
        // not content. Re-merges of the SAME file (diamond imports) are
        // tolerated because origins track the defining file.
        let dir = std::env::temp_dir().join(format!("cubical_dup_ok_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let shared_body = "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
                           def add : Nat -> Nat -> Nat := fun m n => match m return Nat with\n\
                           \x20 | zero => n\n  | suc m' => suc (add m' n)\n";
        let shared_path = dir.join("shared.owl");
        let a_path = dir.join("dupa.owl");
        let b_path = dir.join("dupb.owl");
        let main_path = dir.join("main.owl");

        fs::write(&shared_path, shared_body).unwrap();
        // dupa and dupb each pull Nat/add from shared.owl (single origin) but
        // both declare their own `double`, so it exists under two defining
        // files — a genuine conflict even though the texts are identical.
        let double_def = "def double : Nat -> Nat := fun n => add n n\n";
        fs::write(&a_path, format!("import \"shared.owl\"\n{double_def}")).unwrap();
        fs::write(&b_path, format!("import \"shared.owl\"\n{double_def}")).unwrap();
        fs::write(
            &main_path,
            "import \"dupa.owl\"\n\
             import \"dupb.owl\"\n\
             def main : U0 -> U0 := fun A => A\n",
        )
        .unwrap();

        match run(&main_path) {
            Err(RunError::Import(msg)) => {
                assert!(
                    msg.contains("double"),
                    "error should name the conflicting symbol, got: {}",
                    msg
                );
            }
            other => panic!(
                "expected import conflict error, got: {:?}",
                other.map(|o| o.name)
            ),
        }

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_diamond_import_of_same_file_tolerated() {
        // main imports da.owl and db.owl; both import shared.owl. shared's
        // names arrive twice but from the same defining file, so no conflict.
        let dir = std::env::temp_dir().join(format!("cubical_diamond_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let shared_path = dir.join("shared.owl");
        let a_path = dir.join("da.owl");
        let b_path = dir.join("db.owl");
        let main_path = dir.join("main.owl");

        fs::write(&shared_path, "def idty : U0 -> U0 := fun A => A\n").unwrap();
        fs::write(
            &a_path,
            "import \"shared.owl\"\ndef a_v : U0 -> U0 := idty\n",
        )
        .unwrap();
        fs::write(
            &b_path,
            "import \"shared.owl\"\ndef b_v : U0 -> U0 := idty\n",
        )
        .unwrap();
        fs::write(
            &main_path,
            "import \"da.owl\"\n\
             import \"db.owl\"\n\
             def main : U0 -> U0 := idty\n",
        )
        .unwrap();

        let output = run(&main_path).expect("diamond import of same file should unify");
        assert_eq!(output.name, "main");

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_conflicting_imported_definitions_rejected() {
        let dir = std::env::temp_dir().join(format!("cubical_dup_bad_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let nat_decl = "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n";
        let a_path = dir.join("confa.owl");
        let b_path = dir.join("confb.owl");
        let main_path = dir.join("main.owl");

        fs::write(
            &a_path,
            format!("{nat_decl}def helper : Nat -> Nat := fun n => suc n\n"),
        )
        .unwrap();
        fs::write(
            &b_path,
            // confa's declarations arrive transitively (same origin, no
            // conflict); confb's own `helper` genuinely differs.
            "import \"confa.owl\"\ndef helper : Nat -> Nat := fun n => suc (suc n)\n",
        )
        .unwrap();
        fs::write(
            &main_path,
            "import \"confa.owl\"\n\
             import \"confb.owl\"\n\
             def main : U0 -> U0 := fun A => A\n",
        )
        .unwrap();

        match run(&main_path) {
            Err(RunError::Import(msg)) => {
                assert!(
                    msg.contains("helper"),
                    "error should name the conflicting symbol, got: {}",
                    msg
                );
            }
            other => panic!(
                "expected import conflict error, got: {:?}",
                other.map(|o| o.name)
            ),
        }

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_conflicting_imported_datatypes_rejected() {
        let dir = std::env::temp_dir().join(format!("cubical_dup_dt_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let a_path = dir.join("dta.owl");
        let b_path = dir.join("dtb.owl");
        let main_path = dir.join("main.owl");

        fs::write(&a_path, "inductive Mode where | on : Mode | off : Mode\n").unwrap();
        fs::write(
            &b_path,
            "inductive Mode where | on : Mode | flip : Mode -> Mode\n",
        )
        .unwrap();
        fs::write(
            &main_path,
            "import \"dta.owl\"\n\
             import \"dtb.owl\"\n\
             def main : U0 -> U0 := fun A => A\n",
        )
        .unwrap();

        match run(&main_path) {
            Err(RunError::Import(msg)) => {
                assert!(
                    msg.contains("'Mode'"),
                    "error should name the conflicting datatype, got: {}",
                    msg
                );
            }
            other => panic!(
                "expected import conflict error, got: {:?}",
                other.map(|o| o.name)
            ),
        }

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_parameterized_module_defs_typecheck_and_compute() {
        // Defs inside `module M (A : Type) where` become globals closed over
        // the parameter; sibling references apply it automatically; consumers
        // instantiate explicitly.
        let src = "\
inductive Nat where\n\
 \x20 | zero : Nat\n\
 \x20 | suc : Nat -> Nat\n\
def one : Nat := suc zero\n\
module Semi (A : Type) where\n\
 \x20 def idty : A -> A := fun x => x\n\
 \x20 def twice_id : A -> A := fun x => idty (idty x)\n\
end\n\
def v : Nat := ((Semi.twice_id Nat) one)\n\
def main : Nat := v\n";

        let output = run_str(src).expect("parameterized module program should run");
        assert_eq!(output.name, "main");
    }

    #[test]
    fn run_parameterized_module_rejects_datatype_inside() {
        let src = "\
module M (A : Type) where\n\
 \x20 inductive T where | mk : T\n\
end\n";
        assert!(
            run_str(src).is_err(),
            "datatype in parameterized module must be rejected"
        );
    }

    #[test]
    fn run_aliased_import_folds_parameterized_module_member() {
        let dir =
            std::env::temp_dir().join(format!("cubical_param_alias_test_{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();

        let lib_path = dir.join("plib.owl");
        let plain_path = dir.join("plain.owl");
        let aliased_path = dir.join("aliased.owl");

        fs::write(
            &lib_path,
            "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
             module Semi (A : Type) where\n\
             \x20 def idty : A -> A := fun x => x\n\
             end\n",
        )
        .unwrap();
        // Plain import keeps the module path: Semi.idty.
        fs::write(
            &plain_path,
            "import \"plib.owl\"\n\
             def v : Nat := ((Semi.idty Nat) (suc zero))\n",
        )
        .unwrap();
        // Aliased import folds the file's own modules: P.idty.
        fs::write(
            &aliased_path,
            "import \"plib.owl\" as P\n\
             def v : P.Nat := ((P.idty P.Nat) (P.suc P.zero))\n",
        )
        .unwrap();

        let out1 = run(&plain_path).expect("plain import of param-module lib should run");
        assert_eq!(out1.name, "v");
        let out2 = run(&aliased_path).expect("aliased folding of param module should run");
        assert_eq!(out2.name, "v");

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn run_module_instantiation_typechecks_and_computes() {
        // Parameterized instantiation: N.x behaves like the source member at
        // the given arguments, without explicit parameter application.
        let src = "\
inductive Nat where\n\
 \x20 | zero : Nat\n\
 \x20 | suc : Nat -> Nat\n\
def one : Nat := suc zero\n\
module Semi (A : Type) where\n\
 \x20 def idty : A -> A := fun x => x\n\
end\n\
module NatSemi = Semi (Nat)\n\
def v : Nat := (NatSemi.idty one)\n\
def main : Nat := v\n";

        let output = run_str(src).expect("instantiated module program should run");
        assert_eq!(output.name, "main");
    }

    #[test]
    fn run_module_instantiation_of_plain_module() {
        let src = "\
inductive Nat where\n\
 \x20 | zero : Nat\n\
 \x20 | suc : Nat -> Nat\n\
module Plain where\n\
 \x20 def two : Nat := suc (suc zero)\n\
end\n\
module N2 = Plain\n\
def v : Nat := N2.two\n\
def main : Nat := v\n";

        let output = run_str(src).expect("plain module instantiation should run");
        assert_eq!(output.name, "main");
    }

    #[test]
    fn natcommring_demo_example_checks() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/natcommring_demo.owl");
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .unwrap();
        handle
            .join()
            .unwrap()
            .expect("natcommring_demo.owl should typecheck");
    }

    #[test]
    fn int_omega_example_checks() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/int_demo.owl");
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .unwrap();
        handle
            .join()
            .unwrap()
            .expect("int_demo.owl should typecheck");
    }

    #[test]
    fn group_demo_example_checks() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/group_demo.owl");
        // Deep proof trees from the generated law-application chains exceed
        // the default 2 MiB test-thread stack in debug builds.
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .unwrap();
        handle
            .join()
            .unwrap()
            .expect("group_demo.owl should typecheck");
    }

    #[test]
    fn eq_tactic_refl_sym_chain() {
        // `by eq` closes reflexive goals, single hypotheses (either
        // orientation, via inline symmetry), and multi-hop chains through a
        // context-provided transitivity lemma.
        let src = "inductive Nat where\n\
 \x20 | zero : Nat\n\
 \x20 | suc : Nat -> Nat\n\
def trans : forall (a : Nat), forall (b : Nat), forall (c : Nat),\n\
 \x20 Path Nat a b -> Path Nat b c -> Path Nat a c :=\n\
 \x20 fun a b c p q => <i> hcomp Nat [~i => <j> a, i => q] (p @ i)\n\
def t_refl : forall (a : Nat), Path Nat a a := by intro a; eq\n\
def t_direct : forall (a : Nat), forall (b : Nat),\n\
 \x20 Path Nat a b -> Path Nat b a := by intro a b p; eq\n\
def t_chain : forall (a : Nat), forall (b : Nat), forall (c : Nat),\n\
 \x20 Path Nat a b -> Path Nat b c -> Path Nat a c :=\n\
 \x20 by intro a b c p q; eq\n\
def t_long : forall (a : Nat), forall (b : Nat), forall (c : Nat), forall (d : Nat),\n\
 \x20 Path Nat a b -> Path Nat b c -> Path Nat c d -> Path Nat a d :=\n\
 \x20 by intro a b c d p q r; eq\n";
        let output = run_str(src).expect("by eq programs should check");
        assert_eq!(output.name, "t_long");
    }

    #[test]
    fn eq_tactic_needs_trans_lemma_for_chains() {
        let src = "inductive Nat where\n\
 \x20 | zero : Nat\n\
 \x20 | suc : Nat -> Nat\n\
def t_chain : forall (a : Nat), forall (b : Nat), forall (c : Nat),\n\
 \x20 Path Nat a b -> Path Nat b c -> Path Nat a c :=\n\
 \x20 by intro a b c p q; eq\n";
        match run_str(src) {
            Err(RunError::Type(e)) => {
                let msg = format!("{}", e);
                assert!(
                    msg.contains("transitivity lemma"),
                    "expected missing-trans error, got: {}",
                    msg
                );
            }
            other => panic!(
                "expected missing-trans-lemma rejection, got: {:?}",
                other.map(|o| o.name)
            ),
        }
    }

    #[test]
    fn group_solver_rejects_non_identity() {
        let src = "\
record Group (A : Type) (mul : A -> A -> A) (inv : A -> A) (one : A) where\n\
 \x20 field trans : forall (a : A), forall (b : A), forall (c : A), Path A a b -> Path A b c -> Path A a c\n\
 \x20 field sym : forall (a : A), forall (b : A), Path A a b -> Path A b a\n\
 \x20 field cong_mul_l : forall (a : A), forall (b : A), forall (n : A), Path A a b -> Path A (mul a n) (mul b n)\n\
 \x20 field cong_mul_r : forall (a : A), forall (b : A), forall (m : A), Path A a b -> Path A (mul m a) (mul m b)\n\
 \x20 field cong_inv : forall (a : A), forall (b : A), Path A a b -> Path A (inv a) (inv b)\n\
 \x20 field mul_assoc : forall (a : A), forall (b : A), forall (c : A), Path A (mul (mul a b) c) (mul a (mul b c))\n\
 \x20 field one_mul : forall (a : A), Path A (mul one a) a\n\
 \x20 field mul_one : forall (a : A), Path A (mul a one) a\n\
 \x20 field inv_l : forall (a : A), Path A (mul (inv a) a) one\n\
 \x20 field inv_r : forall (a : A), Path A (mul a (inv a)) one\n\
 \x20 field inv_one : Path A (inv one) one\n\
 \x20 field inv_inv : forall (a : A), Path A (inv (inv a)) a\n\
 \x20 field inv_mul : forall (a : A), forall (b : A), Path A (inv (mul a b)) (mul (inv b) (inv a))\n\
def bad :\n\
 \x20 forall (A : Type), forall (mul : A -> A -> A), forall (inv : A -> A),\n\
 \x20 forall (one : A),\n\
 \x20 forall (G : Group A mul inv one), forall (a : A), forall (b : A),\n\
 \x20 Path A (mul a b) (mul b a) :=\n\
 \x20 by intro A mul inv one G a b; group with G\n";
        match run_str(src) {
            Err(RunError::Type(e)) => {
                assert!(
                    format!("{}", e).contains("words do not match"),
                    "expected word-mismatch error, got: {}",
                    e
                );
            }
            other => panic!(
                "expected word-mismatch rejection, got: {:?}",
                other.map(|o| o.name)
            ),
        }
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
        let _output = run(&path).expect("mul should compute");
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
    fn forall_after_arrow_example_checks() {
        // Guard against regressions in `forall` binders following a
        // non-dependent `->` (H10 ergonomics): `A -> forall (x : B), C` must
        // parse with the forall binding looser than the arrow, and the whole
        // thing must typecheck.
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("forall_after_arrow.owl");
        check(&path).expect("examples/forall_after_arrow.owl should typecheck");
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
    fn refined_hit_cases_example_checks() {
        // Guard against regressions in refined (nested) constructor patterns
        // on path-constructor HIT cases (`mer (suc m) i => ...`): the
        // typechecker's per-leaf boundary coherence, the nested-eliminator
        // compilation, and the NBE env layout (the case's interval binder is a
        // phantom slot below the ordinary args). Deep nested-eliminator normal
        // forms need a bigger stack than the default 2 MiB test-thread stack.
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("refined_hit_cases.owl");
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .expect("spawn refined hit cases check thread");
        handle
            .join()
            .expect("refined hit cases check thread panicked")
            .expect("examples/refined_hit_cases.owl should typecheck");
    }

    #[test]
    fn refined_pcon_arms_reject_incoherent_endpoints() {
        // A refined pcon arm whose body is not endpoint-coherent must be
        // rejected: the leaf body `<j> zero` violates the boundary at the
        // constructor's faces (the refined binder `suc m` carries the
        // constraint), so it cannot typecheck.
        let source = "inductive Nat where\n\
             | zero : Nat\n\
             | suc : Nat -> Nat\n\
             inductive SuspX where\n\
             | ntr : Nat -> SuspX\n\
             | sso : Nat -> SuspX\n\
             | mer : Nat -> SuspX [ ntr mer_0 , sso mer_0 ]\n\
             def bad : SuspX -> Nat :=\n\
               fun s =>\n\
               match s return Nat with\n\
               | ntr n => n\n\
               | sso n => n\n\
               | mer zero i => <j> zero\n\
               | mer (suc m) i => <j> zero\n\
             def main : Nat := bad (mer (suc zero) @ i1)";
        let err = run_str(source).expect_err("incoherent refined arm must be rejected");
        assert!(err.to_string().contains("Type mismatch"));
    }

    #[test]
    fn hit_constructor_endpoints_reduce_to_faces() {
        // Square/cell/path constructors applied at concrete endpoints are
        // definitionally their faces: `square @ i0 @ i1 = base` (face_j0 at
        // the outer interval, applied to the second), and `cube3 @ i0 @ i1 @
        // i0 = base` (the outermost face pair, then the remaining interval
        // args applied outermost-first). This must hold in the NBE normal
        // form, not just in the typechecker's endpoint checks.
        let header = "inductive Cube where\n\
             | base : Cube\n\
             | line1 : Cube [ base , base ]\n\
             | line2 : Cube [ base , base ]\n\
             | square : Cube [[ base , base , line2 , line2 ]]\n\
             | cube3 : Cube [[[ base , base , line2 , line2 , square , square ]]]\n";
        let base = Term::TCon("Cube".to_string(), "base".to_string(), vec![]);
        for combo in [
            "square @ i0 @ i0",
            "square @ i0 @ i1",
            "square @ i1 @ i0",
            "square @ i1 @ i1",
            "cube3 @ i0 @ i0 @ i0",
            "cube3 @ i1 @ i1 @ i1",
            "cube3 @ i0 @ i1 @ i0",
            "cube3 @ i0 @ i1 @ i1",
            "cube3 @ i1 @ i0 @ i1",
        ] {
            let source = format!("{}def main : Cube := {}", header, combo);
            let output =
                run_str(&source).unwrap_or_else(|e| panic!("{} should evaluate: {e}", combo));
            assert_eq!(output.value, base, "{} should reduce to base", combo);
        }
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
    fn instance_search_example_checks() {
        // Guards instance search: `by ring` / `by field` without an explicit
        // `with C` / `with F` resolve the bundled record from the context by
        // carrier, and the operations are extracted from the instance's type.
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join("instance_search.owl");
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .expect("spawn instance search check thread");
        handle
            .join()
            .expect("instance search check thread panicked")
            .expect("examples/instance_search.owl should typecheck");
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
