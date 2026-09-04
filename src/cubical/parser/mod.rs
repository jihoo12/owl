//! Hand-written parser for the cubical surface language.
//!
//! The parser resolves ordinary variables and interval variables to de Bruijn
//! indices as it parses. Top-level definitions parsed earlier in a program are
//! available to later declarations as globals.
//!
//! The implementation is split into:
//! - [`lexer`]: turns source text into a token stream.
//! - [`grammar`]: the recursive-descent [`grammar::Parser`] that consumes tokens.
//! - this module: the public API ([`parse_term`], [`parse_program`],
//!   [`ProgramParser`], [`typecheck_program`]) built on top of the two.

mod grammar;
mod lexer;
mod patterns;
#[cfg(test)]
mod tests;

use grammar::Parser;
use lexer::{Lexer, TokenKind};
use std::fmt;

use crate::cubical::session::Session;
use crate::cubical::syntax::{Datatype, Name, Term};
use crate::cubical::typechecker::errors::Pos;
use crate::cubical::typechecker::infer_closed_dt;

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub line: usize,
    pub col: usize,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}:{}", self.message, self.line, self.col)
    }
}

impl std::error::Error for ParseError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    Def {
        name: Name,
        ty: Term,
        val: Term,
        by_wf: bool,
    },
    Data(Datatype),
    /// Mutually-defined inductive types: `inductive A where ... with B where ...`
    DataMutual(Vec<Datatype>),
    /// Induction-recursion: `inductive D where ... with f : T := e`
    DataWithFunc {
        dt: Datatype,
        func_name: Name,
        func_ty: Term,
        func_val: Term,
    },
    /// Record type: `record R where field x : A; field y : B`
    /// Desugars to a single-constructor inductive type.
    Record(Datatype),
    Import {
        path: String,
        /// `import "f.owl" as X` — the imported file's names are stored under
        /// the `X.` prefix (forced module), overriding the file's own `module`
        /// declarations. `None` keeps the file's own names.
        alias: Option<Name>,
        /// `import "f.owl" only [x, M.y]` — selective import. Entries are
        /// dotted paths relative to the imported file's top level; a name
        /// stays visible iff some entry equals it or prefixes its module path.
        /// `None` exposes everything.
        only: Option<Vec<Name>>,
    },
    /// `module M where ...` / `module M (A : Type) where ...` — starts a
    /// namespace; following declarations get the `M.` prefix. With
    /// parameters, every def inside is closed over them into Pi/lambda form
    /// (`M.x : Pi params. T`). The parser already updated its scope, the
    /// driver just sees this for bookkeeping.
    Module {
        name: Name,
        /// Parameter binders in declaration order; empty for plain modules.
        #[allow(dead_code)]
        params: Vec<(Name, Term)>,
    },
    /// `module N = M (e1) (e2)` — instantiation: every def of module `M`
    /// (`source`, resolved to its full dotted path by the parser) is redefined
    /// as `N.<member> := M.<member> e1 ... en`. The driver expands this into
    /// ordinary definitions, so the kernel re-checks everything.
    ModuleInst {
        name: Name,
        source: Name,
        args: Vec<Term>,
    },
    /// `end` — closes the innermost `module ... where` block.
    ModuleEnd,
    /// `postulate x : T` — declares `x` as an axiom with type `T` but no body.
    Postulate {
        name: Name,
        ty: Term,
    },
}

#[allow(dead_code)]
pub fn parse_term(src: &str, session: &mut Session) -> Result<Term, ParseError> {
    let tokens = Lexer::new(src).lex()?;
    let mut parser = Parser::new(tokens, session);
    let term = parser.parse_term()?;
    parser.expect(TokenKind::Eof, "expected end of input")?;
    Ok(term)
}

#[allow(dead_code)]
pub fn parse_program(src: &str, session: &mut Session) -> Result<Vec<Decl>, ParseError> {
    let mut parser = ProgramParser::new(src, session)?;
    let mut decls = Vec::new();
    while let Some(decl) = parser.next_decl()? {
        decls.push(decl);
    }
    Ok(decls)
}

/// Incremental top-level parser for multi-file programs.
///
/// After processing `import` declarations at runtime, call [`sync_from_env`]
/// so later declarations can resolve names from the merged environment.
pub struct ProgramParser {
    parser: Parser,
    /// When set, the file is parsed as if wrapped in `module <prefix> where`.
    /// Used by `import "f.owl" as X`; the file's own `module` declarations are
    /// then folded into the alias (ignored).
    forced_prefix: Option<String>,
}

impl ProgramParser {
    pub fn new(src: &str, session: &mut Session) -> Result<Self, ParseError> {
        Self::new_with_prefix(src, None, session)
    }

    /// Parse `src` with an optional forced module prefix (aliased imports).
    pub fn new_with_prefix(
        src: &str,
        prefix: Option<&str>,
        session: &mut Session,
    ) -> Result<Self, ParseError> {
        let tokens = Lexer::new(src).lex()?;
        let mut parser = Parser::new(tokens, session);
        if let Some(prefix) = prefix {
            parser.module_stack.push(prefix.to_string());
        }
        Ok(Self {
            parser,
            forced_prefix: prefix.map(|s| s.to_string()),
        })
    }

    pub fn sync_from_env(&mut self, env: &crate::cubical::env::Env) {
        self.parser.global_env = env.defs.iter().map(|(name, _, _)| name.clone()).collect();
        self.parser.datatypes = env.datatypes.clone();
    }

    pub fn next_decl(&mut self) -> Result<Option<Decl>, ParseError> {
        if self.parser.at(&TokenKind::Eof) {
            return Ok(None);
        }
        self.parser.decl_positions.clear();
        let decl = if self.parser.consume_ident("def") {
            self.parser.parse_def()?
        } else if self.parser.consume_ident("module") {
            self.parse_module_decl()?
        } else if self.parser.consume_ident("end") {
            if self.forced_prefix.is_some() {
                // Aliased import: drop a folded parameter scope opened by a
                // skipped `module` header, if one is open.
                if self.parser.module_params.len() > self.parser.module_stack.len() {
                    let params = self.parser.module_params.pop().unwrap_or_default();
                    for _ in &params {
                        self.parser.term_env.remove(0);
                    }
                }
                Decl::ModuleEnd
            } else if self.parser.module_stack.pop().is_some() {
                // Leave the module's parameter scope together with its name.
                let params = self.parser.module_params.pop().unwrap_or_default();
                for _ in &params {
                    self.parser.term_env.remove(0);
                }
                Decl::ModuleEnd
            } else {
                return Err(self.parser.error_here("'end' without a matching 'module'"));
            }
        } else if self.parser.consume_ident("inductive") {
            self.parser.parse_data_decl()?
        } else if self.parser.consume_ident("record") {
            let dt = self.parser.parse_record_decl()?;
            Decl::Record(dt)
        } else if self.parser.consume_ident("import") {
            self.parser.reject_inside_parameterized_module("import")?;
            self.parser.parse_import()?
        } else if self.parser.consume_ident("postulate") {
            self.parser.parse_postulate()?
        } else {
            return Err(self.parser.error_here("expected top-level declaration"));
        };
        match &decl {
            Decl::Def { .. } => {}
            Decl::Module { .. } | Decl::ModuleEnd => {}
            Decl::ModuleInst { .. } => {}
            Decl::Data(dt) => self.parser.datatypes.push(dt.clone()),
            Decl::DataMutual(dts) => {
                for dt in dts {
                    self.parser.datatypes.push(dt.clone());
                }
            }
            Decl::DataWithFunc { dt, .. } => {
                self.parser.datatypes.push(dt.clone());
            }
            Decl::Record(dt) => {
                self.parser.datatypes.push(dt.clone());
            }
            Decl::Import { .. } => {}
            Decl::Postulate { .. } => {}
        }
        Ok(Some(decl))
    }

    /// Parse `module M where` / `module M (A : Type) where`: pushes the
    /// (qualified) module name onto the parser's module stack together with
    /// its parameter list. Parameter binders always enter `term_env` because
    /// the block's definitions are parsed either way; under an aliased import
    /// only the name-stack push is skipped (the alias folds the namespace),
    /// and the matching parameter scope is dropped at the folded `end`.
    fn parse_module_decl(&mut self) -> Result<Decl, ParseError> {
        let raw = self
            .parser
            .expect_ident("expected module name after 'module'")?;
        // Instantiation: `module N = M (e1) (e2)` — args are parenthesized so
        // the declaration is self-delimiting.
        if self.parser.consume(&TokenKind::Equals) {
            if self.forced_prefix.is_some() {
                return Err(self
                    .parser
                    .error_here("module instantiation inside an aliased import is not supported"));
            }
            if self.parser.inside_parameterized_module() {
                return Err(self.parser.error_here(
                    "module instantiation inside a parameterized module is not supported",
                ));
            }
            let source_raw = self
                .parser
                .expect_ident("expected source module name after '='")?;
            let mut args = Vec::new();
            while self.parser.at(&TokenKind::LParen) {
                self.parser.expect(TokenKind::LParen, "expected '('")?;
                let arg = self.parser.parse_term()?;
                self.parser
                    .expect(TokenKind::RParen, "expected ')' after argument")?;
                args.push(arg);
            }
            let name = self.parser.qualify(&raw);
            let source = self.parser.resolve_module_source(&source_raw)?;
            return Ok(Decl::ModuleInst { name, source, args });
        }
        // Optional parameter binders: `module M (A : Type) where`.
        let params = self.parser.parse_module_binders()?;
        self.parser
            .expect_ident("expected 'where' after module name")
            .and_then(|keyword| {
                if keyword == "where" {
                    Ok(())
                } else {
                    Err(self.parser.error_here("expected 'where' after module name"))
                }
            })?;
        if !params.is_empty() && self.parser.inside_parameterized_module() {
            return Err(self
                .parser
                .error_here("nested parameterized modules are not supported"));
        }
        if self.forced_prefix.is_some() {
            // Aliased import: the namespace is folded into the alias, so no
            // name-stack entry — but the binder scope stays open until the
            // block's `end`, exactly as for plain modules.
            self.parser.module_params.push(params);
            return Ok(Decl::ModuleEnd);
        }
        // Qualify before pushing so the new segment isn't included.
        let name = self.parser.qualify(&raw);
        // The stack stores raw segments so `qualify` can join the full path
        // (`module Inner where` inside `module Outer where` → `Outer.Inner`).
        self.parser.module_stack.push(raw);
        self.parser.module_params.push(params.clone());
        Ok(Decl::Module { name, params })
    }

    /// Collect the name-position table accumulated while parsing the most
    /// recent declaration, for use by the typechecker's error reporting.
    /// Drains the parser's internal buffer.
    pub fn take_decl_positions(&mut self) -> Vec<(Name, Pos, bool)> {
        std::mem::take(&mut self.parser.decl_positions)
    }
}

/// Parse and typecheck a complete program.
///
/// Declarations are processed in order. Each `data` declaration is added to
/// the datatype environment before the next declaration is checked, so a `def`
/// can refer to any datatype declared above it — exactly the behaviour the
/// user expects.
///
/// Returns the list of successfully checked definitions (name, type, value)
/// together with the collected datatypes, or a human-readable error string.
#[allow(dead_code, clippy::type_complexity)]
pub fn typecheck_program(
    src: &str,
    session: &mut crate::cubical::session::Session,
) -> Result<
    (
        Vec<crate::cubical::syntax::Datatype>,
        Vec<(
            String,
            crate::cubical::syntax::Term,
            crate::cubical::syntax::Term,
        )>,
    ),
    String,
> {
    use crate::cubical::syntax::Datatype;
    use crate::cubical::typechecker::check_closed_dt;

    let decls = parse_program(src, session).map_err(|e| e.to_string())?;

    let mut dts: Vec<Datatype> = Vec::new();
    let mut defs: Vec<(
        String,
        crate::cubical::syntax::Term,
        crate::cubical::syntax::Term,
    )> = Vec::new();

    for decl in decls {
        match decl {
            Decl::Import { .. } => {
                return Err("import requires a file path; use cubical::run instead".to_string());
            }
            Decl::Module { .. } | Decl::ModuleEnd => {}
            Decl::ModuleInst { .. } => {}
            Decl::Data(dt) => {
                // Check positivity before making the datatype available.
                crate::cubical::syntax::check_datatype_positivity(&dt)
                    .map_err(|e| format!("{}", e))?;
                // Make the datatype available to all subsequent declarations.
                dts.push(dt);
            }
            Decl::DataMutual(new_dts) => {
                for dt in &new_dts {
                    crate::cubical::syntax::check_datatype_positivity(dt)
                        .map_err(|e| format!("{}", e))?;
                    dts.push(dt.clone());
                }
            }
            Decl::DataWithFunc {
                dt,
                func_name,
                func_ty,
                func_val,
            } => {
                crate::cubical::syntax::check_datatype_positivity(&dt)
                    .map_err(|e| format!("{}", e))?;
                dts.push(dt.clone());
                check_closed_dt(&dts, &func_val, &func_ty, session)
                    .map_err(|e| format!("type error in '{}': {}", func_name, e))?;
                defs.push((func_name, func_ty, func_val));
            }
            Decl::Record(dt) => {
                // Record desugars to a single-constructor inductive type.
                crate::cubical::syntax::check_datatype_positivity(&dt)
                    .map_err(|e| format!("{}", e))?;
                dts.push(dt.clone());
            }
            Decl::Def { name, ty, val, .. } => {
                // Check the definition body against its declared type, with
                // all datatypes declared so far in scope.
                check_closed_dt(&dts, &val, &ty, session)
                    .map_err(|e| format!("type error in '{}': {}", name, e))?;
                defs.push((name, ty, val));
            }
            Decl::Postulate { name, ty } => {
                // Postulates: check the type is well-formed (in a universe).
                let ty_ty = infer_closed_dt(&dts, &ty, session)
                    .map_err(|e| format!("type error in postulate '{}': {}", name, e))?;
                match ty_ty {
                    Term::TUniv(_) => {}
                    other => {
                        return Err(format!(
                            "postulate '{}' type must be in a universe, got {}",
                            name,
                            crate::cubical::syntax::show_term(&[], &other)
                        ));
                    }
                }
                defs.push((name, ty, Term::TVar(0)));
            }
        }
    }

    Ok((dts, defs))
}
