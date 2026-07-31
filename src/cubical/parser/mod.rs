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
#[cfg(test)]
mod tests;

use grammar::Parser;
use lexer::{Lexer, TokenKind};
use std::fmt;

use crate::cubical::syntax::{Datatype, Name, Term};
use crate::cubical::typechecker::errors::Pos;

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
    Def { name: Name, ty: Term, val: Term, by_wf: bool },
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
    Import { path: String },
}

#[allow(dead_code)]
pub fn parse_term(src: &str) -> Result<Term, ParseError> {
    let tokens = Lexer::new(src).lex()?;
    let mut parser = Parser::new(tokens);
    let term = parser.parse_term()?;
    parser.expect(TokenKind::Eof, "expected end of input")?;
    Ok(term)
}

#[allow(dead_code)]
pub fn parse_program(src: &str) -> Result<Vec<Decl>, ParseError> {
    let mut parser = ProgramParser::new(src)?;
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
}

impl ProgramParser {
    pub fn new(src: &str) -> Result<Self, ParseError> {
        let tokens = Lexer::new(src).lex()?;
        Ok(Self {
            parser: Parser::new(tokens),
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
        } else if self.parser.consume_ident("inductive") {
            self.parser.parse_data_decl()?
        } else if self.parser.consume_ident("record") {
            let dt = self.parser.parse_record_decl()?;
            Decl::Record(dt)
        } else if self.parser.consume_ident("import") {
            self.parser.parse_import()?
        } else {
            return Err(self.parser.error_here("expected top-level declaration"));
        };
        match &decl {
            Decl::Def { .. } => {}
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
        }
        Ok(Some(decl))
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

    let decls = parse_program(src).map_err(|e| e.to_string())?;

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
            Decl::DataWithFunc { dt, func_name, func_ty, func_val } => {
                crate::cubical::syntax::check_datatype_positivity(&dt)
                    .map_err(|e| format!("{}", e))?;
                dts.push(dt.clone());
                check_closed_dt(&dts, &func_val, &func_ty)
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
                check_closed_dt(&dts, &val, &ty)
                    .map_err(|e| format!("type error in '{}': {}", name, e))?;
                defs.push((name, ty, val));
            }
        }
    }

    Ok((dts, defs))
}
