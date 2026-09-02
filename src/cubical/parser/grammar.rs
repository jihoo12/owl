//! Recursive-descent parser: consumes the [`Token`] stream produced by the
//! [`Lexer`](super::lexer::Lexer) and builds [`Term`]s / [`Decl`]s, resolving
//! variables to de Bruijn indices along the way.

use super::lexer::{Token, TokenKind, err};
use super::patterns::{MatchArm, Pat};
use super::{Decl, ParseError};
use crate::cubical::interval::I;
use crate::cubical::syntax::{
    CellConSig, ConSig, Datatype, ElimCase, LevelExpr, Name, PConSig, SqConSig, Tactic, Term,
    shift, subst,
};
use crate::cubical::typechecker::errors::Pos;
use std::sync::Arc;

pub(super) struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    pub(super) term_env: Vec<Name>,
    pub(super) ivar_env: Vec<Name>,
    pub(super) global_env: Vec<Name>,
    pub(super) datatypes: Vec<Datatype>,
    /// Module path segments for the current scope (outermost first).
    /// While non-empty, names defined here are qualified as `A.B.<name>` and
    /// unqualified references prefer the innermost module's qualified name.
    pub(super) module_stack: Vec<Name>,
    /// Parameter binder lists parallel to `module_stack` (entry `i` holds the
    /// parameters of `module_stack[i]`; empty for plain modules). v1 supports
    /// at most one non-empty layer: defs inside a parameterized module are
    /// closed over its parameters into Pi/lambda form.
    pub(super) module_params: Vec<Vec<(Name, Term)>>,
    /// `(name, source position, is_introduction)` for every variable name
    /// observed while parsing the current top-level declaration, in source
    /// order. The driver installs this into the typechecker's thread-local
    /// table so type errors can point back at the offending variable.
    pub(super) decl_positions: Vec<(Name, Pos, bool)>,
    /// When true, `starts_atom` treats the keyword `with` as a stop token.
    stop_at_with: bool,
    /// When true, `starts_atom` treats the keyword `in` as a stop token.
    stop_at_in: bool,
    /// When true, `starts_atom` treats the keyword `by_wf` as a stop token.
    stop_at_by_wf: bool,
    /// When true, `parse_pair` does not consume commas (used inside system entries).
    stop_at_comma: bool,
    /// When true, `starts_atom` treats the keyword `field` as a stop token
    /// (used inside record field type parsing).
    stop_at_field: bool,
    /// Raw pointer to the session, used only for `fresh_meta_id` / `set_meta_name`
    /// in `parse_atom`. Safety invariant: the caller must ensure the pointer is
    /// valid and that `&mut Session` is not used elsewhere while `parse_atom`
    /// is executing.  In practice the driver yields the `&mut Session` reference
    /// only during `next_decl` calls, so no aliasing occurs.
    session_ptr: *mut crate::cubical::session::Session,
}

impl Parser {
    pub(super) fn new(tokens: Vec<Token>, session: &mut crate::cubical::session::Session) -> Self {
        Self {
            tokens,
            pos: 0,
            term_env: Vec::new(),
            ivar_env: Vec::new(),
            global_env: Vec::new(),
            datatypes: Vec::new(),
            module_stack: Vec::new(),
            module_params: Vec::new(),
            decl_positions: Vec::new(),
            stop_at_with: false,
            stop_at_in: false,
            stop_at_by_wf: false,
            stop_at_comma: false,
            stop_at_field: false,
            session_ptr: session as *mut crate::cubical::session::Session,
        }
    }

    /// SAFETY: the caller must ensure the session pointer is valid and that
    /// the `&mut Session` used to create this parser is not accessed elsewhere
    /// while this reference is live.
    fn session(&self) -> &mut crate::cubical::session::Session {
        assert!(!self.session_ptr.is_null(), "session pointer must be set");
        unsafe { &mut *self.session_ptr }
    }

    pub(super) fn parse_import(&mut self) -> Result<Decl, ParseError> {
        let path = self.expect_string("expected string literal after 'import'")?;
        let alias = if self.consume_ident("as") {
            Some(self.expect_ident("expected module name after 'as'")?)
        } else {
            None
        };
        // `only [x, M.y]` selects which of the imported file's top-level names
        // stay visible; entries are dotted paths relative to the imported
        // file's top level (its own module prefixes, not the import alias).
        let only = if self.consume_ident("only") {
            Some(self.parse_only_list()?)
        } else {
            None
        };
        Ok(Decl::Import { path, alias, only })
    }

    /// Parse the `[name, ...]` list after `only`: comma-separated dotted
    /// names in brackets. An empty list is allowed but hides everything;
    /// a trailing comma is accepted.
    fn parse_only_list(&mut self) -> Result<Vec<Name>, ParseError> {
        self.expect(TokenKind::LBracket, "expected '[' after 'only'")?;
        let mut items: Vec<Name> = Vec::new();
        while !self.at(&TokenKind::RBracket) {
            items.push(self.expect_ident("expected name in 'only' list")?);
            while self.consume(&TokenKind::Dot) {
                let seg = self.expect_ident("expected name after '.'")?;
                let last = items.last_mut().expect("just pushed an item");
                *last = format!("{}.{}", last, seg);
            }
            if !self.consume(&TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::RBracket, "expected ']' after 'only' list")?;
        Ok(items)
    }

    pub(super) fn parse_def(&mut self) -> Result<Decl, ParseError> {
        let raw_name = self.expect_ident("expected definition name")?;
        let name = self.qualify(&raw_name);
        let (line, col) = self.token_pos();
        self.record_name_pos(&name, line, col, true);
        self.expect(
            TokenKind::Colon,
            format!("expected ':' after definition name '{}'", name),
        )?;
        self.stop_at_by_wf = true;
        let ty = self.parse_term()?;
        self.stop_at_by_wf = false;
        // Check for well-founded recursion annotation.
        let by_wf = self.consume_ident_maybe("by_wf");
        self.expect_definition_value(&name)?;
        // Allow the definition body to refer to itself (and later globals).
        self.global_env.insert(0, name.clone());
        let val = self.parse_term()?;
        // Inside a parameterized module the definition is closed over the
        // module parameters (Pi on the type, lambdas on the value).
        let (ty, val) = self.wrap_with_module_params(ty, val);
        Ok(Decl::Def {
            name,
            ty,
            val,
            by_wf,
        })
    }

    pub(super) fn parse_postulate(&mut self) -> Result<Decl, ParseError> {
        let raw_name = self.expect_ident("expected postulate name")?;
        let name = self.qualify(&raw_name);
        let (line, col) = self.token_pos();
        self.record_name_pos(&name, line, col, true);
        self.expect(
            TokenKind::Colon,
            format!("expected ':' after postulate '{}'", name),
        )?;
        let ty = self.parse_term()?;
        let (ty,) = self.wrap_with_module_params_one(ty);
        Ok(Decl::Postulate { name, ty })
    }

    pub(super) fn parse_data_decl(&mut self) -> Result<Decl, ParseError> {
        let first_dt = self.parse_data_decl_inner()?;

        // Check for `with` keyword: mutual inductive or induction-recursion.
        if self.consume_ident_maybe("with") {
            // Determine if the next token starts another `inductive` block or a function def.
            if self.peek_ident() == "inductive" {
                // Mutual inductive: `with inductive B where | ...`
                self.expect_ident("expected 'inductive'")?;
                let mut all_dts = vec![first_dt];
                // Make all previously declared datatypes visible so constructors
                // can reference each other (forward references).
                let old_dts_len = self.datatypes.len();
                for dt in &all_dts {
                    self.datatypes.push(dt.clone());
                }
                loop {
                    let dt = self.parse_data_decl_inner()?;
                    all_dts.push(dt);
                    // Extend scope with the new datatype for subsequent blocks.
                    self.datatypes.push(all_dts.last().unwrap().clone());
                    if !self.consume_ident_maybe("with") {
                        break;
                    }
                    if self.peek_ident() != "inductive" {
                        self.datatypes.truncate(old_dts_len);
                        return Err(
                            self.error_here("expected 'inductive' after 'with' in mutual block")
                        );
                    }
                    self.expect_ident("expected 'inductive'")?;
                }
                self.datatypes.truncate(old_dts_len);
                return Ok(Decl::DataMutual(all_dts));
            } else {
                // Induction-recursion: `with f : T := e`
                let raw_func = self.expect_ident("expected function name after 'with'")?;
                let func_name = self.qualify(&raw_func);
                self.expect(
                    TokenKind::Colon,
                    format!("expected ':' after '{}'", func_name),
                )?;
                // Parse the function type with the datatype visible.
                let old_dts_len = self.datatypes.len();
                self.datatypes.push(first_dt.clone());
                let func_ty = self.parse_term()?;
                self.datatypes.truncate(old_dts_len);
                self.expect(
                    TokenKind::ColonEquals,
                    format!("expected ':=' after type of '{}'", func_name),
                )?;
                // Parse the function value with the datatype visible and the function name in scope.
                self.global_env.insert(0, func_name.clone());
                let old_dts_len = self.datatypes.len();
                self.datatypes.push(first_dt.clone());
                let func_val = self.parse_term()?;
                self.datatypes.truncate(old_dts_len);
                return Ok(Decl::DataWithFunc {
                    dt: first_dt,
                    func_name,
                    func_ty,
                    func_val,
                });
            }
        }
        Ok(Decl::Data(first_dt))
    }

    /// Parse a single inductive datatype block. Returns the `Datatype` directly.
    /// Used by both `parse_data_decl` and the mutual-inductive `with` handler.
    pub(super) fn parse_data_decl_inner(&mut self) -> Result<Datatype, ParseError> {
        let raw_name = self.expect_ident("expected datatype name")?;
        let name = self.qualify(&raw_name);

        // Parse optional parameter binders: `inductive Trunc (A : Type) where`
        let mut params: Vec<(Name, Term)> = Vec::new();
        while self.at(&TokenKind::LParen) && self.peek_ahead_is_binder() {
            self.expect(TokenKind::LParen, "expected '(' for parameter binder")?;
            let param_name = self.expect_ident("expected parameter name")?;
            self.expect(
                TokenKind::Colon,
                format!("expected ':' after parameter name '{}'", param_name),
            )?;
            let param_ty = self.parse_term()?;
            self.expect(TokenKind::RParen, "expected ')' after parameter type")?;
            self.term_env.insert(0, param_name.clone());
            params.push((param_name, param_ty));
        }

        // Optional universe annotation: `data D : U_n = ...`
        let mut uni_level: Option<LevelExpr> = None;
        if self.consume(&TokenKind::Colon) {
            // Try level expression first (for `data D : U (lsuc l) = ...`)
            // Fall back to identifier-based universe (for `data D : U0 = ...`)
            let save = self.pos;
            match self.parse_level_expr() {
                Ok(lvl) => {
                    uni_level = Some(lvl);
                }
                Err(_) => {
                    self.pos = save;
                    let uni_name = self.expect_ident("expected universe level after ':'")?;
                    uni_level = Some(LevelExpr::LConst(parse_universe(&uni_name).ok_or_else(
                        || {
                            self.error_here(format!(
                                "expected universe level (e.g. U0, U1) after ':', got '{}'",
                                uni_name
                            ))
                        },
                    )?));
                }
            }
        }

        self.expect_ident("expected 'where' after inductive datatype name")
            .and_then(|keyword| {
                if keyword == "where" {
                    Ok(())
                } else {
                    Err(self.error_here("expected 'where' after inductive datatype name"))
                }
            })?;
        let mut cons = Vec::new();
        let mut pcons = Vec::new();
        let mut sqcons = Vec::new();
        let mut cellcons = Vec::new();
        let mut local_dt = Datatype {
            name: name.clone(),
            params: params.clone(),
            cons: Vec::new(),
            pcons: Vec::new(),
            sqcons: Vec::new(),
            cellcons: Vec::new(),
            universe_level: None,
            field_names: None,
        };
        while self.consume(&TokenKind::Pipe) {
            let con_name = self.expect_ident("expected constructor name after '|'")?;
            self.expect(
                TokenKind::Colon,
                format!("expected ':' after constructor name '{}'", con_name),
            )?;
            self.stop_at_with = true;
            let (arg_tys, result) = self.parse_constructor_type(&name, &local_dt)?;
            self.stop_at_with = false;
            // For parameterized types, the result is TData(name, param_args).
            // For non-parameterized types, the result is TData(name, []).
            match &result {
                Term::TData(n, result_args) if n == &name => {
                    // OK — return type matches the declared datatype
                    let _ = result_args;
                }
                _ => {
                    return Err(self.error_here(format!(
                        "constructor '{}' must return datatype '{}'",
                        con_name, name
                    )));
                }
            }
            if self.consume(&TokenKind::LBracket) {
                // Check for double bracket `[[` for square constructors
                if self.consume(&TokenKind::LBracket) {
                    // Count additional brackets for n-dimensional cells (dim >= 3).
                    let mut extra_brackets = 0;
                    while self.consume(&TokenKind::LBracket) {
                        extra_brackets += 1;
                    }
                    let dim = 2 + extra_brackets;
                    if dim == 2 {
                        // Square constructor: `sqcon : A [[ face_i0, face_i1, face_j0, face_j1 ]]`
                        let num_args = arg_tys.len();
                        for k in 0..num_args {
                            self.term_env.insert(0, format!("{}_{}", con_name, k));
                        }
                        let face_i0 = self.parse_face_with_extra_datatype(&local_dt)?;
                        self.expect(
                            TokenKind::Comma,
                            "expected ',' between square-constructor faces",
                        )?;
                        let face_i1 = self.parse_face_with_extra_datatype(&local_dt)?;
                        self.expect(
                            TokenKind::Comma,
                            "expected ',' between square-constructor faces",
                        )?;
                        let face_j0 = self.parse_face_with_extra_datatype(&local_dt)?;
                        self.expect(
                            TokenKind::Comma,
                            "expected ',' between square-constructor faces",
                        )?;
                        let face_j1 = self.parse_face_with_extra_datatype(&local_dt)?;
                        self.expect(
                            TokenKind::RBracket,
                            "expected ']' after square-constructor faces",
                        )?;
                        self.expect(
                            TokenKind::RBracket,
                            "expected ']]' after square-constructor faces",
                        )?;
                        for _ in 0..num_args {
                            self.term_env.remove(0);
                        }
                        let sig = SqConSig {
                            name: con_name,
                            arg_tys,
                            face_i0,
                            face_i1,
                            face_j0,
                            face_j1,
                        };
                        local_dt.sqcons.push(sig.clone());
                        sqcons.push(sig);
                    } else {
                        // N-dimensional cell constructor: `cellcon : A [[[ ... dim faces ... ]]]`
                        let num_args = arg_tys.len();
                        for k in 0..num_args {
                            self.term_env.insert(0, format!("{}_{}", con_name, k));
                        }
                        let mut faces = Vec::new();
                        for fi in 0..(2 * dim) {
                            if fi > 0 {
                                self.expect(
                                    TokenKind::Comma,
                                    "expected ',' between cell-constructor faces",
                                )?;
                            }
                            faces.push(self.parse_face_with_extra_datatype(&local_dt)?);
                        }
                        // Close all brackets: dim closing brackets.
                        for bi in 0..dim {
                            self.expect(
                                TokenKind::RBracket,
                                &format!(
                                    "expected ']' to close cell-constructor brackets ({} of {})",
                                    bi + 1,
                                    dim
                                ),
                            )?;
                        }
                        for _ in 0..num_args {
                            self.term_env.remove(0);
                        }
                        let sig = CellConSig {
                            name: con_name,
                            arg_tys,
                            faces,
                        };
                        local_dt.cellcons.push(sig.clone());
                        cellcons.push(sig);
                    }
                } else {
                    // Path constructor: `pcon : A [ face0, face1 ]`
                    let num_args = arg_tys.len();
                    for k in 0..num_args {
                        self.term_env.insert(0, format!("{}_{}", con_name, k));
                    }
                    let face0 = self.parse_face_with_extra_datatype(&local_dt)?;
                    self.expect(
                        TokenKind::Comma,
                        "expected ',' between path-constructor faces",
                    )?;
                    let face1 = self.parse_face_with_extra_datatype(&local_dt)?;
                    self.expect(
                        TokenKind::RBracket,
                        "expected ']' after path-constructor faces",
                    )?;
                    for _ in 0..num_args {
                        self.term_env.remove(0);
                    }
                    let sig = PConSig {
                        name: con_name,
                        arg_tys,
                        face0,
                        face1,
                    };
                    local_dt.pcons.push(sig.clone());
                    pcons.push(sig);
                }
            } else {
                let sig = ConSig {
                    name: con_name,
                    arg_tys,
                };
                local_dt.cons.push(sig.clone());
                cons.push(sig);
            }
        }
        // A datatype with no constructors at all is legal: it is the empty
        // type (e.g. `Empty`), eliminated only by an empty `match`.
        // Remove parameter binders from term_env
        for _ in &params {
            self.term_env.remove(0);
        }
        Ok(Datatype {
            name,
            params,
            cons,
            pcons,
            sqcons,
            cellcons,
            universe_level: uni_level,
            field_names: None,
        })
    }

    /// Parse a record declaration:
    ///   record R where
    ///     field x : A
    ///     field y : B
    ///
    /// Desugars to a single-constructor inductive type plus projection definitions.
    pub(super) fn parse_record_decl(&mut self) -> Result<Datatype, ParseError> {
        let raw_name = self.expect_ident("expected record type name")?;
        let name = self.qualify(&raw_name);

        // Parse optional parameter binders: `record Pair (A : Type) where`
        let mut params: Vec<(Name, Term)> = Vec::new();
        while self.at(&TokenKind::LParen) && self.peek_ahead_is_binder() {
            self.expect(TokenKind::LParen, "expected '(' for parameter binder")?;
            let param_name = self.expect_ident("expected parameter name")?;
            self.expect(
                TokenKind::Colon,
                format!("expected ':' after parameter name '{}'", param_name),
            )?;
            let param_ty = self.parse_term()?;
            self.expect(TokenKind::RParen, "expected ')' after parameter type")?;
            self.term_env.insert(0, param_name.clone());
            params.push((param_name, param_ty));
        }

        self.expect_ident("expected 'where' after record name")
            .and_then(|keyword| {
                if keyword == "where" {
                    Ok(())
                } else {
                    Err(self.error_here("expected 'where' after record name"))
                }
            })?;

        // Parse field declarations
        let mut field_names = Vec::new();
        let mut field_tys = Vec::new();
        let mut local_dt = Datatype {
            name: name.clone(),
            params: params.clone(),
            cons: Vec::new(),
            pcons: Vec::new(),
            sqcons: Vec::new(),
            cellcons: Vec::new(),
            universe_level: None,
            field_names: None,
        };

        while self.consume_ident("field") {
            let field_name = self.expect_ident("expected field name after 'field'")?;
            self.expect(
                TokenKind::Colon,
                format!("expected ':' after field name '{}'", field_name),
            )?;
            self.stop_at_with = true;
            self.stop_at_field = true;
            let field_ty = self.parse_term()?;
            self.stop_at_with = false;
            self.stop_at_field = false;
            field_names.push(field_name);
            field_tys.push(field_ty);
        }

        if field_names.is_empty() {
            return Err(self.error_here("record must have at least one field"));
        }

        // Build the single constructor: `mkR : (field1 : A) -> (field2 : B) -> ... -> R`
        let con_name = format!("mk{}", name);
        let con_sig = ConSig {
            name: con_name,
            arg_tys: field_tys,
        };
        local_dt.cons.push(con_sig);
        local_dt.field_names = Some(field_names);

        // Remove parameter binders from term_env
        for _ in &params {
            self.term_env.remove(0);
        }

        Ok(local_dt)
    }

    fn parse_constructor_type(
        &mut self,
        dt_name: &str,
        local_dt: &Datatype,
    ) -> Result<(Vec<Term>, Term), ParseError> {
        let old_dts_len = self.datatypes.len();
        self.datatypes.push(local_dt.clone());
        let ty = self.parse_term()?;
        self.datatypes.truncate(old_dts_len);
        let mut args = Vec::new();
        let mut cur = ty;
        let mut depth: i32 = 0;
        loop {
            match cur {
                Term::TPi(_, a, b, _) => {
                    let shifted_a = shift(-depth, 0, &a);
                    args.push(shifted_a);
                    depth += 1;
                    cur = b.as_ref().clone();
                }
                Term::TData(ref n, _) if n == dt_name => {
                    let result = shift(-depth, 0, &cur);
                    return Ok((args, result));
                }
                other => {
                    let result = shift(-depth, 0, &other);
                    return Ok((args, result));
                }
            }
        }
    }

    fn parse_face_with_extra_datatype(&mut self, dt: &Datatype) -> Result<Term, ParseError> {
        let old_len = self.datatypes.len();
        self.datatypes.push(dt.clone());
        let term = self.parse_arrow();
        self.datatypes.truncate(old_len);
        term
    }

    pub(super) fn parse_term(&mut self) -> Result<Term, ParseError> {
        self.parse_lambda()
    }

    fn parse_lambda(&mut self) -> Result<Term, ParseError> {
        if self.consume_ident("let") {
            return self.parse_let();
        }
        if self.consume_ident("by") {
            return self.parse_tactic_block();
        }
        if self.consume_ident("fun") {
            let binders = self.parse_lambda_binders("expected binder after 'fun'")?;
            self.expect(
                TokenKind::FatArrow,
                "expected '=>' after function binder list",
            )?;
            for binder in &binders {
                self.term_env.insert(0, binder.clone());
            }
            let body = self.parse_term()?;
            for _ in &binders {
                self.term_env.remove(0);
            }
            let mut term = body;
            for binder in binders.into_iter().rev() {
                term = Term::TAbs(binder, Arc::new(term));
            }
            return Ok(term);
        }
        if self.consume(&TokenKind::LAngle) {
            let binder = self.expect_ident("expected interval binder after '<'")?;
            self.expect(TokenKind::RAngle, "expected '>' after interval binder")?;
            self.ivar_env.insert(0, binder.clone());
            self.term_env.insert(0, "".to_string());
            let body = self.parse_term()?;
            self.term_env.remove(0);
            self.ivar_env.remove(0);
            return Ok(Term::PLam(binder, Arc::new(body)));
        }
        // Implicit binder: {x : A}
        if self.consume(&TokenKind::LBrace) {
            let binder = self.expect_ident("expected binder name in implicit binder")?;
            self.expect(
                TokenKind::Colon,
                "expected ':' after binder in implicit binder",
            )?;
            let ty = self.parse_term()?;
            self.expect(TokenKind::RBrace, "expected '}' to close implicit binder")?;
            self.expect_binder_separator("implicit Pi")?;
            self.term_env.insert(0, binder.clone());
            let body = self.parse_term()?;
            self.term_env.remove(0);
            return Ok(Term::TPi(binder, Arc::new(ty), Arc::new(body), true));
        }
        if self.consume_ident("∀") || self.consume_ident("forall") {
            let (binder, ty) = self.parse_parenthesized_binder("Pi")?;
            self.expect_binder_separator("Pi")?;
            self.term_env.insert(0, binder.clone());
            let body = self.parse_term()?;
            self.term_env.remove(0);
            return Ok(Term::TPi(binder, Arc::new(ty), Arc::new(body), false));
        }
        if self.consume_ident("Σ") {
            let (binder, ty) = self.parse_parenthesized_binder("Sigma")?;
            self.expect_binder_separator("Sigma")?;
            self.term_env.insert(0, binder.clone());
            let body = self.parse_term()?;
            self.term_env.remove(0);
            return Ok(Term::TSigma(binder, Arc::new(ty), Arc::new(body)));
        }
        self.parse_pair()
    }

    fn parse_let(&mut self) -> Result<Term, ParseError> {
        let binder = self.expect_ident("expected binder after 'let'")?;

        if self.consume(&TokenKind::Colon) {
            let _ty = self.parse_term()?;
        }
        self.expect(TokenKind::ColonEquals, "expected ':=' after let binder")?;

        let value = {
            self.stop_at_in = true;
            let v = self.parse_term()?;
            self.stop_at_in = false;
            v
        };
        self.expect_ident("in")?;

        self.term_env.insert(0, binder.clone());
        let body = self.parse_term()?;
        self.term_env.remove(0);

        Ok(Term::TApp(
            Arc::new(Term::TAbs(binder, Arc::new(body))),
            Arc::new(value),
        ))
    }

    fn parse_tactic_block(&mut self) -> Result<Term, ParseError> {
        let mut tactics = Vec::new();
        let mut intro_count = 0;
        tactics.push(self.parse_tactic(&mut intro_count)?);
        while self.consume(&TokenKind::Semicolon) {
            tactics.push(self.parse_tactic(&mut intro_count)?);
        }
        for _ in 0..intro_count {
            self.term_env.remove(0);
        }
        Ok(Term::TBy(tactics))
    }

    fn parse_tactic(&mut self, intro_count: &mut usize) -> Result<Tactic, ParseError> {
        if self.consume_ident("exact") {
            let term = self.parse_term()?;
            return Ok(Tactic::Exact(term));
        }
        if self.consume_ident("intro") {
            let mut names = Vec::new();
            loop {
                match self.peek().kind {
                    TokenKind::Ident(ref name) if !is_tactic_keyword(name) => {
                        let name = self.expect_ident("expected name after 'intro'")?;
                        self.term_env.insert(0, name.clone());
                        *intro_count += 1;
                        names.push(name);
                    }
                    _ => break,
                }
            }
            return Ok(Tactic::Intro(names));
        }
        if self.consume_ident("apply") {
            let term = self.parse_term()?;
            return Ok(Tactic::Apply(term));
        }
        if self.consume_ident("assumption") {
            return Ok(Tactic::Assumption);
        }
        if self.consume_ident("reflexivity") {
            return Ok(Tactic::Reflexivity);
        }
        if self.consume_ident("symmetry") {
            return Ok(Tactic::Symmetry);
        }
        if self.consume_ident("split") {
            return Ok(Tactic::Split);
        }
        if self.consume_ident("constructor") {
            // Optional: `constructor con_name` to pick a specific constructor
            let name = match self.peek().kind.clone() {
                TokenKind::Ident(ref n) if !is_tactic_keyword(n) => {
                    self.pos += 1;
                    Some(n.clone())
                }
                _ => None,
            };
            return Ok(Tactic::Constructor(name));
        }
        if self.consume_ident("destruct") {
            let name = self.expect_ident("expected hypothesis name after 'destruct'")?;
            return Ok(Tactic::Destruct(name));
        }
        if self.consume_ident("transitivity") {
            return Ok(Tactic::Transitivity);
        }
        if self.consume_ident("compute") {
            return Ok(Tactic::Compute);
        }
        if self.consume_ident("trivial") {
            return Ok(Tactic::Trivial);
        }
        if self.consume_ident("omega") {
            return Ok(Tactic::Omega);
        }
        if self.consume_ident("ring") {
            if self.consume_ident("with") {
                let term = self.parse_term()?;
                return Ok(Tactic::Ring(Some(term)));
            }
            return Ok(Tactic::Ring(None));
        }
        if self.consume_ident("field") {
            if self.consume_ident("with") {
                let term = self.parse_term()?;
                return Ok(Tactic::Field(Some(term)));
            }
            return Ok(Tactic::Field(None));
        }
        if self.consume_ident("group") {
            if self.consume_ident("with") {
                let term = self.parse_term()?;
                return Ok(Tactic::Group(Some(term)));
            }
            return Ok(Tactic::Group(None));
        }
        if self.consume_ident("eq") {
            return Ok(Tactic::Eq);
        }
        Err(self.error_here("expected tactic: 'exact', 'intro', 'apply', 'assumption', 'reflexivity', 'symmetry', 'split', 'constructor', 'destruct', 'transitivity', 'compute', 'trivial', 'omega', 'ring', 'field', 'group', 'ring with <term>', 'field with <term>', or 'group with <term>'"))
    }

    fn parse_pair(&mut self) -> Result<Term, ParseError> {
        let left = self.parse_arrow()?;
        if !self.stop_at_comma && self.consume(&TokenKind::Comma) {
            let right = self.parse_term()?;
            Ok(Term::TPair(Arc::new(left), Arc::new(right)))
        } else {
            Ok(left)
        }
    }

    /// Parse `->` (non-dependent Pi) at the lowest precedence.
    /// `A * B -> C * D` parses as `(A * B) -> (C * D)`.
    fn parse_arrow(&mut self) -> Result<Term, ParseError> {
        let left = self.parse_sigma()?;
        if self.consume(&TokenKind::Arrow) {
            self.term_env.insert(0, "_".to_string());
            let right = self.parse_arrow_codomain()?;
            self.term_env.remove(0);
            Ok(Term::TPi(
                "_".to_string(),
                Arc::new(left),
                Arc::new(right),
                false,
            ))
        } else {
            Ok(left)
        }
    }

    /// Parse the codomain of a `->`.  A `forall`/`∀` binder may directly
    /// follow a non-dependent arrow — it binds looser than `->`, so
    /// `A -> forall (x : B), C -> D` parses as `A -> forall (x : B), (C -> D)`.
    fn parse_arrow_codomain(&mut self) -> Result<Term, ParseError> {
        // Implicit binder: {x : A}
        if self.consume(&TokenKind::LBrace) {
            let binder = self.expect_ident("expected binder name in implicit binder")?;
            self.expect(
                TokenKind::Colon,
                "expected ':' after binder in implicit binder",
            )?;
            let ty = self.parse_term()?;
            self.expect(TokenKind::RBrace, "expected '}' to close implicit binder")?;
            self.expect_binder_separator("implicit Pi")?;
            self.term_env.insert(0, binder.clone());
            let body = self.parse_term()?;
            self.term_env.remove(0);
            return Ok(Term::TPi(binder, Arc::new(ty), Arc::new(body), true));
        }
        if self.consume_ident("∀") || self.consume_ident("forall") {
            let (binder, ty) = self.parse_parenthesized_binder("Pi")?;
            self.expect_binder_separator("Pi")?;
            self.term_env.insert(0, binder.clone());
            let body = self.parse_term()?;
            self.term_env.remove(0);
            Ok(Term::TPi(binder, Arc::new(ty), Arc::new(body), false))
        } else {
            self.parse_arrow()
        }
    }

    /// Parse `*` (non-dependent Sigma/product) at a higher precedence than `->`.
    /// `A * B * C` parses as `A * (B * C)` (right-associative).
    fn parse_sigma(&mut self) -> Result<Term, ParseError> {
        let left = self.parse_join()?;
        if self.consume(&TokenKind::Star) {
            self.term_env.insert(0, "_".to_string());
            let right = self.parse_sigma()?;
            self.term_env.remove(0);
            Ok(Term::TSigma(
                "_".to_string(),
                Arc::new(left),
                Arc::new(right),
            ))
        } else {
            Ok(left)
        }
    }

    fn parse_join(&mut self) -> Result<Term, ParseError> {
        let mut term = self.parse_meet()?;
        while self.consume(&TokenKind::OrSym) {
            let rhs = self.parse_meet()?;
            term = interval_binary(term, rhs, |a, b| I::Join(Arc::new(a), Arc::new(b)), self)?;
        }
        Ok(term)
    }

    fn parse_meet(&mut self) -> Result<Term, ParseError> {
        let mut term = self.parse_tilde()?;
        while self.consume(&TokenKind::AndSym) {
            let rhs = self.parse_tilde()?;
            term = interval_binary(term, rhs, |a, b| I::Meet(Arc::new(a), Arc::new(b)), self)?;
        }
        Ok(term)
    }

    fn parse_tilde(&mut self) -> Result<Term, ParseError> {
        if self.consume(&TokenKind::Tilde) {
            let term = self.parse_tilde()?;
            let i = expect_interval(term, self)?;
            Ok(Term::TInterval(I::Neg(Arc::new(i))))
        } else {
            self.parse_papp()
        }
    }

    fn parse_interval_arg(&mut self) -> Result<Term, ParseError> {
        if self.consume(&TokenKind::Tilde) {
            let inner = self.parse_prefix_or_atom()?;
            let i = expect_interval(inner, self)?;
            Ok(Term::TInterval(I::Neg(Arc::new(i))))
        } else {
            self.parse_prefix_or_atom()
        }
    }

    fn parse_papp(&mut self) -> Result<Term, ParseError> {
        let mut term = self.parse_app()?;
        if let Term::TCon(ref dt, ref con, _) = term {
            if let Some(dim) = self.is_cell_constructor(dt, con) {
                if dim >= 2 && self.peek().kind == TokenKind::At {
                    // Cell constructor: parse `dim` interval args
                    let mut interval_args = Vec::new();
                    for _ in 0..dim {
                        self.expect(
                            TokenKind::At,
                            "expected '@' for cell constructor interval arg",
                        )?;
                        interval_args.push(self.parse_interval_arg()?);
                    }
                    if let Term::TCon(dt, con, args) = term {
                        term = Term::TCellCon(dt, con, args, interval_args);
                    }
                }
            } else if self.is_square_constructor(dt, con) && self.peek().kind == TokenKind::At {
                // Square constructor: parse both interval args without going through
                // parse_papp recursion (which would consume the second @)
                self.consume(&TokenKind::At);
                let rhs = self.parse_interval_arg()?;
                self.expect(
                    TokenKind::At,
                    "expected '@' for square constructor second interval",
                )?;
                let rhs2 = self.parse_interval_arg()?;
                if let Term::TCon(dt, con, args) = term {
                    term = Term::TSqCon(dt, con, args, Arc::new(rhs), Arc::new(rhs2));
                }
            }
        }
        while self.consume(&TokenKind::At) {
            let rhs = self.parse_tilde()?;
            if let Term::TCon(dt, con, args) = term {
                if self.is_path_constructor(&dt, &con) {
                    term = Term::TPCon(dt, con, args, Arc::new(rhs));
                } else {
                    term = Term::PApp(Arc::new(Term::TCon(dt, con, args)), Arc::new(rhs));
                }
            } else {
                term = Term::PApp(Arc::new(term), Arc::new(rhs));
            }
        }
        Ok(term)
    }

    fn parse_app(&mut self) -> Result<Term, ParseError> {
        let first = self.parse_prefix_or_atom()?;
        let mut args = Vec::new();
        while self.starts_atom() {
            args.push(self.parse_prefix_or_atom()?);
        }
        if let Term::TCon(dt, con, mut con_args) = first {
            con_args.extend(args);
            return Ok(Term::TCon(dt, con, con_args));
        }
        if let Term::TData(name, mut params) = first {
            params.extend(args);
            return Ok(Term::TData(name, params));
        }
        let mut term = first;
        for arg in args {
            term = Term::TApp(Arc::new(term), Arc::new(arg));
        }
        Ok(term)
    }

    fn parse_prefix_or_atom(&mut self) -> Result<Term, ParseError> {
        if self.consume_ident("fst") {
            return Ok(Term::TFst(Arc::new(self.parse_prefix_or_atom()?)));
        }
        if self.consume_ident("snd") {
            return Ok(Term::TSnd(Arc::new(self.parse_prefix_or_atom()?)));
        }
        if self.consume_ident("ua") {
            return Ok(Term::TUa(Arc::new(self.parse_prefix_or_atom()?)));
        }
        if self.consume_ident("transport") || self.consume_ident("coe") {
            let p = self.parse_prefix_or_atom()?;
            let x = self.parse_prefix_or_atom()?;
            return Ok(Term::TTransport(Arc::new(p), Arc::new(x)));
        }
        if self.consume_ident("transp") {
            let a = self.parse_prefix_or_atom()?;
            let r = self.parse_prefix_or_atom()?;
            let x = self.parse_prefix_or_atom()?;
            return Ok(Term::TTransp(Arc::new(a), Arc::new(r), Arc::new(x)));
        }
        if self.consume_ident("equivFwd") {
            let e = self.parse_prefix_or_atom()?;
            let x = self.parse_prefix_or_atom()?;
            return Ok(Term::TEquivFwd(Arc::new(e), Arc::new(x)));
        }
        if self.consume_ident("Force") {
            return Ok(Term::TForce(Arc::new(self.parse_prefix_or_atom()?)));
        }
        if self.consume_ident("Next") {
            return Ok(Term::TNext(Arc::new(self.parse_prefix_or_atom()?)));
        }
        if self.consume_ident("lift") {
            let a = self.parse_prefix_or_atom()?;
            let lvl = self.parse_level_expr()?;
            return Ok(Term::TLift(Arc::new(a), lvl));
        }
        if self.consume_ident("lower") {
            return Ok(Term::TLower(Arc::new(self.parse_prefix_or_atom()?)));
        }
        if self.consume_ident("Refl") {
            let x = self.parse_prefix_or_atom()?;
            return Ok(Term::TRefl(Arc::new(x)));
        }
        if self.consume_ident("J") {
            let motive = self.parse_prefix_or_atom()?;
            let base = self.parse_prefix_or_atom()?;
            let p = self.parse_prefix_or_atom()?;
            return Ok(Term::TJ(Arc::new(motive), Arc::new(base), Arc::new(p)));
        }
        // Module-qualified reference: `M.name`, `M.Nat`, `M.Nat.zero`.  Only
        // fires when the leading segment is a module prefix; otherwise the
        // name falls through to the plain atom / record-projection path.
        if let TokenKind::Ident(first) = &self.peek().kind
            && matches!(
                self.tokens.get(self.pos + 1).map(|t| &t.kind),
                Some(TokenKind::Dot)
            )
            && self.is_module_prefix(first)
        {
            let mut segments = vec![self.expect_ident("expected module name")?];
            while self.consume(&TokenKind::Dot) {
                segments.push(self.expect_ident("expected name after '.'")?);
            }
            return self.resolve_dotted(&segments);
        }
        // Record field projection: `record.field` — parse as TProj
        // This is handled after prefix operators so that `Force x.y` etc. work.
        let mut term = self.parse_atom()?;
        // Check for `.field` suffix (projection) — loop for chained projections
        while self.consume(&TokenKind::Dot) {
            if let TokenKind::Ident(field) = self.peek().kind.clone() {
                // If the term is `TData("Foo", [])` and "Foo" has a constructor
                // named `field`, treat this as a constructor reference: `Foo.field`.
                // Only use projection when the term is NOT a datatype name.
                if let Term::TData(ref dt_name, _) = term {
                    if self
                        .datatypes
                        .iter()
                        .any(|dt| dt.name == *dt_name && dt.cons.iter().any(|c| c.name == field))
                    {
                        self.pos += 1;
                        return Ok(Term::TCon(dt_name.clone(), field, Vec::new()));
                    }
                }
                self.pos += 1;
                term = Term::TProj(field, Arc::new(term));
            } else {
                break;
            }
        }
        // Record update syntax: `expr { field = value, ... }`
        if self.consume(&TokenKind::LBrace) {
            let mut updates = Vec::new();
            if !self.at(&TokenKind::RBrace) {
                let saved_stop_at_comma = self.stop_at_comma;
                self.stop_at_comma = true;
                loop {
                    let field = self.expect_ident("expected field name in record update")?;
                    self.expect(
                        TokenKind::Equals,
                        format!("expected '=' after field '{}' in record update", field),
                    )?;
                    let value = self.parse_term()?;
                    updates.push((field, value));
                    if !self.consume(&TokenKind::Comma) {
                        break;
                    }
                }
                self.stop_at_comma = saved_stop_at_comma;
            }
            self.expect(TokenKind::RBrace, "expected '}' after record update fields")?;
            term = Term::TRecordUpdate(Arc::new(term), updates);
        }
        Ok(term)
    }

    fn parse_atom(&mut self) -> Result<Term, ParseError> {
        if self.consume_ident("Delay") {
            let a = self.parse_prefix_or_atom()?;
            return Ok(Term::TDelay(Arc::new(a)));
        }
        if self.consume_ident("Path") {
            let a = self.parse_prefix_or_atom()?;
            let u = self.parse_prefix_or_atom()?;
            let v = self.parse_prefix_or_atom()?;
            return Ok(Term::TPath(Arc::new(a), Arc::new(u), Arc::new(v)));
        }
        if self.consume_ident("PathP") {
            let a = self.parse_prefix_or_atom()?;
            let u = self.parse_prefix_or_atom()?;
            let v = self.parse_prefix_or_atom()?;
            return Ok(Term::TPath(Arc::new(a), Arc::new(u), Arc::new(v)));
        }
        if self.consume_ident("Id") {
            let a = self.parse_prefix_or_atom()?;
            let x = self.parse_prefix_or_atom()?;
            let y = self.parse_prefix_or_atom()?;
            return Ok(Term::TId(Arc::new(a), Arc::new(x), Arc::new(y)));
        }
        if self.consume_ident("isProp") {
            let a = self.parse_prefix_or_atom()?;
            // isProp A = forall (_ : A), forall (_ : A), Path A x y
            //
            // de Bruijn layout (outermost first):
            //   1: x : A        (context depth 2)
            //   0: y : A        (context depth 1, type seen from depth 0)
            //
            // Type of y is checked at depth 1: A shifted by 1 (A[+1])
            // Body Path A x y is checked at depth 2: A shifted by 2 (A[+2])
            //   x = TVar(1), y = TVar(0)
            return Ok(self.build_isprop(a));
        }
        if self.consume_ident("isSet") {
            let a = self.parse_prefix_or_atom()?;
            // isSet A = forall (_ : A), forall (_ : A), forall (_ : Path A x y), forall (_ : Path A x y), Path (Path A x y) p q
            //
            // de Bruijn layout (outermost first):
            //   3: x : A                     (type checked at depth 0: A[+0] = A)
            //   2: y : A                     (type checked at depth 1: A[+1])
            //   1: p : Path A x y            (type checked at depth 2: A[+2], x=TVar(1), y=TVar(0))
            //   0: q : Path A x y            (type checked at depth 3: A[+3], x=TVar(2), y=TVar(1))
            //
            // Body Path (Path A x y) p q is checked at depth 4:
            //   A[+4], x=TVar(3), y=TVar(2), p=TVar(1), q=TVar(0)
            return Ok(self.build_isset(a));
        }
        if self.consume_ident("isGroupoid") {
            let a = self.parse_prefix_or_atom()?;
            // isGroupoid A = forall (_ : A), forall (_ : A), forall (_ : Path A x y), forall (_ : Path A x y),
            //                forall (_ : Path (Path A x y) p q), forall (_ : Path (Path A x y) p q),
            //                Path (Path (Path A x y) p q) r s
            //
            // de Bruijn layout (outermost first):
            //   5: x : A
            //   4: y : A
            //   3: p : Path A x y
            //   2: q : Path A x y
            //   1: r : Path (Path A x y) p q
            //   0: s : Path (Path A x y) p q
            return Ok(self.build_isgroupoid(a));
        }
        if self.consume_ident("isNType") {
            // Parse the truncation level (must be a non-negative integer literal)
            let level = match self.peek().kind {
                TokenKind::Int(n) if n >= 0 => {
                    self.pos += 1;
                    n as u32
                }
                _ => return Err(self.error_here("expected non-negative integer after isNType")),
            };
            let a = self.parse_prefix_or_atom()?;
            return Ok(self.build_isntype(level, a));
        }
        if self.consume_ident("hcomp") {
            let a = self.parse_prefix_or_atom()?;
            let system = if self.at(&TokenKind::LBracket) {
                self.parse_system()?
            } else {
                let phi = self.parse_prefix_or_atom()?;
                let u = self.parse_prefix_or_atom()?;
                vec![(phi, u)]
            };
            let u0 = self.parse_prefix_or_atom()?;
            return Ok(Term::THComp(Arc::new(a), system, Arc::new(u0)));
        }
        if self.consume_ident("comp") {
            let a = self.parse_prefix_or_atom()?;
            let system = if self.at(&TokenKind::LBracket) {
                self.parse_system()?
            } else {
                let phi = self.parse_prefix_or_atom()?;
                let u = self.parse_prefix_or_atom()?;
                vec![(phi, u)]
            };
            let u0 = self.parse_prefix_or_atom()?;
            return Ok(Term::TComp(Arc::new(a), system, Arc::new(u0)));
        }
        if self.consume_ident("fill") {
            let a = self.parse_prefix_or_atom()?;
            let system = if self.at(&TokenKind::LBracket) {
                self.parse_system()?
            } else {
                let phi = self.parse_prefix_or_atom()?;
                let u = self.parse_prefix_or_atom()?;
                vec![(phi, u)]
            };
            let u0 = self.parse_prefix_or_atom()?;
            return Ok(Term::TFill(Arc::new(a), system, Arc::new(u0)));
        }
        if self.consume_ident("hfill") {
            let a = self.parse_prefix_or_atom()?;
            let system = if self.at(&TokenKind::LBracket) {
                self.parse_system()?
            } else {
                let phi = self.parse_prefix_or_atom()?;
                let u = self.parse_prefix_or_atom()?;
                vec![(phi, u)]
            };
            let u0 = self.parse_prefix_or_atom()?;
            return Ok(Term::THFill(Arc::new(a), system, Arc::new(u0)));
        }
        if self.consume_ident("Equiv") {
            let a = self.parse_prefix_or_atom()?;
            let b = self.parse_prefix_or_atom()?;
            return Ok(Term::TEquiv(Arc::new(a), Arc::new(b)));
        }
        if self.consume_ident("mkEquiv") {
            let a = self.parse_prefix_or_atom()?;
            let b = self.parse_prefix_or_atom()?;
            let f = self.parse_prefix_or_atom()?;
            let g = self.parse_prefix_or_atom()?;
            let eta = self.parse_prefix_or_atom()?;
            let eps = self.parse_prefix_or_atom()?;
            return Ok(Term::TMkEquiv(
                Arc::new(a),
                Arc::new(b),
                Arc::new(f),
                Arc::new(g),
                Arc::new(eta),
                Arc::new(eps),
            ));
        }
        if self.consume_ident("Glue") {
            let a = self.parse_prefix_or_atom()?;
            let phi = self.parse_prefix_or_atom()?;
            let te = self.parse_prefix_or_atom()?;
            return Ok(Term::TGlue(Arc::new(a), Arc::new(phi), Arc::new(te)));
        }
        if self.consume_ident("Partial") {
            let phi = self.parse_prefix_or_atom()?;
            let a = self.parse_prefix_or_atom()?;
            return Ok(Term::TPartial(Arc::new(phi), Arc::new(a)));
        }
        if self.consume_ident("glueElem") || self.consume_ident("glue") {
            let phi = self.parse_prefix_or_atom()?;
            let t = self.parse_prefix_or_atom()?;
            let a = self.parse_prefix_or_atom()?;
            return Ok(Term::TGlueElem(Arc::new(phi), Arc::new(t), Arc::new(a)));
        }
        if self.consume_ident("unglue") {
            let phi = self.parse_prefix_or_atom()?;
            let te = self.parse_prefix_or_atom()?;
            let g = self.parse_prefix_or_atom()?;
            return Ok(Term::TUnglue(Arc::new(phi), Arc::new(te), Arc::new(g)));
        }
        if self.consume_ident("match") {
            return self.parse_match();
        }

        // U — universe formation with level expression
        if self.consume_ident("U") {
            let level = self.parse_level_expr()?;
            return Ok(Term::TUniv(level));
        }

        // [_ | phi] A — partial element type (bracket syntax)
        // [phi => A, psi => B] — system type (bracket syntax in type position)
        if self.peek().kind == TokenKind::LBracket {
            // Try [_ | phi] first
            if let Some(TokenKind::Ident(name)) = self.tokens.get(self.pos + 1).map(|t| &t.kind) {
                if name == "_" {
                    if let Some(TokenKind::Pipe) = self.tokens.get(self.pos + 2).map(|t| &t.kind) {
                        self.pos += 3; // consume [ _ |
                        let phi = self.parse_join()?;
                        self.expect(
                            TokenKind::RBracket,
                            "expected ']' after phi in partial type",
                        )?;
                        let a = self.parse_prefix_or_atom()?;
                        return Ok(Term::TPartial(Arc::new(phi), Arc::new(a)));
                    }
                }
            }
            // Try [phi => A, ...] — system type
            {
                let save = self.pos;
                match self.try_parse_system_type() {
                    Ok(sys) => return Ok(sys),
                    Err(_) => self.pos = save,
                }
            }
        }

        if self.peek_ident() == "_" {
            self.pos += 1;
            return Ok(Term::Meta(self.session().fresh_meta_id()));
        }

        if self.at(&TokenKind::Question) {
            // Hole: `?` (anonymous) or `?name` (named).
            self.pos += 1;
            let id = self.session().fresh_meta_id();
            if let TokenKind::Ident(name) = self.peek().kind.clone() {
                self.pos += 1;
                self.session().set_meta_name(id, name);
            }
            return Ok(Term::Meta(id));
        }

        match self.peek().kind.clone() {
            TokenKind::Ident(name) => {
                self.pos += 1;
                self.resolve_ident(name)
            }
            TokenKind::Int(0) => {
                self.pos += 1;
                Ok(Term::TInterval(I::I0))
            }
            TokenKind::Int(1) => {
                self.pos += 1;
                Ok(Term::TInterval(I::I1))
            }
            TokenKind::LParen => self.parse_paren(),
            other => Err(self.error_here(format!("expected term, found {}", describe(&other)))),
        }
    }

    /// Parse a system: `[phi1 -> tube1, phi2 -> tube2, ...]`
    /// Returns a System (Vec<(Term, Term)>).
    fn parse_system(&mut self) -> Result<crate::cubical::syntax::System, ParseError> {
        self.expect(TokenKind::LBracket, "expected '[' to start system")?;
        let mut system = Vec::new();
        self.stop_at_comma = true;
        loop {
            if self.at(&TokenKind::RBracket) {
                break;
            }
            let phi = self.parse_join()?;
            self.expect(TokenKind::FatArrow, "expected '=>' in system entry")?;
            let tube = self.parse_term()?;
            system.push((phi, tube));
            if !self.consume(&TokenKind::Comma) {
                break;
            }
        }
        self.stop_at_comma = false;
        self.expect(TokenKind::RBracket, "expected ']' after system")?;
        Ok(system)
    }

    fn parse_paren(&mut self) -> Result<Term, ParseError> {
        self.expect(TokenKind::LParen, "expected '('")?;
        if let Some((names, _ty)) = self.try_parse_binder_header()? {
            self.expect(TokenKind::RParen, "unmatched '('")?;
            if names.len() == 1 {
                return self.resolve_ident(names[0].clone());
            } else {
                return Err(self.error_here("use '∀ (x y : A), ...' for dependent binders"));
            }
        }
        let term = self.parse_term()?;
        if self.consume(&TokenKind::Colon) {
            let _ty = self.parse_term()?;
            self.expect(TokenKind::RParen, "unmatched '('")?;
            return Ok(term);
        }
        self.expect(TokenKind::RParen, "unmatched '('")?;
        Ok(term)
    }

    fn parse_parenthesized_binder(&mut self, form: &str) -> Result<(Name, Term), ParseError> {
        self.expect(
            TokenKind::LParen,
            format!("expected '(' after {} type former", form),
        )?;
        let binder = self.expect_ident(format!("expected binder name in {} type former", form))?;
        self.expect(
            TokenKind::Colon,
            format!("expected ':' after binder name '{}'", binder),
        )?;
        let ty = self.parse_term()?;
        self.expect(TokenKind::RParen, "unmatched '('")?;
        Ok((binder, ty))
    }

    /// Parse Lean-style lambda binders: both `fun x y => ...` and
    /// `fun (x : A) (y : B) => ...`.  Binder annotations are accepted for
    /// readability; lambda terms do not retain annotations in the core AST.
    fn parse_lambda_binders(
        &mut self,
        message: impl Into<String>,
    ) -> Result<Vec<Name>, ParseError> {
        let message = message.into();
        let mut binders = Vec::new();
        loop {
            match self.peek().kind.clone() {
                TokenKind::Ident(name) => {
                    self.pos += 1;
                    self.term_env.insert(0, name.clone());
                    binders.push(name);
                }
                TokenKind::LParen => {
                    self.pos += 1;
                    let mut names = Vec::new();
                    while let TokenKind::Ident(name) = self.peek().kind.clone() {
                        self.pos += 1;
                        names.push(name);
                    }
                    if names.is_empty() {
                        self.term_env.drain(0..binders.len());
                        return Err(self.error_here("expected binder name after '('"));
                    }
                    if let Err(error) =
                        self.expect(TokenKind::Colon, "expected ':' in typed lambda binder")
                    {
                        self.term_env.drain(0..binders.len());
                        return Err(error);
                    }
                    // Annotations are checked by the surrounding declaration;
                    // parsing them here still validates their syntax.
                    let annotation = self.parse_term();
                    if let Err(error) = annotation {
                        self.term_env.drain(0..binders.len());
                        return Err(error);
                    }
                    if let Err(error) =
                        self.expect(TokenKind::RParen, "unmatched '(' in lambda binder")
                    {
                        self.term_env.drain(0..binders.len());
                        return Err(error);
                    }
                    for name in names {
                        self.term_env.insert(0, name.clone());
                        binders.push(name);
                    }
                }
                _ => break,
            }
        }
        self.term_env.drain(0..binders.len());
        if binders.is_empty() {
            Err(self.error_here(message))
        } else {
            Ok(binders)
        }
    }

    fn expect_binder_separator(&mut self, form: &str) -> Result<(), ParseError> {
        if self.consume(&TokenKind::Dot) || self.consume(&TokenKind::Comma) {
            Ok(())
        } else {
            Err(self.error_here(format!("expected '.' or ',' after {} binder", form)))
        }
    }

    fn expect_definition_value(&mut self, name: &str) -> Result<(), ParseError> {
        if self.consume(&TokenKind::ColonEquals) {
            Ok(())
        } else {
            Err(self.error_here(format!(
                "expected ':=' after type for definition '{}'",
                name
            )))
        }
    }

    /// Try to parse a system type: [phi => A, psi => B]
    /// Expects current position to be at the opening bracket.
    fn try_parse_system_type(&mut self) -> Result<Term, ParseError> {
        self.expect(TokenKind::LBracket, "expected '[' for system type")?;
        let mut sys = Vec::new();
        loop {
            let phi = self.parse_join()?;
            self.expect(TokenKind::FatArrow, "expected '=>' in system type")?;
            let a = self.parse_prefix_or_atom()?;
            sys.push((phi, a));
            if self.consume(&TokenKind::Comma) {
                continue;
            } else {
                break;
            }
        }
        self.expect(TokenKind::RBracket, "expected ']' after system type")?;
        Ok(Term::TSystemType(sys))
    }

    fn try_parse_binder_header(&mut self) -> Result<Option<(Vec<Name>, Term)>, ParseError> {
        let save = self.pos;
        let mut names = Vec::new();
        while let TokenKind::Ident(n) = self.peek().kind.clone() {
            self.pos += 1;
            names.push(n);
        }
        if names.is_empty() {
            self.pos = save;
            return Ok(None);
        }
        if !self.consume(&TokenKind::Colon) {
            self.pos = save;
            return Ok(None);
        }
        let ty = self.parse_term()?;
        Ok(Some((names, ty)))
    }

    fn parse_match(&mut self) -> Result<Term, ParseError> {
        let (scrutinee, binder) = if let TokenKind::Ident(name) = self.peek().kind.clone() {
            self.pos += 1;
            let scrut = self.resolve_ident(name.clone())?;
            (scrut, name)
        } else {
            (self.parse_term()?, "_match".to_string())
        };

        self.term_env.insert(0, binder.clone());
        self.expect_ident("return")?;
        self.stop_at_with = true;
        let return_type = self.parse_term()?;
        self.stop_at_with = false;
        self.term_env.remove(0);

        self.expect_ident("with")?;
        let motive = Term::TAbs(binder, Arc::new(return_type));
        let cases = self.parse_match_cases(&motive, &scrutinee)?;
        Ok(Term::TElim(Arc::new(motive), cases, Arc::new(scrutinee)))
    }

    /// Parse the `| constructor binders => body` arms of a `match`.
    /// A `match` with no `|` cases at all is legal — it eliminates the empty
    /// type (`match e return A with`), whose type checker only fires when the
    /// scrutinee normalizes to a value of an empty datatype.
    ///
    /// Each arm is read in two passes. The first ([`Self::parse_match_arm`])
    /// scans the leading column into a tree of [`Pat`]s and stops at the
    /// `=>`; the second parses the body with the right binders in scope and
    /// assembles the flat [`ElimCase`]s the kernel expects. Arms whose
    /// patterns are all plain variables keep producing byte-identical output
    /// to the flat parser. Arms with nested constructor patterns (`suc (suc
    /// zero)`) are collected and compiled by [`Self::compile_nested_arms`]
    /// into chains of nested `TElim`s once every arm is known, so that arms
    /// sharing a constructor head merge into a single complete case.
    fn parse_match_cases(
        &mut self,
        motive: &Term,
        scrutinee: &Term,
    ) -> Result<Vec<ElimCase>, ParseError> {
        if !self.at(&TokenKind::Pipe) {
            return Ok(Vec::new());
        }

        let my_col = self.peek().col;
        let mut cases = Vec::new();
        let mut nested_arms: Vec<(Pat, Box<Term>, Option<Name>)> = Vec::new();
        let mut flat_heads: Vec<Name> = Vec::new();
        self.consume(&TokenKind::Pipe);
        loop {
            // Pass A: leading column -> pattern tree(s), as/record handling.
            let arm = self.parse_match_arm(my_col)?;
            // Absurd pattern `()` desugars to a zero-case match.
            if arm.absurd {
                return Ok(Vec::new());
            }
            // Pass B: body + ElimCase assembly.
            if arm.record_bindings.is_some() {
                let elim = self.parse_record_case_body(arm)?;
                cases.push(elim);
            } else if arm.pats.iter().any(|p| p.has_nested_con()) {
                self.parse_nested_arm(arm, &mut nested_arms, &mut cases, &mut flat_heads)?;
            } else {
                let flat = self.parse_flat_case_body(arm)?;
                for e in &flat {
                    if !e.con.is_empty() {
                        flat_heads.push(e.con.clone());
                    }
                }
                cases.extend(flat);
            }
            if self.at(&TokenKind::Pipe) && self.peek().col >= my_col {
                self.consume(&TokenKind::Pipe);
            } else {
                break;
            }
        }

        // A flat (all-variable) case and a nested-pattern case for the same
        // constructor cannot both be compiled: the kernel's first-matching-case
        // semantics would silently shadow the nested arms.
        let nested = self.compile_nested_arms(nested_arms, motive)?;
        for e in &nested {
            if flat_heads.contains(&e.con) {
                return Err(self.error_here(
                    "mixed variable and constructor patterns for the same constructor",
                ));
            }
        }
        cases.extend(nested);
        // Only matches over an open scrutinee must be exhaustive; the kernel
        // reduces eliminators over closed constructor values, so partial
        // matches like `match (suc zero) with | suc n => n` are legal.
        if matches!(scrutinee, Term::TVar(_)) {
            self.check_match_completeness(&cases)?;
        }
        Ok(cases)
    }

    /// Pass A of an eliminator-case arm: scan the leading column into a list
    /// of [`Pat`]s (one per or-alternative), handle `as`-patterns and record
    /// patterns `{ field = binder }`, and consume the `=>`.
    fn parse_match_arm(&mut self, my_col: usize) -> Result<MatchArm, ParseError> {
        // Absurd pattern: `()` — no body, desugars to zero-case match.
        if self.at(&TokenKind::LParen)
            && self.pos + 1 < self.tokens.len()
            && self.tokens[self.pos + 1].kind == TokenKind::RParen
        {
            self.consume(&TokenKind::LParen);
            self.consume(&TokenKind::RParen);
            return Ok(MatchArm {
                pats: vec![],
                as_name: None,
                record_bindings: None,
                absurd: true,
            });
        }
        let mut pats: Vec<Pat> = Vec::new();
        let mut as_name: Option<Name> = None;
        let mut record_bindings: Option<Vec<(Name, Name)>> = None;
        loop {
            if self.at(&TokenKind::LBrace) {
                // Record pattern: { field = binder, ... }
                // Typechecker will desugar to constructor pattern once the datatype is known.
                let mut bindings = Vec::new();
                self.consume(&TokenKind::LBrace);
                if !self.at(&TokenKind::RBrace) {
                    loop {
                        let field = self.expect_ident("expected field name in record pattern")?;
                        self.expect(
                            TokenKind::Equals,
                            format!("expected '=' after field '{}' in record pattern", field),
                        )?;
                        let binder = self.expect_ident("expected binder name in record pattern")?;
                        bindings.push((field, binder));
                        if !self.consume(&TokenKind::Comma) {
                            break;
                        }
                    }
                }
                self.expect(
                    TokenKind::RBrace,
                    "expected '}' after record pattern fields",
                )?;
                record_bindings = Some(bindings);
                pats.push(Pat::Con {
                    con: String::new(),
                    args: Vec::new(),
                });
            } else {
                let con = self.expect_ident(
                    "expected constructor name or record pattern in eliminator case",
                )?;
                pats.push(self.parse_pattern_after_con(con)?);
            }

            // Check for as-pattern: ... as name (after binders, before => or |)
            if self.consume_ident("as") {
                let as_n = self.expect_ident("expected name after 'as' in as-pattern")?;
                as_name = Some(as_n);
                break; // as-pattern ends the pattern group
            }

            // Check for or-pattern separator
            if self.at(&TokenKind::Pipe) && self.peek().col >= my_col {
                self.consume(&TokenKind::Pipe);
            } else {
                break;
            }
        }
        if !(self.consume(&TokenKind::FatArrow) || self.consume(&TokenKind::Arrow)) {
            return Err(self.error_here("expected '=>' after eliminator case binders"));
        }
        Ok(MatchArm {
            pats,
            as_name,
            record_bindings,
            absurd: false,
        })
    }

    /// Parse the argument patterns following a constructor head. Identifiers
    /// that resolve to constructors (via the global environment) are read
    /// recursively as nested constructor patterns — `suc zero` is `suc` applied
    /// to the `zero` constructor — while non-constructor identifiers become
    /// variable binders. Parenthesized constructor applications are read
    /// recursively too. No existing example or library pattern binder collides
    /// with a constructor name (audited), so this is a safe behaviour change.
    fn parse_pattern_after_con(&mut self, con: Name) -> Result<Pat, ParseError> {
        // Known ordinary constructors consume exactly their arity of
        // arguments, so a zero-arity constructor like `nil` does not swallow
        // its siblings. Interval-binder constructors (path/square/cell) and
        // unknown heads (no datatype environment, e.g. parser unit tests)
        // fall back to the flat parser's greedy behaviour: read identifiers
        // until `=>`, `|` or `as`.
        let arity = match self.find_constructor_arity(&con) {
            Some((_, false, a)) => Some(a),
            _ => None,
        };
        let mut args = Vec::new();
        loop {
            if let Some(max) = arity {
                if args.len() >= max {
                    break;
                }
            }
            if let TokenKind::Ident(name) = self.peek().kind.clone() {
                if name == "=>" || name == "|" || name == "as" {
                    break;
                }
                self.pos += 1;
                if self.find_constructor_arity(&name).is_some() {
                    let inner = self.parse_pattern_after_con(name)?;
                    args.push(inner);
                } else {
                    args.push(Pat::Var(name));
                }
            } else if self.at(&TokenKind::LParen) {
                self.pos += 1;
                let inner_con = self
                    .expect_ident("expected constructor name inside nested pattern parentheses")?;
                let inner = self.parse_pattern_after_con(inner_con)?;
                self.expect(
                    TokenKind::RParen,
                    "expected ')' after nested constructor pattern",
                )?;
                args.push(inner);
            } else {
                break;
            }
        }
        Ok(Pat::Con { con, args })
    }

    /// Pass B for a record-pattern arm: push the field binders (and the
    /// `as`-binder, if any), parse the body, and build the `ElimCase` the
    /// typechecker's record-pattern desugaring expects. Byte-identical to the
    /// flat parser.
    fn parse_record_case_body(&mut self, arm: MatchArm) -> Result<ElimCase, ParseError> {
        let bindings = arm.record_bindings.unwrap();
        let as_name = arm.as_name;
        let binder_names: Vec<Name> = bindings.iter().map(|(_, b)| b.clone()).collect();
        for b in binder_names.iter() {
            self.term_env.insert(0, b.clone());
        }
        if let Some(ref as_n) = as_name {
            self.term_env.insert(0, as_n.clone());
        }
        let body_box = Box::new(self.parse_term()?);
        if as_name.is_some() {
            self.term_env.remove(0);
        }
        for _ in &binder_names {
            self.term_env.remove(0);
        }
        Ok(ElimCase {
            con: "".to_string(),
            binders: binder_names,
            body: body_box,
            as_name,
            record_bindings: Some(bindings),
            refinements: None,
        })
    }

    /// Pass B for a flat arm: parse the body with the original ord/ivar binder
    /// split and assemble one `ElimCase` per or-alternative. This keeps the
    /// output byte-identical to the pre-nested-pattern parser.
    fn parse_flat_case_body(&mut self, arm: MatchArm) -> Result<Vec<ElimCase>, ParseError> {
        let MatchArm {
            pats,
            as_name,
            record_bindings: _,
            absurd: _,
        } = arm;
        let last_pat = pats.last().unwrap();
        // Determine the type of constructor:
        // - plain constructor: no interval binders
        // - path constructor: last binder is the interval variable
        // - square constructor: last TWO binders are interval variables
        // - cell constructor: last `dim` binders are interval variables
        let last_con = last_pat.con().unwrap_or("");
        let cell_dim = self.is_cell_constructor_case(last_con);
        let is_sqcon = self.is_square_constructor_case(last_con);
        let is_path_con = self
            .find_constructor(last_con)
            .is_some_and(|(_, is_path)| is_path);
        let mut binders = Vec::new();
        last_pat.binders(&mut binders);
        let (ord_binders, ivar_binders) = if let Some(dim) = cell_dim {
            if binders.len() >= dim {
                let split = binders.len() - dim;
                (&binders[..split], &binders[split..])
            } else {
                (&binders[..], &[] as &[String])
            }
        } else if is_sqcon && binders.len() >= 2 {
            let split = binders.len() - 2;
            (&binders[..split], &binders[split..])
        } else if is_path_con && !binders.is_empty() && !is_sqcon {
            let split = binders.len() - 1;
            (&binders[..split], &binders[split..])
        } else {
            (&binders[..], &[] as &[String])
        };

        for binder in ord_binders.iter() {
            self.term_env.insert(0, binder.clone());
        }
        for iv in ivar_binders {
            self.ivar_env.insert(0, iv.clone());
            self.term_env.insert(0, "".to_string());
        }
        if let Some(ref as_n) = as_name {
            self.term_env.insert(0, as_n.clone());
        }
        let body = self.parse_term()?;
        if as_name.is_some() {
            self.term_env.remove(0);
        }
        for _ in ivar_binders {
            self.term_env.remove(0);
            self.ivar_env.remove(0);
        }
        for _ in ord_binders {
            self.term_env.remove(0);
        }

        let body_box = Box::new(body);
        let mut cases = Vec::new();
        for pat in pats {
            let mut binders = Vec::new();
            pat.binders(&mut binders);
            cases.push(ElimCase {
                con: pat.con().unwrap_or("").to_string(),
                binders,
                body: body_box.clone(),
                as_name: as_name.clone(),
                record_bindings: None,
                refinements: None,
            });
        }
        Ok(cases)
    }

    /// Pass B for an arm containing a nested constructor pattern: parse the
    /// body with the last pattern's binders (in the compiled chain's order) in
    /// scope, then hand the nested patterns to the final merge. Plain-variable
    /// alternatives of a mixed or-pattern arm are emitted immediately.
    fn parse_nested_arm(
        &mut self,
        arm: MatchArm,
        nested_arms: &mut Vec<(Pat, Box<Term>, Option<Name>)>,
        cases: &mut Vec<ElimCase>,
        flat_heads: &mut Vec<Name>,
    ) -> Result<(), ParseError> {
        let last_pat = arm.pats.last().unwrap();
        let mut env = Vec::new();
        last_pat.pattern_env_with_as(&mut env, arm.as_name.as_ref());
        for n in env.iter() {
            self.term_env.insert(0, n.clone());
        }
        let body = self.parse_term()?;
        for _ in &env {
            self.term_env.remove(0);
        }
        let body_box = Box::new(body);
        for pat in arm.pats {
            if pat.has_nested_con() {
                nested_arms.push((pat, body_box.clone(), arm.as_name.clone()));
            } else {
                let mut binders = Vec::new();
                pat.binders(&mut binders);
                if let Some(head) = pat.con() {
                    flat_heads.push(head.to_string());
                }
                cases.push(ElimCase {
                    con: pat.con().unwrap_or("").to_string(),
                    binders,
                    body: body_box.clone(),
                    as_name: arm.as_name.clone(),
                    record_bindings: None,
                    refinements: None,
                });
            }
        }
        Ok(())
    }

    /// Merge all nested-pattern arms of a match, grouped by constructor head,
    /// into one `ElimCase` per head whose body is a chain of nested `TElim`s.
    /// The body of a nested `ElimCase` is computed by [`Self::compile_columns`];
    /// the case binders come from the first arm's arguments (a phantom name
    /// for a nested constructor slot). Arms merged into one head must agree on
    /// their `as`-binding; the shared name becomes the case's `as_name`.
    fn compile_nested_arms(
        &mut self,
        arms: Vec<(Pat, Box<Term>, Option<Name>)>,
        motive: &Term,
    ) -> Result<Vec<ElimCase>, ParseError> {
        // Group by head, preserving first-appearance order.
        let mut groups: Vec<(Name, Vec<(Pat, Box<Term>, Option<Name>)>)> = Vec::new();
        for (pat, body, as_name) in arms {
            let head = pat.con().unwrap_or("").to_string();
            match groups.iter_mut().find(|(h, _)| *h == head) {
                Some((_, g)) => g.push((pat, body, as_name)),
                None => groups.push((head, vec![(pat, body, as_name)])),
            }
        }
        let mut cases = Vec::new();
        for (head, group) in groups {
            // All arms sharing a head must bind the same name with `as`.
            let as_name = group[0].2.clone();
            if group.iter().any(|(_, _, an)| *an != as_name) {
                return Err(self
                    .error_here("inconsistent as-bindings between arms that merge into one case"));
            }
            let extra_shift = if as_name.is_some() { 1usize } else { 0usize };
            let first = &group[0].0;
            let args = first.args();
            let arity = args.len();
            let mut binders = Vec::new();
            for a in args {
                match a {
                    Pat::Var(n) => binders.push(n.clone()),
                    Pat::Con { con, .. } => binders.push(con.clone()),
                }
            }
            // A path constructor head (single interval, e.g. `merid`) may
            // carry nested constructor patterns on its ordinary arguments;
            // square/cell heads are not refined yet (their multi-interval
            // leaf checking is future work).
            let head_is_pcon = self.is_single_interval_path_con(&head);
            let head_dt = self.nested_head_datatype(&head, head_is_pcon)?;
            // The expected type of this case, exactly as the typechecker
            // computes it: motive applied to the constructor with the case
            // binders as variables (shifted up when an as-binder sits at 0).
            let con_args: Vec<Term> = (0..arity)
                .map(|k| Term::TVar((arity - 1 - k + extra_shift) as i32))
                .collect();
            // Refinement marker for HIT heads: one entry per ordinary
            // argument (everything before the trailing interval binder),
            // `Some(leaf_binders)` for a nested constructor slot.
            let refinements = if head_is_pcon {
                Some(
                    args.iter()
                        .take(args.len().saturating_sub(1))
                        .map(|a| match a {
                            Pat::Var(_) => None,
                            Pat::Con { .. } => {
                                let mut leaves = Vec::new();
                                a.binders(&mut leaves);
                                Some(leaves)
                            }
                        })
                        .collect(),
                )
            } else {
                None
            };
            let case_expected = Term::TApp(
                Arc::new(shift((arity + extra_shift) as i32, 0, motive)),
                Arc::new(Term::TCon(head_dt, head.clone(), con_args)),
            );
            // One column per argument, with the argument's index in the case
            // context (innermost-first binder list, plus the as-binder's slot).
            let mut cols: Vec<(Vec<Pat>, usize)> = Vec::new();
            for k in 0..arity {
                let pats: Vec<Pat> = group.iter().map(|(p, _, _)| p.args()[k].clone()).collect();
                cols.push((pats, arity - 1 - k + extra_shift));
            }
            let bodies: Vec<Box<Term>> = group.iter().map(|(_, b, _)| b.clone()).collect();
            let body = self.compile_columns(cols, &bodies, &case_expected)?;
            cases.push(ElimCase {
                con: head,
                binders,
                body,
                as_name,
                record_bindings: None,
                refinements,
            });
        }
        Ok(cases)
    }

    /// Whether `con` names a single-interval path constructor (`pcon`), as
    /// opposed to a square (`sqcon`, two intervals) or cell (`cellcon`, n
    /// intervals) constructor.
    fn is_single_interval_path_con(&self, con: &str) -> bool {
        self.find_constructor(con)
            .is_some_and(|(_, is_path)| is_path)
            && !self.is_square_constructor_case(con)
            && self.is_cell_constructor_case(con).is_none()
    }

    /// Resolve a nested pattern's constructor to its datatype, rejecting
    /// square/cell constructors and, for ordinary sub-patterns, path
    /// constructors (which carry interval binders the nested machinery does
    /// not understand). The head constructor of a HIT case arm may be a
    /// single-interval path constructor when `allow_pcon` is set.
    fn nested_head_datatype(&self, con: &str, allow_pcon: bool) -> Result<Name, ParseError> {
        match self.find_constructor(con) {
            Some((dt, true)) => {
                if allow_pcon && self.is_single_interval_path_con(con) {
                    Ok(dt)
                } else {
                    Err(ParseError {
                        message: format!(
                            "nested pattern constructor '{}' has interval binders; \
                             nested patterns are only supported for ordinary constructors \
                             (or a single-interval path constructor in the head of a HIT case)",
                            con
                        ),
                        line: 0,
                        col: 0,
                    })
                }
            }
            Some((dt, false)) => Ok(dt),
            None => Err(ParseError {
                message: format!("unknown constructor '{}' in nested pattern", con),
                line: 0,
                col: 0,
            }),
        }
    }

    /// Compile the body of a constructor case whose arms' patterns share a
    /// head. `cols` lists every argument column (patterns across the arms
    /// together with the argument's index in the current case context);
    /// `bodies` holds one leaf body per arm.
    ///
    /// The leftmost nested column is eliminated first, producing a `TElim`
    /// whose motive plugs the eliminated variable into the case's expected
    /// type; arms that share a sub-constructor merge recursively. When every
    /// remaining column is a plain variable the first arm's body wins (the
    /// kernel's "first matching case" semantics).
    fn compile_columns(
        &mut self,
        cols: Vec<(Vec<Pat>, usize)>,
        bodies: &[Box<Term>],
        expected_ty: &Term,
    ) -> Result<Box<Term>, ParseError> {
        // A column mixing a variable pattern with a constructor pattern cannot
        // be compiled into the kernel's first-matching-case eliminator (the
        // variable arm would silently shadow the constructor arms).
        for (pats, _) in &cols {
            let has_var = pats.iter().any(|p| p.con().is_none());
            let has_con = pats.iter().any(|p| p.con().is_some());
            if has_var && has_con {
                return Err(
                    self.error_here("mixed variable and constructor patterns in the same column")
                );
            }
        }
        let nested_k = cols
            .iter()
            .position(|(pats, _)| pats.iter().any(|p| p.con().is_some()));
        let Some(k) = nested_k else {
            return Ok(bodies[0].clone());
        };
        let (pats, slot) = &cols[k];

        // Motive of the eliminator: λz. expected[slot := z], with the current
        // case context lifted under the fresh λ binder.
        let motive = Term::TAbs(
            "z".to_string(),
            Arc::new(subst(
                (*slot + 1) as i32,
                &Term::TVar(0),
                &shift(1, 0, expected_ty),
            )),
        );

        // Group the arms at this column by sub-constructor.
        let mut groups: Vec<(Name, Vec<usize>)> = Vec::new();
        for (i, p) in pats.iter().enumerate() {
            let head = p.con().unwrap_or("").to_string();
            match groups.iter_mut().find(|(h, _)| *h == head) {
                Some((_, g)) => g.push(i),
                None => groups.push((head, vec![i])),
            }
        }

        let mut cases = Vec::new();
        for (head, idxs) in groups {
            let sub_first = &pats[idxs[0]];
            let sub_args = sub_first.args();
            let sub_arity = sub_args.len();
            let mut sub_binders = Vec::new();
            for a in sub_args {
                match a {
                    Pat::Var(n) => sub_binders.push(n.clone()),
                    Pat::Con { con, .. } => sub_binders.push(con.clone()),
                }
            }
            let head_dt = self.nested_head_datatype(&head, false)?;
            // The sub-case's columns: its own arguments first, then the parent
            // head's remaining columns (their context indices shifted up by the
            // sub-case's binder count).
            let mut sub_cols: Vec<(Vec<Pat>, usize)> = Vec::new();
            for a in 0..sub_arity {
                let sub_pats: Vec<Pat> = idxs.iter().map(|&i| pats[i].args()[a].clone()).collect();
                sub_cols.push((sub_pats, sub_arity - 1 - a));
            }
            for (j, (rest_pats, rest_slot)) in cols.iter().enumerate() {
                if j == k {
                    continue;
                }
                let sub_pats: Vec<Pat> = idxs.iter().map(|&i| rest_pats[i].clone()).collect();
                sub_cols.push((sub_pats, rest_slot + sub_arity));
            }
            // The expected type of this sub-case, as the typechecker computes
            // it from the eliminator motive.
            let con_args: Vec<Term> = (0..sub_arity)
                .map(|a| Term::TVar((sub_arity - 1 - a) as i32))
                .collect();
            let sub_expected = Term::TApp(
                Arc::new(shift(sub_arity as i32, 0, &motive)),
                Arc::new(Term::TCon(head_dt, head.clone(), con_args)),
            );
            let sub_bodies: Vec<Box<Term>> = idxs.iter().map(|&i| bodies[i].clone()).collect();
            let sub_body = self.compile_columns(sub_cols, &sub_bodies, &sub_expected)?;
            cases.push(ElimCase {
                con: head,
                binders: sub_binders,
                body: sub_body,
                as_name: None,
                record_bindings: None,
                refinements: None,
            });
        }

        Ok(Box::new(Term::TElim(
            Arc::new(motive),
            cases,
            Arc::new(Term::TVar(*slot as i32)),
        )))
    }
    fn token_pos(&self) -> (usize, usize) {
        let tok = &self.tokens[self.pos - 1];
        (tok.line, tok.col)
    }

    /// Record a variable name occurrence for the current declaration so the
    /// The current module path as a single dotted name ("" at top level).
    fn current_prefix(&self) -> String {
        self.module_stack.join(".")
    }

    /// Qualify a raw definition/datatype name with the current module path.
    pub(super) fn qualify(&self, raw: &Name) -> Name {
        let prefix = self.current_prefix();
        if prefix.is_empty() {
            raw.clone()
        } else {
            format!("{}.{}", prefix, raw)
        }
    }

    /// Parse an optional module-parameter binder list: `(A : Type) (B : Nat)`.
    /// Binders are inserted front-first into `term_env` exactly like record
    /// parameters (last binder at index 0). Each parsed parameter type is
    /// immediately weakened by one slot (`shift(-1)`): it was parsed in the
    /// layout that already contains its own binder, but the final Pi-chain
    /// places it before that binder.
    pub(super) fn parse_module_binders(&mut self) -> Result<Vec<(Name, Term)>, ParseError> {
        let mut params: Vec<(Name, Term)> = Vec::new();
        while self.at(&TokenKind::LParen) && self.peek_ahead_is_binder() {
            self.expect(TokenKind::LParen, "expected '(' for parameter binder")?;
            let pname = self.expect_ident("expected parameter name")?;
            self.expect(
                TokenKind::Colon,
                format!("expected ':' after parameter name '{}'", pname),
            )?;
            let pty = self.parse_term()?;
            self.expect(TokenKind::RParen, "expected ')' after parameter type")?;
            self.term_env.insert(0, pname.clone());
            params.push((pname, shift(-1, 0, &pty)));
        }
        Ok(params)
    }

    /// The single active parameterized-module layer, if any: its full dotted
    /// path and its parameter list. v1 rejects nested parameterized modules,
    /// so at most one layer exists.
    fn active_param_module(&self) -> Option<(String, &Vec<(Name, Term)>)> {
        let idx = self.module_params.iter().position(|ps| !ps.is_empty())?;
        Some((
            self.module_stack[..=idx].join("."),
            &self.module_params[idx],
        ))
    }

    /// True when any enclosing module carries parameters. Datatypes, records,
    /// imports and further parameterized modules are rejected inside (v1).
    pub(super) fn inside_parameterized_module(&self) -> bool {
        self.module_params.iter().any(|ps| !ps.is_empty())
    }

    /// Reject a declaration kind that v1 does not support inside a
    /// parameterized module.
    pub(super) fn reject_inside_parameterized_module(&self, what: &str) -> Result<(), ParseError> {
        if self.inside_parameterized_module() {
            Err(self.error_here(format!(
                "{}s inside a parameterized module are not supported",
                what
            )))
        } else {
            Ok(())
        }
    }

    /// Close a definition's type and value over the enclosing parameterized
    /// module's parameters: `ty` becomes `Pi p1 => ... => Pi pn => ty` and
    /// `val` becomes `fun p1 => ... => fun pn => val`.
    ///
    /// The parsed body already references parameters through their
    /// `term_env` slots (last parameter at index 0), which is exactly the de
    /// Bruijn layout under the added leading binders, so no shifting is
    /// needed there. Parameter types were weakened at parse time (see
    /// [`Self::parse_module_binders`]).
    fn wrap_with_module_params(&self, ty: Term, val: Term) -> (Term, Term) {
        match self.active_param_module() {
            Some((_, params)) => {
                let mut ty_w = ty;
                let mut val_w = val;
                // Innermost parameter binds closest, so wrap in reverse.
                for (pname, pty) in params.iter().rev() {
                    ty_w = Term::TPi(pname.clone(), Arc::new(pty.clone()), Arc::new(ty_w), false);
                    val_w = Term::TAbs(pname.clone(), Arc::new(val_w));
                }
                (ty_w, val_w)
            }
            None => (ty, val),
        }
    }

    /// Wrap a type with the enclosing parameterized module's parameters as Pi.
    fn wrap_with_module_params_one(&self, ty: Term) -> (Term,) {
        match self.active_param_module() {
            Some((_, params)) => {
                let mut ty_w = ty;
                for (pname, pty) in params.iter().rev() {
                    ty_w = Term::TPi(pname.clone(), Arc::new(pty.clone()), Arc::new(ty_w), false);
                }
                (ty_w,)
            }
            None => (ty,),
        }
    }

    /// Wrap a resolved global reference into applications of the enclosing
    /// parameterized module's parameters (outermost parameter applied first).
    ///
    /// Only members OF the parameterized module — candidates whose dotted name
    /// starts with the module's path — are parameterized; unrelated globals
    /// stay unapplied. Parameter variables occupy the bottom `n` slots of
    /// `term_env`, front-inserted so the LAST declared parameter is innermost
    /// (`[p_n, ..., p_1]`); references may also occur under additional local
    /// binders (e.g. inside a lambda), so the i-th declared parameter's index
    /// is computed relative to the *current* environment depth as `L-1-i`.
    fn apply_module_params(&self, candidate: &str, global_ref: Term) -> Term {
        match self.active_param_module() {
            Some((prefix, params)) if candidate.starts_with(&format!("{prefix}.")) => {
                let l = self.term_env.len() as i32;
                params.iter().enumerate().fold(global_ref, |acc, (i, _)| {
                    Term::TApp(Arc::new(acc), Arc::new(Term::TVar(l - 1 - i as i32)))
                })
            }
            _ => global_ref,
        }
    }

    /// Module path prefixes innermost-first for candidate lookup, e.g. the
    /// stack `["A", "B"]` yields `["A.B", "A"]`.
    fn module_path_prefixes(&self) -> Vec<String> {
        let mut out = Vec::new();
        let mut acc: Vec<Name> = Vec::new();
        for seg in &self.module_stack {
            acc.push(seg.clone());
            out.push(acc.join("."));
        }
        out
    }

    /// Candidate names for unqualified global/datatype resolution inside the
    /// current module: innermost-qualified first, then top-level plain name.
    fn qualified_candidates(&self, name: &Name) -> Vec<Name> {
        let mut out = Vec::new();
        for prefix in self.module_path_prefixes() {
            out.push(format!("{}.{}", prefix, name));
        }
        out.push(name.clone());
        out
    }

    /// True if `prefix` is usable as a module-qualification prefix: a segment
    /// of the current module path, a module nested in the current module, or
    /// the leading segment of some global or datatype name (which covers
    /// `import "f.owl" as X` — the imported names are stored as `X.<name>`).
    fn is_module_prefix(&self, prefix: &str) -> bool {
        if self.module_stack.iter().any(|s| s == prefix) {
            return true;
        }
        let qualified = self.qualify(&prefix.to_string());
        let dot = format!("{}.", qualified);
        self.global_env.iter().any(|n| n.starts_with(&dot))
            || self.datatypes.iter().any(|dt| dt.name.starts_with(&dot))
    }

    /// Resolve the source module of an instantiation `module N = M (...)` to
    /// its full dotted path: innermost-qualified candidates first, then the
    /// bare name, accepting the first candidate that actually prefixes known
    /// globals.
    pub(super) fn resolve_module_source(&self, raw: &Name) -> Result<Name, ParseError> {
        for cand in self.qualified_candidates(raw) {
            let dot = format!("{cand}.");
            if self.global_env.iter().any(|n| n.starts_with(&dot)) {
                return Ok(cand);
            }
        }
        Err(self.error_here(format!("unknown module '{raw}' in module instantiation")))
    }

    /// Resolve a dotted, module-qualified reference `M.name`, `M.Nat`, or
    /// `M.Nat.zero` (also datatype-qualified constructors like `Nat.zero`).
    /// Both the absolute path (`Outer.Inner.T`) and the current-module-relative
    /// path (`Inner.T` from inside `Outer`) are attempted.
    fn resolve_dotted(&mut self, segments: &[Name]) -> Result<Term, ParseError> {
        let (line, col) = self.token_pos();
        let joined = segments.join(".");
        let qualified_joined = self.qualify(&joined);
        let mut candidates: Vec<String> = Vec::new();
        if qualified_joined != joined {
            candidates.push(qualified_joined.clone());
        }
        candidates.push(joined.clone());
        for cand in &candidates {
            if let Some(idx) = self.global_env.iter().position(|n| n == cand) {
                self.record_name_pos(cand, line, col, false);
                let gref = Term::TVar((self.term_env.len() + idx) as i32);
                return Ok(self.apply_module_params(cand, gref));
            }
        }
        for cand in &candidates {
            if self.datatypes.iter().any(|dt| dt.name == *cand) {
                return Ok(Term::TData(cand.clone(), vec![]));
            }
        }
        // Constructor reference: the trailing segments name a constructor of a
        // datatype whose qualified name is the leading segments.
        for k in 1..segments.len() {
            let member = segments[k..].join(".");
            let mut prefixes = Vec::new();
            let raw_prefix = segments[..k].join(".");
            let qualified_prefix = self.qualify(&raw_prefix);
            if qualified_prefix != raw_prefix {
                prefixes.push(qualified_prefix);
            }
            prefixes.push(raw_prefix);
            for prefix in &prefixes {
                for dt in self.datatypes.iter().rev() {
                    if dt.name == *prefix || dt.name.starts_with(&format!("{}.", prefix)) {
                        if let Some(_c) = dt.cons.iter().find(|c| c.name == member) {
                            return Ok(Term::TCon(dt.name.clone(), member, Vec::new()));
                        }
                        if let Some(_c) = dt.pcons.iter().find(|c| c.name == member) {
                            return Ok(Term::TCon(dt.name.clone(), member, Vec::new()));
                        }
                        if let Some(_c) = dt.sqcons.iter().find(|c| c.name == member) {
                            return Ok(Term::TCon(dt.name.clone(), member, Vec::new()));
                        }
                        if let Some(_c) = dt.cellcons.iter().find(|c| c.name == member) {
                            return Ok(Term::TCon(dt.name.clone(), member, Vec::new()));
                        }
                    }
                }
            }
        }
        Err(self.error_here(format!(
            "unknown name '{}' in module '{}'",
            segments.last().unwrap(),
            segments[..segments.len() - 1].join(".")
        )))
    }

    /// Global definition index for an unqualified name, preferring the current
    /// module's qualified names (innermost first), then the top-level name.
    /// Also returns the qualified candidate that matched — needed to decide
    /// module-parameter application.
    fn find_global_candidate_with_name(&self, name: &Name) -> Option<(usize, Name)> {
        for cand in self.qualified_candidates(name) {
            if let Some(idx) = self.global_env.iter().position(|n| n == &cand) {
                return Some((idx, cand));
            }
        }
        None
    }

    /// Datatype name for an unqualified name, preferring the current module's
    /// qualified datatype names. A datatype declared in a nested module is also
    /// visible unqualified from an enclosing module (`Inner.T` as `T` from
    /// inside `Outer`) — this keeps library files portable between plain and
    /// aliased imports.
    fn find_datatype_candidate(&self, name: &Name) -> Option<Name> {
        for cand in self.qualified_candidates(name) {
            if self.datatypes.iter().any(|dt| dt.name == cand) {
                return Some(cand);
            }
        }
        for prefix in self.module_path_prefixes() {
            let dot = format!("{}.", prefix);
            if let Some(dt) = self.datatypes.iter().find(|dt| {
                dt.name.starts_with(&dot) && dt.name.rsplit('.').next() == Some(name.as_str())
            }) {
                return Some(dt.name.clone());
            }
        }
        None
    }

    /// Constructor for an unqualified name, preferring datatypes declared in
    /// the current module, then any datatype (existing behaviour).
    fn find_constructor_candidate(&self, name: &str) -> Option<(Name, bool)> {
        for prefix in self.module_path_prefixes() {
            let dot = format!("{}.", prefix);
            for dt in self.datatypes.iter().rev() {
                if dt.name.starts_with(&dot) {
                    if let Some((dtn, is_path)) = self.find_constructor_in_dt(dt, name) {
                        return Some((dtn, is_path));
                    }
                }
            }
        }
        self.find_constructor(name)
    }

    fn find_constructor_in_dt(&self, dt: &Datatype, name: &str) -> Option<(Name, bool)> {
        if dt.cons.iter().any(|c| c.name == name) {
            return Some((dt.name.clone(), false));
        }
        if dt.pcons.iter().any(|c| c.name == name) {
            return Some((dt.name.clone(), true));
        }
        if dt.sqcons.iter().any(|c| c.name == name) {
            return Some((dt.name.clone(), true));
        }
        if dt.cellcons.iter().any(|c| c.name == name) {
            return Some((dt.name.clone(), true));
        }
        None
    }

    /// typechecker can attach a source position to errors involving it.
    fn record_name_pos(&mut self, name: &Name, line: usize, col: usize, is_introduction: bool) {
        self.decl_positions
            .push((name.clone(), Pos { line, col }, is_introduction));
    }

    fn resolve_ident(&mut self, name: Name) -> Result<Term, ParseError> {
        if name == "Type" {
            return Ok(Term::TUniv(LevelExpr::LConst(0)));
        }
        if name == "Prop" {
            return Ok(Term::TProp);
        }
        if name == "SSet" {
            return Ok(Term::TSSet);
        }
        if name == "Level" {
            return Ok(Term::TLevelTy);
        }
        if name == "I" || name == "𝕀" {
            return Ok(Term::TIntervalTy);
        }
        if name == "i0" {
            return Ok(Term::TInterval(I::I0));
        }
        if name == "i1" {
            return Ok(Term::TInterval(I::I1));
        }
        if let Some(level) = parse_universe(&name) {
            return Ok(Term::TUniv(LevelExpr::LConst(level)));
        }
        let (line, col) = self.token_pos();
        if let Some(idx) = self.term_env.iter().position(|n| n == &name) {
            self.record_name_pos(&name, line, col, false);
            return Ok(Term::TVar(idx as i32));
        }
        // Globals: prefer the current module's qualified names, then the
        // top-level name. Members of an enclosing parameterized module are
        // automatically applied to that module's parameters.
        if let Some((idx, candidate)) = self.find_global_candidate_with_name(&name) {
            self.record_name_pos(&name, line, col, false);
            let gref = Term::TVar((self.term_env.len() + idx) as i32);
            return Ok(self.apply_module_params(&candidate, gref));
        }
        if let Some(idx) = self.ivar_env.iter().position(|n| n == &name) {
            self.record_name_pos(&name, line, col, false);
            return Ok(Term::TInterval(I::Var(idx as i32)));
        }
        if let Some(dt_name) = self.find_datatype_candidate(&name) {
            return Ok(Term::TData(dt_name, vec![]));
        }
        if let Some((dt, _)) = self.find_constructor_candidate(&name) {
            return Ok(Term::TCon(dt, name, Vec::new()));
        }
        Err(self.error_here(format!("unknown name or constructor '{}'", name)))
    }

    fn find_constructor(&self, name: &str) -> Option<(Name, bool)> {
        self.find_constructor_arity(name)
            .map(|(dt, interval, _)| (dt, interval))
    }

    /// Like [`Self::find_constructor`], but also reports the constructor's
    /// ordinary-argument count so pattern parsing can consume exactly that many
    /// arguments. Path/square/cell constructors report `interval = true`.
    fn find_constructor_arity(&self, name: &str) -> Option<(Name, bool, usize)> {
        for dt in self.datatypes.iter().rev() {
            if let Some(c) = dt.cons.iter().find(|c| c.name == name) {
                return Some((dt.name.clone(), false, c.arity()));
            }
            if let Some(c) = dt.pcons.iter().find(|c| c.name == name) {
                return Some((dt.name.clone(), true, c.arity()));
            }
            if let Some(c) = dt.sqcons.iter().find(|c| c.name == name) {
                return Some((dt.name.clone(), true, c.arity()));
            }
            if let Some(c) = dt.cellcons.iter().find(|c| c.name == name) {
                return Some((dt.name.clone(), true, c.arity()));
            }
        }
        None
    }

    /// Early completeness check for a `match`: every constructor of the
    /// scrutinee datatype must have a case. The scrutinee datatype is inferred
    /// from the constructor heads; the check is skipped whenever that
    /// inference is unreliable (unknown or conflicting heads, record patterns,
    /// or an empty case list — the empty-type match). The typechecker's
    /// `MissingCase` remains the soundness backstop, so this is purely a
    /// friendlier, earlier error.
    fn check_match_completeness(&self, cases: &[ElimCase]) -> Result<(), ParseError> {
        if cases.is_empty()
            || cases.iter().any(|c| c.record_bindings.is_some())
            || cases.iter().any(|c| c.con.is_empty())
        {
            return Ok(());
        }
        // Infer the scrutinee datatype from the case heads.
        let mut inferred: Option<Name> = None;
        for case in cases {
            match self.find_constructor(&case.con) {
                Some((dt, _)) => {
                    if let Some(prev) = &inferred {
                        if *prev != dt {
                            // Conflicting heads: let the typechecker decide.
                            return Ok(());
                        }
                    } else {
                        inferred = Some(dt);
                    }
                }
                None => return Ok(()), // Unknown head: typechecker's problem.
            }
        }
        let Some(dt_name) = inferred else {
            return Ok(());
        };
        let dt = self
            .datatypes
            .iter()
            .rev()
            .find(|dt| dt.name == dt_name)
            .ok_or_else(|| ParseError {
                message: format!("unknown datatype '{}' in pattern match", dt_name),
                line: 0,
                col: 0,
            })?;
        let names: Vec<Name> = dt
            .cons
            .iter()
            .map(|c| c.name.clone())
            .chain(dt.pcons.iter().map(|c| c.name.clone()))
            .chain(dt.sqcons.iter().map(|c| c.name.clone()))
            .chain(dt.cellcons.iter().map(|c| c.name.clone()))
            .collect();
        for con in names {
            if !cases.iter().any(|c| c.con == con) {
                return Err(ParseError {
                    message: format!("incomplete pattern match: missing case for '{}'", con),
                    line: 0,
                    col: 0,
                });
            }
        }
        Ok(())
    }

    fn is_square_constructor_case(&self, con_name: &str) -> bool {
        self.datatypes
            .iter()
            .rev()
            .any(|dt| dt.sqcons.iter().any(|c| c.name == con_name))
    }

    fn is_cell_constructor_case(&self, con_name: &str) -> Option<usize> {
        self.datatypes
            .iter()
            .rev()
            .find(|dt| dt.cellcons.iter().any(|c| c.name == con_name))
            .and_then(|dt| dt.cellcons.iter().find(|c| c.name == con_name))
            .map(|c| c.dimension())
    }

    fn is_path_constructor(&self, dt_name: &str, con_name: &str) -> bool {
        self.datatypes
            .iter()
            .rev()
            .find(|dt| dt.name == dt_name)
            .is_some_and(|dt| dt.pcons.iter().any(|c| c.name == con_name))
    }

    fn is_square_constructor(&self, dt_name: &str, con_name: &str) -> bool {
        self.datatypes
            .iter()
            .rev()
            .find(|dt| dt.name == dt_name)
            .is_some_and(|dt| dt.sqcons.iter().any(|c| c.name == con_name))
    }

    fn is_cell_constructor(&self, dt_name: &str, con_name: &str) -> Option<usize> {
        self.datatypes
            .iter()
            .rev()
            .find(|dt| dt.name == dt_name)
            .and_then(|dt| dt.cellcons.iter().find(|c| c.name == con_name))
            .map(|c| c.dimension())
    }

    fn is_decl_start(&self) -> bool {
        matches!(
            &self.peek().kind,
            TokenKind::Ident(name)
                if name == "def"
                    || name == "inductive"
                    || name == "record"
                    || name == "import"
                    || name == "module"
                    || name == "end"
                    || name == "postulate"
        )
    }

    fn starts_atom(&self) -> bool {
        if self.is_decl_start() {
            return false;
        }
        if self.stop_at_with
            && let TokenKind::Ident(name) = &self.peek().kind
            && name == "with"
        {
            return false;
        }
        if self.stop_at_in
            && let TokenKind::Ident(name) = &self.peek().kind
            && name == "in"
        {
            return false;
        }
        if self.stop_at_by_wf
            && let TokenKind::Ident(name) = &self.peek().kind
            && name == "by_wf"
        {
            return false;
        }
        if self.stop_at_field
            && let TokenKind::Ident(name) = &self.peek().kind
            && name == "field"
        {
            return false;
        }
        if let TokenKind::Ident(name) = &self.peek().kind
            && name == "return"
        {
            return false;
        }
        matches!(
            &self.peek().kind,
            TokenKind::Ident(_) | TokenKind::Int(_) | TokenKind::LParen | TokenKind::Question
        )
    }

    pub(super) fn expect_ident(&mut self, message: impl Into<String>) -> Result<Name, ParseError> {
        match self.peek().kind.clone() {
            TokenKind::Ident(name) => {
                self.pos += 1;
                Ok(name)
            }
            _ => Err(self.error_here(message)),
        }
    }

    fn expect_string(&mut self, message: impl Into<String>) -> Result<String, ParseError> {
        match self.peek().kind.clone() {
            TokenKind::String(path) => {
                self.pos += 1;
                Ok(path)
            }
            _ => Err(self.error_here(message)),
        }
    }

    pub(super) fn consume_ident(&mut self, expected: &str) -> bool {
        match &self.peek().kind {
            TokenKind::Ident(name) if name == expected => {
                self.pos += 1;
                true
            }
            _ => false,
        }
    }

    /// Consume the current identifier if it matches `expected`.
    pub(super) fn consume_ident_maybe(&mut self, expected: &str) -> bool {
        match &self.peek().kind {
            TokenKind::Ident(name) if name == expected => {
                self.pos += 1;
                true
            }
            _ => false,
        }
    }

    /// Peek at the current identifier without consuming it.
    pub(super) fn peek_ident(&self) -> &str {
        match &self.peek().kind {
            TokenKind::Ident(name) => name,
            _ => "",
        }
    }

    pub(super) fn consume(&mut self, expected: &TokenKind) -> bool {
        if self.at(expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    pub(super) fn expect(
        &mut self,
        expected: TokenKind,
        message: impl Into<String>,
    ) -> Result<(), ParseError> {
        if self.consume(&expected) {
            Ok(())
        } else {
            Err(self.error_here(message))
        }
    }

    pub(super) fn at(&self, expected: &TokenKind) -> bool {
        std::mem::discriminant(&self.peek().kind) == std::mem::discriminant(expected)
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.pos]
    }

    pub(super) fn error_here(&self, message: impl Into<String>) -> ParseError {
        let token = self.peek();
        err(message, token.line, token.col)
    }

    /// Check if the current position looks like `(name : type)` — a parenthesized
    /// binder. Returns true if we see `(` followed by an identifier.
    fn peek_ahead_is_binder(&self) -> bool {
        if self.pos + 1 < self.tokens.len() {
            matches!(&self.tokens[self.pos + 1].kind, TokenKind::Ident(_))
        } else {
            false
        }
    }

    /// Build `isProp A` = `forall (_ : A), forall (_ : A), Path A x y`
    ///
    /// Context depths:  outer A is at depth 0 (type of first binder).
    ///                 inner A is at depth 1 (type of second binder).
    ///                 body `Path A x y` is at depth 2.
    ///                 x = TVar(1), y = TVar(0) at depth 2.
    fn build_isprop(&self, a: Term) -> Term {
        Term::TPi(
            "_".to_string(),
            Arc::new(a.clone()),
            Arc::new(Term::TPi(
                "_".to_string(),
                Arc::new(shift(1, 0, &a)),
                Arc::new(Term::TPath(
                    Arc::new(shift(2, 0, &a)),
                    Arc::new(Term::TVar(1)),
                    Arc::new(Term::TVar(0)),
                )),
                false,
            )),
            false,
        )
    }

    /// Build `isSet A` = `forall (_ : A), forall (_ : A), forall (_ : Path A x y), forall (_ : Path A x y), Path (Path A x y) p q`
    ///
    /// Context depths (outermost first):
    ///   depth 0: x : A            (type of x: A)
    ///   depth 1: y : A            (type of y: A[+1])
    ///   depth 2: p : Path A x y   (type of p: Path A[+2] (TVar@1) (TVar@0))
    ///   depth 3: q : Path A x y   (type of q: Path A[+3] (TVar@2) (TVar@1))
    ///   depth 4: body              (Path (Path A[+4] (TVar@3) (TVar@2)) (TVar@1) (TVar@0))
    fn build_isset(&self, a: Term) -> Term {
        // type of 3rd binder (p): Path A x y, checked at depth 2
        //   A shifted by 2, x = TVar(1), y = TVar(0)
        let ty_p = Term::TPath(
            Arc::new(shift(2, 0, &a)),
            Arc::new(Term::TVar(1)),
            Arc::new(Term::TVar(0)),
        );
        // type of 4th binder (q): Path A x y, checked at depth 3
        //   A shifted by 3, x = TVar(2), y = TVar(1)
        let ty_q = Term::TPath(
            Arc::new(shift(3, 0, &a)),
            Arc::new(Term::TVar(2)),
            Arc::new(Term::TVar(1)),
        );
        // body: Path (Path A x y) p q, checked at depth 4
        //   inner Path A x y: A shifted by 4, x = TVar(3), y = TVar(2)
        //   p = TVar(1), q = TVar(0)
        let inner_path = Term::TPath(
            Arc::new(shift(4, 0, &a)),
            Arc::new(Term::TVar(3)),
            Arc::new(Term::TVar(2)),
        );
        let body = Term::TPath(
            Arc::new(inner_path),
            Arc::new(Term::TVar(1)),
            Arc::new(Term::TVar(0)),
        );
        Term::TPi(
            "_".to_string(),
            Arc::new(a.clone()),
            Arc::new(Term::TPi(
                "_".to_string(),
                Arc::new(shift(1, 0, &a)),
                Arc::new(Term::TPi(
                    "_".to_string(),
                    Arc::new(ty_p),
                    Arc::new(Term::TPi(
                        "_".to_string(),
                        Arc::new(ty_q),
                        Arc::new(body),
                        false,
                    )),
                    false,
                )),
                false,
            )),
            false,
        )
    }

    /// Build `isGroupoid A` = six nested foralls with body Path (Path (Path A x y) p q) r s
    fn build_isgroupoid(&self, a: Term) -> Term {
        // type of p: Path A x y at depth 2
        let ty_p = Term::TPath(
            Arc::new(shift(2, 0, &a)),
            Arc::new(Term::TVar(1)),
            Arc::new(Term::TVar(0)),
        );
        // type of q: Path A x y at depth 3
        let ty_q = Term::TPath(
            Arc::new(shift(3, 0, &a)),
            Arc::new(Term::TVar(2)),
            Arc::new(Term::TVar(1)),
        );
        // type of r: Path (Path A x y) p q at depth 4
        let inner_path_4 = Term::TPath(
            Arc::new(shift(4, 0, &a)),
            Arc::new(Term::TVar(3)),
            Arc::new(Term::TVar(2)),
        );
        let ty_r = Term::TPath(
            Arc::new(inner_path_4),
            Arc::new(Term::TVar(1)),
            Arc::new(Term::TVar(0)),
        );
        // type of s: Path (Path A x y) p q at depth 5
        let inner_path_5 = Term::TPath(
            Arc::new(shift(5, 0, &a)),
            Arc::new(Term::TVar(4)),
            Arc::new(Term::TVar(3)),
        );
        let ty_s = Term::TPath(
            Arc::new(inner_path_5),
            Arc::new(Term::TVar(2)),
            Arc::new(Term::TVar(1)),
        );
        // body: Path (Path (Path A x y) p q) r s at depth 6
        let innermost_path = Term::TPath(
            Arc::new(shift(6, 0, &a)),
            Arc::new(Term::TVar(5)),
            Arc::new(Term::TVar(4)),
        );
        let inner_path_6 = Term::TPath(
            Arc::new(innermost_path),
            Arc::new(Term::TVar(3)),
            Arc::new(Term::TVar(2)),
        );
        let body = Term::TPath(
            Arc::new(inner_path_6),
            Arc::new(Term::TVar(1)),
            Arc::new(Term::TVar(0)),
        );
        Term::TPi(
            "_".to_string(),
            Arc::new(a.clone()),
            Arc::new(Term::TPi(
                "_".to_string(),
                Arc::new(shift(1, 0, &a)),
                Arc::new(Term::TPi(
                    "_".to_string(),
                    Arc::new(ty_p),
                    Arc::new(Term::TPi(
                        "_".to_string(),
                        Arc::new(ty_q),
                        Arc::new(Term::TPi(
                            "_".to_string(),
                            Arc::new(ty_r),
                            Arc::new(Term::TPi(
                                "_".to_string(),
                                Arc::new(ty_s),
                                Arc::new(body),
                                false,
                            )),
                            false,
                        )),
                        false,
                    )),
                    false,
                )),
                false,
            )),
            false,
        )
    }

    /// Build `isNType n A` for arbitrary non-negative `n`.
    ///
    /// Generates `2*(n+1)` nested Pi binders with a nested Path body:
    /// - n=0 (isProp): `forall (_ : A), forall (_ : A), Path A x y`
    /// - n=1 (isSet): 4 foralls, body `Path (Path A x y) p q`
    /// - n=2 (isGroupoid): 6 foralls, body `Path (Path (Path A x y) p q) r s`
    /// - n=k: `2*(k+1)` foralls, body is a `(k+1)`-fold nested Path.
    fn build_isntype(&self, n: u32, a: Term) -> Term {
        let depth = n + 1; // number of Path layers = number of pairs of binders

        // Build the nested Path body.
        // At level k (1..=depth), body at depth 2*k wraps the previous in Path.
        // Reference element vars from the k-th pair: introduced at depths 2*(k-1) and 2*(k-1)+1.
        let mut body: Term = shift(2 * depth as i32, 0, &a);
        for k in 1..=depth {
            let d = 2 * k as i32;
            let left_depth = d - 2; // depth where left element was introduced
            let right_depth = d - 1; // depth where right element was introduced
            // Shift from introduction depth to body depth (2*depth)
            let left = 2 * depth as i32 - 1 - left_depth;
            let right = 2 * depth as i32 - 1 - right_depth;
            body = Term::TPath(
                Arc::new(body),
                Arc::new(Term::TVar(left)),
                Arc::new(Term::TVar(right)),
            );
        }

        // Wrap with 2*depth Pi binders (innermost last).
        // Even position j (element binder): type = A shifted by j
        // Odd position j (path binder): type = Path(A at pair_start, left_var, right_var)
        //   where pair_start = j-1 (the pair's starting depth), and vars are at
        //   pair_start (left) and pair_start+1 (right), shifted to depth j.
        let mut result = body;
        for j in (0..2 * depth).rev() {
            let j_i = j as i32;
            let binder_ty = if j % 2 == 0 {
                // Element binder at depth j
                shift(j_i, 0, &a)
            } else {
                // Path binder: pair starts at depth j-1
                let pair_start = j_i - 1;
                let a_at_pair = shift(pair_start, 0, &a);
                // Left and right element vars introduced at pair_start and pair_start+1
                // Shift to current depth j: shift = j - introduction_depth
                let left = j_i - pair_start; // = 1
                let right = j_i - (pair_start + 1); // = 0
                Term::TPath(
                    Arc::new(a_at_pair),
                    Arc::new(Term::TVar(left)),
                    Arc::new(Term::TVar(right)),
                )
            };
            result = Term::TPi(
                "_".to_string(),
                Arc::new(binder_ty),
                Arc::new(result),
                false,
            );
        }
        result
    }
}

fn parse_universe(name: &str) -> Option<i32> {
    let rest = name.strip_prefix('U')?;
    if rest.is_empty() {
        return None;
    }
    rest.parse::<i32>().ok()
}

/// Parse a level expression: `max l1 l2 | lsuc l | (level_expr) | integer | ident`
impl Parser {
    fn parse_level_expr(&mut self) -> Result<LevelExpr, ParseError> {
        self.parse_level_max()
    }

    fn parse_level_max(&mut self) -> Result<LevelExpr, ParseError> {
        if self.consume_ident("max") {
            let left = self.parse_level_atom()?;
            let right = self.parse_level_max()?;
            return Ok(LevelExpr::LMax(Box::new(left), Box::new(right)));
        }
        self.parse_level_atom()
    }

    fn parse_level_atom(&mut self) -> Result<LevelExpr, ParseError> {
        if self.consume_ident("lsuc") {
            let inner = self.parse_level_atom()?;
            return Ok(LevelExpr::LSuc(Box::new(inner)));
        }
        self.parse_level_base()
    }

    fn parse_level_base(&mut self) -> Result<LevelExpr, ParseError> {
        if self.at(&TokenKind::LParen) {
            self.pos += 1;
            let inner = self.parse_level_expr()?;
            self.expect(TokenKind::RParen, "expected ')' after level expression")?;
            return Ok(inner);
        }
        match self.peek().kind.clone() {
            TokenKind::Int(n) => {
                self.pos += 1;
                Ok(LevelExpr::LConst(n))
            }
            TokenKind::Ident(name) => {
                self.pos += 1;
                // Look up the name in the term environment to get de Bruijn index
                if let Some(idx) = self.term_env.iter().position(|n| n == &name) {
                    Ok(LevelExpr::LVar(idx as i32))
                } else {
                    Err(self.error_here(format!("unknown level variable '{}'", name)))
                }
            }
            other => Err(self.error_here(format!(
                "expected level expression, found {}",
                describe(&other)
            ))),
        }
    }
}

fn expect_interval(term: Term, parser: &Parser) -> Result<I, ParseError> {
    match term {
        Term::TInterval(i) => Ok(i),
        Term::TVar(idx) => Ok(I::Var(idx)),
        other => Err(parser.error_here(format!("expected interval expression, got {:?}", other))),
    }
}

fn interval_binary(
    left: Term,
    right: Term,
    mk: fn(I, I) -> I,
    parser: &Parser,
) -> Result<Term, ParseError> {
    let l = expect_interval(left, parser)?;
    let r = expect_interval(right, parser)?;
    Ok(Term::TInterval(mk(l, r)))
}

fn describe(kind: &TokenKind) -> String {
    match kind {
        TokenKind::Ident(s) => format!("'{}'", s),
        TokenKind::Int(n) => n.to_string(),
        TokenKind::LParen => "'('".to_string(),
        TokenKind::RParen => "')'".to_string(),
        TokenKind::LBrace => "'{'".to_string(),
        TokenKind::RBrace => "'}'".to_string(),
        TokenKind::LAngle => "'<'".to_string(),
        TokenKind::RAngle => "'>'".to_string(),
        TokenKind::Colon => "':'".to_string(),
        TokenKind::ColonEquals => "':='".to_string(),
        TokenKind::Comma => "','".to_string(),
        TokenKind::Dot => "'.'".to_string(),
        TokenKind::Arrow => "'->'".to_string(),
        TokenKind::FatArrow => "'=>'".to_string(),
        TokenKind::Pipe => "'|'".to_string(),
        TokenKind::At => "'@'".to_string(),
        TokenKind::Backslash => "'\\'".to_string(),
        TokenKind::Star => "'*'".to_string(),
        TokenKind::Slash => "'/'".to_string(),
        TokenKind::AndSym => "'/\\'".to_string(),
        TokenKind::OrSym => "'\\/'".to_string(),
        TokenKind::Tilde => "'~'".to_string(),
        TokenKind::LBracket => "'['".to_string(),
        TokenKind::RBracket => "']'".to_string(),
        TokenKind::Equals => "'='".to_string(),
        TokenKind::Semicolon => "';'".to_string(),
        TokenKind::Question => "'?'".to_string(),
        TokenKind::String(s) => format!("\"{}\"", s),
        TokenKind::Eof => "end of input".to_string(),
    }
}

/// Returns true if `name` is a reserved keyword that should NOT be consumed
/// as an optional argument (e.g. the constructor name after `constructor`).
fn is_tactic_keyword(name: &str) -> bool {
    matches!(
        name,
        "exact"
            | "intro"
            | "apply"
            | "assumption"
            | "reflexivity"
            | "symmetry"
            | "split"
            | "constructor"
            | "destruct"
            | "transitivity"
            | "compute"
            | "trivial"
            | "omega"
            | "ring"
            | "field"
            | "group"
            | "eq"
            | "def"
            | "inductive"
            | "record"
            | "import"
            | "module"
            | "end"
            | "match"
            | "return"
            | "with"
            | "fun"
            | "let"
            | "in"
            | "by"
            | "where"
            | "comp"
            | "coe"
            | "fill"
            | "hfill"
            | "hcomp"
            | "PathP"
            | "isProp"
            | "isSet"
            | "isGroupoid"
            | "isNType"
    )
}
