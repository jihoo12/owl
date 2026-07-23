//! Recursive-descent parser: consumes the [`Token`] stream produced by the
//! [`Lexer`](super::lexer::Lexer) and builds [`Term`]s / [`Decl`]s, resolving
//! variables to de Bruijn indices along the way.

use super::lexer::{err, Token, TokenKind};
use super::{Decl, ParseError};
use crate::cubical::interval::I;
use crate::cubical::syntax::{ConSig, Datatype, ElimCase, Name, PConSig, Tactic, Term};

pub(super) struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    pub(super) term_env: Vec<Name>,
    pub(super) ivar_env: Vec<Name>,
    pub(super) global_env: Vec<Name>,
    pub(super) datatypes: Vec<Datatype>,
    /// When true, `starts_atom` treats the keyword `with` as a stop token.
    stop_at_with: bool,
    /// When true, `starts_atom` treats the keyword `in` as a stop token.
    stop_at_in: bool,
}

impl Parser {
    pub(super) fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            pos: 0,
            term_env: Vec::new(),
            ivar_env: Vec::new(),
            global_env: Vec::new(),
            datatypes: Vec::new(),
            stop_at_with: false,
            stop_at_in: false,
        }
    }

    pub(super) fn parse_import(&mut self) -> Result<Decl, ParseError> {
        let path = self.expect_string("expected string literal after 'import'")?;
        Ok(Decl::Import { path })
    }

    pub(super) fn parse_def(&mut self) -> Result<Decl, ParseError> {
        let name = self.expect_ident("expected definition name")?;
        self.expect(
            TokenKind::Colon,
            format!("expected ':' after definition name '{}'", name),
        )?;
        let ty = self.parse_term()?;
        self.expect_definition_value(&name)?;
        // Allow the definition body to refer to itself (and later globals).
        self.global_env.insert(0, name.clone());
        let val = self.parse_term()?;
        Ok(Decl::Def { name, ty, val })
    }

    pub(super) fn parse_data_decl(&mut self) -> Result<Decl, ParseError> {
        let name = self.expect_ident("expected datatype name")?;

        // Optional universe annotation: `data D : U_n = ...`
        let mut uni_level: Option<i32> = None;
        if self.consume(&TokenKind::Colon) {
            let uni_name = self.expect_ident("expected universe level after ':'")?;
            uni_level = Some(parse_universe(&uni_name).ok_or_else(|| {
                self.error_here(format!(
                    "expected universe level (e.g. U0, U1) after ':', got '{}'",
                    uni_name
                ))
            })?);
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
        let mut local_dt = Datatype {
            name: name.clone(),
            cons: Vec::new(),
            pcons: Vec::new(),
            universe_level: None,
        };
        while self.consume(&TokenKind::Pipe) {
            let con_name = self.expect_ident("expected constructor name after '|'")?;
            self.expect(
                TokenKind::Colon,
                format!("expected ':' after constructor name '{}'", con_name),
            )?;
            let (arg_tys, result) = self.parse_constructor_type(&name, &local_dt)?;
            if result != Term::TData(name.clone()) {
                return Err(self.error_here(format!(
                    "constructor '{}' must return datatype '{}'",
                    con_name, name
                )));
            }
            if self.consume(&TokenKind::LBracket) {
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
                let sig = PConSig {
                    name: con_name,
                    arg_tys,
                    face0,
                    face1,
                };
                local_dt.pcons.push(sig.clone());
                pcons.push(sig);
            } else {
                let sig = ConSig {
                    name: con_name,
                    arg_tys,
                };
                local_dt.cons.push(sig.clone());
                cons.push(sig);
            }
        }
        if cons.is_empty() && pcons.is_empty() {
            return Err(self.error_here(format!(
                "datatype '{}' must declare at least one constructor",
                name
            )));
        }
        Ok(Decl::Data(Datatype { name, cons, pcons, universe_level: uni_level }))
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
        loop {
            match cur {
                Term::TPi(_, a, b) => {
                    args.push(*a);
                    cur = *b;
                }
                Term::TData(ref n) if n == dt_name => return Ok((args, cur)),
                other => return Ok((args, other)),
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
                term = Term::TAbs(binder, Box::new(term));
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
            return Ok(Term::PLam(binder, Box::new(body)));
        }
        if self.consume_ident("∀") || self.consume_ident("forall") {
            let (binder, ty) = self.parse_parenthesized_binder("Pi")?;
            self.expect_binder_separator("Pi")?;
            self.term_env.insert(0, binder.clone());
            let body = self.parse_term()?;
            self.term_env.remove(0);
            return Ok(Term::TPi(binder, Box::new(ty), Box::new(body)));
        }
        if self.consume_ident("Σ") {
            let (binder, ty) = self.parse_parenthesized_binder("Sigma")?;
            self.expect_binder_separator("Sigma")?;
            self.term_env.insert(0, binder.clone());
            let body = self.parse_term()?;
            self.term_env.remove(0);
            return Ok(Term::TSigma(binder, Box::new(ty), Box::new(body)));
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
            Box::new(Term::TAbs(binder, Box::new(body))),
            Box::new(value),
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
                    TokenKind::Ident(ref name) if !is_tactic_keyword(name) =>
                    {
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
        Err(self.error_here("expected tactic: 'exact', 'intro', 'apply', 'assumption', 'reflexivity', 'symmetry', 'split', 'constructor', 'destruct', 'transitivity', 'compute', or 'trivial'"))
    }

    fn parse_pair(&mut self) -> Result<Term, ParseError> {
        let left = self.parse_arrow()?;
        if self.consume(&TokenKind::Comma) {
            let right = self.parse_term()?;
            Ok(Term::TPair(Box::new(left), Box::new(right)))
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
            let right = self.parse_arrow()?;
            self.term_env.remove(0);
            Ok(Term::TPi("_".to_string(), Box::new(left), Box::new(right)))
        } else {
            Ok(left)
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
                Box::new(left),
                Box::new(right),
            ))
        } else {
            Ok(left)
        }
    }

    fn parse_join(&mut self) -> Result<Term, ParseError> {
        let mut term = self.parse_meet()?;
        while self.consume(&TokenKind::OrSym) {
            let rhs = self.parse_meet()?;
            term = interval_binary(term, rhs, |a, b| I::Join(Box::new(a), Box::new(b)), self)?;
        }
        Ok(term)
    }

    fn parse_meet(&mut self) -> Result<Term, ParseError> {
        let mut term = self.parse_tilde()?;
        while self.consume(&TokenKind::AndSym) {
            let rhs = self.parse_tilde()?;
            term = interval_binary(term, rhs, |a, b| I::Meet(Box::new(a), Box::new(b)), self)?;
        }
        Ok(term)
    }

    fn parse_tilde(&mut self) -> Result<Term, ParseError> {
        if self.consume(&TokenKind::Tilde) {
            let term = self.parse_tilde()?;
            let i = expect_interval(term, self)?;
            Ok(Term::TInterval(I::Neg(Box::new(i))))
        } else {
            self.parse_papp()
        }
    }

    fn parse_papp(&mut self) -> Result<Term, ParseError> {
        let mut term = self.parse_app()?;
        while self.consume(&TokenKind::At) {
            let rhs = self.parse_tilde()?;
            if let Term::TCon(dt, con, args) = term {
                if self.is_path_constructor(&dt, &con) {
                    term = Term::TPCon(dt, con, args, Box::new(rhs));
                } else {
                    term = Term::PApp(Box::new(Term::TCon(dt, con, args)), Box::new(rhs));
                }
            } else {
                term = Term::PApp(Box::new(term), Box::new(rhs));
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
        let mut term = first;
        for arg in args {
            term = Term::TApp(Box::new(term), Box::new(arg));
        }
        Ok(term)
    }

    fn parse_prefix_or_atom(&mut self) -> Result<Term, ParseError> {
        if self.consume_ident("fst") {
            return Ok(Term::TFst(Box::new(self.parse_prefix_or_atom()?)));
        }
        if self.consume_ident("snd") {
            return Ok(Term::TSnd(Box::new(self.parse_prefix_or_atom()?)));
        }
        if self.consume_ident("ua") {
            return Ok(Term::TUa(Box::new(self.parse_prefix_or_atom()?)));
        }
        if self.consume_ident("transport") {
            let p = self.parse_prefix_or_atom()?;
            let x = self.parse_prefix_or_atom()?;
            return Ok(Term::TTransport(Box::new(p), Box::new(x)));
        }
        if self.consume_ident("equivFwd") {
            let e = self.parse_prefix_or_atom()?;
            let x = self.parse_prefix_or_atom()?;
            return Ok(Term::TEquivFwd(Box::new(e), Box::new(x)));
        }
        self.parse_atom()
    }

    fn parse_atom(&mut self) -> Result<Term, ParseError> {
        if self.consume_ident("Path") {
            let a = self.parse_prefix_or_atom()?;
            let u = self.parse_prefix_or_atom()?;
            let v = self.parse_prefix_or_atom()?;
            return Ok(Term::TPath(Box::new(a), Box::new(u), Box::new(v)));
        }
        if self.consume_ident("PathP") {
            let a = self.parse_prefix_or_atom()?;
            let u = self.parse_prefix_or_atom()?;
            let v = self.parse_prefix_or_atom()?;
            return Ok(Term::TPath(Box::new(a), Box::new(u), Box::new(v)));
        }
        if self.consume_ident("hcomp") {
            let a = self.parse_prefix_or_atom()?;
            let phi = self.parse_prefix_or_atom()?;
            let u = self.parse_prefix_or_atom()?;
            let u0 = self.parse_prefix_or_atom()?;
            return Ok(Term::THComp(
                Box::new(a),
                Box::new(phi),
                Box::new(u),
                Box::new(u0),
            ));
        }
        if self.consume_ident("comp") {
            let a = self.parse_prefix_or_atom()?;
            let phi = self.parse_prefix_or_atom()?;
            let u = self.parse_prefix_or_atom()?;
            let u0 = self.parse_prefix_or_atom()?;
            return Ok(Term::TComp(
                Box::new(a),
                Box::new(phi),
                Box::new(u),
                Box::new(u0),
            ));
        }
        if self.consume_ident("fill") {
            let a = self.parse_prefix_or_atom()?;
            let phi = self.parse_prefix_or_atom()?;
            let u = self.parse_prefix_or_atom()?;
            let u0 = self.parse_prefix_or_atom()?;
            return Ok(Term::TFill(
                Box::new(a),
                Box::new(phi),
                Box::new(u),
                Box::new(u0),
            ));
        }
        if self.consume_ident("hfill") {
            let a = self.parse_prefix_or_atom()?;
            let phi = self.parse_prefix_or_atom()?;
            let u = self.parse_prefix_or_atom()?;
            let u0 = self.parse_prefix_or_atom()?;
            return Ok(Term::THFill(
                Box::new(a),
                Box::new(phi),
                Box::new(u),
                Box::new(u0),
            ));
        }
        if self.consume_ident("Equiv") {
            let a = self.parse_prefix_or_atom()?;
            let b = self.parse_prefix_or_atom()?;
            return Ok(Term::TEquiv(Box::new(a), Box::new(b)));
        }
        if self.consume_ident("mkEquiv") {
            let a = self.parse_prefix_or_atom()?;
            let b = self.parse_prefix_or_atom()?;
            let f = self.parse_prefix_or_atom()?;
            let g = self.parse_prefix_or_atom()?;
            let eta = self.parse_prefix_or_atom()?;
            let eps = self.parse_prefix_or_atom()?;
            return Ok(Term::TMkEquiv(
                Box::new(a),
                Box::new(b),
                Box::new(f),
                Box::new(g),
                Box::new(eta),
                Box::new(eps),
            ));
        }
        if self.consume_ident("Glue") {
            let a = self.parse_prefix_or_atom()?;
            let phi = self.parse_prefix_or_atom()?;
            let te = self.parse_prefix_or_atom()?;
            return Ok(Term::TGlue(Box::new(a), Box::new(phi), Box::new(te)));
        }
        if self.consume_ident("glueElem") || self.consume_ident("glue") {
            let phi = self.parse_prefix_or_atom()?;
            let t = self.parse_prefix_or_atom()?;
            let a = self.parse_prefix_or_atom()?;
            return Ok(Term::TGlueElem(Box::new(phi), Box::new(t), Box::new(a)));
        }
        if self.consume_ident("unglue") {
            let phi = self.parse_prefix_or_atom()?;
            let te = self.parse_prefix_or_atom()?;
            let g = self.parse_prefix_or_atom()?;
            return Ok(Term::TUnglue(Box::new(phi), Box::new(te), Box::new(g)));
        }
        if self.consume_ident("match") {
            return self.parse_match();
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

    fn parse_paren(&mut self) -> Result<Term, ParseError> {
        self.expect(TokenKind::LParen, "expected '('")?;
        if let Some((names, ty)) = self.try_parse_binder_header()? {
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
                        return Err(self.error_here("expected binder name after '('") );
                    }
                    if let Err(error) = self.expect(TokenKind::Colon, "expected ':' in typed lambda binder") {
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
                    if let Err(error) = self.expect(TokenKind::RParen, "unmatched '(' in lambda binder") {
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
        let cases = self.parse_match_cases()?;
        let motive = Term::TAbs(binder, Box::new(return_type));
        Ok(Term::TElim(Box::new(motive), cases, Box::new(scrutinee)))
    }

    /// Parse the `| constructor binders => body` arms of a `match`.
    fn parse_match_cases(&mut self) -> Result<Vec<ElimCase>, ParseError> {
        if !self.at(&TokenKind::Pipe) {
            return Err(self.error_here("expected '|' before match cases"));
        }

        let mut cases = Vec::new();
        self.consume(&TokenKind::Pipe);
        loop {
            let con = self.expect_ident("expected constructor name in eliminator case")?;
            let mut binders = Vec::new();
            while let TokenKind::Ident(name) = self.peek().kind.clone() {
                if name == "=>" {
                    break;
                }
                self.pos += 1;
                binders.push(name);
            }
            if self.consume(&TokenKind::FatArrow) || self.consume(&TokenKind::Arrow) {
                                // Determine if this is a path constructor: if so, the last
                // binder is the interval variable and should go into ivar_env.
                let is_path_con = self
                    .find_constructor(&con)
                    .is_some_and(|(_, is_path)| is_path);
                let (ord_binders, ivar_binder) = if is_path_con && !binders.is_empty() {
                    let split = binders.len() - 1;
                    (&binders[..split], Some(&binders[split]))
                } else {
                    (&binders[..], None)
                };
                for binder in ord_binders.iter().rev() {
                    self.term_env.insert(0, binder.clone());
                }
                if let Some(iv) = ivar_binder {
                    self.ivar_env.insert(0, iv.clone());
                    self.term_env.insert(0, "".to_string());
                }
                let body = self.parse_term()?;
                for _ in ord_binders {
                    self.term_env.remove(0);
                }
                if ivar_binder.is_some() {
                    self.term_env.remove(0);
                    self.ivar_env.remove(0);
                }
                cases.push(ElimCase {
                    con,
                    binders,
                    body: Box::new(body),
                });
            } else {
                return Err(self.error_here("expected '=>' after eliminator case binders"));
            }
            if !self.consume(&TokenKind::Pipe) {
                break;
            }
        }

        Ok(cases)
    }

    fn resolve_ident(&self, name: Name) -> Result<Term, ParseError> {
        if name == "Type" {
            return Ok(Term::TUniv(0));
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
            return Ok(Term::TUniv(level));
        }
        if let Some(idx) = self.term_env.iter().position(|n| n == &name) {
            return Ok(Term::TVar(idx as i32));
        }
        if let Some(idx) = self.global_env.iter().position(|n| n == &name) {
            return Ok(Term::TVar((self.term_env.len() + idx) as i32));
        }
        if let Some(idx) = self.ivar_env.iter().position(|n| n == &name) {
            return Ok(Term::TInterval(I::Var(idx as i32)));
        }
        if let Some((dt, is_path)) = self.find_constructor(&name) {
            if is_path {
                return Ok(Term::TCon(dt, name, Vec::new()));
            }
            return Ok(Term::TCon(dt, name, Vec::new()));
        }
        if self.datatypes.iter().any(|dt| dt.name == name) {
            return Ok(Term::TData(name));
        }
        Err(self.error_here(format!("unknown name or constructor '{}'", name)))
    }

    fn find_constructor(&self, name: &str) -> Option<(Name, bool)> {
        for dt in self.datatypes.iter().rev() {
            if dt.cons.iter().any(|c| c.name == name) {
                return Some((dt.name.clone(), false));
            }
            if dt.pcons.iter().any(|c| c.name == name) {
                return Some((dt.name.clone(), true));
            }
        }
        None
    }

    fn is_path_constructor(&self, dt_name: &str, con_name: &str) -> bool {
        self.datatypes
            .iter()
            .rev()
            .find(|dt| dt.name == dt_name)
            .is_some_and(|dt| dt.pcons.iter().any(|c| c.name == con_name))
    }

    fn is_decl_start(&self) -> bool {
        matches!(
            &self.peek().kind,
            TokenKind::Ident(name) if name == "def" || name == "inductive" || name == "import"
        )
    }

    fn starts_atom(&self) -> bool {
        if self.is_decl_start() {
            return false;
        }
        if self.stop_at_with
            && let TokenKind::Ident(name) = &self.peek().kind
                && name == "with" {
                    return false;
                }
        if self.stop_at_in
            && let TokenKind::Ident(name) = &self.peek().kind
                && name == "in" {
                    return false;
                }
        matches!(
            &self.peek().kind,
            TokenKind::Ident(_) | TokenKind::Int(_) | TokenKind::LParen
        )
    }

    fn expect_ident(&mut self, message: impl Into<String>) -> Result<Name, ParseError> {
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

    fn consume(&mut self, expected: &TokenKind) -> bool {
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
}

fn parse_universe(name: &str) -> Option<i32> {
    let rest = name.strip_prefix('U')?;
    if rest.is_empty() {
        return None;
    }
    rest.parse::<i32>().ok()
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
            | "def"
            | "inductive"
            | "import"
            | "match"
            | "return"
            | "with"
            | "fun"
            | "let"
            | "in"
            | "by"
            | "where"
            | "comp"
            | "fill"
            | "hfill"
            | "hcomp"
            | "PathP"
    )
}
