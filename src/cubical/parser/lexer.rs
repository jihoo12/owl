//! Lexer: turns source text into a flat token stream for the [`Parser`](crate::cubical::parser::grammar::Parser).

use super::ParseError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum TokenKind {
    Ident(String),
    Int(i32),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LAngle,
    RAngle,
    Colon,
    /// Lean-style definition separator (`:=`).
    ColonEquals,
    Comma,
    Dot,
    Arrow,
    FatArrow,
    Pipe,
    At,
    Backslash,
    Star,
    Slash,
    AndSym,
    OrSym,
    Tilde,
    LBracket,
    RBracket,
    Equals,
    Semicolon,
    String(String),
    Eof,
}

#[derive(Debug, Clone)]
pub(super) struct Token {
    pub(super) kind: TokenKind,
    pub(super) line: usize,
    pub(super) col: usize,
}

pub(super) struct Lexer<'a> {
    chars: std::str::Chars<'a>,
    peeked: Option<char>,
    line: usize,
    col: usize,
}

impl<'a> Lexer<'a> {
    pub(super) fn new(src: &'a str) -> Self {
        Self {
            chars: src.chars(),
            peeked: None,
            line: 1,
            col: 1,
        }
    }

    pub(super) fn lex(mut self) -> Result<Vec<Token>, ParseError> {
        let mut tokens = Vec::new();
        while let Some(ch) = self.peek() {
            let line = self.line;
            let col = self.col;
            match ch {
                c if c.is_whitespace() => {
                    self.bump();
                }
                '-' => {
                    self.bump();
                    if self.peek() == Some('-') {
                        while let Some(c) = self.peek() {
                            self.bump();
                            if c == '\n' {
                                break;
                            }
                        }
                    } else if self.peek() == Some('>') {
                        self.bump();
                        tokens.push(tok(TokenKind::Arrow, line, col));
                    } else {
                        return Err(err("unexpected '-'", line, col));
                    }
                }
                '=' => {
                    self.bump();
                    if self.peek() == Some('>') {
                        self.bump();
                        tokens.push(tok(TokenKind::FatArrow, line, col));
                    } else {
                        tokens.push(tok(TokenKind::Equals, line, col));
                    }
                }
                '/' => {
                    self.bump();
                    if self.peek() == Some('\\') {
                        self.bump();
                        tokens.push(tok(TokenKind::AndSym, line, col));
                    } else {
                        tokens.push(tok(TokenKind::Slash, line, col));
                    }
                }
                '\\' => {
                    self.bump();
                    if self.peek() == Some('/') {
                        self.bump();
                        tokens.push(tok(TokenKind::OrSym, line, col));
                    } else {
                        tokens.push(tok(TokenKind::Backslash, line, col));
                    }
                }
                '(' => {
                    self.bump();
                    tokens.push(tok(TokenKind::LParen, line, col));
                }
                ')' => {
                    self.bump();
                    tokens.push(tok(TokenKind::RParen, line, col));
                }
                '{' => {
                    self.bump();
                    tokens.push(tok(TokenKind::LBrace, line, col));
                }
                '}' => {
                    self.bump();
                    tokens.push(tok(TokenKind::RBrace, line, col));
                }
                '<' | '⟨' => {
                    self.bump();
                    tokens.push(tok(TokenKind::LAngle, line, col));
                }
                '>' | '⟩' => {
                    self.bump();
                    tokens.push(tok(TokenKind::RAngle, line, col));
                }
                ':' => {
                    self.bump();
                    if self.peek() == Some('=') {
                        self.bump();
                        tokens.push(tok(TokenKind::ColonEquals, line, col));
                    } else {
                        tokens.push(tok(TokenKind::Colon, line, col));
                    }
                }
                ',' => {
                    self.bump();
                    tokens.push(tok(TokenKind::Comma, line, col));
                }
                ';' => {
                    self.bump();
                    tokens.push(tok(TokenKind::Semicolon, line, col));
                }
                '.' => {
                    self.bump();
                    tokens.push(tok(TokenKind::Dot, line, col));
                }
                '|' => {
                    self.bump();
                    tokens.push(tok(TokenKind::Pipe, line, col));
                }
                '@' => {
                    self.bump();
                    tokens.push(tok(TokenKind::At, line, col));
                }
                '*' | '×' => {
                    self.bump();
                    tokens.push(tok(TokenKind::Star, line, col));
                }
                '[' => {
                    self.bump();
                    tokens.push(tok(TokenKind::LBracket, line, col));
                }
                ']' => {
                    self.bump();
                    tokens.push(tok(TokenKind::RBracket, line, col));
                }
                '~' | '¬' => {
                    self.bump();
                    tokens.push(tok(TokenKind::Tilde, line, col));
                }
                '∧' => {
                    self.bump();
                    tokens.push(tok(TokenKind::AndSym, line, col));
                }
                '∨' => {
                    self.bump();
                    tokens.push(tok(TokenKind::OrSym, line, col));
                }
                // These binders are identifiers so the grammar can handle
                // their binding structure without a separate token family.
                '∀' | 'Σ' => {
                    self.bump();
                    tokens.push(tok(TokenKind::Ident(ch.to_string()), line, col));
                }
                '"' => tokens.push(self.lex_string(line, col)?),
                c if c.is_ascii_digit() => tokens.push(self.lex_int(line, col)?),
                c if is_ident_start(c) => tokens.push(self.lex_ident(line, col)),
                other => return Err(err(format!("unexpected character '{}'", other), line, col)),
            }
        }
        tokens.push(tok(TokenKind::Eof, self.line, self.col));
        Ok(tokens)
    }

    fn lex_int(&mut self, line: usize, col: usize) -> Result<Token, ParseError> {
        let mut text = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                text.push(c);
                self.bump();
            } else {
                break;
            }
        }
        match text.parse::<i32>() {
            Ok(n) => Ok(tok(TokenKind::Int(n), line, col)),
            Err(_) => Err(err("integer literal is too large", line, col)),
        }
    }

    fn lex_ident(&mut self, line: usize, col: usize) -> Token {
        let mut text = String::new();
        while let Some(c) = self.peek() {
            if is_ident_continue(c) {
                text.push(c);
                self.bump();
            } else {
                break;
            }
        }
        tok(TokenKind::Ident(text), line, col)
    }

    fn lex_string(&mut self, line: usize, col: usize) -> Result<Token, ParseError> {
        self.bump(); // opening "
        let mut text = String::new();
        while let Some(c) = self.peek() {
            match c {
                '"' => {
                    self.bump();
                    return Ok(tok(TokenKind::String(text), line, col));
                }
                '\\' => {
                    self.bump();
                    match self.peek() {
                        Some('"') => {
                            self.bump();
                            text.push('"');
                        }
                        Some('\\') => {
                            self.bump();
                            text.push('\\');
                        }
                        Some(other) => {
                            return Err(err(
                                format!("invalid escape sequence '\\{}'", other),
                                self.line,
                                self.col,
                            ));
                        }
                        None => {
                            return Err(err("unterminated string literal", line, col));
                        }
                    }
                }
                '\n' => {
                    return Err(err("unterminated string literal", line, col));
                }
                other => {
                    text.push(other);
                    self.bump();
                }
            }
        }
        Err(err("unterminated string literal", line, col))
    }

    fn peek(&mut self) -> Option<char> {
        if self.peeked.is_none() {
            self.peeked = self.chars.next();
        }
        self.peeked
    }

    fn bump(&mut self) -> Option<char> {
        let ch = match self.peeked.take() {
            Some(c) => Some(c),
            None => self.chars.next(),
        }?;
        if ch == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(ch)
    }
}

pub(super) fn is_ident_start(c: char) -> bool {
    c == '_' || c.is_alphabetic()
}

pub(super) fn is_ident_continue(c: char) -> bool {
    c == '_' || c == '\'' || c == '?' || c == '!' || c == '-' || c.is_alphanumeric()
}

pub(super) fn tok(kind: TokenKind, line: usize, col: usize) -> Token {
    Token { kind, line, col }
}

pub(super) fn err(message: impl Into<String>, line: usize, col: usize) -> ParseError {
    ParseError {
        message: message.into(),
        line,
        col,
    }
}
