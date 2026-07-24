use std::fmt;

use crate::cubical::syntax::{Name, Term};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    UnboundVariable(Name),
    TypeMismatch(Box<Term>, Box<Term>),
    ExpectedPi(Term),
    ExpectedPath(Term),
    ExpectedUniverse(Term),
    ExpectedEquiv(Term),
    ExpectedSigma(Term),
    NotAnInterval(Term),
    CannotInfer(Term),
    EtaFuelExhausted(Box<Term>, Box<Term>),
    Other(String),
    UnknownDatatype(Name),
    UnknownConstructor(Name, Name),
    WrongNumberOfArgs {
        con: Name,
        expected: usize,
        got: usize,
    },
    BadElimCase {
        con: Name,
        msg: String,
    },
    MissingCase(Name),
    ExpectedData(Term),
    #[allow(dead_code)]
    PathPNotTypeFamily(Term),
}

/// Wrapper that attaches definition context to a TypeError.
#[derive(Debug, Clone)]
pub struct ContextualError {
    pub def_name: Name,
    pub inner: TypeError,
}

impl fmt::Display for ContextualError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "  in definition '{}':", self.def_name)?;
        write!(f, "{}", self.inner)
    }
}

impl From<TypeError> for ContextualError {
    fn from(e: TypeError) -> Self {
        ContextualError {
            def_name: "<unknown>".into(),
            inner: e,
        }
    }
}

impl ContextualError {
    pub fn with_def(name: impl Into<Name>, e: TypeError) -> Self {
        ContextualError {
            def_name: name.into(),
            inner: e,
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnboundVariable(x) => write!(f, "  Unbound variable: '{}'", x),
            TypeError::TypeMismatch(ex, got) => write!(
                f,
                "  Type mismatch\n    expected : {}\n    got      : {}",
                ex, got
            ),
            TypeError::ExpectedPi(ty) => write!(f, "  Expected a Π-type, but found:\n    {}", ty),
            TypeError::ExpectedPath(ty) => {
                write!(f, "  Expected a Path type, but found:\n    {}", ty)
            }
            TypeError::ExpectedUniverse(ty) => {
                write!(f, "  Expected a universe U_n, but found:\n    {}", ty)
            }
            TypeError::ExpectedEquiv(ty) => {
                write!(f, "  Expected an Equiv type, but found:\n    {}", ty)
            }
            TypeError::ExpectedSigma(ty) => {
                write!(f, "  Expected a Σ-type, but found:\n    {}", ty)
            }
            TypeError::NotAnInterval(t) => write!(
                f,
                "  Expected an interval expression (𝕀), but got:\n    {}",
                t
            ),
            TypeError::CannotInfer(t) => write!(
                f,
                "  Cannot infer type of term without annotation:\n    {}\n  \
                     (Tip: use 'check' instead of 'infer', or add a type annotation)",
                t
            ),
            TypeError::EtaFuelExhausted(t1, t2) => write!(
                f,
                "  Eta-expansion fuel exhausted while comparing:\n    {}\n  and\n    {}",
                t1, t2
            ),
            TypeError::Other(msg) => write!(f, "  {}", msg),
            TypeError::UnknownDatatype(name) => {
                write!(f, "  Unknown datatype: '{}'", name)
            }
            TypeError::UnknownConstructor(dt, con) => {
                write!(f, "  Unknown constructor '{}::{}'", dt, con)
            }
            TypeError::WrongNumberOfArgs {
                con,
                expected,
                got,
            } => write!(
                f,
                "  Wrong number of arguments for '{}': expected {}, got {}",
                con, expected, got
            ),
            TypeError::BadElimCase { con, msg } => {
                write!(f, "  Bad case for '{}': {}", con, msg)
            }
            TypeError::MissingCase(con) => {
                write!(f, "  Missing case for constructor '{}'", con)
            }
            TypeError::ExpectedData(ty) => {
                write!(f, "  Expected a data type, but found:\n    {}", ty)
            }
            TypeError::PathPNotTypeFamily(ty) => {
                write!(f, "  PathP requires a type family, but found:\n    {}", ty)
            }
        }
    }
}
