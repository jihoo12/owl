use std::fmt;

use crate::cubical::syntax::{Name, Term, show_term};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    UnboundVariable(Name),
    TypeMismatch {
        expected: Box<Term>,
        got: Box<Term>,
        names: Vec<Name>,
    },
    ExpectedPi {
        ty: Term,
        names: Vec<Name>,
    },
    ExpectedPath {
        ty: Term,
        names: Vec<Name>,
    },
    ExpectedUniverse {
        ty: Term,
        names: Vec<Name>,
    },
    ExpectedEquiv {
        ty: Term,
        names: Vec<Name>,
    },
    ExpectedSigma {
        ty: Term,
        names: Vec<Name>,
    },
    NotAnInterval {
        t: Term,
        names: Vec<Name>,
    },
    CannotInfer {
        t: Term,
        names: Vec<Name>,
    },
    EtaFuelExhausted {
        t1: Box<Term>,
        t2: Box<Term>,
        names: Vec<Name>,
    },
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
    ExpectedData {
        ty: Term,
        names: Vec<Name>,
    },
    #[allow(dead_code)]
    PathPNotTypeFamily {
        ty: Term,
        names: Vec<Name>,
    },
    /// Structural recursion guard check failed.
    TerminationViolation {
        datatype: Name,
        case: Name,
        msg: String,
    },
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
            TypeError::TypeMismatch { expected, got, names } => write!(
                f,
                "  Type mismatch\n    expected : {}\n    got      : {}",
                show_term(names, expected),
                show_term(names, got),
            ),
            TypeError::ExpectedPi { ty, names } => {
                write!(f, "  Expected a Π-type, but found:\n    {}", show_term(names, ty))
            }
            TypeError::ExpectedPath { ty, names } => {
                write!(f, "  Expected a Path type, but found:\n    {}", show_term(names, ty))
            }
            TypeError::ExpectedUniverse { ty, names } => {
                write!(f, "  Expected a universe U_n, but found:\n    {}", show_term(names, ty))
            }
            TypeError::ExpectedEquiv { ty, names } => {
                write!(f, "  Expected an Equiv type, but found:\n    {}", show_term(names, ty))
            }
            TypeError::ExpectedSigma { ty, names } => {
                write!(f, "  Expected a Σ-type, but found:\n    {}", show_term(names, ty))
            }
            TypeError::NotAnInterval { t, names } => write!(
                f,
                "  Expected an interval expression (𝕀), but got:\n    {}",
                show_term(names, t),
            ),
            TypeError::CannotInfer { t, names } => write!(
                f,
                "  Cannot infer type of term without annotation:\n    {}\n  \
                     (Tip: use 'check' instead of 'infer', or add a type annotation)",
                show_term(names, t),
            ),
            TypeError::EtaFuelExhausted { t1, t2, names } => write!(
                f,
                "  Eta-expansion fuel exhausted while comparing:\n    {}\n  and\n    {}",
                show_term(names, t1),
                show_term(names, t2),
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
            TypeError::ExpectedData { ty, names } => {
                write!(f, "  Expected a data type, but found:\n    {}", show_term(names, ty))
            }
            TypeError::PathPNotTypeFamily { ty, names } => {
                write!(f, "  PathP requires a type family, but found:\n    {}", show_term(names, ty))
            }
            TypeError::TerminationViolation { datatype, case, msg } => {
                write!(
                    f,
                    "  Termination violation in '{}' case of '{}':\n    {}",
                    case, datatype, msg
                )
            }
        }
    }
}
