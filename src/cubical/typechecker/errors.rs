use std::fmt;

use super::Ctx;
use crate::cubical::syntax::{Name, Term, show_term};

/// A 1-based source position (line, column).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pos {
    pub line: usize,
    pub col: usize,
}

// Names observed by the parser in the current top-level declaration, in
// source order: `(name, source position, is_introduction)`. `is_introduction`
// is true for definition names and false for variable uses. The driver
// accumulates these tables across the whole program and installs them before
// typechecking each declaration, so type errors can point back to the source
// location of the offending variable.
// (Now stored in Session — use session.set/clear_decl_name_positions directly.)

/// The de Bruijn index of the most-local variable occurrence in `t`
/// (smallest index, leftmost pre-order).
fn head_var_idx(t: &Term) -> Option<i32> {
    fn go(t: &Term, best: &mut Option<i32>) {
        match t {
            Term::TVar(i) => {
                *best = Some(match *best {
                    Some(b) => (*i).min(b),
                    None => *i,
                });
            }
            Term::TApp(a, b) => {
                go(a, best);
                go(b, best);
            }
            Term::TAbs(_, b) => go(b, best),
            Term::TLift(a, _) => go(a, best),
            Term::TLower(a) => go(a, best),
            Term::TPi(_, a, b, _) => {
                go(a, best);
                go(b, best);
            }
            Term::TPath(a, u, v) => {
                go(a, best);
                go(u, best);
                go(v, best);
            }
            Term::TId(a, u, v) => {
                go(a, best);
                go(u, best);
                go(v, best);
            }
            Term::TRefl(a) => go(a, best),
            Term::TJ(motive, base, p) => {
                go(motive, best);
                go(base, best);
                go(p, best);
            }
            Term::PLam(_, b) => go(b, best),
            Term::PApp(a, b) => {
                go(a, best);
                go(b, best);
            }
            Term::THComp(a, sys, c)
            | Term::TComp(a, sys, c)
            | Term::TFill(a, sys, c)
            | Term::THFill(a, sys, c) => {
                go(a, best);
                for (phi, tube) in sys {
                    go(phi, best);
                    go(tube, best);
                }
                go(c, best);
            }
            Term::TEquiv(a, b) => {
                go(a, best);
                go(b, best);
            }
            Term::TMkEquiv(a, b, c, d, e, f) => {
                go(a, best);
                go(b, best);
                go(c, best);
                go(d, best);
                go(e, best);
                go(f, best);
            }
            Term::TEquivFwd(a, b) => {
                go(a, best);
                go(b, best);
            }
            Term::TUa(a) => go(a, best),
            Term::TTransport(a, b) => {
                go(a, best);
                go(b, best);
            }
            Term::TTransp(a, r, x) => {
                go(a, best);
                go(r, best);
                go(x, best);
            }
            Term::TGlue(a, b, c) => {
                go(a, best);
                go(b, best);
                go(c, best);
            }
            Term::TGlueElem(a, b, c) => {
                go(a, best);
                go(b, best);
                go(c, best);
            }
            Term::TUnglue(a, b, c) => {
                go(a, best);
                go(b, best);
                go(c, best);
            }
            Term::TPartial(a, b) => {
                go(a, best);
                go(b, best);
            }
            Term::TSystemType(sys) => {
                for (phi, tube) in sys {
                    go(phi, best);
                    go(tube, best);
                }
            }
            Term::TSigma(_, a, b) => {
                go(a, best);
                go(b, best);
            }
            Term::TPair(a, b) => {
                go(a, best);
                go(b, best);
            }
            Term::TFst(a) | Term::TSnd(a) | Term::TDelay(a) | Term::TNext(a) | Term::TForce(a) => {
                go(a, best);
            }
            Term::TData(_, args) => {
                for a in args {
                    go(a, best);
                }
            }
            Term::TCon(_, _, args) => {
                for a in args {
                    go(a, best);
                }
            }
            Term::TPCon(_, _, args, r) => {
                for a in args {
                    go(a, best);
                }
                go(r, best);
            }
            Term::TSqCon(_, _, args, r, s) => {
                for a in args {
                    go(a, best);
                }
                go(r, best);
                go(s, best);
            }
            Term::TCellCon(_, _, args, ivars) => {
                for a in args {
                    go(a, best);
                }
                for i in ivars {
                    go(i, best);
                }
            }
            Term::TElim(motive, cases, scrut) => {
                go(motive, best);
                for case in cases {
                    go(&case.body, best);
                }
                go(scrut, best);
            }
            Term::TProj(_, rec) => go(rec, best),
            Term::TRecordUpdate(rec, fields) => {
                go(rec, best);
                for (_, v) in fields {
                    go(v, best);
                }
            }
            // Leaf or non-term-containing forms: TVar covered above, the rest
            // carry no ordinary variables.
            Term::TUniv(_)
            | Term::TProp
            | Term::TSSet
            | Term::TLevelTy
            | Term::TIntervalTy
            | Term::TInterval(_)
            | Term::TCube(_)
            | Term::Meta(_)
            | Term::TBy(_) => {}
        }
    }
    let mut best = None;
    go(t, &mut best);
    best
}

/// Resolve the source position of the most-local variable in `t`, using the
/// parser-observed name table for the current declaration.
pub fn err_pos(ctx: &Ctx, t: &Term, session: &crate::cubical::session::Session) -> Option<Pos> {
    let idx = head_var_idx(t)?;
    let name = ctx.get(idx as usize)?.0.clone();
    session.with_decl_name_positions(|table| {
        table
            .iter()
            .rev()
            .find(|(n, _, _)| *n == name)
            .map(|(_, p, _)| *p)
    })
}

fn write_pos(f: &mut fmt::Formatter<'_>, pos: Option<Pos>) -> fmt::Result {
    if let Some(pos) = pos {
        writeln!(f, "  at {}:{}", pos.line, pos.col)?;
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    UnboundVariable(Name),
    TypeMismatch {
        expected: Box<Term>,
        got: Box<Term>,
        names: Vec<Name>,
        pos: Option<Pos>,
    },
    ExpectedPi {
        ty: Term,
        names: Vec<Name>,
        pos: Option<Pos>,
    },
    ExpectedPath {
        ty: Term,
        names: Vec<Name>,
        pos: Option<Pos>,
    },
    ExpectedUniverse {
        ty: Term,
        names: Vec<Name>,
        pos: Option<Pos>,
    },
    ExpectedEquiv {
        ty: Term,
        names: Vec<Name>,
        pos: Option<Pos>,
    },
    ExpectedSigma {
        ty: Term,
        names: Vec<Name>,
        pos: Option<Pos>,
    },
    NotAnInterval {
        t: Term,
        names: Vec<Name>,
        pos: Option<Pos>,
    },
    CannotInfer {
        t: Term,
        names: Vec<Name>,
        pos: Option<Pos>,
    },
    EtaFuelExhausted {
        t1: Box<Term>,
        t2: Box<Term>,
        names: Vec<Name>,
        pos: Option<Pos>,
    },
    Other(String),
    UnknownDatatype {
        name: Name,
        pos: Option<Pos>,
    },
    UnknownConstructor {
        datatype: Name,
        con: Name,
        pos: Option<Pos>,
    },
    WrongNumberOfArgs {
        con: Name,
        expected: usize,
        got: usize,
        pos: Option<Pos>,
    },
    BadElimCase {
        con: Name,
        msg: String,
        pos: Option<Pos>,
    },
    MissingCase {
        con: Name,
        pos: Option<Pos>,
    },
    ExpectedData {
        ty: Term,
        names: Vec<Name>,
        pos: Option<Pos>,
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
        pos: Option<Pos>,
    },
    /// The definition still contains unsolved holes (`?`, `?name`, or `_`).
    /// Each entry is `(meta_id, hole_name_if_any, expected_type_if_known)`.
    UnsolvedHoles {
        metas: Vec<(i32, Name, Option<Term>)>,
        names: Vec<Name>,
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
            TypeError::TypeMismatch {
                expected,
                got,
                names,
                pos,
            } => {
                write!(
                    f,
                    "  Type mismatch\n    expected : {}\n    got      : {}",
                    show_term(names, expected),
                    show_term(names, got),
                )?;
                write_pos(f, *pos)
            }
            TypeError::ExpectedPi { ty, names, pos } => {
                write!(
                    f,
                    "  Expected a Π-type, but found:\n    {}",
                    show_term(names, ty)
                )?;
                write_pos(f, *pos)
            }
            TypeError::ExpectedPath { ty, names, pos } => {
                write!(
                    f,
                    "  Expected a Path type, but found:\n    {}",
                    show_term(names, ty)
                )?;
                write_pos(f, *pos)
            }
            TypeError::ExpectedUniverse { ty, names, pos } => {
                write!(
                    f,
                    "  Expected a universe U_n, but found:\n    {}",
                    show_term(names, ty)
                )?;
                write_pos(f, *pos)
            }
            TypeError::ExpectedEquiv { ty, names, pos } => {
                write!(
                    f,
                    "  Expected an Equiv type, but found:\n    {}",
                    show_term(names, ty)
                )?;
                write_pos(f, *pos)
            }
            TypeError::ExpectedSigma { ty, names, pos } => {
                write!(
                    f,
                    "  Expected a Σ-type, but found:\n    {}",
                    show_term(names, ty)
                )?;
                write_pos(f, *pos)
            }
            TypeError::NotAnInterval { t, names, pos } => {
                write!(
                    f,
                    "  Expected an interval expression (𝕀), but got:\n    {}",
                    show_term(names, t),
                )?;
                write_pos(f, *pos)
            }
            TypeError::CannotInfer { t, names, pos } => {
                write!(
                    f,
                    "  Cannot infer type of term without annotation:\n    {}\n  \
                     (Tip: use 'check' instead of 'infer', or add a type annotation)",
                    show_term(names, t),
                )?;
                write_pos(f, *pos)
            }
            TypeError::EtaFuelExhausted { t1, t2, names, pos } => {
                write!(
                    f,
                    "  Eta-expansion fuel exhausted while comparing:\n    {}\n  and\n    {}",
                    show_term(names, t1),
                    show_term(names, t2),
                )?;
                write_pos(f, *pos)
            }
            TypeError::Other(msg) => write!(f, "  {}", msg),
            TypeError::UnknownDatatype { name, pos } => {
                write!(f, "  Unknown datatype: '{}'", name)?;
                write_pos(f, *pos)
            }
            TypeError::UnknownConstructor { datatype, con, pos } => {
                write!(f, "  Unknown constructor '{}::{}'", datatype, con)?;
                write_pos(f, *pos)
            }
            TypeError::WrongNumberOfArgs {
                con,
                expected,
                got,
                pos,
            } => {
                write!(
                    f,
                    "  Wrong number of arguments for '{}': expected {}, got {}",
                    con, expected, got
                )?;
                write_pos(f, *pos)
            }
            TypeError::BadElimCase { con, msg, pos } => {
                write!(f, "  Bad case for '{}': {}", con, msg)?;
                write_pos(f, *pos)
            }
            TypeError::MissingCase { con, pos } => {
                write!(f, "  Missing case for constructor '{}'", con)?;
                write_pos(f, *pos)
            }
            TypeError::ExpectedData { ty, names, pos } => {
                write!(
                    f,
                    "  Expected a data type, but found:\n    {}",
                    show_term(names, ty)
                )?;
                write_pos(f, *pos)
            }
            TypeError::PathPNotTypeFamily { ty, names } => {
                write!(
                    f,
                    "  PathP requires a type family, but found:\n    {}",
                    show_term(names, ty)
                )
            }
            TypeError::TerminationViolation {
                datatype,
                case,
                msg,
                pos,
            } => {
                write!(
                    f,
                    "  Termination violation in '{}' case of '{}':\n    {}",
                    case, datatype, msg
                )?;
                write_pos(f, *pos)
            }
            TypeError::UnsolvedHoles { metas, names } => {
                writeln!(f, "  Unsolved holes remain in this definition:")?;
                for (id, hole_name, expected) in metas {
                    let display = if hole_name.is_empty() {
                        format!("?_{}", id)
                    } else {
                        format!("?{}", hole_name)
                    };
                    match expected {
                        Some(ty) => writeln!(f, "    {} : {}", display, show_term(names, ty),)?,
                        None => writeln!(f, "    {} : <no expected type known>", display,)?,
                    }
                }
                write!(
                    f,
                    "  (fill each hole or provide a complete proof before the definition is accepted)"
                )
            }
        }
    }
}
