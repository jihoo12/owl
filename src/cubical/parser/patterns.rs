//! Pattern AST for match cases with nested constructor patterns.
//!
//! The kernel's `ElimCase` only supports flat binder lists, so a match arm's
//! leading column is first parsed into a tree of [`Pat`]s. `grammar.rs` then
//! compiles nested constructor patterns (`suc (suc zero)`) into a chain of
//! nested `TElim`inators. A pattern whose arguments are all plain variables
//! compiles to exactly the same `ElimCase`s the flat parser produced, so the
//! kernel never observes a difference.

use crate::cubical::interval::I;
use crate::cubical::syntax::{Name, Term};

/// A single pattern in a match arm's leading column.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pat {
    /// A variable binder: `x`.
    Var(Name),
    /// A constructor application: `con pat1 ... patn`.
    Con { con: Name, args: Vec<Pat> },
    /// A path application pattern: `p @ i0` or `p @ i1`.
    /// Desugared at parse time into a let-binding + nested match.
    PathApp { var: Name, interval: I },
    /// A dot (forced) pattern: `.con_name`.
    /// Asserts definitional equality with the given constructor. Irrefutable.
    Dot(Term),
}

impl Pat {
    pub fn is_var(&self) -> bool {
        matches!(self, Pat::Var(_))
    }

    /// Whether this is a path application pattern.
    pub fn is_path_app(&self) -> bool {
        matches!(self, Pat::PathApp { .. })
    }

    /// Whether this is a dot pattern.
    pub fn is_dot(&self) -> bool {
        matches!(self, Pat::Dot(_))
    }

    /// The constructor name of a dot pattern's term, if it references a known constructor.
    pub fn dot_con(&self) -> Option<&str> {
        if let Pat::Dot(Term::TCon(_, name, _)) = self {
            Some(name)
        } else {
            None
        }
    }

    /// The constructor head of a constructor pattern.
    /// For dot patterns, returns the referenced constructor name.
    pub fn con(&self) -> Option<&str> {
        match self {
            Pat::Con { con, .. } => Some(con),
            Pat::Dot(Term::TCon(_, name, _)) => Some(name),
            Pat::Var(_) | Pat::PathApp { .. } | Pat::Dot(_) => None,
        }
    }

    /// The argument patterns of a constructor pattern.
    pub fn args(&self) -> &[Pat] {
        match self {
            Pat::Con { args, .. } => args,
            Pat::Var(_) | Pat::PathApp { .. } | Pat::Dot(_) => &[],
        }
    }

    /// Whether any argument position carries a nested constructor pattern.
    /// `suc m` is flat; `suc (suc zero)`, `suc zero` and `cons x (cons y zs)`
    /// are nested.
    pub fn has_nested_con(&self) -> bool {
        match self {
            Pat::Var(_) | Pat::PathApp { .. } | Pat::Dot(_) => false,
            Pat::Con { args, .. } => args.iter().any(|a| !a.is_var() || a.has_nested_con()),
        }
    }

    /// Collect every variable bound by this pattern, depth-first left-to-right.
    pub fn binders<'a>(&'a self, out: &mut Vec<Name>) {
        match self {
            Pat::Var(n) => out.push(n.clone()),
            Pat::PathApp { var, .. } => out.push(var.clone()),
            Pat::Dot(_) => {} // dot patterns don't bind variables
            Pat::Con { args, .. } => {
                for a in args {
                    a.binders(out);
                }
            }
        }
    }

    /// The environment, innermost-first, in which the compiled eliminator
    /// chain binds this pattern's variables.
    ///
    /// Each constructor node contributes its arguments' binder names — a `""`
    /// phantom for a nested constructor slot — and then the nested constructor
    /// arguments follow, depth-first left-to-right. For an all-variable
    /// pattern this yields exactly the binder list of the flat parser, so flat
    /// arms keep producing byte-identical `ElimCase`s. For a nested pattern it
    /// reproduces the context the typechecker builds while checking the nested
    /// `TElim`s (outermost case's binders deepest), so a body parsed against
    /// this environment needs no re-indexing.
    pub fn pattern_env<'a>(&'a self, out: &mut Vec<Name>) {
        match self {
            Pat::Var(n) => out.push(n.clone()),
            Pat::PathApp { var, .. } => out.push(var.clone()),
            Pat::Dot(_) => {} // dot patterns don't bind variables
            Pat::Con { args, .. } => {
                for a in args {
                    match a {
                        Pat::Var(n) => out.push(n.clone()),
                        Pat::PathApp { var, .. } => out.push(var.clone()),
                        Pat::Con { .. } => out.push(String::new()),
                        Pat::Dot(_) => {} // dot patterns don't bind variables
                    }
                }
                for a in args {
                    if let Pat::Con { .. } = a {
                        a.pattern_env(out);
                    }
                }
            }
        }
    }

    /// Like [`Pat::pattern_env`], but for an arm with an `as`-binding: the
    /// `as`-name binds the whole constructor value. NBE's `do_elim` places the
    /// `as` value innermost of the case's own binders (index 0, above the
    /// phantom argument slots), so the `as`-name sits in the environment
    /// between the case's argument slots and everything nested beneath them.
    pub fn pattern_env_with_as<'a>(&'a self, out: &mut Vec<Name>, as_name: Option<&'a Name>) {
        match self {
            Pat::Var(n) => out.push(n.clone()),
            Pat::PathApp { var, .. } => {
                out.push(var.clone());
                if let Some(as_n) = as_name {
                    out.push(as_n.clone());
                }
            }
            Pat::Dot(_) => {} // dot patterns don't bind variables
            Pat::Con { args, .. } => {
                for a in args {
                    match a {
                        Pat::Var(n) => out.push(n.clone()),
                        Pat::PathApp { var, .. } => out.push(var.clone()),
                        Pat::Con { .. } => out.push(String::new()),
                        Pat::Dot(_) => {} // dot patterns don't bind variables
                    }
                }
                if let Some(as_n) = as_name {
                    out.push(as_n.clone());
                }
                for a in args {
                    if let Pat::Con { .. } = a {
                        a.pattern_env(out);
                    }
                }
            }
        }
    }
}

/// One match arm as read by pass A of [`parse_match_cases`](super::grammar):
/// the leading-column pattern(s), any `as`-binding, and any record bindings.
/// Pass B parses the body and assembles the flat `ElimCase`s.
#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pats: Vec<Pat>,
    pub as_name: Option<Name>,
    pub record_bindings: Option<Vec<(Name, Name)>>,
    /// Absurd pattern `()` — no body, desugars to zero-case match.
    pub absurd: bool,
    /// Whether this arm contains a path application pattern (`p @ i0`/`p @ i1`).
    /// When set, the arm is desugared at parse time into a nested TElim.
    pub has_path_app: bool,
    /// The `with` expression from `match x with e as y ...`.
    /// When set, the match is desugared into nested matches with a let binding.
    pub with_expr: Option<Term>,
    /// The `as` name from the `with` clause (`as y` in `with e as y`).
    pub with_name: Option<Name>,
}
