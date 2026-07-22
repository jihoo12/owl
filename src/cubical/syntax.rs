// Cubical Syntax — Rust port of syntax.hs
//
// Depends on types from interval.rs:
//   use crate::interval::{I, DNF};

use crate::cubical::interval::{DNF, I, dnf_bot, dnf_top};
use std::fmt;

pub type Name = String;
pub type Level = i32;

// ---------------------------------------------------------------------------
// Term Syntax
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    TVar(i32),
    TApp(Box<Term>, Box<Term>),
    TAbs(Name, Box<Term>),
    TUniv(Level),
    TIntervalTy,
    TPi(Name, Box<Term>, Box<Term>),
    TInterval(I),
    TCube(DNF),
    TPath(Box<Term>, Box<Term>, Box<Term>),
    PLam(Name, Box<Term>),
    PApp(Box<Term>, Box<Term>),
    THComp(Box<Term>, Box<Term>, Box<Term>, Box<Term>),
    TEquiv(Box<Term>, Box<Term>),
    TMkEquiv(
        Box<Term>,
        Box<Term>,
        Box<Term>,
        Box<Term>,
        Box<Term>,
        Box<Term>,
    ),
    TEquivFwd(Box<Term>, Box<Term>),
    TUa(Box<Term>),
    TTransport(Box<Term>, Box<Term>),
    TGlue(Box<Term>, Box<Term>, Box<Term>),
    TGlueElem(Box<Term>, Box<Term>, Box<Term>),
    TUnglue(Box<Term>, Box<Term>, Box<Term>),
    TSigma(Name, Box<Term>, Box<Term>),
    TPair(Box<Term>, Box<Term>),
    TFst(Box<Term>),
    TSnd(Box<Term>),

    // -- Tactics / Meta-variables -------------------------------------------
    /// Unsolved meta-variable (tactic hole). `Meta(i)` is created by the
    /// tactic engine and should be fully solved before NbE/typechecking.
    Meta(i32),
    /// A tactic block `by t1; t2; ...` — desugared by the typechecker.
    TBy(Vec<Tactic>),

    // -- Inductive types / Higher Inductive Types (HITs) --------------------
    /// Reference to a declared datatype, used as a type. `TData("S1")` ~ `S¹`.
    TData(Name),
    /// Ordinary constructor application: `TCon(datatype, constructor, args)`.
    /// `args` are positional, in declaration order.
    TCon(Name, Name, Vec<Term>),
    /// Path-constructor application: `TPCon(datatype, constructor, args, r)`.
    /// `r` is the interval argument. `args` are the constructor's ordinary
    /// arguments only (the interval argument is kept separate as `r`,
    /// matching how `PLam`/`PApp` separate interval abstraction from term
    /// abstraction).
    TPCon(Name, Name, Vec<Term>, Box<Term>),
    /// Eliminator (dependent recursor) for a datatype.
    /// `TElim(motive, cases, scrutinee)`.
    /// `motive : (x : TData(d)) -> U_n`, given as a `TAbs`-shaped term
    /// (i.e. `motive` itself binds the scrutinee, index 0 in its body).
    TElim(Box<Term>, Vec<ElimCase>, Box<Term>),
}

/// One arm of an eliminator. Binds `binders.len()` fresh variables over
/// `body`, declared outermost-first (matching `ConSig`/`PConSig` telescopes).
///
/// For an ordinary-constructor case (`con` names a `ConSig`):
///   `binders` has length `arity`, one name per constructor argument,
///   and `body` has type `motive (con binders...)`.
///
/// For a path-constructor case (`con` names a `PConSig`):
///   `binders` has length `arity + 1`: the constructor's ordinary
///   arguments (outermost-first), then the interval variable LAST.
///   `body` has type `Path (motive (pcon args... @ i)) face0case face1case`,
///   where `body` itself is a `PLam`-shaped term over the interval variable
///   (i.e. the interval binder in `binders` corresponds to a `PApp`/`PLam`
///   style abstraction, not an ordinary `TAbs`).
///   Substituting `i = 0` / `i = 1` into `body` must be `definitionally_equal`
///   to the case's own arguments substituted into the datatype's declared
///   `face0` / `face1` for that path constructor.
///
/// Binder scoping: `binders` is listed outermost-to-innermost (declaration
/// order), matching `ConSig::arg_tys` / `PConSig::arg_tys`. When pushed into
/// a context (which is innermost-first — see `Ctx` in typechecker.rs and
/// equality.rs), the LAST element of `binders` becomes index 0. For a path
/// constructor, this means the interval variable is index 0 and the last
/// ordinary argument is index 1, etc. — exactly mirroring how `PLam`/`TAbs`
/// chains nest in this codebase.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ElimCase {
    pub con: Name,
    pub binders: Vec<Name>,
    pub body: Box<Term>,
}

// ---------------------------------------------------------------------------
// Tactics
// ---------------------------------------------------------------------------

/// A single tactic command in a `by` block.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Tactic {
    /// `exact t` — provide a complete proof term `t` for the current goal.
    Exact(Term),
    /// `intro x1 x2 ...` — introduce one or more Pi-type binders.
    Intro(Vec<Name>),
    /// `apply f` — apply a function to the goal; creates a subgoal for the
    /// function's domain type.  Works for both dependent and non-dependent
    /// Pi types.
    Apply(Term),
    /// `assumption` — search the context for a hypothesis matching the goal.
    Assumption,
    /// `reflexivity` — prove `Path A x x` when the endpoints are
    /// definitionally equal.
    Reflexivity,
    /// `symmetry` — flip the goal from `Path A x y` to `Path A y x`.
    Symmetry,
    /// `split` — split a `Sigma`-type goal `(a, b)` into two sub-goals:
    /// first prove the `A` component, then the `B` component.
    Split,
}

// ---------------------------------------------------------------------------
// Datatype schema (the "data" declaration mechanism)
// ---------------------------------------------------------------------------

/// Signature of an ordinary (point) constructor.
/// `arg_tys[k]` is the type of the k-th argument (0-indexed, outermost
/// first), in a scope where index 0 refers to argument 0, index 1 to
/// argument 1, etc. — i.e. `arg_tys` forms a telescope exactly like a
/// chain of `TPi` binders, read outermost-first, indices counting up.
///
/// Non-dependent / non-recursive constructors (the common case — `Bool`,
/// `Nat`, `List`) just use types that don't mention earlier arguments.
/// A self-referencing argument (recursion, e.g. `suc : Nat -> Nat`) uses
/// `TData(d)` directly as the argument type — no special-casing needed,
/// since `TData` is an ordinary term-former.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConSig {
    pub name: Name,
    pub arg_tys: Vec<Term>,
}

impl ConSig {
    pub fn arity(&self) -> usize {
        self.arg_tys.len()
    }
}

/// Signature of a path constructor (the HIT part).
/// E.g. for S¹: `PConSig { name: "loop", arg_tys: vec![], face0: TCon(S1,base,[]), face1: TCon(S1,base,[]) }`.
///
/// `arg_tys` follows the same telescope convention as `ConSig::arg_tys`
/// (outermost-first, counting up). `face0` / `face1` are terms in that
/// same scope of `arg_tys.len()` variables — the ordinary arguments only.
/// The interval argument is NOT in scope in `face0`/`face1`, since at each
/// face it is fixed to `I0`/`I1` and therefore is not a free variable of
/// the boundary term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PConSig {
    pub name: Name,
    pub arg_tys: Vec<Term>,
    pub face0: Term,
    pub face1: Term,
}

impl PConSig {
    pub fn arity(&self) -> usize {
        self.arg_tys.len()
    }
}

/// A full datatype declaration: `data Name = con1 ... | con2 ... | pcon1 ...`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Datatype {
    pub name: Name,
    pub cons: Vec<ConSig>,
    pub pcons: Vec<PConSig>,
    /// Optional universe-level annotation: `data D : U_n = ...`
    /// When `Some(n)`, the datatype lives in `U_n` regardless of its
    /// constructor arguments. When `None`, the level is inferred as
    /// `max` over constructor argument universe levels.
    pub universe_level: Option<Level>,
}

impl Datatype {
    pub fn find_con(&self, name: &str) -> Option<&ConSig> {
        self.cons.iter().find(|c| c.name == name)
    }
    pub fn find_pcon(&self, name: &str) -> Option<&PConSig> {
        self.pcons.iter().find(|c| c.name == name)
    }
}

// ---------------------------------------------------------------------------
// Pretty-printing
// ---------------------------------------------------------------------------

/// If the term is a Nat literal in normal form (chains of `suc` ending in
/// `zero`), return the integer value. Otherwise return None.
pub fn nat_to_int(t: &Term) -> Option<i64> {
    match t {
        Term::TCon(d, c, args) if d == "Nat" => match (c.as_str(), args.as_slice()) {
            ("zero", []) => Some(0),
            ("suc", [arg]) => nat_to_int(arg).map(|n| n + 1),
            _ => None,
        },
        _ => None,
    }
}

pub fn show_term(env: &[Name], t: &Term) -> String {
    match t {
        Term::TVar(i) => {
            let i = *i as usize;
            if i < env.len() {
                env[i].clone()
            } else {
                format!("#{}", i)
            }
        }
        Term::TApp(f, a) => format!("({} {})", show_term(env, f), show_term(env, a)),
        Term::TAbs(x, b) => {
            let mut env2 = vec![x.clone()];
            env2.extend_from_slice(env);
            format!("fun {} => {}", x, show_term(&env2, b))
        }
        Term::TUniv(n) => format!("U{}", n),
        Term::TIntervalTy => "𝕀".to_string(),
        Term::TPi(x, a, b) => {
            let mut env2 = vec![x.clone()];
            env2.extend_from_slice(env);
            format!("∀ ({} : {}), {}", x, show_term(env, a), show_term(&env2, b))
        }
        Term::TInterval(i) => format!("{}", i),
        Term::TCube(c) => format!("{}", c),
        Term::TPath(a, u, v) => format!(
            "Path {} {} {}",
            show_term(env, a),
            show_term(env, u),
            show_term(env, v)
        ),
        Term::PLam(i, b) => {
            let mut env2 = vec![i.clone()];
            env2.extend_from_slice(env);
            format!("⟨{}⟩ {}", i, show_term(&env2, b))
        }
        Term::PApp(p, r) => format!("{} @ {}", show_term(env, p), show_term(env, r)),
        Term::THComp(a, phi, u, u0) => format!(
            "hcomp {} [{}] ({}) {}",
            show_term(env, a),
            show_term(env, phi),
            show_term(env, u),
            show_term(env, u0)
        ),
        Term::TEquiv(a, b) => format!("Equiv {} {}", show_term(env, a), show_term(env, b)),
        Term::TMkEquiv(a, b, f, g, eta, eps) => format!(
            "mkEquiv {} {} {} {} {} {}",
            show_term(env, a),
            show_term(env, b),
            show_term(env, f),
            show_term(env, g),
            show_term(env, eta),
            show_term(env, eps)
        ),
        Term::TEquivFwd(e, x) => format!("equivFwd ({}) {}", show_term(env, e), show_term(env, x)),
        Term::TUa(e) => format!("ua ({})", show_term(env, e)),
        Term::TTransport(p, x) => {
            format!("transport ({}) {}", show_term(env, p), show_term(env, x))
        }
        Term::TGlue(a, phi, te) => format!(
            "Glue {} [{}] ({})",
            show_term(env, a),
            show_term(env, phi),
            show_term(env, te)
        ),
        Term::TGlueElem(phi, t, a) => format!(
            "glue [{}] ({}) {}",
            show_term(env, phi),
            show_term(env, t),
            show_term(env, a)
        ),
        Term::TUnglue(phi, te, g) => format!(
            "unglue [{}] ({}) {}",
            show_term(env, phi),
            show_term(env, te),
            show_term(env, g)
        ),
        Term::TSigma(x, a, b) => {
            let mut env2 = vec![x.clone()];
            env2.extend_from_slice(env);
            format!("Σ ({} : {}), {}", x, show_term(env, a), show_term(&env2, b))
        }
        Term::TPair(a, b) => format!("({} , {})", show_term(env, a), show_term(env, b)),
        Term::TFst(p) => format!("fst {}", show_term(env, p)),
        Term::TSnd(p) => format!("snd {}", show_term(env, p)),
        Term::TData(d) => d.clone(),
        t @ Term::TCon(_, c, args) => {
            if let Some(n) = nat_to_int(t) {
                return format!("{}", n);
            }
            if args.is_empty() {
                c.clone()
            } else {
                let parts: Vec<String> = args.iter().map(|a| show_term(env, a)).collect();
                format!("({} {})", c, parts.join(" "))
            }
        }
        Term::TPCon(_, c, args, r) => {
            let mut parts: Vec<String> = args.iter().map(|a| show_term(env, a)).collect();
            parts.push(format!("@ {}", show_term(env, r)));
            format!("({} {})", c, parts.join(" "))
        }
        Term::TElim(motive, cases, scrut) => {
            let case_strs: Vec<String> = cases
                .iter()
                .map(|case| {
                    // binders are outermost-first in declaration; extend the
                    // pretty-printing env the same way, outermost-first, so
                    // nested show_term calls see innermost-first as usual.
                    let mut env2 = case.binders.clone();
                    env2.reverse();
                    env2.extend_from_slice(env);
                    format!(
                        "{} {} -> {}",
                        case.con,
                        case.binders.join(" "),
                        show_term(&env2, &case.body)
                    )
                })
                .collect();
            format!(
                "elim[{}] {{ {} }} {}",
                show_term(env, motive),
                case_strs.join(" | "),
                show_term(env, scrut)
            )
        }
        Term::Meta(i) => format!("?{}", i),
        Term::TBy(tactics) => {
            let tactic_strs: Vec<String> = tactics.iter().map(|t| show_tactic(env, t)).collect();
            format!("by {}", tactic_strs.join("; "))
        }
    }
}

fn show_tactic(env: &[Name], t: &Tactic) -> String {
    match t {
        Tactic::Exact(term) => format!("exact {}", show_term(env, term)),
        Tactic::Intro(names) => format!("intro {}", names.join(" ")),
        Tactic::Apply(term) => format!("apply {}", show_term(env, term)),
        Tactic::Assumption => "assumption".to_string(),
        Tactic::Reflexivity => "reflexivity".to_string(),
        Tactic::Symmetry => "symmetry".to_string(),
        Tactic::Split => "split".to_string(),
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", show_term(&[], self))
    }
}

// ---------------------------------------------------------------------------
// Shift
// ---------------------------------------------------------------------------

/// Increment all free de Bruijn indices >= `c` by `d`.
pub fn shift(d: i32, c: i32, term: &Term) -> Term {
    match term {
        Term::TVar(i) => Term::TVar(if *i >= c { i + d } else { *i }),
        Term::TApp(f, a) => Term::TApp(b(shift(d, c, f)), b(shift(d, c, a))),
        Term::TAbs(x, body) => Term::TAbs(x.clone(), b(shift(d, c + 1, body))),
        Term::TPi(x, a, body) => Term::TPi(x.clone(), b(shift(d, c, a)), b(shift(d, c + 1, body))),
        Term::TUniv(n) => Term::TUniv(*n),
        Term::TIntervalTy => Term::TIntervalTy,
        Term::TInterval(i) => Term::TInterval(i.clone()),
        Term::TCube(cu) => Term::TCube(cu.clone()),
        Term::TPath(a, u, v) => {
            Term::TPath(b(shift(d, c, a)), b(shift(d, c, u)), b(shift(d, c, v)))
        }
        Term::PLam(x, body) => Term::PLam(x.clone(), b(shift(d, c + 1, body))),
        Term::PApp(p, r) => Term::PApp(b(shift(d, c, p)), b(shift(d, c, r))),
        Term::THComp(a, phi, u, u0) => Term::THComp(
            b(shift(d, c, a)),
            b(shift(d, c, phi)),
            b(shift(d, c, u)),
            b(shift(d, c, u0)),
        ),
        Term::TEquiv(a, bx) => Term::TEquiv(b(shift(d, c, a)), b(shift(d, c, bx))),
        Term::TMkEquiv(a, bx, f, g, eta, eps) => Term::TMkEquiv(
            b(shift(d, c, a)),
            b(shift(d, c, bx)),
            b(shift(d, c, f)),
            b(shift(d, c, g)),
            b(shift(d, c, eta)),
            b(shift(d, c, eps)),
        ),
        Term::TEquivFwd(e, x) => Term::TEquivFwd(b(shift(d, c, e)), b(shift(d, c, x))),
        Term::TUa(e) => Term::TUa(b(shift(d, c, e))),
        Term::TTransport(p, x) => Term::TTransport(b(shift(d, c, p)), b(shift(d, c, x))),
        Term::TGlue(a, phi, te) => {
            Term::TGlue(b(shift(d, c, a)), b(shift(d, c, phi)), b(shift(d, c, te)))
        }
        Term::TGlueElem(phi, t, a) => {
            Term::TGlueElem(b(shift(d, c, phi)), b(shift(d, c, t)), b(shift(d, c, a)))
        }
        Term::TUnglue(phi, te, g) => {
            Term::TUnglue(b(shift(d, c, phi)), b(shift(d, c, te)), b(shift(d, c, g)))
        }
        Term::TSigma(x, a, body) => {
            Term::TSigma(x.clone(), b(shift(d, c, a)), b(shift(d, c + 1, body)))
        }
        Term::TPair(a, bx) => Term::TPair(b(shift(d, c, a)), b(shift(d, c, bx))),
        Term::TFst(p) => Term::TFst(b(shift(d, c, p))),
        Term::TSnd(p) => Term::TSnd(b(shift(d, c, p))),
        Term::TData(name) => Term::TData(name.clone()),
        Term::TCon(data, con, args) => Term::TCon(
            data.clone(),
            con.clone(),
            args.iter().map(|a| shift(d, c, a)).collect(),
        ),
        Term::TPCon(data, con, args, r) => Term::TPCon(
            data.clone(),
            con.clone(),
            args.iter().map(|a| shift(d, c, a)).collect(),
            b(shift(d, c, r)),
        ),
        Term::TElim(motive, cases, scrut) => Term::TElim(
            b(shift(d, c, motive)),
            cases
                .iter()
                .map(|case| ElimCase {
                    con: case.con.clone(),
                    binders: case.binders.clone(),
                    body: b(shift(d, c + case.binders.len() as i32, &case.body)),
                })
                .collect(),
            b(shift(d, c, scrut)),
        ),
        Term::Meta(_) => term.clone(),
        Term::TBy(tactics) => Term::TBy(
            tactics
                .iter()
                .map(|tac| shift_tactic(d, c, tac))
                .collect(),
        ),
    }
}

fn shift_tactic(d: i32, c: i32, tac: &Tactic) -> Tactic {
    match tac {
        Tactic::Exact(t) => Tactic::Exact(shift(d, c, t)),
        Tactic::Apply(t) => Tactic::Apply(shift(d, c, t)),
        Tactic::Reflexivity | Tactic::Symmetry | Tactic::Split | Tactic::Assumption => tac.clone(),
        Tactic::Intro(_) => tac.clone(),
    }
}

// ---------------------------------------------------------------------------
// Substitution
// ---------------------------------------------------------------------------

/// Substitute de Bruijn index `j` with `s` inside `term`.
pub fn subst(j: i32, s: &Term, term: &Term) -> Term {
    match term {
        Term::TVar(i) => {
            if *i == j {
                s.clone()
            } else {
                Term::TVar(*i)
            }
        }
        Term::TApp(f, a) => Term::TApp(b(subst(j, s, f)), b(subst(j, s, a))),
        Term::TAbs(x, body) => {
            let s1 = shift(1, 0, s);
            Term::TAbs(x.clone(), b(subst(j + 1, &s1, body)))
        }
        Term::TPi(x, a, body) => {
            let s1 = shift(1, 0, s);
            Term::TPi(x.clone(), b(subst(j, s, a)), b(subst(j + 1, &s1, body)))
        }
        Term::TUniv(n) => Term::TUniv(*n),
        Term::TIntervalTy => Term::TIntervalTy,
        Term::TInterval(i) => Term::TInterval(i.clone()),
        Term::TCube(cu) => Term::TCube(cu.clone()),
        Term::TPath(a, u, v) => {
            Term::TPath(b(subst(j, s, a)), b(subst(j, s, u)), b(subst(j, s, v)))
        }
        Term::PLam(x, body) => {
            let s1 = shift(1, 0, s);
            Term::PLam(x.clone(), b(subst(j + 1, &s1, body)))
        }
        Term::PApp(p, r) => Term::PApp(b(subst(j, s, p)), b(subst(j, s, r))),
        Term::THComp(a, phi, u, u0) => Term::THComp(
            b(subst(j, s, a)),
            b(subst(j, s, phi)),
            b(subst(j, s, u)),
            b(subst(j, s, u0)),
        ),
        Term::TEquiv(a, bx) => Term::TEquiv(b(subst(j, s, a)), b(subst(j, s, bx))),
        Term::TMkEquiv(a, bx, f, g, eta, eps) => Term::TMkEquiv(
            b(subst(j, s, a)),
            b(subst(j, s, bx)),
            b(subst(j, s, f)),
            b(subst(j, s, g)),
            b(subst(j, s, eta)),
            b(subst(j, s, eps)),
        ),
        Term::TEquivFwd(e, x) => Term::TEquivFwd(b(subst(j, s, e)), b(subst(j, s, x))),
        Term::TUa(e) => Term::TUa(b(subst(j, s, e))),
        Term::TTransport(p, x) => Term::TTransport(b(subst(j, s, p)), b(subst(j, s, x))),
        Term::TGlue(a, phi, te) => {
            Term::TGlue(b(subst(j, s, a)), b(subst(j, s, phi)), b(subst(j, s, te)))
        }
        Term::TGlueElem(phi, t, a) => {
            Term::TGlueElem(b(subst(j, s, phi)), b(subst(j, s, t)), b(subst(j, s, a)))
        }
        Term::TUnglue(phi, te, g) => {
            Term::TUnglue(b(subst(j, s, phi)), b(subst(j, s, te)), b(subst(j, s, g)))
        }
        Term::TSigma(x, a, body) => {
            let s1 = shift(1, 0, s);
            Term::TSigma(x.clone(), b(subst(j, s, a)), b(subst(j + 1, &s1, body)))
        }
        Term::TPair(a, bx) => Term::TPair(b(subst(j, s, a)), b(subst(j, s, bx))),
        Term::TFst(p) => Term::TFst(b(subst(j, s, p))),
        Term::TSnd(p) => Term::TSnd(b(subst(j, s, p))),
        Term::TData(name) => Term::TData(name.clone()),
        Term::TCon(data, con, args) => Term::TCon(
            data.clone(),
            con.clone(),
            args.iter().map(|a| subst(j, s, a)).collect(),
        ),
        Term::TPCon(data, con, args, r) => Term::TPCon(
            data.clone(),
            con.clone(),
            args.iter().map(|a| subst(j, s, a)).collect(),
            b(subst(j, s, r)),
        ),
        Term::TElim(motive, cases, scrut) => Term::TElim(
            b(subst(j, s, motive)),
            cases
                .iter()
                .map(|case| {
                    let n = case.binders.len() as i32;
                    let s1 = shift(n, 0, s);
                    ElimCase {
                        con: case.con.clone(),
                        binders: case.binders.clone(),
                        body: b(subst(j + n, &s1, &case.body)),
                    }
                })
                .collect(),
            b(subst(j, s, scrut)),
        ),
        Term::Meta(_) => term.clone(),
        Term::TBy(tactics) => Term::TBy(
            tactics
                .iter()
                .map(|tac| subst_tactic(j, s, tac))
                .collect(),
        ),
    }
}

fn subst_tactic(j: i32, s: &Term, tac: &Tactic) -> Tactic {
    match tac {
        Tactic::Exact(t) => Tactic::Exact(subst(j, s, t)),
        Tactic::Apply(t) => Tactic::Apply(subst(j, s, t)),
        Tactic::Reflexivity | Tactic::Symmetry | Tactic::Split | Tactic::Assumption => tac.clone(),
        Tactic::Intro(_) => tac.clone(),
    }
}

// ---------------------------------------------------------------------------
// Beta reduction
// ---------------------------------------------------------------------------

/// Apply `body` (with de Bruijn index 0 free) to `arg`.
pub fn beta(body: &Term, arg: &Term) -> Term {
    shift(-1, 0, &subst(0, &shift(1, 0, arg), body))
}

// ---------------------------------------------------------------------------
// Max variable index
// ---------------------------------------------------------------------------

/// Return the highest de Bruijn index used in a term (or -1 if none).
pub fn max_var(t: &Term) -> i32 {
    match t {
        Term::TVar(i) => *i,
        Term::TApp(f, a) => max_var(f).max(max_var(a)),
        Term::TAbs(_, b) => (max_var(b) - 1).max(-1),
        Term::TUniv(_) => -1,
        Term::TIntervalTy => -1,
        Term::TPi(_, a, b) => max_var(a).max(max_var(b) - 1).max(-1),
        Term::TInterval(_) => -1,
        Term::TCube(_) => -1,
        Term::TPath(a, u, v) => max_var(a).max(max_var(u)).max(max_var(v)),
        Term::PLam(_, b) => (max_var(b) - 1).max(-1),
        Term::PApp(p, r) => max_var(p).max(max_var(r)),
        Term::THComp(a, phi, u, u0) => max_var(a).max(max_var(phi)).max(max_var(u)).max(max_var(u0)),
        Term::TEquiv(a, b) => max_var(a).max(max_var(b)),
        Term::TMkEquiv(a, b, f, g, eta, eps) => max_var(a)
            .max(max_var(b))
            .max(max_var(f))
            .max(max_var(g))
            .max(max_var(eta))
            .max(max_var(eps)),
        Term::TEquivFwd(e, x) => max_var(e).max(max_var(x)),
        Term::TUa(e) => max_var(e),
        Term::TTransport(p, x) => max_var(p).max(max_var(x)),
        Term::TGlue(a, phi, te) => max_var(a).max(max_var(phi)).max(max_var(te)),
        Term::TGlueElem(phi, t, a) => max_var(phi).max(max_var(t)).max(max_var(a)),
        Term::TUnglue(phi, te, g) => max_var(phi).max(max_var(te)).max(max_var(g)),
        Term::TSigma(_, a, b) => max_var(a).max(max_var(b) - 1).max(-1),
        Term::TPair(a, b) => max_var(a).max(max_var(b)),
        Term::TFst(p) => max_var(p),
        Term::TSnd(p) => max_var(p),
        Term::TData(_) => -1,
        Term::TCon(_, _, args) => args.iter().map(max_var).fold(-1, |m, x| m.max(x)),
        Term::TPCon(_, _, args, r) => args.iter().map(max_var).fold(-1, |m, x| m.max(x)).max(max_var(r)),
        Term::TElim(motive, cases, scrut) => {
            let mut m = max_var(motive).max(max_var(scrut));
            for case in cases {
                let n = case.binders.len() as i32;
                m = m.max(max_var(&case.body) - n);
            }
            m.max(-1)
        }
        Term::Meta(_) => -1,
        Term::TBy(_) => -1,
    }
}

// ---------------------------------------------------------------------------
// DNF helpers for terms
// ---------------------------------------------------------------------------

pub fn is_top_dnf(t: &Term) -> bool {
    matches!(t, Term::TCube(d) if *d == dnf_top())
}

pub fn is_bot_dnf(t: &Term) -> bool {
    matches!(t, Term::TCube(d) if *d == dnf_bot())
}

// ---------------------------------------------------------------------------
// Extract the domain type from an equivalence term.
// ---------------------------------------------------------------------------

pub fn equiv_dom(t: &Term) -> Term {
    match t {
        Term::TMkEquiv(a, _, _, _, _, _) => (**a).clone(),
        Term::TEquiv(a, _) => (**a).clone(),
        Term::TPair(a, _) => (**a).clone(),
        other => other.clone(),
    }
}

// ---------------------------------------------------------------------------
// Positivity checking for datatypes
// ---------------------------------------------------------------------------

/// An error returned when a datatype occurs negatively in its own definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PositivityError {
    pub datatype: Name,
    pub constructor: Name,
    pub message: String,
}

impl fmt::Display for PositivityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "positivity violation in constructor '{}' of '{}': {}",
            self.constructor, self.datatype, self.message
        )
    }
}

/// Check that `target` occurs strictly positively in `ty`.
///
/// `negative` tracks whether we are currently under an odd number of arrow
/// domains (i.e. a negative position). When `negative` is true and `target`
/// appears, that is a violation.
fn check_positivity_in(target: &str, ty: &Term, negative: bool) -> Result<(), PositivityError> {
    match ty {
        Term::TVar(_) => Ok(()),
        Term::TUniv(_) | Term::TIntervalTy | Term::TInterval(_) | Term::TCube(_) => Ok(()),
        Term::TData(name) => {
            if name == target && negative {
                Err(PositivityError {
                    datatype: target.to_string(),
                    constructor: String::new(),
                    message: format!(
                        "datatype '{}' appears on the left side of an arrow",
                        target
                    ),
                })
            } else {
                Ok(())
            }
        }
        Term::TApp(f, a) | Term::PApp(f, a) | Term::TEquiv(f, a) | Term::TEquivFwd(f, a)
        | Term::TTransport(f, a) | Term::TPair(f, a) => {
            check_positivity_in(target, f, negative)?;
            check_positivity_in(target, a, negative)
        }
        Term::TFst(p) | Term::TSnd(p) => check_positivity_in(target, p, negative),
        Term::TAbs(_, body) | Term::PLam(_, body) | Term::TUa(body) => {
            check_positivity_in(target, body, negative)
        }
        Term::TPi(_, a, b) => {
            // Domain A is in a negative position (argument position).
            check_positivity_in(target, a, true)?;
            // Codomain B is in a positive position (result position).
            check_positivity_in(target, b, false)
        }
        Term::TSigma(_, a, b) => {
            check_positivity_in(target, a, negative)?;
            check_positivity_in(target, b, negative)
        }
        Term::TPath(a, u, v) | Term::TGlue(a, u, v) | Term::TGlueElem(a, u, v)
        | Term::TUnglue(a, u, v) => {
            check_positivity_in(target, a, negative)?;
            check_positivity_in(target, u, negative)?;
            check_positivity_in(target, v, negative)
        }
        Term::THComp(a, phi, u, u0) => {
            check_positivity_in(target, a, negative)?;
            check_positivity_in(target, phi, negative)?;
            check_positivity_in(target, u, negative)?;
            check_positivity_in(target, u0, negative)
        }
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            check_positivity_in(target, a, negative)?;
            check_positivity_in(target, b, negative)?;
            check_positivity_in(target, f, negative)?;
            check_positivity_in(target, g, negative)?;
            check_positivity_in(target, eta, negative)?;
            check_positivity_in(target, eps, negative)
        }
        Term::TCon(_, _, args) => {
            for arg in args {
                check_positivity_in(target, arg, negative)?;
            }
            Ok(())
        }
        Term::TPCon(_, _, args, r) => {
            for arg in args {
                check_positivity_in(target, arg, negative)?;
            }
            check_positivity_in(target, r, negative)
        }
        Term::TElim(motive, cases, scrut) => {
            check_positivity_in(target, motive, negative)?;
            for case in cases {
                check_positivity_in(target, &case.body, negative)?;
            }
            check_positivity_in(target, scrut, negative)
        }
        Term::Meta(_) => Ok(()),
        Term::TBy(_) => Ok(()),
    }
}

/// Check that a constructor's argument types are strictly positive with respect
/// to the given datatype.
fn check_con_positivity(
    dt_name: &str,
    con_name: &str,
    arg_tys: &[Term],
) -> Result<(), PositivityError> {
    for (i, ty) in arg_tys.iter().enumerate() {
        check_positivity_in(dt_name, ty, false).map_err(|mut e| {
            e.constructor = con_name.to_string();
            e.message = format!(
                "argument {} of constructor '{}': {}",
                i, con_name, e.message
            );
            e
        })?;
    }
    Ok(())
}

/// Check that a datatype declaration is strictly positive.
///
/// Returns `Ok(())` if all constructors are positive, or the first
/// `PositivityError` found.
pub fn check_datatype_positivity(dt: &Datatype) -> Result<(), PositivityError> {
    for con in &dt.cons {
        check_con_positivity(&dt.name, &con.name, &con.arg_tys)?;
    }
    for pcon in &dt.pcons {
        check_con_positivity(&dt.name, &pcon.name, &pcon.arg_tys)?;
        // Also check face terms — they use the constructor's ordinary args
        // in scope, so TData(dt.name) in face0/face1 would be positive
        // (face terms are results, not arguments).
        check_positivity_in(&dt.name, &pcon.face0, false).map_err(|mut e| {
            e.constructor = pcon.name.clone();
            e.message = format!(
                "face0 of path constructor '{}': {}",
                pcon.name, e.message
            );
            e
        })?;
        check_positivity_in(&dt.name, &pcon.face1, false).map_err(|mut e| {
            e.constructor = pcon.name.clone();
            e.message = format!(
                "face1 of path constructor '{}': {}",
                pcon.name, e.message
            );
            e
        })?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Helper: box a value
// ---------------------------------------------------------------------------

#[inline]
fn b<T>(v: T) -> Box<T> {
    Box::new(v)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn b(t: Term) -> Box<Term> {
        Box::new(t)
    }

    #[test]
    fn positive_nat_is_ok() {
        let dt = Datatype {
            name: "Nat".into(),
            cons: vec![
                ConSig { name: "zero".into(), arg_tys: vec![] },
                ConSig { name: "suc".into(), arg_tys: vec![Term::TData("Nat".into())] },
            ],
            pcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn positive_list_is_ok() {
        let dt = Datatype {
            name: "List".into(),
            cons: vec![
                ConSig { name: "nil".into(), arg_tys: vec![] },
                ConSig {
                    name: "cons".into(),
                    arg_tys: vec![
                        Term::TUniv(0),
                        Term::TData("List".into()),
                    ],
                },
            ],
            pcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn positive_nested_pi_is_ok() {
        // data Bad = mk ((Nat -> Nat) -> Nat)
        // The Nat in (Nat -> Nat) is in the domain of the outer arrow,
        // which is a negative position — but it's not the recursive type.
        let dt = Datatype {
            name: "Bad".into(),
            cons: vec![ConSig {
                name: "mk".into(),
                arg_tys: vec![Term::TPi(
                    "_".into(),
                    b(Term::TPi("_".into(), b(Term::TData("Nat".into())), b(Term::TData("Nat".into())))),
                    b(Term::TData("Nat".into())),
                )],
            }],
            pcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn negative_recursive_type_is_rejected() {
        // data Bad = cons (Bad -> Bad)
        // Bad appears as the domain of an arrow — negative occurrence.
        let dt = Datatype {
            name: "Bad".into(),
            cons: vec![ConSig {
                name: "cons".into(),
                arg_tys: vec![Term::TPi(
                    "_".into(),
                    b(Term::TData("Bad".into())),
                    b(Term::TData("Bad".into())),
                )],
            }],
            pcons: vec![],
            universe_level: None,
        };
        let err = check_datatype_positivity(&dt).unwrap_err();
        assert_eq!(err.datatype, "Bad");
        assert_eq!(err.constructor, "cons");
    }

    #[test]
    fn positive_deeply_nested_pi_is_ok() {
        // data Bad = cons ((Nat -> Bad) -> Bad)
        // Bad appears as the codomain of the inner arrow (positive) and
        // as the return type (positive). This IS strictly positive.
        let dt = Datatype {
            name: "Bad".into(),
            cons: vec![ConSig {
                name: "cons".into(),
                arg_tys: vec![Term::TPi(
                    "_".into(),
                    b(Term::TPi(
                        "_".into(),
                        b(Term::TData("Nat".into())),
                        b(Term::TData("Bad".into())),
                    )),
                    b(Term::TData("Bad".into())),
                )],
            }],
            pcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn negative_domain_in_pi_is_rejected() {
        // data Bad = cons ((Bad -> Nat) -> Bad)
        // Bad appears as the domain of the inner arrow — negative.
        let dt = Datatype {
            name: "Bad".into(),
            cons: vec![ConSig {
                name: "cons".into(),
                arg_tys: vec![Term::TPi(
                    "_".into(),
                    b(Term::TPi(
                        "_".into(),
                        b(Term::TData("Bad".into())),
                        b(Term::TData("Nat".into())),
                    )),
                    b(Term::TData("Bad".into())),
                )],
            }],
            pcons: vec![],
            universe_level: None,
        };
        let err = check_datatype_positivity(&dt).unwrap_err();
        assert_eq!(err.datatype, "Bad");
    }

    #[test]
    fn positive_sigma_is_ok() {
        // data Pair = mk (Σ(_ : Nat). Nat)
        let dt = Datatype {
            name: "Pair".into(),
            cons: vec![ConSig {
                name: "mk".into(),
                arg_tys: vec![Term::TSigma(
                    "_".into(),
                    b(Term::TData("Nat".into())),
                    b(Term::TData("Nat".into())),
                )],
            }],
            pcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn positive_path_type_is_ok() {
        // data S1 = | base : S1 | loop : Path S1 base base
        // Path type is always positive.
        let dt = Datatype {
            name: "S1".into(),
            cons: vec![ConSig { name: "base".into(), arg_tys: vec![] }],
            pcons: vec![PConSig {
                name: "loop".into(),
                arg_tys: vec![],
                face0: Term::TCon("S1".into(), "base".into(), vec![]),
                face1: Term::TCon("S1".into(), "base".into(), vec![]),
            }],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }
}
