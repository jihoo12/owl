// Cubical Syntax — Rust port of syntax.hs
//
// Depends on types from interval.rs:
//   use crate::interval::{I, DNF};

pub mod pretty;
pub mod positivity;

pub use pretty::show_term;
pub use positivity::check_datatype_positivity;

use crate::cubical::interval::{DNF, I, dnf_bot, dnf_top};

pub type Name = String;
pub type Level = i32;

/// A system of face-tube pairs: `[(phi₁, t₁), (phi₂, t₂), ...]`
/// Used in hcomp/comp/fill/hfill to specify boundary conditions on multiple faces.
pub type System = Vec<(Term, Term)>;

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
    THComp(Box<Term>, System, Box<Term>),
    TComp(Box<Term>, System, Box<Term>),
    TFill(Box<Term>, System, Box<Term>),
    THFill(Box<Term>, System, Box<Term>),
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
    /// Reference to a declared datatype, used as a type.
    /// `TData("S1", [])` ~ `S¹`. For parameterized types:
    /// `TData("List", [A])` ~ `List A`.
    TData(Name, Vec<Term>),
    /// Ordinary constructor application: `TCon(datatype, constructor, args)`.
    /// `args` are positional, in declaration order.
    TCon(Name, Name, Vec<Term>),
    /// Path-constructor application: `TPCon(datatype, constructor, args, r)`.
    /// `r` is the interval argument. `args` are the constructor's ordinary
    /// arguments only (the interval argument is kept separate as `r`,
    /// matching how `PLam`/`PApp` separate interval abstraction from term
    /// abstraction).
    TPCon(Name, Name, Vec<Term>, Box<Term>),
    /// Square-constructor application: `TSqCon(datatype, constructor, args, r, s)`.
    /// `r` and `s` are the two interval arguments. `args` are the constructor's
    /// ordinary arguments only.
    TSqCon(Name, Name, Vec<Term>, Box<Term>, Box<Term>),
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
    /// `constructor` — apply a constructor of the goal datatype, creating
    /// subgoals for each argument.  When the goal is an inductive type,
    /// picks the first constructor (or the named one) and applies it.
    Constructor(Option<Name>),
    /// `destruct x` — case-split on a hypothesis `x` of an inductive type,
    /// creating a subgoal for each constructor case.
    Destruct(Name),
    /// `transitivity` — when the goal is `Path A x z`, split into two
    /// subgoals: prove `Path A x y` and `Path A y z` for an intermediate `y`.
    Transitivity,
    /// `compute` — normalize the current goal type (does not produce a proof
    /// term; purely informational).
    Compute,
    /// `trivial` — attempt `reflexivity`; succeeds when the goal is a path
    /// with definitionally equal endpoints.
    Trivial,
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

/// Signature of a square constructor (2-dimensional HIT part).
/// Represents a 2-cell with 4 faces: i0, i1, j0, j1.
///
/// The square constructor `sq : A [[ face_i0, face_i1, face_j0, face_j1 ]]`
/// creates a 2-dimensional path. The type is:
/// `PathP (<r> PathP (<s> A) face_i0 face_i1) face_j0 face_j1`
///
/// - face_i0, face_i1: points of A (s-boundaries at r=0 and r=1)
/// - face_j0, face_j1: paths in A from face_i0 to face_i1 (r-boundaries at s=0 and s=1)
///
/// Boundary coherence: face_j0 and face_j1 must start/end at face_i0/face_i1:
///   PApp(face_j0, I0) == face_i0
///   PApp(face_j0, I1) == face_i1
///   PApp(face_j1, I0) == face_i0
///   PApp(face_j1, I1) == face_i1
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SqConSig {
    pub name: Name,
    pub arg_tys: Vec<Term>,
    pub face_i0: Term,
    pub face_i1: Term,
    pub face_j0: Term,
    pub face_j1: Term,
}

impl SqConSig {
    pub fn arity(&self) -> usize {
        self.arg_tys.len()
    }
}

/// A full datatype declaration: `data Name = con1 ... | con2 ... | pcon1 ...`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Datatype {
    pub name: Name,
    /// Parameter declarations, e.g. `(A : Type)` in `inductive Trunc (A : Type) where ...`.
    /// Each entry is (param_name, param_type). Parameters are in outermost-first
    /// order and their types form a telescope (each type can reference earlier params).
    pub params: Vec<(Name, Term)>,
    pub cons: Vec<ConSig>,
    pub pcons: Vec<PConSig>,
    pub sqcons: Vec<SqConSig>,
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
    pub fn find_sqcon(&self, name: &str) -> Option<&SqConSig> {
        self.sqcons.iter().find(|c| c.name == name)
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
        Term::THComp(a, sys, u0) => Term::THComp(
            b(shift(d, c, a)),
            sys.iter().map(|(phi, t)| (shift(d, c, phi), shift(d, c, t))).collect(),
            b(shift(d, c, u0)),
        ),
        Term::TComp(a, sys, u0) => Term::TComp(
            b(shift(d, c, a)),
            sys.iter().map(|(phi, t)| (shift(d, c, phi), shift(d, c, t))).collect(),
            b(shift(d, c, u0)),
        ),
        Term::TFill(a, sys, u0) => Term::TFill(
            b(shift(d, c, a)),
            sys.iter().map(|(phi, t)| (shift(d, c, phi), shift(d, c, t))).collect(),
            b(shift(d, c, u0)),
        ),
        Term::THFill(a, sys, u0) => Term::THFill(
            b(shift(d, c, a)),
            sys.iter().map(|(phi, t)| (shift(d, c, phi), shift(d, c, t))).collect(),
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
        Term::TData(name, params) => Term::TData(
            name.clone(),
            params.iter().map(|p| shift(d, c, p)).collect(),
        ),
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
        Term::TSqCon(data, con, args, r, s) => Term::TSqCon(
            data.clone(),
            con.clone(),
            args.iter().map(|a| shift(d, c, a)).collect(),
            b(shift(d, c, r)),
            b(shift(d, c, s)),
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
        Tactic::Reflexivity
        | Tactic::Symmetry
        | Tactic::Split
        | Tactic::Assumption
        | Tactic::Transitivity
        | Tactic::Compute
        | Tactic::Trivial => tac.clone(),
        Tactic::Intro(_) => tac.clone(),
        Tactic::Constructor(_) => tac.clone(),
        Tactic::Destruct(_) => tac.clone(),
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
        Term::THComp(a, sys, u0) => Term::THComp(
            b(subst(j, s, a)),
            sys.iter().map(|(phi, t)| (subst(j, s, phi), subst(j, s, t))).collect(),
            b(subst(j, s, u0)),
        ),
        Term::TComp(a, sys, u0) => Term::TComp(
            b(subst(j, s, a)),
            sys.iter().map(|(phi, t)| (subst(j, s, phi), subst(j, s, t))).collect(),
            b(subst(j, s, u0)),
        ),
        Term::TFill(a, sys, u0) => Term::TFill(
            b(subst(j, s, a)),
            sys.iter().map(|(phi, t)| (subst(j, s, phi), subst(j, s, t))).collect(),
            b(subst(j, s, u0)),
        ),
        Term::THFill(a, sys, u0) => Term::THFill(
            b(subst(j, s, a)),
            sys.iter().map(|(phi, t)| (subst(j, s, phi), subst(j, s, t))).collect(),
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
        Term::TData(name, params) => Term::TData(
            name.clone(),
            params.iter().map(|p| subst(j, s, p)).collect(),
        ),
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
        Term::TSqCon(data, con, args, r, s) => Term::TSqCon(
            data.clone(),
            con.clone(),
            args.iter().map(|a| subst(j, s, a)).collect(),
            b(subst(j, s, r)),
            b(subst(j, s, s)),
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
        Tactic::Reflexivity
        | Tactic::Symmetry
        | Tactic::Split
        | Tactic::Assumption
        | Tactic::Transitivity
        | Tactic::Compute
        | Tactic::Trivial => tac.clone(),
        Tactic::Intro(_) => tac.clone(),
        Tactic::Constructor(_) => tac.clone(),
        Tactic::Destruct(_) => tac.clone(),
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
        Term::THComp(a, sys, u0) => {
            let mut m = max_var(a).max(max_var(u0));
            for (phi, t) in sys {
                m = m.max(max_var(phi)).max(max_var(t));
            }
            m
        }
        Term::TComp(a, sys, u0) => {
            let mut m = max_var(a).max(max_var(u0));
            for (phi, t) in sys {
                m = m.max(max_var(phi)).max(max_var(t));
            }
            m
        }
        Term::TFill(a, sys, u0) => {
            let mut m = max_var(a).max(max_var(u0));
            for (phi, t) in sys {
                m = m.max(max_var(phi)).max(max_var(t));
            }
            m
        }
        Term::THFill(a, sys, u0) => {
            let mut m = max_var(a).max(max_var(u0));
            for (phi, t) in sys {
                m = m.max(max_var(phi)).max(max_var(t));
            }
            m
        }
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
        Term::TData(_, params) => params.iter().map(max_var).fold(-1, |m, x| m.max(x)),
        Term::TCon(_, _, args) => args.iter().map(max_var).fold(-1, |m, x| m.max(x)),
        Term::TPCon(_, _, args, r) => args.iter().map(max_var).fold(-1, |m, x| m.max(x)).max(max_var(r)),
        Term::TSqCon(_, _, args, r, s) => args.iter().map(max_var).fold(-1, |m, x| m.max(x)).max(max_var(r)).max(max_var(s)),
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
// Positivity checking is in syntax::positivity
// ---------------------------------------------------------------------------

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
    use super::pretty::show_term;
    use super::positivity::check_datatype_positivity;

    fn b(t: Term) -> Box<Term> {
        Box::new(t)
    }

    #[test]
    fn shift_increments_free() {
        let t = Term::TVar(0);
        let s = shift(1, 0, &t);
        assert_eq!(s, Term::TVar(1));
    }

    #[test]
    fn shift_preserves_bound() {
        let t = Term::TAbs("x".into(), b(Term::TVar(0)));
        let s = shift(1, 0, &t);
        assert_eq!(s, Term::TAbs("x".into(), b(Term::TVar(0))));
    }

    #[test]
    fn subst_identity() {
        let t = Term::TVar(0);
        let s = subst(0, &Term::TVar(42), &t);
        assert_eq!(s, Term::TVar(42));
    }

    #[test]
    fn beta_reduces() {
        let body = Term::TVar(0);
        let arg = Term::TUniv(0);
        let r = beta(&body, &arg);
        assert_eq!(r, Term::TUniv(0));
    }

    #[test]
    fn show_nat_zero() {
        let t = Term::TCon("Nat".into(), "zero".into(), vec![]);
        assert_eq!(show_term(&[], &t), "0");
    }

    #[test]
    fn show_nat_two() {
        let t = Term::TCon(
            "Nat".into(),
            "suc".into(),
            vec![Term::TCon("Nat".into(), "suc".into(), vec![
                Term::TCon("Nat".into(), "zero".into(), vec![]),
            ])],
        );
        assert_eq!(show_term(&[], &t), "2");
    }

    #[test]
    fn max_var_free() {
        assert_eq!(max_var(&Term::TVar(5)), 5);
    }

    #[test]
    fn max_var_abs() {
        assert_eq!(max_var(&Term::TAbs("x".into(), b(Term::TVar(0)))), -1);
    }

    #[test]
    fn nat_positivity_ok() {
        let dt = Datatype {
            name: "Nat".into(),
            params: vec![],
            cons: vec![
                ConSig { name: "zero".into(), arg_tys: vec![] },
                ConSig { name: "suc".into(), arg_tys: vec![Term::TData("Nat".into(), vec![])] },
            ],
            pcons: vec![],
            sqcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }
}
