// Cubical Syntax — Rust port of syntax.hs
//
// Depends on types from interval.rs:
//   use crate::interval::{I, DNF};

pub mod positivity;
pub mod pretty;

pub use positivity::{Variance, check_datatype_positivity, compute_param_variances};
pub use pretty::show_term;

use crate::cubical::interval::{DNF, I, dnf_bot, dnf_top};
use std::sync::Arc;

pub type Name = String;
pub type Level = i32;

// ---------------------------------------------------------------------------
// Level Expressions — the sub-language of universe levels
// ---------------------------------------------------------------------------

/// A level expression in the universe polymorphism system.
/// Levels form a small sub-language: variables, constants, successor, and max.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LevelExpr {
    /// A de Bruijn level variable (bound by a `{l : Level}` binder).
    LVar(i32),
    /// A concrete level constant: `0`, `1`, `2`, ...
    LConst(i32),
    /// Successor: `lsuc l`.
    LSuc(Box<LevelExpr>),
    /// Maximum: `max l1 l2`.
    LMax(Box<LevelExpr>, Box<LevelExpr>),
}

impl LevelExpr {
    /// Evaluate a level expression to a concrete level, given a context of
    /// bound level variables (outermost first). Returns `None` if the
    /// expression contains unbound variables.
    pub fn eval(&self, ctx: &[i32]) -> Option<i32> {
        match self {
            LevelExpr::LVar(i) => ctx.get(*i as usize).copied(),
            LevelExpr::LConst(n) => Some(*n),
            LevelExpr::LSuc(l) => l.eval(ctx).map(|n| n + 1),
            LevelExpr::LMax(a, b) => {
                let av = a.eval(ctx)?;
                let b_ = b.eval(ctx)?;
                Some(av.max(b_))
            }
        }
    }

    /// Evaluate to a concrete level, defaulting to 0 for unbound variables.
    pub fn eval_or_default(&self, ctx: &[i32]) -> i32 {
        self.eval(ctx).unwrap_or(0)
    }

    /// Compute the maximum of two level expressions.
    pub fn max(l1: LevelExpr, l2: LevelExpr) -> LevelExpr {
        match (&l1, &l2) {
            (LevelExpr::LConst(a), LevelExpr::LConst(b)) => LevelExpr::LConst((*a).max(*b)),
            _ => LevelExpr::LMax(Box::new(l1), Box::new(l2)),
        }
    }

    /// Compute the successor of a level expression.
    pub fn suc(l: LevelExpr) -> LevelExpr {
        match l {
            LevelExpr::LConst(n) => LevelExpr::LConst(n + 1),
            _ => LevelExpr::LSuc(Box::new(l)),
        }
    }

    /// Compare two level expressions for `≤` in a given context.
    /// Returns `None` if the comparison is undecidable (contains unbound vars).
    pub fn leq(&self, other: &Self, ctx: &[i32]) -> Option<bool> {
        let a = self.eval(ctx)?;
        let b = other.eval(ctx)?;
        Some(a <= b)
    }

    /// Check if this level expression is a concrete constant.
    pub fn is_concrete(&self) -> bool {
        matches!(self, LevelExpr::LConst(_))
    }

    /// Return the concrete level if this is a constant, else `None`.
    pub fn as_const(&self) -> Option<i32> {
        match self {
            LevelExpr::LConst(n) => Some(*n),
            _ => None,
        }
    }

    /// Shift level variable de Bruijn indices >= `c` by `d`.
    pub fn shift(d: i32, c: i32, l: &LevelExpr) -> LevelExpr {
        match l {
            LevelExpr::LVar(i) => LevelExpr::LVar(if *i >= c { i + d } else { *i }),
            LevelExpr::LConst(_) => l.clone(),
            LevelExpr::LSuc(inner) => LevelExpr::LSuc(Box::new(LevelExpr::shift(d, c, inner))),
            LevelExpr::LMax(a, b) => LevelExpr::LMax(
                Box::new(LevelExpr::shift(d, c, a)),
                Box::new(LevelExpr::shift(d, c, b)),
            ),
        }
    }

    /// Substitute level variable `j` with `s` in a level expression.
    pub fn subst(j: i32, s: &LevelExpr, l: &LevelExpr) -> LevelExpr {
        match l {
            LevelExpr::LVar(i) => {
                if *i == j {
                    s.clone()
                } else if *i > j {
                    LevelExpr::LVar(i - 1)
                } else {
                    l.clone()
                }
            }
            LevelExpr::LConst(_) => l.clone(),
            LevelExpr::LSuc(inner) => LevelExpr::LSuc(Box::new(LevelExpr::subst(j, s, inner))),
            LevelExpr::LMax(a, b) => LevelExpr::LMax(
                Box::new(LevelExpr::subst(j, s, a)),
                Box::new(LevelExpr::subst(j, s, b)),
            ),
        }
    }

    /// Maximum level variable index used in a level expression (-1 if none).
    pub fn max_var(l: &LevelExpr) -> i32 {
        match l {
            LevelExpr::LVar(i) => *i,
            LevelExpr::LConst(_) => -1,
            LevelExpr::LSuc(inner) => LevelExpr::max_var(inner),
            LevelExpr::LMax(a, b) => LevelExpr::max_var(a).max(LevelExpr::max_var(b)),
        }
    }
}

/// A system of face-tube pairs: `[(phi₁, t₁), (phi₂, t₂), ...]`
/// Used in hcomp/comp/fill/hfill to specify boundary conditions on multiple faces.
pub type System = Vec<(Term, Term)>;

// ---------------------------------------------------------------------------
// Term Syntax
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    TVar(i32),
    TApp(Arc<Term>, Arc<Term>),
    TAbs(Name, Arc<Term>),
    TUniv(LevelExpr),
    TProp,
    TSSet,
    TLift(Arc<Term>, LevelExpr),
    TLower(Arc<Term>),
    TIntervalTy,
    TLevelTy,
    TPi(Name, Arc<Term>, Arc<Term>, bool),
    TInterval(I),
    TCube(DNF),
    TPath(Arc<Term>, Arc<Term>, Arc<Term>),
    PLam(Name, Arc<Term>),
    PApp(Arc<Term>, Arc<Term>),
    // -- Cubical identity types (A4) ----------------------------------------
    TId(Arc<Term>, Arc<Term>, Arc<Term>),
    TRefl(Arc<Term>),
    TJ(Arc<Term>, Arc<Term>, Arc<Term>),
    THComp(Arc<Term>, System, Arc<Term>),
    TComp(Arc<Term>, System, Arc<Term>),
    TFill(Arc<Term>, System, Arc<Term>),
    THFill(Arc<Term>, System, Arc<Term>),
    TEquiv(Arc<Term>, Arc<Term>),
    TMkEquiv(
        Arc<Term>,
        Arc<Term>,
        Arc<Term>,
        Arc<Term>,
        Arc<Term>,
        Arc<Term>,
    ),
    TEquivFwd(Arc<Term>, Arc<Term>),
    TUa(Arc<Term>),
    TTransport(Arc<Term>, Arc<Term>),
    TTransp(Arc<Term>, Arc<Term>, Arc<Term>),
    TGlue(Arc<Term>, Arc<Term>, Arc<Term>),
    TGlueElem(Arc<Term>, Arc<Term>, Arc<Term>),
    TUnglue(Arc<Term>, Arc<Term>, Arc<Term>),
    TPartial(Arc<Term>, Arc<Term>),
    TSystemType(System),
    TSigma(Name, Arc<Term>, Arc<Term>),
    TPair(Arc<Term>, Arc<Term>),
    TFst(Arc<Term>),
    TSnd(Arc<Term>),

    // -- Tactics / Meta-variables -------------------------------------------
    Meta(i32),
    TBy(Vec<Tactic>),

    // -- Inductive types / Higher Inductive Types (HITs) --------------------
    TData(Name, Vec<Term>),
    TCon(Name, Name, Vec<Term>),
    TPCon(Name, Name, Vec<Term>, Arc<Term>),
    TSqCon(Name, Name, Vec<Term>, Arc<Term>, Arc<Term>),
    TCellCon(Name, Name, Vec<Term>, Vec<Term>),
    TElim(Arc<Term>, Vec<ElimCase>, Arc<Term>),

    // -- Record types --------------------------------------------------------
    TProj(Name, Arc<Term>),
    TRecordUpdate(Arc<Term>, Vec<(Name, Term)>),

    // -- Coinduction ---------------------------------------------------------
    TDelay(Arc<Term>),
    TNext(Arc<Term>),
    TForce(Arc<Term>),

    // -- Reflection (E1) ----------------------------------------------------
    /// Quote a term to its AST representation.  `quote t` normalises `t` and
    /// returns the result as a first-class `Term` value.
    TQuote(Arc<Term>),
    /// Unquote a quoted AST back into a term.  `unquote ast` evaluates `ast`
    /// (which must be a well-formed `Term` value) and returns the result.
    TUnquote(Arc<Term>),
    /// Return the current typing context as a quoted AST.
    TGetContext,
    /// Return the type of a term as a quoted AST.
    TGetType(Arc<Term>),
    /// Check that two terms are definitionally equal (reflection E1).
    /// Returns Unit on success; type error on failure.
    TUnify(Arc<Term>, Arc<Term>),
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
    /// As-pattern: `con binders as name => body`
    /// `name` is bound to the full constructor application in the body.
    pub as_name: Option<Name>,
    /// Record pattern: `{ field = binder, ... }` in place of constructor + binders.
    /// When set, `con` and `binders` may be empty/synthetic; the typechecker
    /// desugars this to a constructor pattern once the datatype is known.
    pub record_bindings: Option<Vec<(Name, Name)>>,
    /// Nested-pattern refinement of a path/square/cell constructor case.
    ///
    /// When a HIT case head carries nested constructor patterns (e.g.
    /// `merid (suc m) i => …`), the parser compiles the arm bodies into a
    /// nested `TElim` chain whose scrutinee is the case's ordinary-argument
    /// binder. The typechecker must then (a) check the body against a
    /// *refined* expected type that does not push the case's interval binders
    /// into the checking context (so the nested elim's de Bruijn indices match
    /// the runtime evaluation environment), and (b) verify boundary coherence
    /// by descending the nested elim and checking every leaf at each endpoint.
    ///
    /// The value is `Some(v)` for every refined HIT case; `v` has one entry per
    /// ordinary argument of the case head and, for each argument carrying a
    /// nested pattern, `Some(leaf_binder_names)` listing the leaf binders that
    /// the nested elim introduces (innermost-last). Flat cases and ordinary
    /// constructor cases leave this `None`. The parser emits the case body as
    /// `PLam`-wrapped; the typechecker uses this marker to choose the refined
    /// checking path, so a user-written `PLam` over an eliminator is never
    /// mistaken for a compiler-generated refinement.
    pub refinements: Option<Vec<Option<Vec<Name>>>>,
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
    /// `omega` — decision procedure for linear arithmetic over Nat.
    ///
    /// Proves goals of the form `Path Nat u v` where `u` and `v` are linear
    /// expressions over the context's Nat variables, by (1) definitional
    /// reflexivity after normalization and (2) direct application of a
    /// previously verified global lemma to the context's variables — both
    /// re-checked by the kernel. Produces a complete proof term (like
    /// `exact`). See `src/cubical/omega.rs`.
    Omega,
    /// `ring` — decision procedure for commutative semiring/ring identities.
    ///
    /// `ring` without an argument is the concrete path: it proves goals of
    /// the form `Path Nat u v` where `u` and `v` are polynomial expressions
    /// over the context's Nat variables (built with `add`, `mul`, `zero`,
    /// `one`), by canonicalizing both sides to a sum of monomials and proving
    /// the equality from the law names in `lib/ring_laws.owl`.
    ///
    /// `ring with C` proves the same class of identities over an *abstract*
    /// commutative ring bundled in the record `C : CommRing A`: the operations
    /// (`add`/`mul`/`zero`/`one`) and law proofs are resolved as projections
    /// of `C`, and recognized by head-symbol equality instead of by unfolding
    /// Nat eliminators. See `src/cubical/ring.rs`.
    ///
    /// In both modes the constructed proof is re-checked by the kernel, which
    /// is the soundness backstop.
    Ring(Option<Term>),
    /// `field` — field identities with inverse reasoning, over an abstract
    /// `Field` record bundled as `field with F`.
    ///
    /// Both sides of the goal `Path A u v` are reified to fractions
    /// `(N, D)` with a proof `t = mul (canon N) (inv (canon D))` (denominator
    /// always a single monomial); add/mul combine through common-denominator
    /// rewrites, and `inv` swaps numerator and denominator (restricted to a
    /// single coefficient-1 monomial numerator).  The final step derives the
    /// goal from the ring-proved cross-multiplication via a scale lemma.
    /// Nonzero obligations `(Path A zero x -> Empty)` are discharged
    /// structurally against `nz_one`/`nz_mul` and context hypotheses.
    /// See `src/cubical/field.rs`.
    Field(Option<Term>),
    /// `group` — group word problems over an abstract `Group` record bundled
    /// as `group with G`.
    ///
    /// Both sides of the goal `Path A u v` are parsed into signed-generator
    /// words and decided by free reduction; on agreement a proof tree is
    /// assembled from the record's law fields (assoc/unit/cancellation plus
    /// `inv_one`/`inv_inv`/`inv_mul`).  The kernel re-checks the proof.
    /// See `src/cubical/group.rs`.
    Group(Option<Term>),
    /// `eq` — close a path goal by reflexivity or by composing context path
    /// hypotheses into a chain (BFS over endpoints matched up to
    /// normalization).  See `src/cubical/eq.rs`.
    Eq,
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

/// Signature of an n-dimensional cell constructor (generalises PConSig/SqConSig).
/// For dimension `d` there are `2*d` faces stored as pairs from innermost to
/// outermost:
///
/// ```text
/// faces = [ face_d0, face_d1,          // innermost dimension
///           face_{d-1}0, face_{d-1}1,  // next
///           ...,
///           face_10, face_11 ]         // outermost dimension
/// ```
///
/// The type of the cell constructor is:
/// ```text
/// PathP (<i_1> PathP (<i_2> ... PathP (<i_d> A) face_d0 face_d1) ... face_20 face_21) face_10 face_11
/// ```
///
/// Each face_k0/face_k1 pair corresponds to the boundary at interval variable
/// `i_k = 0` / `i_k = 1`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CellConSig {
    pub name: Name,
    pub arg_tys: Vec<Term>,
    pub faces: Vec<Term>,
}

impl CellConSig {
    pub fn arity(&self) -> usize {
        self.arg_tys.len()
    }
    /// The dimension (number of interval arguments) of this cell constructor.
    pub fn dimension(&self) -> usize {
        self.faces.len() / 2
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
    /// N-dimensional cell constructors (dimension >= 3).
    /// Generalises `pcons` (dim 1) and `sqcons` (dim 2).
    pub cellcons: Vec<CellConSig>,
    /// Optional universe-level annotation: `data D : U_n = ...`
    /// When `Some(n)`, the datatype lives in `U_n` regardless of its
    /// constructor arguments. When `None`, the level is inferred as
    /// `max` over constructor argument universe levels.
    pub universe_level: Option<LevelExpr>,
    /// Field names for record types. When `Some(names)`, this is a record type
    /// with a single constructor, and `names[i]` is the name of the i-th field
    /// (constructor argument). Used by projection (`r.field`) to find the
    /// correct argument index.
    pub field_names: Option<Vec<Name>>,
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
    pub fn find_cellcon(&self, name: &str) -> Option<&CellConSig> {
        self.cellcons.iter().find(|c| c.name == name)
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
        Term::TPi(x, a, body, implicit) => Term::TPi(
            x.clone(),
            b(shift(d, c, a)),
            b(shift(d, c + 1, body)),
            *implicit,
        ),
        Term::TUniv(n) => Term::TUniv(LevelExpr::shift(d, c, &n)),
        Term::TProp => Term::TProp,
        Term::TSSet => Term::TSSet,
        Term::TLift(a, lvl) => Term::TLift(b(shift(d, c, a)), LevelExpr::shift(d, c, &lvl)),
        Term::TLower(a) => Term::TLower(b(shift(d, c, a))),
        Term::TIntervalTy => Term::TIntervalTy,
        Term::TLevelTy => Term::TLevelTy,
        Term::TInterval(i) => Term::TInterval(i.clone()),
        Term::TCube(cu) => Term::TCube(cu.clone()),
        Term::TPath(a, u, v) => {
            Term::TPath(b(shift(d, c, a)), b(shift(d, c, u)), b(shift(d, c, v)))
        }
        Term::TId(a, u, v) => Term::TId(b(shift(d, c, a)), b(shift(d, c, u)), b(shift(d, c, v))),
        Term::TRefl(a) => Term::TRefl(b(shift(d, c, a))),
        Term::TJ(motive, base, p) => Term::TJ(
            b(shift(d, c, motive)),
            b(shift(d, c, base)),
            b(shift(d, c, p)),
        ),
        Term::PLam(x, body) => Term::PLam(x.clone(), b(shift(d, c + 1, body))),
        Term::PApp(p, r) => Term::PApp(b(shift(d, c, p)), b(shift(d, c, r))),
        Term::THComp(a, sys, u0) => Term::THComp(
            b(shift(d, c, a)),
            sys.iter()
                .map(|(phi, t)| (shift(d, c, phi), shift(d, c, t)))
                .collect(),
            b(shift(d, c, u0)),
        ),
        Term::TComp(a, sys, u0) => Term::TComp(
            b(shift(d, c, a)),
            sys.iter()
                .map(|(phi, t)| (shift(d, c, phi), shift(d, c, t)))
                .collect(),
            b(shift(d, c, u0)),
        ),
        Term::TFill(a, sys, u0) => Term::TFill(
            b(shift(d, c, a)),
            sys.iter()
                .map(|(phi, t)| (shift(d, c, phi), shift(d, c, t)))
                .collect(),
            b(shift(d, c, u0)),
        ),
        Term::THFill(a, sys, u0) => Term::THFill(
            b(shift(d, c, a)),
            sys.iter()
                .map(|(phi, t)| (shift(d, c, phi), shift(d, c, t)))
                .collect(),
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
        Term::TTransp(a, r, x) => {
            Term::TTransp(b(shift(d, c, a)), b(shift(d, c, r)), b(shift(d, c, x)))
        }
        Term::TGlue(a, phi, te) => {
            Term::TGlue(b(shift(d, c, a)), b(shift(d, c, phi)), b(shift(d, c, te)))
        }
        Term::TGlueElem(phi, t, a) => {
            Term::TGlueElem(b(shift(d, c, phi)), b(shift(d, c, t)), b(shift(d, c, a)))
        }
        Term::TUnglue(phi, te, g) => {
            Term::TUnglue(b(shift(d, c, phi)), b(shift(d, c, te)), b(shift(d, c, g)))
        }
        Term::TPartial(phi, a) => Term::TPartial(b(shift(d, c, phi)), b(shift(d, c, a))),
        Term::TSystemType(sys) => Term::TSystemType(
            sys.iter()
                .map(|(phi, a)| (shift(d, c, phi), shift(d, c, a)))
                .collect(),
        ),
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
        Term::TCellCon(data, con, args, ivars) => Term::TCellCon(
            data.clone(),
            con.clone(),
            args.iter().map(|a| shift(d, c, a)).collect(),
            ivars.iter().map(|v| shift(d, c, v)).collect(),
        ),
        Term::TElim(motive, cases, scrut) => Term::TElim(
            b(shift(d, c, motive)),
            cases
                .iter()
                .map(|case| ElimCase {
                    con: case.con.clone(),
                    binders: case.binders.clone(),
                    body: Box::new(shift(d, c + case.binders.len() as i32, &case.body)),
                    as_name: case.as_name.clone(),
                    record_bindings: case.record_bindings.clone(),
                    refinements: case.refinements.clone(),
                })
                .collect(),
            b(shift(d, c, scrut)),
        ),
        Term::Meta(_) => term.clone(),
        Term::TBy(tactics) => {
            Term::TBy(tactics.iter().map(|tac| shift_tactic(d, c, tac)).collect())
        }
        Term::TProj(field, r) => Term::TProj(field.clone(), b(shift(d, c, r))),
        Term::TRecordUpdate(r, updates) => Term::TRecordUpdate(
            b(shift(d, c, r)),
            updates
                .iter()
                .map(|(f, e)| (f.clone(), shift(d, c, e)))
                .collect(),
        ),
        Term::TDelay(a) => Term::TDelay(b(shift(d, c, a))),
        Term::TNext(a) => Term::TNext(b(shift(d, c, a))),
        Term::TForce(a) => Term::TForce(b(shift(d, c, a))),
        Term::TQuote(a) => Term::TQuote(b(shift(d, c, a))),
        Term::TUnquote(a) => Term::TUnquote(b(shift(d, c, a))),
        Term::TGetContext => Term::TGetContext,
        Term::TGetType(a) => Term::TGetType(b(shift(d, c, a))),
        Term::TUnify(a, bx) => Term::TUnify(b(shift(d, c, a)), b(shift(d, c, bx))),
    }
}

fn shift_tactic(d: i32, c: i32, tac: &Tactic) -> Tactic {
    match tac {
        Tactic::Exact(t) => Tactic::Exact(shift(d, c, t)),
        Tactic::Apply(t) => Tactic::Apply(shift(d, c, t)),
        Tactic::Ring(t) => Tactic::Ring(t.as_ref().map(|t| shift(d, c, t))),
        Tactic::Field(t) => Tactic::Field(t.as_ref().map(|t| shift(d, c, t))),
        Tactic::Group(t) => Tactic::Group(t.as_ref().map(|t| shift(d, c, t))),
        Tactic::Eq => Tactic::Eq,
        Tactic::Reflexivity
        | Tactic::Symmetry
        | Tactic::Split
        | Tactic::Assumption
        | Tactic::Transitivity
        | Tactic::Compute
        | Tactic::Trivial
        | Tactic::Omega => tac.clone(),
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
        Term::TPi(x, a, body, implicit) => {
            let s1 = shift(1, 0, s);
            Term::TPi(
                x.clone(),
                b(subst(j, s, a)),
                b(subst(j + 1, &s1, body)),
                *implicit,
            )
        }
        Term::TUniv(n) => Term::TUniv(n.clone()),
        Term::TProp => Term::TProp,
        Term::TSSet => Term::TSSet,
        Term::TLift(a, lvl) => Term::TLift(b(subst(j, s, a)), lvl.clone()),
        Term::TLower(a) => Term::TLower(b(subst(j, s, a))),
        Term::TIntervalTy => Term::TIntervalTy,
        Term::TLevelTy => Term::TLevelTy,
        Term::TInterval(i) => Term::TInterval(i.clone()),
        Term::TCube(cu) => Term::TCube(cu.clone()),
        Term::TPath(a, u, v) => {
            Term::TPath(b(subst(j, s, a)), b(subst(j, s, u)), b(subst(j, s, v)))
        }
        Term::TId(a, u, v) => Term::TId(b(subst(j, s, a)), b(subst(j, s, u)), b(subst(j, s, v))),
        Term::TRefl(a) => Term::TRefl(b(subst(j, s, a))),
        Term::TJ(motive, base, p) => Term::TJ(
            b(subst(j, s, motive)),
            b(subst(j, s, base)),
            b(subst(j, s, p)),
        ),
        Term::PLam(x, body) => {
            let s1 = shift(1, 0, s);
            Term::PLam(x.clone(), b(subst(j + 1, &s1, body)))
        }
        Term::PApp(p, r) => Term::PApp(b(subst(j, s, p)), b(subst(j, s, r))),
        Term::THComp(a, sys, u0) => Term::THComp(
            b(subst(j, s, a)),
            sys.iter()
                .map(|(phi, t)| (subst(j, s, phi), subst(j, s, t)))
                .collect(),
            b(subst(j, s, u0)),
        ),
        Term::TComp(a, sys, u0) => Term::TComp(
            b(subst(j, s, a)),
            sys.iter()
                .map(|(phi, t)| (subst(j, s, phi), subst(j, s, t)))
                .collect(),
            b(subst(j, s, u0)),
        ),
        Term::TFill(a, sys, u0) => Term::TFill(
            b(subst(j, s, a)),
            sys.iter()
                .map(|(phi, t)| (subst(j, s, phi), subst(j, s, t)))
                .collect(),
            b(subst(j, s, u0)),
        ),
        Term::THFill(a, sys, u0) => Term::THFill(
            b(subst(j, s, a)),
            sys.iter()
                .map(|(phi, t)| (subst(j, s, phi), subst(j, s, t)))
                .collect(),
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
        Term::TTransp(a, r, x) => {
            Term::TTransp(b(subst(j, s, a)), b(subst(j, s, r)), b(subst(j, s, x)))
        }
        Term::TGlue(a, phi, te) => {
            Term::TGlue(b(subst(j, s, a)), b(subst(j, s, phi)), b(subst(j, s, te)))
        }
        Term::TGlueElem(phi, t, a) => {
            Term::TGlueElem(b(subst(j, s, phi)), b(subst(j, s, t)), b(subst(j, s, a)))
        }
        Term::TUnglue(phi, te, g) => {
            Term::TUnglue(b(subst(j, s, phi)), b(subst(j, s, te)), b(subst(j, s, g)))
        }
        Term::TPartial(phi, a) => Term::TPartial(b(subst(j, s, phi)), b(subst(j, s, a))),
        Term::TSystemType(sys) => Term::TSystemType(
            sys.iter()
                .map(|(phi, a)| (subst(j, s, phi), subst(j, s, a)))
                .collect(),
        ),
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
        Term::TCellCon(data, con, args, ivars) => Term::TCellCon(
            data.clone(),
            con.clone(),
            args.iter().map(|a| subst(j, s, a)).collect(),
            ivars.iter().map(|v| subst(j, s, v)).collect(),
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
                        body: Box::new(subst(j + n, &s1, &case.body)),
                        as_name: case.as_name.clone(),
                        record_bindings: case.record_bindings.clone(),
                        refinements: case.refinements.clone(),
                    }
                })
                .collect(),
            b(subst(j, s, scrut)),
        ),
        Term::Meta(_) => term.clone(),
        Term::TBy(tactics) => {
            Term::TBy(tactics.iter().map(|tac| subst_tactic(j, s, tac)).collect())
        }
        Term::TProj(field, r) => Term::TProj(field.clone(), b(subst(j, s, r))),
        Term::TRecordUpdate(r, updates) => Term::TRecordUpdate(
            b(subst(j, s, r)),
            updates
                .iter()
                .map(|(f, e)| (f.clone(), subst(j, s, e)))
                .collect(),
        ),
        Term::TDelay(a) => Term::TDelay(b(subst(j, s, a))),
        Term::TNext(a) => Term::TNext(b(subst(j, s, a))),
        Term::TForce(a) => Term::TForce(b(subst(j, s, a))),
        Term::TQuote(a) => Term::TQuote(b(subst(j, s, a))),
        Term::TUnquote(a) => Term::TUnquote(b(subst(j, s, a))),
        Term::TGetContext => Term::TGetContext,
        Term::TGetType(a) => Term::TGetType(b(subst(j, s, a))),
        Term::TUnify(a, bx) => Term::TUnify(b(subst(j, s, a)), b(subst(j, s, bx))),
    }
}

fn subst_tactic(j: i32, s: &Term, tac: &Tactic) -> Tactic {
    match tac {
        Tactic::Exact(t) => Tactic::Exact(subst(j, s, t)),
        Tactic::Apply(t) => Tactic::Apply(subst(j, s, t)),
        Tactic::Ring(t) => Tactic::Ring(t.as_ref().map(|t| subst(j, s, t))),
        Tactic::Field(t) => Tactic::Field(t.as_ref().map(|t| subst(j, s, t))),
        Tactic::Group(t) => Tactic::Group(t.as_ref().map(|t| subst(j, s, t))),
        Tactic::Eq => Tactic::Eq,
        Tactic::Reflexivity
        | Tactic::Symmetry
        | Tactic::Split
        | Tactic::Assumption
        | Tactic::Transitivity
        | Tactic::Compute
        | Tactic::Trivial
        | Tactic::Omega => tac.clone(),
        Tactic::Intro(_) => tac.clone(),
        Tactic::Constructor(_) => tac.clone(),
        Tactic::Destruct(_) => tac.clone(),
    }
}

// ---------------------------------------------------------------------------
// Parallel substitution for record parameters
// ---------------------------------------------------------------------------

/// Parallel substitution for record constructor parameters.
///
/// `param_values[i]` is the replacement for the parameter at de Bruijn index
/// `(num_params - 1 - i)`. When inside `k` binders, the parameter's de Bruijn
/// index is `k + (num_params - 1 - i)`, and the replacement term is shifted
/// up by `k` to stay well-scoped.
///
/// This avoids the sequential-substitution interference bug where composing
/// individual `subst` calls corrupts de Bruijn indices when parameter values
/// contain variables that happen to coincide with other substitution targets.
pub fn subst_params(num_params: usize, param_values: &[Option<Term>], term: &Term) -> Term {
    subst_params_inner(num_params, param_values, 0, term)
}

fn subst_params_inner(
    num_params: usize,
    param_values: &[Option<Term>],
    binder_depth: i32,
    term: &Term,
) -> Term {
    match term {
        Term::TVar(i) => {
            let shifted_i = *i - binder_depth;
            if shifted_i >= 0 && (shifted_i as usize) < num_params {
                let param_idx = num_params - 1 - shifted_i as usize;
                if let Some(ref pv) = param_values[param_idx] {
                    shift(binder_depth, 0, pv)
                } else {
                    term.clone()
                }
            } else {
                term.clone()
            }
        }
        Term::TApp(f, a) => Term::TApp(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                f,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
        ),
        Term::TAbs(x, body) => Term::TAbs(
            x.clone(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth + 1,
                body,
            )),
        ),
        Term::TPi(x, a, body, implicit) => Term::TPi(
            x.clone(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth + 1,
                body,
            )),
            *implicit,
        ),
        Term::TUniv(n) => Term::TUniv(n.clone()),
        Term::TProp => Term::TProp,
        Term::TSSet => Term::TSSet,
        Term::TLift(a, lvl) => Term::TLift(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            lvl.clone(),
        ),
        Term::TLower(a) => Term::TLower(b(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            a,
        ))),
        Term::TIntervalTy => Term::TIntervalTy,
        Term::TLevelTy => Term::TLevelTy,
        Term::TInterval(i) => Term::TInterval(i.clone()),
        Term::TCube(cu) => Term::TCube(cu.clone()),
        Term::TPath(a, u, v) => Term::TPath(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                u,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                v,
            )),
        ),
        Term::TId(a, u, v) => Term::TId(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                u,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                v,
            )),
        ),
        Term::TRefl(a) => Term::TRefl(b(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            a,
        ))),
        Term::TJ(motive, base, p) => Term::TJ(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                motive,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                base,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                p,
            )),
        ),
        Term::PLam(x, body) => Term::PLam(
            x.clone(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth + 1,
                body,
            )),
        ),
        Term::PApp(p, r) => Term::PApp(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                p,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                r,
            )),
        ),
        Term::THComp(a, sys, u0) => Term::THComp(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        subst_params_inner(num_params, param_values, binder_depth, phi),
                        subst_params_inner(num_params, param_values, binder_depth, t),
                    )
                })
                .collect(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                u0,
            )),
        ),
        Term::TComp(a, sys, u0) => Term::TComp(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        subst_params_inner(num_params, param_values, binder_depth, phi),
                        subst_params_inner(num_params, param_values, binder_depth, t),
                    )
                })
                .collect(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                u0,
            )),
        ),
        Term::TFill(a, sys, u0) => Term::TFill(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        subst_params_inner(num_params, param_values, binder_depth, phi),
                        subst_params_inner(num_params, param_values, binder_depth, t),
                    )
                })
                .collect(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                u0,
            )),
        ),
        Term::THFill(a, sys, u0) => Term::THFill(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        subst_params_inner(num_params, param_values, binder_depth, phi),
                        subst_params_inner(num_params, param_values, binder_depth, t),
                    )
                })
                .collect(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                u0,
            )),
        ),
        Term::TEquiv(a, bx) => Term::TEquiv(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                bx,
            )),
        ),
        Term::TMkEquiv(a, bx, f, g, eta, eps) => Term::TMkEquiv(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                bx,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                f,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                g,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                eta,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                eps,
            )),
        ),
        Term::TEquivFwd(e, x) => Term::TEquivFwd(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                e,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                x,
            )),
        ),
        Term::TUa(e) => Term::TUa(b(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            e,
        ))),
        Term::TTransport(p, x) => Term::TTransport(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                p,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                x,
            )),
        ),
        Term::TTransp(a, r, x) => Term::TTransp(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                r,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                x,
            )),
        ),
        Term::TGlue(a, phi, te) => Term::TGlue(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                phi,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                te,
            )),
        ),
        Term::TGlueElem(phi, t, a) => Term::TGlueElem(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                phi,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                t,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
        ),
        Term::TUnglue(phi, te, g) => Term::TUnglue(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                phi,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                te,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                g,
            )),
        ),
        Term::TPartial(phi, a) => Term::TPartial(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                phi,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
        ),
        Term::TSystemType(sys) => Term::TSystemType(
            sys.iter()
                .map(|(phi, a)| {
                    (
                        subst_params_inner(num_params, param_values, binder_depth, phi),
                        subst_params_inner(num_params, param_values, binder_depth, a),
                    )
                })
                .collect(),
        ),
        Term::TSigma(x, a, body) => Term::TSigma(
            x.clone(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth + 1,
                body,
            )),
        ),
        Term::TPair(a, bx) => Term::TPair(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                bx,
            )),
        ),
        Term::TFst(p) => Term::TFst(b(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            p,
        ))),
        Term::TSnd(p) => Term::TSnd(b(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            p,
        ))),
        Term::TData(name, params) => Term::TData(
            name.clone(),
            params
                .iter()
                .map(|p| subst_params_inner(num_params, param_values, binder_depth, p))
                .collect(),
        ),
        Term::TCon(data, con, args) => Term::TCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| subst_params_inner(num_params, param_values, binder_depth, a))
                .collect(),
        ),
        Term::TPCon(data, con, args, r) => Term::TPCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| subst_params_inner(num_params, param_values, binder_depth, a))
                .collect(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                r,
            )),
        ),
        Term::TSqCon(data, con, args, r, s) => Term::TSqCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| subst_params_inner(num_params, param_values, binder_depth, a))
                .collect(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                r,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                s,
            )),
        ),
        Term::TCellCon(data, con, args, ivars) => Term::TCellCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| subst_params_inner(num_params, param_values, binder_depth, a))
                .collect(),
            ivars
                .iter()
                .map(|v| subst_params_inner(num_params, param_values, binder_depth, v))
                .collect(),
        ),
        Term::TElim(motive, cases, scrut) => Term::TElim(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                motive,
            )),
            cases
                .iter()
                .map(|case| {
                    let n = case.binders.len() as i32;
                    ElimCase {
                        con: case.con.clone(),
                        binders: case.binders.clone(),
                        body: Box::new(subst_params_inner(
                            num_params,
                            param_values,
                            binder_depth + n,
                            &case.body,
                        )),
                        as_name: case.as_name.clone(),
                        record_bindings: case.record_bindings.clone(),
                        refinements: case.refinements.clone(),
                    }
                })
                .collect(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                scrut,
            )),
        ),
        Term::Meta(_) => term.clone(),
        Term::TBy(tactics) => Term::TBy(
            tactics
                .iter()
                .map(|tac| subst_params_tactic(num_params, param_values, binder_depth, tac))
                .collect(),
        ),
        Term::TProj(field, r) => Term::TProj(
            field.clone(),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                r,
            )),
        ),
        Term::TRecordUpdate(r, updates) => Term::TRecordUpdate(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                r,
            )),
            updates
                .iter()
                .map(|(f, e)| {
                    (
                        f.clone(),
                        subst_params_inner(num_params, param_values, binder_depth, e),
                    )
                })
                .collect(),
        ),
        Term::TDelay(a) => Term::TDelay(b(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            a,
        ))),
        Term::TNext(a) => Term::TNext(b(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            a,
        ))),
        Term::TForce(a) => Term::TForce(b(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            a,
        ))),
        Term::TQuote(a) => Term::TQuote(b(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            a,
        ))),
        Term::TUnquote(a) => Term::TUnquote(b(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            a,
        ))),
        Term::TGetContext => Term::TGetContext,
        Term::TGetType(a) => Term::TGetType(b(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            a,
        ))),
        Term::TUnify(a, bx) => Term::TUnify(
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                a,
            )),
            b(subst_params_inner(
                num_params,
                param_values,
                binder_depth,
                bx,
            )),
        ),
    }
}

fn subst_params_tactic(
    num_params: usize,
    param_values: &[Option<Term>],
    binder_depth: i32,
    tac: &Tactic,
) -> Tactic {
    match tac {
        Tactic::Exact(t) => Tactic::Exact(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            t,
        )),
        Tactic::Apply(t) => Tactic::Apply(subst_params_inner(
            num_params,
            param_values,
            binder_depth,
            t,
        )),
        Tactic::Ring(t) => Tactic::Ring(
            t.as_ref()
                .map(|t| subst_params_inner(num_params, param_values, binder_depth, t)),
        ),
        Tactic::Field(t) => Tactic::Field(
            t.as_ref()
                .map(|t| subst_params_inner(num_params, param_values, binder_depth, t)),
        ),
        Tactic::Group(t) => Tactic::Group(
            t.as_ref()
                .map(|t| subst_params_inner(num_params, param_values, binder_depth, t)),
        ),
        Tactic::Eq => Tactic::Eq,
        Tactic::Reflexivity
        | Tactic::Symmetry
        | Tactic::Split
        | Tactic::Assumption
        | Tactic::Transitivity
        | Tactic::Compute
        | Tactic::Trivial
        | Tactic::Omega => tac.clone(),
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
        Term::TUniv(n) => LevelExpr::max_var(n),
        Term::TProp => -1,
        Term::TSSet => -1,
        Term::TLevelTy => -1,
        Term::TLift(a, _) => max_var(a),
        Term::TLower(a) => max_var(a),
        Term::TIntervalTy => -1,
        Term::TPi(_, a, b, _) => max_var(a).max(max_var(b) - 1).max(-1),
        Term::TInterval(_) => -1,
        Term::TCube(_) => -1,
        Term::TPath(a, u, v) => max_var(a).max(max_var(u)).max(max_var(v)),
        Term::TId(a, u, v) => max_var(a).max(max_var(u)).max(max_var(v)),
        Term::TRefl(a) => max_var(a),
        Term::TJ(motive, base, p) => max_var(motive).max(max_var(base)).max(max_var(p)),
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
        Term::TTransp(a, r, x) => max_var(a).max(max_var(r)).max(max_var(x)),
        Term::TGlue(a, phi, te) => max_var(a).max(max_var(phi)).max(max_var(te)),
        Term::TGlueElem(phi, t, a) => max_var(phi).max(max_var(t)).max(max_var(a)),
        Term::TUnglue(phi, te, g) => max_var(phi).max(max_var(te)).max(max_var(g)),
        Term::TPartial(phi, a) => max_var(phi).max(max_var(a)),
        Term::TSystemType(sys) => {
            let mut m = -1;
            for (phi, a) in sys {
                m = m.max(max_var(phi)).max(max_var(a));
            }
            m
        }
        Term::TSigma(_, a, b) => max_var(a).max(max_var(b) - 1).max(-1),
        Term::TPair(a, b) => max_var(a).max(max_var(b)),
        Term::TFst(p) => max_var(p),
        Term::TSnd(p) => max_var(p),
        Term::TData(_, params) => params.iter().map(max_var).fold(-1, |m, x| m.max(x)),
        Term::TCon(_, _, args) => args.iter().map(max_var).fold(-1, |m, x| m.max(x)),
        Term::TPCon(_, _, args, r) => args
            .iter()
            .map(max_var)
            .fold(-1, |m, x| m.max(x))
            .max(max_var(r)),
        Term::TSqCon(_, _, args, r, s) => args
            .iter()
            .map(max_var)
            .fold(-1, |m, x| m.max(x))
            .max(max_var(r))
            .max(max_var(s)),
        Term::TCellCon(_, _, args, ivars) => args
            .iter()
            .map(max_var)
            .fold(-1, |m, x| m.max(x))
            .max(ivars.iter().map(max_var).fold(-1, |m, x| m.max(x))),
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
        Term::TProj(_, r) => max_var(r),
        Term::TRecordUpdate(r, updates) => {
            let mut m = max_var(r);
            for (_, e) in updates {
                m = m.max(max_var(e));
            }
            m
        }
        Term::TDelay(a) => max_var(a),
        Term::TNext(a) => max_var(a),
        Term::TForce(a) => max_var(a),
        Term::TQuote(a) => max_var(a),
        Term::TUnquote(a) => max_var(a),
        Term::TGetContext => -1,
        Term::TGetType(a) => max_var(a),
        Term::TUnify(a, bx) => max_var(a).max(max_var(bx)),
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
fn b<T>(v: T) -> Arc<T> {
    Arc::new(v)
}

#[cfg(test)]
mod tests {
    use super::positivity::check_datatype_positivity;
    use super::pretty::show_term;
    use super::*;

    fn b(t: Term) -> Arc<Term> {
        Arc::new(t)
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
        let arg = Term::TUniv(LevelExpr::LConst(0));
        let r = beta(&body, &arg);
        assert_eq!(r, Term::TUniv(LevelExpr::LConst(0)));
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
            vec![Term::TCon(
                "Nat".into(),
                "suc".into(),
                vec![Term::TCon("Nat".into(), "zero".into(), vec![])],
            )],
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
                ConSig {
                    name: "zero".into(),
                    arg_tys: vec![],
                },
                ConSig {
                    name: "suc".into(),
                    arg_tys: vec![Term::TData("Nat".into(), vec![])],
                },
            ],
            pcons: vec![],
            sqcons: vec![],
            cellcons: vec![],
            universe_level: None,
            field_names: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }
}
