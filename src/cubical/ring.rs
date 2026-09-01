//! `by ring` — commutative semiring solver over `Nat`.
//!
//! Proves goals of the form `Path Nat u v` where `u` and `v` are polynomial
//! expressions over the context's `Nat` variables, built with the ring
//! operations.  Both sides are canonicalized to a sorted sum of monomials
//! (`add` of `mul (numeral k) (product of atoms)`) and the equality is
//! proved from the law names in `lib/ring_laws.owl`:
//!
//! * `add_comm`/`add_assoc`/`add_0_l`/`add_0_r` for the additive monoid,
//! * `mul_comm`/`mul_assoc`/`mul_1_l`/`mul_1_r`/`mul_0_l`/`mul_0_r` for the
//!   multiplicative monoid,
//! * `mul_add_l`/`mul_add_r` for distributivity,
//! * `_owl_cong_add_*`/`_owl_cong_mul_*`/`_owl_trans`/`_owl_sym` for the
//!   structural glue.
//!
//! The goals reaching this tactic are normalized (definitional unfoldings),
//! so the ring operations appear as their eliminators: `add a b` unfolds to
//! `elim[fun m => Nat] { zero -> b | suc m' -> suc (add m' b) } a` and
//! `mul a b` to `elim[fun m => Nat] { zero -> zero | suc m' -> add (mul m' b) b } a`.
//! The solver recognizes these shapes, and builds its proof against the raw
//! `add`/`mul` operation terms — the kernel connects them definitionally.
//!
//! The constructed proof term is re-checked by the typechecker, so the
//! tactic is sound by construction: any mis-step fails the kernel check and
//! surfaces as an error rather than an unsound proof.

use crate::cubical::nbe::nbe_eval_ctx;
use crate::cubical::session::Session;
use crate::cubical::syntax::{Datatype, Term, shift};
use crate::cubical::typechecker::{Ctx, TypeError, check_dt, infer_dt};
use std::sync::Arc;

/// Extract the ring operations `(add, mul, zero, one)` from a term whose type
/// is a bundled algebra record applied to its parameters — `CommRing A add mul
/// zero one` or `Field A add mul inv zero one`.  The operations are record
/// *parameters*, so they are not `TProj`-able; they live as the record type's
/// `TData` parameter list.  Resolving the operations from the instance's type
/// (instead of by ctx name) makes `ring with C` robust to how the parameters
/// are bound, and is what instance search relies on.
pub(crate) fn ring_ops_from_type(
    dts: &[Datatype],
    ctx: &Ctx,
    inst_term: &Term,
    session: &mut Session,
) -> Result<(Term, Term, Term, Term), TypeError> {
    let inst_ty = infer_dt(dts, ctx, inst_term, session)?;
    match nbe_eval_ctx(ctx.len(), &inst_ty, session) {
        // CommRing A add mul zero one
        Term::TData(dname, params) if dname == "CommRing" && params.len() == 5 => Ok((
            params[1].clone(),
            params[2].clone(),
            params[3].clone(),
            params[4].clone(),
        )),
        // Field A add mul inv zero one
        Term::TData(dname, params) if dname == "Field" && params.len() == 6 => Ok((
            params[1].clone(),
            params[2].clone(),
            params[4].clone(),
            params[5].clone(),
        )),
        other => Err(TypeError::Other(format!(
            "ring: '{}' is not a CommRing/Field record (its type is '{}')",
            inst_term, other,
        ))),
    }
}

/// Carrier type of the bundled record instance (`CommRing ...` params[0]),
/// normalized; `None` when `inst` is not such a record.
fn ring_ops_carrier(
    dts: &[Datatype],
    ctx: &Ctx,
    inst_term: &Term,
    session: &mut Session,
) -> Option<Term> {
    let Ok(inst_ty) = infer_dt(dts, ctx, inst_term, session) else {
        return None;
    };
    match nbe_eval_ctx(ctx.len(), &inst_ty, session) {
        Term::TData(dname, params) if dname == "CommRing" && !params.is_empty() => {
            Some(params[0].clone())
        }
        _ => None,
    }
}

/// Search the context for a bundled algebra record instance whose carrier
/// matches `carrier`: a context variable `C` whose type is
/// `CommRing A ...` or `Field A ...` with `A` definitionally equal to
/// `carrier`.  Returns the `TVar` reference to the instance.
fn find_ring_instance(ctx: &Ctx, carrier: &Term, session: &mut Session) -> Option<Term> {
    let car_nf = nbe_eval_ctx(ctx.len(), carrier, session);
    for (i, (_name, ty)) in ctx.iter().enumerate() {
        // Stored binder types are recorded relative to the binder's own frame
        // (binder at index 0); re-anchor with the same shift `lookup_ctx`
        // applies before comparing against the carrier.
        let ty_shifted = shift(i as i32 + 1, 0, ty);
        if let Term::TData(dname, params) = nbe_eval_ctx(ctx.len(), &ty_shifted, session) {
            let arity = match dname.as_str() {
                "CommRing" => 5,
                "Field" => 6,
                _ => continue,
            };
            if params.len() == arity && nbe_eval_ctx(ctx.len(), &params[0], session) == car_nf {
                return Some(Term::TVar(i as i32));
            }
        }
    }
    None
}

/// A path proof `p : Path Nat a b`, with its endpoints tracked so the
/// proof term can be composed with `trans`/`sym`/congruence lemmas.
#[derive(Clone)]
pub(crate) struct EqP {
    pub(crate) a: Term,
    pub(crate) b: Term,
    pub(crate) p: Term,
}

/// A monomial: `coeff` times the product of `atoms`.  Canonical polynomials
/// are sorted lists of these with distinct atom vectors and positive
/// coefficients.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Mono {
    pub(crate) coeff: i64,
    pub(crate) atoms: Vec<Term>,
}

/// The ring the solver is working over.
///
/// - `Concrete`: the natural numbers. Operations and laws are resolved by
///   name from the context (`lib/ring_laws.owl`), and operations in the
///   goal are recognized by the shape of their normal forms (the `nat_add`/
///   `nat_mul` eliminators).
/// - `Structured`: an abstract commutative ring bundled in the record term
///   given by `ring with C`. Operations, laws, and glue lemmas are resolved
///   as projections of `C`, and operations in the goal are recognized by
///   head-symbol equality with those projections. Numerals are iterated
///   `one + ...` built from `C.add`/`C.one`/`C.zero`.
#[derive(Clone, Copy, PartialEq)]
pub(crate) enum Mode {
    Concrete,
    Structured,
}

/// Resolved references to the ring operations, structural lemmas, and law
/// names. In `Concrete` mode these are global `TVar` references looked up in
/// the context by name; in `Structured` mode they are field projections of
/// the bundled `CommRing` record.
pub(crate) struct Ring {
    pub(crate) add: Term,
    pub(crate) mul: Term,
    pub(crate) zero: Term,
    pub(crate) one: Term,
    pub(crate) trans: Term,
    pub(crate) sym: Term,
    pub(crate) cong_add_l: Term,
    pub(crate) cong_add_r: Term,
    pub(crate) cong_mul_l: Term,
    pub(crate) cong_mul_r: Term,
    pub(crate) add_comm: Term,
    pub(crate) add_assoc: Term,
    pub(crate) add_0_l: Term,
    pub(crate) add_0_r: Term,
    pub(crate) mul_comm: Term,
    pub(crate) mul_assoc: Term,
    pub(crate) mul_1_l: Term,
    pub(crate) mul_1_r: Term,
    pub(crate) mul_0_l: Term,
    pub(crate) mul_0_r: Term,
    pub(crate) mul_add_l: Term,
    pub(crate) mul_add_r: Term,
    pub(crate) ctx_len: usize,
    pub(crate) mode: Mode,
    /// True when the carrier datatype is `Nat`: numerals are then the
    /// constructor suc-chain `TCon("Nat","suc",..)` form, recognized and
    /// emitted accordingly (the abstract `add one (...)` canonical form
    /// would not match user-written suc literals).
    pub(crate) numerals_are_suc: bool,
}

impl Ring {
    pub(crate) fn resolve(
        dts: &[Datatype],
        ctx: &Ctx,
        ring_term: Option<&Term>,
        session: &mut Session,
    ) -> Result<Ring, TypeError> {
        let mode = if ring_term.is_some() {
            Mode::Structured
        } else {
            Mode::Concrete
        };
        let var = |name: &str| -> Result<Term, TypeError> {
            let gi = ctx.iter().position(|(n, _)| n == name).ok_or_else(|| {
                TypeError::Other(format!(
                    "ring: missing lemma '{}'; import lib/ring_laws.owl",
                    name
                ))
            })?;
            Ok(Term::TVar(gi as i32))
        };
        let proj = |field: &str| -> Result<Term, TypeError> {
            let c = ring_term.ok_or_else(|| {
                TypeError::Other(
                    "ring: internal error — structured mode without a ring term".into(),
                )
            })?;
            Ok(Term::TProj(field.to_string(), Arc::new(c.clone())))
        };
        // The ring operations. In `Concrete` mode these are the globals
        // `add`/`mul`/`zero`/`one`; in `Structured` mode they are extracted
        // from the bundled record's type (`CommRing A add mul zero one` /
        // `Field A add mul inv zero one`), so they work regardless of how the
        // parameter names are bound in the context.
        // Numerals are suc-chains exactly when the carrier is concrete Nat.
        let numerals_are_suc = match mode {
            Mode::Concrete => true,
            Mode::Structured => {
                let carrier_nf = ring_term
                    .and_then(|c| ring_ops_carrier(dts, ctx, c, session))
                    .map(|c| nbe_eval_ctx(ctx.len(), &c, session));
                matches!(
                    carrier_nf,
                    Some(Term::TData(d, ref p)) if d == "Nat" && p.is_empty()
                )
            }
        };
        let mut op = |name: &str| -> Result<Term, TypeError> {
            match mode {
                Mode::Concrete => var(name),
                Mode::Structured => {
                    let c = ring_term.unwrap();
                    let (add, mul, zero, one) = ring_ops_from_type(dts, ctx, c, session)?;
                    match name {
                        "add" => Ok(add),
                        "mul" => Ok(mul),
                        "zero" => Ok(zero),
                        "one" => Ok(one),
                        _ => Err(TypeError::Other(format!(
                            "ring: unknown operation '{}'",
                            name
                        ))),
                    }
                }
            }
        };
        // The structural glue and law lemmas. In `Concrete` mode these are the
        // `_owl_*`/`add_*`/`mul_*` globals; in `Structured` mode they are
        // field projections of the bundled `CommRing` record.
        let law = |field: &str, name: &str| -> Result<Term, TypeError> {
            match mode {
                Mode::Concrete => var(name),
                Mode::Structured => proj(field),
            }
        };
        Ok(Ring {
            ctx_len: ctx.len(),
            mode,
            numerals_are_suc,
            add: op("add")?,
            mul: op("mul")?,
            zero: op("zero")?,
            one: op("one")?,
            trans: law("trans", "_owl_trans")?,
            sym: law("sym", "_owl_sym")?,
            cong_add_l: law("cong_add_l", "_owl_cong_add_l")?,
            cong_add_r: law("cong_add_r", "_owl_cong_add_r")?,
            cong_mul_l: law("cong_mul_l", "_owl_cong_mul_l")?,
            cong_mul_r: law("cong_mul_r", "_owl_cong_mul_r")?,
            add_comm: law("add_comm", "add_comm")?,
            add_assoc: law("add_assoc", "add_assoc")?,
            add_0_l: law("add_0_l", "add_0_l")?,
            add_0_r: law("add_0_r", "add_0_r")?,
            mul_comm: law("mul_comm", "mul_comm")?,
            mul_assoc: law("mul_assoc", "mul_assoc")?,
            mul_1_l: law("mul_1_l", "mul_1_l")?,
            mul_1_r: law("mul_1_r", "mul_1_r")?,
            mul_0_l: law("mul_0_l", "mul_0_l")?,
            mul_0_r: law("mul_0_r", "mul_0_r")?,
            mul_add_l: law("mul_add_l", "mul_add_l")?,
            mul_add_r: law("mul_add_r", "mul_add_r")?,
        })
    }
}

// ---------------------------------------------------------------------------
// Term / proof-term plumbing
// ---------------------------------------------------------------------------

pub(crate) fn app(f: &Term, a: &Term) -> Term {
    Term::TApp(Arc::new(f.clone()), Arc::new(a.clone()))
}

pub(crate) fn inst(f: &Term, args: &[&Term]) -> Term {
    args.iter().fold(f.clone(), |acc, a| app(&acc, a))
}

/// Path reflection: `Path t t`.
pub(crate) fn refl(t: &Term) -> Term {
    Term::PLam("_i".into(), Arc::new(shift(1, 0, t)))
}

/// `refl` adjusted to the declared endpoints `a`, `b` — valid when `a` and
/// `b` are definitionally equal (the kernel accepts `Path a a` as `Path a b`).
pub(crate) fn refl2(a: &Term, b: &Term) -> EqP {
    EqP {
        a: a.clone(),
        b: b.clone(),
        p: refl(a),
    }
}

pub(crate) fn trp(r: &Ring, p: &EqP, q: &EqP) -> EqP {
    EqP {
        a: p.a.clone(),
        b: q.b.clone(),
        p: inst(&r.trans, &[&p.a, &p.b, &q.b, &p.p, &q.p]),
    }
}

pub(crate) fn syp(r: &Ring, p: &EqP) -> EqP {
    EqP {
        a: p.b.clone(),
        b: p.a.clone(),
        p: inst(&r.sym, &[&p.a, &p.b, &p.p]),
    }
}

pub(crate) fn cong_add_l(r: &Ring, p: &EqP, n: &Term) -> EqP {
    EqP {
        a: app(&app(&r.add, &p.a), n),
        b: app(&app(&r.add, &p.b), n),
        p: inst(&r.cong_add_l, &[&p.a, &p.b, n, &p.p]),
    }
}

pub(crate) fn cong_add_r(r: &Ring, p: &EqP, m: &Term) -> EqP {
    EqP {
        a: app(&app(&r.add, m), &p.a),
        b: app(&app(&r.add, m), &p.b),
        p: inst(&r.cong_add_r, &[&p.a, &p.b, m, &p.p]),
    }
}

pub(crate) fn cong_mul_l(r: &Ring, p: &EqP, n: &Term) -> EqP {
    EqP {
        a: app(&app(&r.mul, &p.a), n),
        b: app(&app(&r.mul, &p.b), n),
        p: inst(&r.cong_mul_l, &[&p.a, &p.b, n, &p.p]),
    }
}

pub(crate) fn cong_mul_r(r: &Ring, p: &EqP, m: &Term) -> EqP {
    EqP {
        a: app(&app(&r.mul, m), &p.a),
        b: app(&app(&r.mul, m), &p.b),
        p: inst(&r.cong_mul_r, &[&p.a, &p.b, m, &p.p]),
    }
}

// ---------------------------------------------------------------------------
// Canonical term construction
// ---------------------------------------------------------------------------

/// The natural number `k` as a constructor numeral: `suc (suc ... zero)`.
/// The canonical term for the numeral `k`.
///
/// - `Concrete`: the Nat constructor numeral `suc^k zero`.
/// - `Structured`: `zero` for 0 and right-associated `add one (add one ...)`
///   otherwise, built from the bundled ring's projections.
pub(crate) fn numeral(r: &Ring, k: i64) -> Term {
    match r.mode {
        Mode::Concrete => {
            let mut t = Term::TCon("Nat".into(), "zero".into(), Vec::new());
            for _ in 0..k {
                t = Term::TCon("Nat".into(), "suc".into(), vec![t]);
            }
            t
        }
        Mode::Structured => {
            if r.numerals_are_suc {
                // Concrete Nat carrier: emit the constructor chain so goal
                // occurrences written as suc-literals match syntactically.
                let mut t = Term::TCon("Nat".into(), "zero".into(), Vec::new());
                for _ in 0..k {
                    t = Term::TCon("Nat".into(), "suc".into(), vec![t]);
                }
                return t;
            }
            let mut t = r.zero.clone();
            for _ in 0..k {
                t = app(&app(&r.add, &r.one), &t);
            }
            t
        }
    }
}

/// Recognize a numeral term, returning the count.  In `Structured` mode only
/// the canonical shapes are recognized (`zero`, `add one (add one ...)`), so
/// the recognized term may still need a propositional proof to equal
/// `numeral(k)` — see `numeral_refl_eq`.
pub(crate) fn numeral_of(r: &Ring, t: &Term, session: &mut Session) -> Option<i64> {
    match r.mode {
        Mode::Concrete => match t {
            Term::TCon(d, c, args) if d == "Nat" && c == "zero" && args.is_empty() => Some(0),
            Term::TCon(d, c, args) if d == "Nat" && c == "suc" && args.len() == 1 => {
                numeral_of(r, &args[0], session).map(|k| k + 1)
            }
            _ => None,
        },
        Mode::Structured => {
            // Raw syntactic match first: concrete global `add` unfolds under
            // nbe and would destroy the head symbol.
            if *t == r.zero {
                return Some(0);
            }
            if let Term::TApp(outer, inner) = t {
                if let Term::TApp(g, one_t) = outer.as_ref() {
                    let g_nf = crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, g, session);
                    let add_nf = crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, &r.add, session);
                    if g_nf == add_nf && **one_t == r.one {
                        return numeral_of(r, inner, session).map(|j| j + 1);
                    }
                }
            }
            if r.numerals_are_suc {
                if let Some(k) = nat_suc_chain(t) {
                    return Some(k);
                }
            }
            let nf = crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, t, session);
            if nf == r.zero {
                return Some(0);
            }
            if nf == r.one {
                return Some(1);
            }
            match nf {
                Term::TApp(outer, inner) => match outer.as_ref() {
                    Term::TApp(g, one_t) if **g == r.add && **one_t == r.one => {
                        numeral_of(r, &inner, session).map(|j| j + 1)
                    }
                    _ => None,
                },
                _ => None,
            }
        }
    }
}

/// Recognize the concrete-Nat suc-chain numerals (`zero`, `suc zero`, ...)
/// against `numeral_of`'s count.
fn nat_suc_chain(t: &Term) -> Option<i64> {
    match t {
        Term::TCon(d, c, args) if d == "Nat" && c == "zero" && args.is_empty() => Some(0),
        Term::TCon(d, c, args) if d == "Nat" && c == "suc" && args.len() == 1 => {
            nat_suc_chain(&args[0]).map(|k| k + 1)
        }
        _ => None,
    }
}

/// In `Structured` mode, prove `t = numeral(k)` for a term `t` recognized as
/// the numeral `k` by `numeral_of` (which may be written non-canonically,
/// e.g. `add one zero`).
fn numeral_refl_eq(r: &Ring, t: &Term, k: i64) -> EqP {
    // Concrete Nat carrier: both the user-written suc-chain and the emitted
    // numeral are the same constructor chain, so the equation is rfl.
    if r.numerals_are_suc {
        return EqP {
            a: t.clone(),
            b: numeral(r, k),
            p: refl(t),
        };
    }
    if k == 0 {
        return EqP {
            a: t.clone(),
            b: r.zero.clone(),
            p: refl(t),
        };
    }
    match t {
        Term::TApp(outer, inner) => {
            if let Term::TApp(g, one_t) = &**outer {
                if **g == r.add && **one_t == r.one {
                    let inner_eq = numeral_refl_eq(r, inner, k - 1);
                    let p = cong_add_r(r, &inner_eq, &r.one);
                    return EqP {
                        a: t.clone(),
                        b: numeral(r, k),
                        p: p.p,
                    };
                }
            }
            EqP {
                a: t.clone(),
                b: numeral(r, k),
                p: refl(t),
            }
        }
        // t == one, k == 1: `one = add one zero`.
        _ => EqP {
            a: t.clone(),
            b: numeral(r, 1),
            p: syp(
                r,
                &EqP {
                    a: app(&app(&r.add, &r.one), &r.zero),
                    b: r.one.clone(),
                    p: inst(&r.add_0_r, &[&r.one]),
                },
            )
            .p,
        },
    }
}

/// `mul (numeral 1) x = x` over an abstract ring.  The bundled `mul_1_l`
/// only covers `mul one x`, not the numeral-fold `one` (`add one zero`), so
/// this pushes the folded one in via `mul_add_r`/`mul_1_l`/`mul_0_l`/
/// `add_0_r`.
fn numeral_one_left_mul_eq(r: &Ring, x: &Term) -> EqP {
    let mul_one_x = app(&app(&r.mul, &r.one), x);
    let mul_zero_x = app(&app(&r.mul, &r.zero), x);
    let lhs = app(&app(&r.mul, &numeral(r, 1)), x);
    let mid = app(&app(&r.add, &mul_one_x), &mul_zero_x);
    let e_mr = EqP {
        a: lhs.clone(),
        b: mid.clone(),
        p: inst(&r.mul_add_r, &[&r.one, &r.zero, x]),
    };
    let e_m1 = cong_add_l(
        r,
        &EqP {
            a: mul_one_x.clone(),
            b: x.clone(),
            p: inst(&r.mul_1_l, &[x]),
        },
        &mul_zero_x,
    );
    let e_m0 = cong_add_r(
        r,
        &EqP {
            a: mul_zero_x,
            b: r.zero.clone(),
            p: inst(&r.mul_0_l, &[x]),
        },
        x,
    );
    let e_0r = EqP {
        a: app(&app(&r.add, x), &r.zero),
        b: x.clone(),
        p: inst(&r.add_0_r, &[x]),
    };
    let p = trp(r, &trp(r, &trp(r, &e_mr, &e_m1), &e_m0), &e_0r);
    EqP {
        a: lhs,
        b: x.clone(),
        p: p.p,
    }
}

/// Right-associated product of `atoms` (`mul a1 (mul a2 ...)`).
pub(crate) fn prod_term(r: &Ring, atoms: &[Term]) -> Term {
    let mut t = r.one.clone();
    for a in atoms.iter().rev() {
        t = app(&app(&r.mul, a), &t);
    }
    t
}

/// The canonical term for a monomial.
///
/// In `Structured` mode the coefficient is always wrapped in `mul (numeral k)
/// _` (even `mul (numeral 1) _` and constant monomials become `mul (numeral k)
/// one`), so that canonical forms are built from the exact same projection
/// head symbols regardless of how the goal was written — the shape glues in
/// the polynomial arithmetic then hold definitionally, and the coefficient
/// arithmetic (`numeral_add_eq`/`numeral_mul_eq`) is proved propositionally.
pub(crate) fn mono_term(r: &Ring, m: &Mono) -> Term {
    if m.atoms.is_empty() && r.mode == Mode::Concrete {
        return numeral(r, m.coeff);
    }
    let p = prod_term(r, &m.atoms);
    if m.coeff == 1 && r.mode == Mode::Concrete {
        p
    } else {
        app(&app(&r.mul, &numeral(r, m.coeff)), &p)
    }
}

/// Right-associated sum of canonical monomial terms.
pub(crate) fn sum_term(r: &Ring, poly: &[Mono]) -> Term {
    let mut t = r.zero.clone();
    for m in poly.iter().rev() {
        t = app(&app(&r.add, &mono_term(r, m)), &t);
    }
    t
}

pub(crate) fn canon_term(r: &Ring, poly: &[Mono]) -> Term {
    sum_term(r, poly)
}

/// Deterministic total order on terms (by pretty-print), used for sorting
/// monomial atoms.
fn term_ord(t: &Term) -> String {
    format!("{}", t)
}

fn atoms_key(m: &Mono) -> Vec<String> {
    m.atoms.iter().map(term_ord).collect()
}

// ---------------------------------------------------------------------------
// Operation-shape recognition
// ---------------------------------------------------------------------------

fn is_nat_motive(t: &Term) -> bool {
    matches!(t, Term::TAbs(_, body)
        if matches!(&**body, Term::TData(d, p) if d == "Nat" && p.is_empty()))
}

/// The add-eliminator shape: `elim[fun _ => Nat] { zero -> _ | suc m' -> suc (_) } _`.
fn is_addshape_elim(t: &Term) -> bool {
    match t {
        Term::TElim(motive, cases, _) => {
            is_nat_motive(motive)
                && cases.len() == 2
                && cases[0].con == "zero"
                && cases[0].binders.is_empty()
                && cases[1].con == "suc"
                && cases[1].binders.len() == 1
                && matches!(
                    &*cases[1].body,
                    Term::TCon(d, c, args)
                        if d == "Nat" && c == "suc" && args.len() == 1
                )
        }
        _ => false,
    }
}

/// Is `t` an add-call whose normal form is the add-eliminator? Accepts both the
/// unfolded eliminator and a stuck application of the `add` global (which is
/// what an add-call with neutral arguments reduces to). `t` is read in a
/// case-body frame, i.e. under one extra binder.
fn is_add_call(r: &Ring, t: &Term, session: &mut Session) -> bool {
    match t {
        Term::TApp(_, _) => {
            let nf = crate::cubical::nbe::nbe_eval_ctx(r.ctx_len + 1, t, session);
            is_addshape_elim(&nf)
        }
        _ => is_addshape_elim(t),
    }
}

/// The mul-eliminator shape:
/// `elim[fun _ => Nat] { zero -> zero | suc m' -> add (mul m' _) _ } _`.
fn is_mulshape_elim(r: &Ring, t: &Term, session: &mut Session) -> bool {
    match t {
        Term::TElim(motive, cases, _) => {
            if !(is_nat_motive(motive)
                && cases.len() == 2
                && cases[0].con == "zero"
                && cases[0].binders.is_empty()
                && cases[1].con == "suc"
                && cases[1].binders.len() == 1)
            {
                return false;
            }
            let zero_body = matches!(
                &*cases[0].body,
                Term::TCon(d, c, args) if d == "Nat" && c == "zero" && args.is_empty()
            );
            // suc-case body must be an add-call: `add (mul m' b) b`.
            let suc_body_is_add = is_add_call(r, &cases[1].body, session);
            zero_body && suc_body_is_add
        }
        _ => false,
    }
}

/// Syntactic binary-spine match: if `t` is literally `op a b` (head term
/// structurally equal to `op`, exactly two arguments) return `(a, b)`
/// without normalizing.  Concrete global operations unfold under nbe even
/// on neutral arguments, destroying the head symbol; matching the raw
/// elaborated term first keeps structured mode working over bundled
/// concrete instances such as `NatCommRing`.
fn raw_as_binop(r: &Ring, op: &Term, t: &Term, session: &mut Session) -> Option<(Term, Term)> {
    if let Term::TApp(outer, b) = t {
        if let Term::TApp(g, a) = &**outer {
            // The head may carry a different de Bruijn offset than the
            // resolved op term (the raw annotation is shifted by the
            // definition slot); comparing their normal forms is a cheap
            // single-symbol check that tolerates that shift.
            let g_nf = crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, g, session);
            let op_nf = crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, op, session);
            if g_nf == op_nf {
                return Some(((**a).clone(), (**b).clone()));
            }
        }
    }
    None
}

/// Treat `t` as an `add` operation, returning `(a, b)` with `t ~ add a b`.
///
/// - `Concrete`: the operation may be the unfolded eliminator or a stuck
///   application of the `add` global; normalize the latter so both give the
///   eliminator normal form.
/// - `Structured`: normalize `t` and match its head symbol against the
///   bundled ring's `add` projection (both compared in normal form).
pub(crate) fn as_add(r: &Ring, t: &Term, session: &mut Session) -> Option<(Term, Term)> {
    match r.mode {
        Mode::Concrete => {
            let nf = match t {
                Term::TApp(_, _) => crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, t, session),
                _ => t.clone(),
            };
            if is_addshape_elim(&nf) {
                if let Term::TElim(_, cases, scrut) = nf {
                    return Some(((*scrut).clone(), (*cases[0].body).clone()));
                }
            }
            None
        }
        Mode::Structured => {
            if let Some(res) = raw_as_binop(r, &r.add, t, session) {
                return Some(res);
            }
            let nf = crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, t, session);
            match nf {
                Term::TApp(outer, b) => match outer.as_ref() {
                    Term::TApp(g, a) => {
                        let add_nf = crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, &r.add, session);
                        if crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, g, session) == add_nf {
                            Some((a.as_ref().clone(), b.as_ref().clone()))
                        } else {
                            None
                        }
                    }
                    _ => None,
                },
                _ => None,
            }
        }
    }
}

/// The second argument of the mul-eliminator, extracted from the suc-case
/// body `add (mul m' b) b` (dropping the case binder's shift).
fn mul_suc_arg(body: &Term) -> Term {
    if let Term::TApp(f, arg) = body {
        if let Term::TApp(_, _) = &**f {
            return shift(-1, 0, arg);
        }
    }
    shift(-1, 0, body)
}

/// Treat `t` as a `mul` operation, returning `(a, b)` with `t ~ mul a b`.
pub(crate) fn as_mul(r: &Ring, t: &Term, session: &mut Session) -> Option<(Term, Term)> {
    match r.mode {
        Mode::Concrete => {
            let nf = match t {
                Term::TApp(_, _) => crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, t, session),
                _ => t.clone(),
            };
            if is_mulshape_elim(r, &nf, session) {
                if let Term::TElim(_, cases, scrut) = nf {
                    let arg = mul_suc_arg(&cases[1].body);
                    return Some(((*scrut).clone(), arg));
                }
            }
            None
        }
        Mode::Structured => {
            if let Some(res) = raw_as_binop(r, &r.mul, t, session) {
                return Some(res);
            }
            let nf = crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, t, session);
            match nf {
                Term::TApp(outer, b) => match outer.as_ref() {
                    Term::TApp(g, a) => {
                        let mul_nf = crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, &r.mul, session);
                        if crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, g, session) == mul_nf {
                            Some((a.as_ref().clone(), b.as_ref().clone()))
                        } else {
                            None
                        }
                    }
                    _ => None,
                },
                _ => None,
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Reification
// ---------------------------------------------------------------------------

/// Reify `t` into a canonical polynomial with a proof `Path t canon`.
pub(crate) fn decomp(
    r: &Ring,
    t: &Term,
    session: &mut Session,
) -> Result<(Vec<Mono>, EqP), TypeError> {
    crate::debug_log!(
        "decomp: {}",
        crate::cubical::syntax::pretty::show_term(&[], t)
    );
    if let Some((s, z)) = as_add(r, t, session) {
        let (ps, pfs) = decomp(r, &s, session)?;
        let (pz, pfz) = decomp(r, &z, session)?;
        return reify_add(r, &s, &ps, &pfs, &z, &pz, &pfz);
    }
    if let Some((s, a)) = as_mul(r, t, session) {
        let (ps, pfs) = decomp(r, &s, session)?;
        let (pa, pfa) = decomp(r, &a, session)?;
        return reify_mul(r, &s, &ps, &pfs, &a, &pa, &pfa);
    }
    if let Some(k) = numeral_of(r, t, session) {
        if k == 0 {
            return Ok((
                Vec::new(),
                EqP {
                    a: t.clone(),
                    b: r.zero.clone(),
                    p: refl(t),
                },
            ));
        }
        let mono = Mono {
            coeff: k,
            atoms: Vec::new(),
        };
        let canon = canon_term(r, &[mono.clone()]);
        let pf = match r.mode {
            // canon = add (numeral k) zero; `t` is the literal numeral.
            Mode::Concrete => syp(
                r,
                &EqP {
                    a: canon.clone(),
                    b: numeral(r, k),
                    p: inst(&r.add_0_r, &[&numeral(r, k)]),
                },
            ),
            // canon = add (mul (numeral k) one) zero; prove t = numeral k,
            // numeral k = mul (numeral k) one, then add-0-r.
            Mode::Structured => {
                let e1 = numeral_refl_eq(r, t, k);
                let e2 = syp(
                    r,
                    &EqP {
                        a: app(&app(&r.mul, &numeral(r, k)), &r.one),
                        b: numeral(r, k),
                        p: inst(&r.mul_1_r, &[&numeral(r, k)]),
                    },
                );
                let e3 = syp(
                    r,
                    &EqP {
                        a: canon.clone(),
                        b: app(&app(&r.mul, &numeral(r, k)), &r.one),
                        p: inst(&r.add_0_r, &[&app(&app(&r.mul, &numeral(r, k)), &r.one)]),
                    },
                );
                trp(r, &trp(r, &e1, &e2), &e3)
            }
        };
        return Ok((
            vec![mono],
            EqP {
                a: t.clone(),
                b: canon,
                p: pf.p,
            },
        ));
    }
    let atom_mono = Mono {
        coeff: 1,
        atoms: vec![t.clone()],
    };
    let atom = mono_term(r, &atom_mono);
    let canon = canon_term(r, &[atom_mono.clone()]);
    let pf = match r.mode {
        // atom = mul t one; canon = add (mul t one) zero.
        Mode::Concrete => {
            let p1 = syp(
                r,
                &EqP {
                    a: atom.clone(),
                    b: t.clone(),
                    p: inst(&r.mul_1_r, &[t]),
                },
            );
            let p2 = syp(
                r,
                &EqP {
                    a: canon.clone(),
                    b: atom.clone(),
                    p: inst(&r.add_0_r, &[&atom]),
                },
            );
            trp(r, &p1, &p2)
        }
        // atom = mul (numeral 1) (mul t one); canon = add atom zero.
        Mode::Structured => {
            let prod = prod_term(r, &[t.clone()]);
            let p1 = syp(
                r,
                &EqP {
                    a: prod.clone(),
                    b: t.clone(),
                    p: inst(&r.mul_1_r, &[t]),
                },
            );
            let p2 = syp(r, &numeral_one_left_mul_eq(r, &prod));
            let p3 = syp(
                r,
                &EqP {
                    a: canon.clone(),
                    b: atom.clone(),
                    p: inst(&r.add_0_r, &[&atom]),
                },
            );
            trp(r, &trp(r, &p1, &p2), &p3)
        }
    };
    Ok((
        vec![atom_mono],
        EqP {
            a: t.clone(),
            b: canon,
            p: pf.p,
        },
    ))
}

fn reify_add(
    r: &Ring,
    s: &Term,
    ps: &[Mono],
    pfs: &EqP,
    z: &Term,
    pz: &[Mono],
    pfz: &EqP,
) -> Result<(Vec<Mono>, EqP), TypeError> {
    let s_c = canon_term(r, ps);
    let p1 = trp(r, &cong_add_l(r, pfs, z), &cong_add_r(r, pfz, &s_c));
    let (p_m, pf_m) = poly_merge(r, ps, pz);
    let b = canon_term(r, &p_m);
    Ok((
        p_m,
        EqP {
            a: app(&app(&r.add, s), z),
            b,
            p: trp(r, &p1, &pf_m).p,
        },
    ))
}

fn reify_mul(
    r: &Ring,
    s: &Term,
    ps: &[Mono],
    pfs: &EqP,
    a: &Term,
    pa: &[Mono],
    pfa: &EqP,
) -> Result<(Vec<Mono>, EqP), TypeError> {
    let s_c = canon_term(r, ps);
    let p1 = trp(r, &cong_mul_l(r, pfs, a), &cong_mul_r(r, pfa, &s_c));
    let (products, pf_exp) = expand(r, ps, pa);
    let (p_sum, pf_sum) = sum_canon(r, &products);
    let b = canon_term(r, &p_sum);
    Ok((
        p_sum,
        EqP {
            a: app(&app(&r.mul, s), a),
            b,
            p: trp(r, &trp(r, &p1, &pf_exp), &pf_sum).p,
        },
    ))
}

// ---------------------------------------------------------------------------
// Polynomial arithmetic with proofs
// ---------------------------------------------------------------------------

/// `add (canon pa) (canon pb) = canon (pa + pb)` for sorted polys.
pub(crate) fn poly_merge(r: &Ring, pa: &[Mono], pb: &[Mono]) -> (Vec<Mono>, EqP) {
    let c_pb = canon_term(r, pb);
    match pa {
        [] => (
            pb.to_vec(),
            EqP {
                a: app(&app(&r.add, &r.zero), &c_pb),
                b: c_pb.clone(),
                p: inst(&r.add_0_l, &[&c_pb]),
            },
        ),
        [m, rest @ ..] => {
            let m_term = mono_term(r, m);
            let c_rest = sum_term(r, rest);
            let a = app(&app(&r.add, &app(&app(&r.add, &m_term), &c_rest)), &c_pb);
            let mid = app(&app(&r.add, &m_term), &app(&app(&r.add, &c_rest), &c_pb));
            let p_assoc = inst(&r.add_assoc, &[&m_term, &c_rest, &c_pb]);
            let (p_r, pf_r) = poly_merge(r, rest, pb);
            let p_ctx = cong_add_r(r, &pf_r, &m_term);
            let (p_i, pf_i) = insert(r, m, &p_r);
            let p = trp(
                r,
                &trp(
                    r,
                    &EqP {
                        a: a.clone(),
                        b: mid,
                        p: p_assoc,
                    },
                    &p_ctx,
                ),
                &pf_i,
            );
            let b = canon_term(r, &p_i);
            (p_i, EqP { a, b, p: p.p })
        }
    }
}

/// Insert a monomial into a sorted poly:
/// `add m_term (canon sorted) = canon (inserted)`.
fn insert(r: &Ring, m: &Mono, sorted: &[Mono]) -> (Vec<Mono>, EqP) {
    let m_term = mono_term(r, m);
    match sorted {
        [] => {
            let canon = app(&app(&r.add, &m_term), &r.zero);
            let p = refl(&canon);
            (
                vec![m.clone()],
                EqP {
                    a: canon.clone(),
                    b: canon,
                    p,
                },
            )
        }
        [h, rest @ ..] => {
            let h_term = mono_term(r, h);
            let c_rest = sum_term(r, rest);
            let a = app(&app(&r.add, &m_term), &app(&app(&r.add, &h_term), &c_rest));
            let km = atoms_key(m);
            let kh = atoms_key(h);
            if km < kh {
                let mut res = vec![m.clone()];
                res.extend(sorted.iter().cloned());
                (
                    res,
                    EqP {
                        a: a.clone(),
                        b: a.clone(),
                        p: refl(&a),
                    },
                )
            } else if km == kh {
                let k = m.coeff + h.coeff;
                let combined = Mono {
                    coeff: k,
                    atoms: m.atoms.clone(),
                };
                let c_term = mono_term(r, &combined);
                let p_assoc = syp(
                    r,
                    &EqP {
                        a: app(&app(&r.add, &app(&app(&r.add, &m_term), &h_term)), &c_rest),
                        b: a.clone(),
                        p: inst(&r.add_assoc, &[&m_term, &h_term, &c_rest]),
                    },
                );
                let p_comb = combine_proof(r, m, h, &combined);
                let p2 = cong_add_l(r, &p_comb, &c_rest);
                let p = trp(r, &p_assoc, &p2);
                let mut res = vec![combined];
                res.extend(rest.iter().cloned());
                (
                    res,
                    EqP {
                        a,
                        b: app(&app(&r.add, &c_term), &c_rest),
                        p: p.p,
                    },
                )
            } else {
                let p_swap = {
                    let p1 = syp(
                        r,
                        &EqP {
                            a: app(&app(&r.add, &app(&app(&r.add, &m_term), &h_term)), &c_rest),
                            b: a.clone(),
                            p: inst(&r.add_assoc, &[&m_term, &h_term, &c_rest]),
                        },
                    );
                    let c = inst(&r.add_comm, &[&m_term, &h_term]);
                    let c1 = cong_add_l(
                        r,
                        &EqP {
                            a: app(&app(&r.add, &m_term), &h_term),
                            b: app(&app(&r.add, &h_term), &m_term),
                            p: c,
                        },
                        &c_rest,
                    );
                    let p3 = inst(&r.add_assoc, &[&h_term, &m_term, &c_rest]);
                    trp(
                        r,
                        &trp(r, &p1, &c1),
                        &EqP {
                            a: app(&app(&r.add, &app(&app(&r.add, &h_term), &m_term)), &c_rest),
                            b: app(&app(&r.add, &h_term), &app(&app(&r.add, &m_term), &c_rest)),
                            p: p3,
                        },
                    )
                };
                let (p_r, pf_r) = insert(r, m, rest);
                let p2 = cong_add_r(r, &pf_r, &h_term);
                let p = trp(r, &p_swap, &p2);
                let mut res = vec![h.clone()];
                res.extend(p_r);
                let b = app(&app(&r.add, &h_term), &sum_term(r, &res[1..]));
                (res, EqP { a, b, p: p.p })
            }
        }
    }
}

/// `add m_term h_term = combined_term` for two monomials with equal atoms.
fn combine_proof(r: &Ring, m: &Mono, h: &Mono, combined: &Mono) -> EqP {
    let m_term = mono_term(r, m);
    let h_term = mono_term(r, h);
    let c_term = mono_term(r, combined);
    let a = app(&app(&r.add, &m_term), &h_term);
    let b = c_term;
    match r.mode {
        // Over Nat, `add (numeral k1) (numeral k2)` computes to the numeral
        // for the sum, so `refl` glues the coefficient-combining steps.
        Mode::Concrete => {
            if m.atoms.is_empty() {
                refl2(&a, &b)
            } else {
                let ka = numeral(r, m.coeff);
                let kb = numeral(r, h.coeff);
                let p = prod_term(r, &m.atoms);
                let p_mr = syp(
                    r,
                    &EqP {
                        a: app(&app(&r.mul, &app(&app(&r.add, &ka), &kb)), &p),
                        b: app(
                            &app(&r.add, &app(&app(&r.mul, &ka), &p)),
                            &app(&app(&r.mul, &kb), &p),
                        ),
                        p: inst(&r.mul_add_r, &[&ka, &kb, &p]),
                    },
                );
                trp(r, &trp(r, &refl2(&a, &p_mr.a), &p_mr), &refl2(&p_mr.b, &b))
            }
        }
        // Over an abstract ring, `add (numeral k1) (numeral k2) = numeral (k1
        // + k2)` needs `add_assoc` and is proved by `numeral_add_eq`; the
        // coefficient is distributed over the shared atom product with
        // `mul_add_r`.
        Mode::Structured => {
            let p = prod_term(r, &m.atoms);
            let ka = numeral(r, m.coeff);
            let kb = numeral(r, h.coeff);
            let p_mr = syp(
                r,
                &EqP {
                    a: app(&app(&r.mul, &app(&app(&r.add, &ka), &kb)), &p),
                    b: app(
                        &app(&r.add, &app(&app(&r.mul, &ka), &p)),
                        &app(&app(&r.mul, &kb), &p),
                    ),
                    p: inst(&r.mul_add_r, &[&ka, &kb, &p]),
                },
            );
            let p_comb = cong_mul_l(r, &numeral_add_eq(r, m.coeff, h.coeff), &p);
            trp(r, &p_mr, &p_comb)
        }
    }
}

/// `add (numeral a) (numeral b) = numeral (a + b)` over an abstract ring,
/// proved from `add_assoc`/`add_0_l` by iterating the left addend.
fn numeral_add_eq(r: &Ring, a: i64, b: i64) -> EqP {
    let nb = numeral(r, b);
    if a == 0 {
        return EqP {
            a: app(&app(&r.add, &r.zero), &nb),
            b: nb.clone(),
            p: inst(&r.add_0_l, &[&nb]),
        };
    }
    let na1 = numeral(r, a - 1);
    let lhs = app(&app(&r.add, &app(&app(&r.add, &r.one), &na1)), &nb);
    let mid = app(&app(&r.add, &r.one), &app(&app(&r.add, &na1), &nb));
    let p_assoc = inst(&r.add_assoc, &[&r.one, &na1, &nb]);
    let ih = numeral_add_eq(r, a - 1, b);
    let p_ctx = cong_add_r(r, &ih, &r.one);
    let p = trp(
        r,
        &EqP {
            a: lhs.clone(),
            b: mid,
            p: p_assoc,
        },
        &p_ctx,
    );
    EqP {
        a: lhs,
        b: numeral(r, a + b),
        p: p.p,
    }
}

/// `mul (numeral a) (numeral b) = numeral (a * b)` over an abstract ring,
/// proved from `mul_0_l`/`mul_1_l`/`mul_add_r` plus `numeral_add_eq`.
fn numeral_mul_eq(r: &Ring, a: i64, b: i64) -> EqP {
    let nb = numeral(r, b);
    if a == 0 {
        return EqP {
            a: app(&app(&r.mul, &r.zero), &nb),
            b: r.zero.clone(),
            p: inst(&r.mul_0_l, &[&nb]),
        };
    }
    let na1 = numeral(r, a - 1);
    let lhs = app(&app(&r.mul, &app(&app(&r.add, &r.one), &na1)), &nb);
    let mul_one_nb = app(&app(&r.mul, &r.one), &nb);
    let mul_na1_nb = app(&app(&r.mul, &na1), &nb);
    let mid = app(&app(&r.add, &mul_one_nb), &mul_na1_nb);
    let p_step = inst(&r.mul_add_r, &[&r.one, &na1, &nb]);
    let p_m1 = EqP {
        a: mul_one_nb.clone(),
        b: nb.clone(),
        p: inst(&r.mul_1_l, &[&nb]),
    };
    let ih = numeral_mul_eq(r, a - 1, b);
    // mul_add_r: lhs = add (mul one nb) (mul na1 nb).
    let p1 = EqP {
        a: lhs.clone(),
        b: mid.clone(),
        p: p_step,
    };
    // mul_1_l: add (mul one nb) (mul na1 nb) = add nb (mul na1 nb).
    let p2 = cong_add_l(r, &p_m1, &mul_na1_nb);
    // induction: add nb (mul na1 nb) = add nb (numeral ((a-1)*b)).
    let p3 = cong_add_r(r, &ih, &nb);
    // numeral_add_eq: add nb (numeral ((a-1)*b)) = numeral (a*b).
    let p4 = numeral_add_eq(r, b, (a - 1) * b);
    let p = trp(r, &trp(r, &trp(r, &p1, &p2), &p3), &p4);
    EqP {
        a: lhs,
        b: numeral(r, a * b),
        p: p.p,
    }
}

/// `mul (canon pa) (canon pb) = sum_term products` — full distributivity
/// expansion of the product of two canonical polynomials.
pub(crate) fn expand(r: &Ring, pa: &[Mono], pb: &[Mono]) -> (Vec<Mono>, EqP) {
    let c_pb = canon_term(r, pb);
    match pa {
        [] => (
            Vec::new(),
            EqP {
                a: app(&app(&r.mul, &r.zero), &c_pb),
                b: r.zero.clone(),
                p: inst(&r.mul_0_l, &[&c_pb]),
            },
        ),
        [m, rest @ ..] => {
            let m_term = mono_term(r, m);
            let c_rest = sum_term(r, rest);
            let a = app(&app(&r.mul, &app(&app(&r.add, &m_term), &c_rest)), &c_pb);
            let p_mr = inst(&r.mul_add_r, &[&m_term, &c_rest, &c_pb]);
            let (pl, pf_l) = expand_single(r, m, pb);
            let (pr, pf_r) = expand(r, rest, pb);
            let mid = app(
                &app(&r.add, &app(&app(&r.mul, &m_term), &c_pb)),
                &app(&app(&r.mul, &c_rest), &c_pb),
            );
            let p2 = trp(
                r,
                &cong_add_l(r, &pf_l, &app(&app(&r.mul, &c_rest), &c_pb)),
                &cong_add_r(r, &pf_r, &sum_term(r, &pl)),
            );
            let p_cc = sum_concat(r, &pl, &pr);
            let p = trp(
                r,
                &trp(
                    r,
                    &EqP {
                        a: a.clone(),
                        b: mid,
                        p: p_mr,
                    },
                    &p2,
                ),
                &p_cc,
            );
            let mut products = pl;
            products.extend(pr);
            let b = sum_term(r, &products);
            (products, EqP { a, b, p: p.p })
        }
    }
}

/// `mul m_term (canon pb) = sum_term products` — distribute one monomial
/// over the monomials of `pb`.
fn expand_single(r: &Ring, m: &Mono, pb: &[Mono]) -> (Vec<Mono>, EqP) {
    let m_term = mono_term(r, m);
    match pb {
        [] => (
            Vec::new(),
            EqP {
                a: app(&app(&r.mul, &m_term), &r.zero),
                b: r.zero.clone(),
                p: inst(&r.mul_0_r, &[&m_term]),
            },
        ),
        [n, rest @ ..] => {
            let n_term = mono_term(r, n);
            let c_rest = sum_term(r, rest);
            let a = app(&app(&r.mul, &m_term), &app(&app(&r.add, &n_term), &c_rest));
            let p_ml = inst(&r.mul_add_l, &[&m_term, &n_term, &c_rest]);
            let (p_mn, pf_mn) = mono_mul(r, m, n);
            let (pr, pf_r) = expand_single(r, m, rest);
            let mn_term = mono_term(r, &p_mn);
            let mid = app(
                &app(&r.add, &app(&app(&r.mul, &m_term), &n_term)),
                &app(&app(&r.mul, &m_term), &c_rest),
            );
            let p2 = trp(
                r,
                &cong_add_l(r, &pf_mn, &app(&app(&r.mul, &m_term), &c_rest)),
                &cong_add_r(r, &pf_r, &mn_term),
            );
            let p = trp(
                r,
                &EqP {
                    a: a.clone(),
                    b: mid,
                    p: p_ml,
                },
                &p2,
            );
            let mut products = vec![p_mn];
            products.extend(pr);
            let b = sum_term(r, &products);
            (products, EqP { a, b, p: p.p })
        }
    }
}

/// `add (sum_term la) (sum_term lb) = sum_term (la ++ lb)`.
fn sum_concat(r: &Ring, la: &[Mono], lb: &[Mono]) -> EqP {
    let s_lb = sum_term(r, lb);
    match la {
        [] => EqP {
            a: app(&app(&r.add, &r.zero), &s_lb),
            b: s_lb.clone(),
            p: inst(&r.add_0_l, &[&s_lb]),
        },
        [t, rest @ ..] => {
            let t_term = mono_term(r, t);
            let s_rest = sum_term(r, rest);
            let a = app(&app(&r.add, &app(&app(&r.add, &t_term), &s_rest)), &s_lb);
            let mid = app(&app(&r.add, &t_term), &app(&app(&r.add, &s_rest), &s_lb));
            let p_assoc = inst(&r.add_assoc, &[&t_term, &s_rest, &s_lb]);
            let p_rc = sum_concat(r, rest, lb);
            let p2 = cong_add_r(r, &p_rc, &t_term);
            let mut both = vec![t.clone()];
            both.extend(rest.iter().cloned());
            both.extend(lb.iter().cloned());
            EqP {
                a: a.clone(),
                b: sum_term(r, &both),
                p: trp(
                    r,
                    &EqP {
                        a,
                        b: mid,
                        p: p_assoc,
                    },
                    &p2,
                )
                .p,
            }
        }
    }
}

/// Canonicalize a right-associated sum in arbitrary order:
/// `sum_term list = canon poly`.
pub(crate) fn sum_canon(r: &Ring, list: &[Mono]) -> (Vec<Mono>, EqP) {
    match list {
        [] => (
            Vec::new(),
            EqP {
                a: r.zero.clone(),
                b: r.zero.clone(),
                p: refl(&r.zero),
            },
        ),
        [t, rest @ ..] => {
            let t_term = mono_term(r, t);
            let s_rest = sum_term(r, rest);
            let a = app(&app(&r.add, &t_term), &s_rest);
            let (pr, pf_r) = sum_canon(r, rest);
            let (pi, pf_i) = insert(r, t, &pr);
            let p = trp(r, &cong_add_r(r, &pf_r, &t_term), &pf_i);
            let b = canon_term(r, &pi);
            (pi, EqP { a, b, p: p.p })
        }
    }
}

/// `mul m_term n_term = mono_term (m * n)` — normalize a product of two
/// monomials (coefficients multiply, atoms merge sorted).
fn mono_mul(r: &Ring, m: &Mono, n: &Mono) -> (Mono, EqP) {
    let m_term = mono_term(r, m);
    let n_term = mono_term(r, n);
    let a = app(&app(&r.mul, &m_term), &n_term);
    let ka = numeral(r, m.coeff);
    let kb = numeral(r, n.coeff);
    let aa = prod_term(r, &m.atoms);
    let bb = prod_term(r, &n.atoms);
    let full = app(
        &app(&r.mul, &app(&app(&r.mul, &ka), &aa)),
        &app(&app(&r.mul, &kb), &bb),
    );
    let p0 = refl2(&a, &full);
    let p_ac = regroup(r, &ka, &aa, &kb, &bb);
    let k = m.coeff * n.coeff;
    let kk = numeral(r, k);
    let grouped = app(
        &app(&r.mul, &app(&app(&r.mul, &ka), &kb)),
        &app(&app(&r.mul, &aa), &bb),
    );
    let p3 = match r.mode {
        // `mul ka kb` computes to `kk` definitionally over Nat.
        Mode::Concrete => refl2(
            &grouped,
            &app(&app(&r.mul, &kk), &app(&app(&r.mul, &aa), &bb)),
        ),
        // Over an abstract ring the coefficient product needs
        // `numeral_mul_eq`, applied on the left of the shared atom product.
        Mode::Structured => cong_mul_l(
            r,
            &numeral_mul_eq(r, m.coeff, n.coeff),
            &app(&app(&r.mul, &aa), &bb),
        ),
    };
    let (merged, pf_merge) = atom_merge(r, &m.atoms, &n.atoms);
    let p2 = cong_mul_r(r, &pf_merge, &kk);
    let mn = Mono {
        coeff: k,
        atoms: merged,
    };
    let p5 = refl2(
        &app(&app(&r.mul, &kk), &prod_term(r, &mn.atoms)),
        &mono_term(r, &mn),
    );
    let p = trp(r, &trp(r, &trp(r, &p0, &p_ac), &trp(r, &p3, &p2)), &p5);
    let b = mono_term(r, &mn);
    (mn, EqP { a, b, p: p.p })
}

/// `mul (mul ka aa) (mul kb bb) = mul (mul ka kb) (mul aa bb)` — the
/// associativity/commutativity regrouping used by `mono_mul`.
pub(crate) fn regroup(r: &Ring, ka: &Term, aa: &Term, kb: &Term, bb: &Term) -> EqP {
    let a = app(
        &app(&r.mul, &app(&app(&r.mul, ka), aa)),
        &app(&app(&r.mul, kb), bb),
    );
    let p1 = inst(&r.mul_assoc, &[ka, aa, &app(&app(&r.mul, kb), bb)]);
    let p_swap = {
        let s1 = syp(
            r,
            &EqP {
                a: app(&app(&r.mul, &app(&app(&r.mul, aa), kb)), bb),
                b: app(&app(&r.mul, aa), &app(&app(&r.mul, kb), bb)),
                p: inst(&r.mul_assoc, &[aa, kb, bb]),
            },
        );
        let c = inst(&r.mul_comm, &[aa, kb]);
        let c1 = cong_mul_l(
            r,
            &EqP {
                a: app(&app(&r.mul, aa), kb),
                b: app(&app(&r.mul, kb), aa),
                p: c,
            },
            bb,
        );
        let p3 = inst(&r.mul_assoc, &[kb, aa, bb]);
        trp(
            r,
            &trp(r, &s1, &c1),
            &EqP {
                a: app(&app(&r.mul, &app(&app(&r.mul, kb), aa)), bb),
                b: app(&app(&r.mul, kb), &app(&app(&r.mul, aa), bb)),
                p: p3,
            },
        )
    };
    let p2 = cong_mul_r(r, &p_swap, ka);
    let p3 = syp(
        r,
        &EqP {
            a: app(
                &app(&r.mul, &app(&app(&r.mul, ka), kb)),
                &app(&app(&r.mul, aa), bb),
            ),
            b: app(
                &app(&r.mul, ka),
                &app(&app(&r.mul, kb), &app(&app(&r.mul, aa), bb)),
            ),
            p: inst(&r.mul_assoc, &[ka, kb, &app(&app(&r.mul, aa), bb)]),
        },
    );
    let mid = app(
        &app(&r.mul, ka),
        &app(&app(&r.mul, aa), &app(&app(&r.mul, kb), bb)),
    );
    trp(r, &trp(r, &EqP { a, b: mid, p: p1 }, &p2), &p3)
}

/// `mul (prod la) (prod lb) = prod (merged)` — merge two sorted atom lists.
fn atom_merge(r: &Ring, la: &[Term], lb: &[Term]) -> (Vec<Term>, EqP) {
    let c_lb = prod_term(r, lb);
    match la {
        [] => (
            lb.to_vec(),
            EqP {
                a: app(&app(&r.mul, &r.one), &c_lb),
                b: c_lb.clone(),
                p: inst(&r.mul_1_l, &[&c_lb]),
            },
        ),
        [t, rest @ ..] => {
            let t = t.clone();
            let c_rest = prod_term(r, rest);
            let a = app(&app(&r.mul, &app(&app(&r.mul, &t), &c_rest)), &c_lb);
            let mid = app(&app(&r.mul, &t), &app(&app(&r.mul, &c_rest), &c_lb));
            let p_assoc = inst(&r.mul_assoc, &[&t, &c_rest, &c_lb]);
            let (p_r, pf_r) = atom_merge(r, rest, lb);
            let p_ctx = cong_mul_r(r, &pf_r, &t);
            let (p_i, pf_i) = atom_insert(r, &t, &p_r);
            let p = trp(
                r,
                &trp(
                    r,
                    &EqP {
                        a: a.clone(),
                        b: mid,
                        p: p_assoc,
                    },
                    &p_ctx,
                ),
                &pf_i,
            );
            let b = prod_term(r, &p_i);
            (p_i, EqP { a, b, p: p.p })
        }
    }
}

/// Insert an atom into a sorted atom list:
/// `mul t (prod sorted) = prod (inserted)`.
fn atom_insert(r: &Ring, t: &Term, sorted: &[Term]) -> (Vec<Term>, EqP) {
    match sorted {
        [] => {
            let canon = app(&app(&r.mul, t), &r.one);
            let p = refl(&canon);
            (
                vec![t.clone()],
                EqP {
                    a: canon.clone(),
                    b: canon,
                    p,
                },
            )
        }
        [h, rest @ ..] => {
            let h = h.clone();
            let c_rest = prod_term(r, rest);
            let a = app(&app(&r.mul, t), &app(&app(&r.mul, &h), &c_rest));
            let ka = term_ord(t);
            let kh = term_ord(&h);
            if ka < kh {
                let mut res = vec![t.clone()];
                res.extend(sorted.iter().cloned());
                (
                    res,
                    EqP {
                        a: a.clone(),
                        b: a.clone(),
                        p: refl(&a),
                    },
                )
            } else {
                let p_swap = {
                    let p1 = syp(
                        r,
                        &EqP {
                            a: app(&app(&r.mul, &app(&app(&r.mul, t), &h)), &c_rest),
                            b: a.clone(),
                            p: inst(&r.mul_assoc, &[t, &h, &c_rest]),
                        },
                    );
                    let c = inst(&r.mul_comm, &[t, &h]);
                    let c1 = cong_mul_l(
                        r,
                        &EqP {
                            a: app(&app(&r.mul, t), &h),
                            b: app(&app(&r.mul, &h), t),
                            p: c,
                        },
                        &c_rest,
                    );
                    let p3 = inst(&r.mul_assoc, &[&h, t, &c_rest]);
                    trp(
                        r,
                        &trp(r, &p1, &c1),
                        &EqP {
                            a: app(&app(&r.mul, &app(&app(&r.mul, &h), t)), &c_rest),
                            b: app(&app(&r.mul, &h), &app(&app(&r.mul, t), &c_rest)),
                            p: p3,
                        },
                    )
                };
                let (p_r, pf_r) = atom_insert(r, t, rest);
                let p2 = cong_mul_r(r, &pf_r, &h);
                let p = trp(r, &p_swap, &p2);
                let mut res = vec![h.clone()];
                res.extend(p_r);
                let b = app(&app(&r.mul, &h), &prod_term(r, &res[1..]));
                (res, EqP { a, b, p: p.p })
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Display name of the carrier for error messages.
fn ring_carrier(r: &Ring) -> &'static str {
    match r.mode {
        Mode::Concrete => "Nat",
        Mode::Structured => "_",
    }
}

/// Entry point called by the `Tactic::Ring` arm.
///
/// - `ctx` is the full context the goal lives in (tactic binders innermost).
/// - `goal_ty` is the normalized goal type.
/// - `num_tactic` is the number of binders `ctx` has beyond the outer context.
/// - `num_intro` is the number of names introduced by `intro`.
/// - `ring_term` is the `C` in `ring with C`; `None` selects the concrete
///   natural-number solver when the goal is over `Nat`, and otherwise triggers
///   *instance search*: the context is scanned for a bundled `CommRing`/`Field`
///   record whose carrier matches the goal, which is then used as if the user
///   had written `ring with C`.

/// Extract `(lhs, rhs, carrier)` from a normalized path goal.
fn sides_from_nf(
    ctx: &Ctx,
    goal_ty: &Term,
    session: &mut Session,
) -> Result<(Term, Term, Term), TypeError> {
    let goal_nf = nbe_eval_ctx(ctx.len(), goal_ty, session);
    match goal_nf {
        Term::TPath(a, u, v) => {
            let a_nf = nbe_eval_ctx(ctx.len(), &a, session);
            Ok((u.as_ref().clone(), v.as_ref().clone(), a_nf))
        }
        other => Err(TypeError::Other(format!(
            "ring: goal is not a path (got '{}')",
            other,
        ))),
    }
}

pub fn prove(
    dts: &[Datatype],
    ctx: &Ctx,
    goal_ty: &Term,
    raw_goal_ty: Option<&Term>,
    _num_tactic: usize,
    _num_intro: usize,
    ring_term: Option<&Term>,
    session: &mut Session,
) -> Result<Term, TypeError> {
    // Sides are taken from the RAW goal when available: concrete global
    // operations unfold under normalization and would defeat the raw
    // syntactic head-matching in `as_add`/`as_mul`/`numeral_of`.  The NF
    // path stays as the fallback (abstract-parameter instances).
    if let Some(raw) = raw_goal_ty {
        crate::debug_log!(
            "ring: RAW sides u={} v={}",
            match raw {
                Term::TPath(_, a, _) => crate::cubical::syntax::pretty::show_term(&[], a),
                _ => "<not-path>".into(),
            },
            match raw {
                Term::TPath(_, _, b) => crate::cubical::syntax::pretty::show_term(&[], b),
                _ => "<not-path>".into(),
            }
        );
    }
    let (u, v, carrier) = if let Some(raw) = raw_goal_ty {
        // Strip the Pi telescope peeled off by `intro` tactics.
        let mut r_cur = raw;
        while let Term::TPi(_, _, body, _) = r_cur {
            r_cur = body;
        }
        let raw = r_cur;
        match raw {
            Term::TPath(a, ru, rv) => {
                let a_nf = nbe_eval_ctx(ctx.len(), &a, session);
                ((**ru).clone(), (**rv).clone(), a_nf)
            }
            _ => sides_from_nf(ctx, goal_ty, session)?,
        }
    } else {
        sides_from_nf(ctx, goal_ty, session)?
    };

    // Select the ring: an explicit `ring with C` wins; otherwise the goal
    // carrier decides between the concrete Nat solver and instance search.
    let ring_term = match ring_term {
        some @ Some(_) => some.cloned(),
        None => {
            if matches!(carrier, Term::TData(ref d, ref p) if d == "Nat" && p.is_empty()) {
                None
            } else {
                match find_ring_instance(ctx, &carrier, session) {
                    Some(inst) => Some(inst),
                    None => {
                        return Err(TypeError::Other(format!(
                            "ring: goal is over '{}' but no CommRing/Field instance \
                             for it is in context; use `ring with C`",
                            carrier,
                        )));
                    }
                }
            }
        }
    };

    let ring = Ring::resolve(dts, ctx, ring_term.as_ref(), session)?;

    let (pu, pfu) = decomp(&ring, &u, session)?;
    let (pv, pfv) = decomp(&ring, &v, session)?;

    let cu = canon_term(&ring, &pu);
    let cv = canon_term(&ring, &pv);
    if cu != cv {
        return Err(TypeError::Other(format!(
            "ring: unable to solve goal\n  goal : Path {} {} {}\n  left  : {}\n  right : {}",
            ring_carrier(&ring),
            u,
            v,
            cu,
            cv,
        )));
    }

    let pf = trp(&ring, &pfu, &syp(&ring, &pfv));
    // Return the proof in its raw law-application form.  Earlier workaround
    // normalized the whole proof (nbe_eval_ctx over pf.p) so law args were
    // embedded as normal forms, but that re-quote mis-anchors the de-Bruijn
    // refs captured inside the unfolded elim case bodies (fatal faces at
    // check_faces / termination violations with out-of-range TVar refs).
    // The raw proof already checks: kernel re-infers each leaf from raw law
    // declarations (lookup_ctx / TApp raw beta), and check_dt(dts, ctx, &pf.p,
    // goal_ty) passes.
    // Verify-once policy (see field.rs): the driver's `process_def` re-check
    // is the soundness backstop; this diagnostic pass runs only under --debug.
    let prev_skip = crate::cubical::typechecker::termination::should_skip_guard(session);
    crate::cubical::typechecker::termination::set_skip_guard(true, session);
    let check_res = if crate::cubical::debug::is_active() {
        check_dt(dts, ctx, &pf.p, goal_ty, session)
    } else {
        Ok(())
    };
    crate::cubical::typechecker::termination::set_skip_guard(prev_skip, session);
    if let Err(e) = check_res {
        let detail = match &e {
            crate::cubical::typechecker::TypeError::TypeMismatch {
                expected, got, pos, ..
            } => format!(
                "  expected : {}\n  got      : {}\n  pos      : {:?}",
                crate::cubical::syntax::show_term(
                    &ctx.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(),
                    expected
                ),
                crate::cubical::syntax::show_term(
                    &ctx.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(),
                    got
                ),
                pos,
            ),
            _ => format!("{:?}", e),
        };
        Err(TypeError::Other(format!(
            "ring: kernel rejected the constructed proof for\n  goal : Path {} {} {}\n  error: {}",
            ring_carrier(&ring),
            u,
            v,
            detail,
        )))
    } else {
        Ok(pf.p)
    }
}
