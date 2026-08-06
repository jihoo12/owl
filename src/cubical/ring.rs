//! `by ring` — commutative semiring solver over `Nat`.
//!
//! Proves goals of the form `Path Nat u v` where `u` and `v` are polynomial
//! expressions over the context's `Nat` variables, built with the ring
//! operations.  Both sides are canonicalized to a sorted sum of monomials
//! (`add` of `mul (numeral k) (product of atoms)`) and the equality is
//! proved from the law names in `examples/ring_laws.owl`:
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
use crate::cubical::syntax::{shift, Datatype, Term};
use crate::cubical::typechecker::{check_dt, Ctx, TypeError};

/// A path proof `p : Path Nat a b`, with its endpoints tracked so the
/// proof term can be composed with `trans`/`sym`/congruence lemmas.
#[derive(Clone)]
struct EqP {
    a: Term,
    b: Term,
    p: Term,
}

/// A monomial: `coeff` times the product of `atoms`.  Canonical polynomials
/// are sorted lists of these with distinct atom vectors and positive
/// coefficients.
#[derive(Clone, Debug, PartialEq)]
struct Mono {
    coeff: i64,
    atoms: Vec<Term>,
}

/// Resolved references to the ring operations, structural lemmas, and law
/// names (all looked up in the context by name).
struct Ring {
    add: Term,
    mul: Term,
    zero: Term,
    one: Term,
    trans: Term,
    sym: Term,
    cong_add_l: Term,
    cong_add_r: Term,
    cong_mul_l: Term,
    cong_mul_r: Term,
    add_comm: Term,
    add_assoc: Term,
    add_0_l: Term,
    add_0_r: Term,
    mul_comm: Term,
    mul_assoc: Term,
    mul_1_l: Term,
    mul_1_r: Term,
    mul_0_l: Term,
    mul_0_r: Term,
    mul_add_l: Term,
    mul_add_r: Term,
    ctx_len: usize,
}

impl Ring {
    fn resolve(ctx: &Ctx) -> Result<Ring, TypeError> {
        let var = |name: &str| -> Result<Term, TypeError> {
            let gi = ctx
                .iter()
                .position(|(n, _)| n == name)
                .ok_or_else(|| {
                    TypeError::Other(format!(
                        "ring: missing lemma '{}'; import examples/ring_laws.owl",
                        name
                    ))
                })?;
            Ok(Term::TVar(gi as i32))
        };
        Ok(Ring {
            ctx_len: ctx.len(),
            add: var("add")?,
            mul: var("mul")?,
            zero: var("zero")?,
            one: var("one")?,
            trans: var("_owl_trans")?,
            sym: var("_owl_sym")?,
            cong_add_l: var("_owl_cong_add_l")?,
            cong_add_r: var("_owl_cong_add_r")?,
            cong_mul_l: var("_owl_cong_mul_l")?,
            cong_mul_r: var("_owl_cong_mul_r")?,
            add_comm: var("add_comm")?,
            add_assoc: var("add_assoc")?,
            add_0_l: var("add_0_l")?,
            add_0_r: var("add_0_r")?,
            mul_comm: var("mul_comm")?,
            mul_assoc: var("mul_assoc")?,
            mul_1_l: var("mul_1_l")?,
            mul_1_r: var("mul_1_r")?,
            mul_0_l: var("mul_0_l")?,
            mul_0_r: var("mul_0_r")?,
            mul_add_l: var("mul_add_l")?,
            mul_add_r: var("mul_add_r")?,
        })
    }
}

// ---------------------------------------------------------------------------
// Term / proof-term plumbing
// ---------------------------------------------------------------------------

fn app(f: &Term, a: &Term) -> Term {
    Term::TApp(Box::new(f.clone()), Box::new(a.clone()))
}

fn inst(f: &Term, args: &[&Term]) -> Term {
    args.iter().fold(f.clone(), |acc, a| app(&acc, a))
}

/// Path reflection: `Path t t`.
fn refl(t: &Term) -> Term {
    Term::PLam("_i".into(), Box::new(shift(1, 0, t)))
}

/// `refl` adjusted to the declared endpoints `a`, `b` — valid when `a` and
/// `b` are definitionally equal (the kernel accepts `Path a a` as `Path a b`).
fn refl2(a: &Term, b: &Term) -> EqP {
    EqP {
        a: a.clone(),
        b: b.clone(),
        p: refl(a),
    }
}

fn trp(r: &Ring, p: &EqP, q: &EqP) -> EqP {
    EqP {
        a: p.a.clone(),
        b: q.b.clone(),
        p: inst(&r.trans, &[&p.a, &p.b, &q.b, &p.p, &q.p]),
    }
}

fn syp(r: &Ring, p: &EqP) -> EqP {
    EqP {
        a: p.b.clone(),
        b: p.a.clone(),
        p: inst(&r.sym, &[&p.a, &p.b, &p.p]),
    }
}

fn cong_add_l(r: &Ring, p: &EqP, n: &Term) -> EqP {
    EqP {
        a: app(&app(&r.add, &p.a), n),
        b: app(&app(&r.add, &p.b), n),
        p: inst(&r.cong_add_l, &[&p.a, &p.b, n, &p.p]),
    }
}

fn cong_add_r(r: &Ring, p: &EqP, m: &Term) -> EqP {
    EqP {
        a: app(&app(&r.add, m), &p.a),
        b: app(&app(&r.add, m), &p.b),
        p: inst(&r.cong_add_r, &[&p.a, &p.b, m, &p.p]),
    }
}

fn cong_mul_l(r: &Ring, p: &EqP, n: &Term) -> EqP {
    EqP {
        a: app(&app(&r.mul, &p.a), n),
        b: app(&app(&r.mul, &p.b), n),
        p: inst(&r.cong_mul_l, &[&p.a, &p.b, n, &p.p]),
    }
}

fn cong_mul_r(r: &Ring, p: &EqP, m: &Term) -> EqP {
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
fn numeral(k: i64) -> Term {
    let mut t = Term::TCon("Nat".into(), "zero".into(), Vec::new());
    for _ in 0..k {
        t = Term::TCon("Nat".into(), "suc".into(), vec![t]);
    }
    t
}

/// Recognize a constructor numeral, returning the count.
fn numeral_of(t: &Term) -> Option<i64> {
    match t {
        Term::TCon(d, c, args) if d == "Nat" && c == "zero" && args.is_empty() => Some(0),
        Term::TCon(d, c, args) if d == "Nat" && c == "suc" && args.len() == 1 => {
            numeral_of(&args[0]).map(|k| k + 1)
        }
        _ => None,
    }
}

/// Right-associated product of `atoms` (`mul a1 (mul a2 ...)`).
fn prod_term(r: &Ring, atoms: &[Term]) -> Term {
    let mut t = r.one.clone();
    for a in atoms.iter().rev() {
        t = app(&app(&r.mul, a), &t);
    }
    t
}

/// The canonical term for a monomial.
fn mono_term(r: &Ring, m: &Mono) -> Term {
    if m.atoms.is_empty() {
        return numeral(m.coeff);
    }
    let p = prod_term(r, &m.atoms);
    if m.coeff == 1 {
        p
    } else {
        app(&app(&r.mul, &numeral(m.coeff)), &p)
    }
}

/// Right-associated sum of canonical monomial terms.
fn sum_term(r: &Ring, poly: &[Mono]) -> Term {
    let mut t = r.zero.clone();
    for m in poly.iter().rev() {
        t = app(&app(&r.add, &mono_term(r, m)), &t);
    }
    t
}

fn canon_term(r: &Ring, poly: &[Mono]) -> Term {
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
fn is_add_call(r: &Ring, t: &Term) -> bool {
    match t {
        Term::TApp(_, _) => {
            let nf = crate::cubical::nbe::nbe_eval_ctx(r.ctx_len + 1, t);
            is_addshape_elim(&nf)
        }
        _ => is_addshape_elim(t),
    }
}

/// The mul-eliminator shape:
/// `elim[fun _ => Nat] { zero -> zero | suc m' -> add (mul m' _) _ } _`.
fn is_mulshape_elim(r: &Ring, t: &Term) -> bool {
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
            let suc_body_is_add = is_add_call(r, &cases[1].body);
            zero_body && suc_body_is_add
        }
        _ => false,
    }
}

/// Treat `t` as an `add` operation, returning `(a, b)` with `t ~ add a b`.
/// The operation may be the unfolded eliminator or a stuck application of the
/// `add` global; normalize the latter so both give the eliminator normal form.
fn as_add(r: &Ring, t: &Term) -> Option<(Term, Term)> {
    let nf = match t {
        Term::TApp(_, _) => crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, t),
        _ => t.clone(),
    };
    if is_addshape_elim(&nf) {
        if let Term::TElim(_, cases, scrut) = nf {
            return Some(((*scrut).clone(), (*cases[0].body).clone()));
        }
    }
    None
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
fn as_mul(r: &Ring, t: &Term) -> Option<(Term, Term)> {
    let nf = match t {
        Term::TApp(_, _) => crate::cubical::nbe::nbe_eval_ctx(r.ctx_len, t),
        _ => t.clone(),
    };
    if is_mulshape_elim(r, &nf) {
        if let Term::TElim(_, cases, scrut) = nf {
            let arg = mul_suc_arg(&cases[1].body);
            return Some(((*scrut).clone(), arg));
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Reification
// ---------------------------------------------------------------------------

/// Reify `t` into a canonical polynomial with a proof `Path t canon`.
fn decomp(r: &Ring, t: &Term) -> Result<(Vec<Mono>, EqP), TypeError> {
    if let Some((s, z)) = as_add(r, t) {
        let (ps, pfs) = decomp(r, &s)?;
        let (pz, pfz) = decomp(r, &z)?;
        return reify_add(r, &s, &ps, &pfs, &z, &pz, &pfz);
    }
    if let Some((s, a)) = as_mul(r, t) {
        let (ps, pfs) = decomp(r, &s)?;
        let (pa, pfa) = decomp(r, &a)?;
        return reify_mul(r, &s, &ps, &pfs, &a, &pa, &pfa);
    }
    if let Some(k) = numeral_of(t) {
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
        let canon = app(&app(&r.add, &numeral(k)), &r.zero);
        let pf = syp(
            r,
            &EqP {
                a: canon.clone(),
                b: numeral(k),
                p: inst(&r.add_0_r, &[&numeral(k)]),
            },
        );
        return Ok((
            vec![Mono {
                coeff: k,
                atoms: Vec::new(),
            }],
            EqP {
                a: t.clone(),
                b: canon,
                p: pf.p,
            },
        ));
    }
    let atom = app(&app(&r.mul, t), &r.one);
    let canon = app(&app(&r.add, &atom), &r.zero);
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
    let pf = trp(r, &p1, &p2);
    Ok((
        vec![Mono {
            coeff: 1,
            atoms: vec![t.clone()],
        }],
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
fn poly_merge(r: &Ring, pa: &[Mono], pb: &[Mono]) -> (Vec<Mono>, EqP) {
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
            let mid = app(
                &app(&r.add, &m_term),
                &app(&app(&r.add, &c_rest), &c_pb),
            );
            let p_assoc = inst(&r.add_assoc, &[&m_term, &c_rest, &c_pb]);
            let (p_r, pf_r) = poly_merge(r, rest, pb);
            let p_ctx = cong_add_r(r, &pf_r, &m_term);
            let (p_i, pf_i) = insert(r, m, &p_r);
            let p = trp(r, &trp(r, &EqP { a: a.clone(), b: mid, p: p_assoc }, &p_ctx), &pf_i);
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
            let a = app(
                &app(&r.add, &m_term),
                &app(&app(&r.add, &h_term), &c_rest),
            );
            let km = atoms_key(m);
            let kh = atoms_key(h);
            if km < kh {
                let mut res = vec![m.clone()];
                res.extend(sorted.iter().cloned());
                (res, EqP { a: a.clone(), b: a.clone(), p: refl(&a) })
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
                        a: app(
                            &app(&r.add, &app(&app(&r.add, &m_term), &h_term)),
                            &c_rest,
                        ),
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
                            a: app(
                                &app(&r.add, &app(&app(&r.add, &m_term), &h_term)),
                                &c_rest,
                            ),
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
                            a: app(
                                &app(&r.add, &app(&app(&r.add, &h_term), &m_term)),
                                &c_rest,
                            ),
                            b: app(
                                &app(&r.add, &h_term),
                                &app(&app(&r.add, &m_term), &c_rest),
                            ),
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
                (
                    res,
                    EqP {
                        a,
                        b,
                        p: p.p,
                    },
                )
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
    if m.atoms.is_empty() {
        refl2(&a, &b)
    } else {
        let ka = numeral(m.coeff);
        let kb = numeral(h.coeff);
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
        trp(
            r,
            &trp(r, &refl2(&a, &p_mr.a), &p_mr),
            &refl2(&p_mr.b, &b),
        )
    }
}

/// `mul (canon pa) (canon pb) = sum_term products` — full distributivity
/// expansion of the product of two canonical polynomials.
fn expand(r: &Ring, pa: &[Mono], pb: &[Mono]) -> (Vec<Mono>, EqP) {
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
            let p = trp(r, &trp(r, &EqP { a: a.clone(), b: mid, p: p_mr }, &p2), &p_cc);
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
            let a = app(
                &app(&r.mul, &m_term),
                &app(&app(&r.add, &n_term), &c_rest),
            );
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
            let p = trp(r, &EqP { a: a.clone(), b: mid, p: p_ml }, &p2);
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
            let a = app(
                &app(&r.add, &app(&app(&r.add, &t_term), &s_rest)),
                &s_lb,
            );
            let mid = app(
                &app(&r.add, &t_term),
                &app(&app(&r.add, &s_rest), &s_lb),
            );
            let p_assoc = inst(&r.add_assoc, &[&t_term, &s_rest, &s_lb]);
            let p_rc = sum_concat(r, rest, lb);
            let p2 = cong_add_r(r, &p_rc, &t_term);
            let mut both = vec![t.clone()];
            both.extend(rest.iter().cloned());
            both.extend(lb.iter().cloned());
            EqP {
                a: a.clone(),
                b: sum_term(r, &both),
                p: trp(r, &EqP { a, b: mid, p: p_assoc }, &p2).p,
            }
        }
    }
}

/// Canonicalize a right-associated sum in arbitrary order:
/// `sum_term list = canon poly`.
fn sum_canon(r: &Ring, list: &[Mono]) -> (Vec<Mono>, EqP) {
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
    let ka = numeral(m.coeff);
    let kb = numeral(n.coeff);
    let aa = prod_term(r, &m.atoms);
    let bb = prod_term(r, &n.atoms);
    let full = app(
        &app(&r.mul, &app(&app(&r.mul, &ka), &aa)),
        &app(&app(&r.mul, &kb), &bb),
    );
    let p0 = refl2(&a, &full);
    let p_ac = regroup(r, &ka, &aa, &kb, &bb);
    let k = m.coeff * n.coeff;
    let kk = numeral(k);
    let grouped = app(
        &app(&r.mul, &app(&app(&r.mul, &ka), &kb)),
        &app(&app(&r.mul, &aa), &bb),
    );
    let p3 = refl2(
        &grouped,
        &app(&app(&r.mul, &kk), &app(&app(&r.mul, &aa), &bb)),
    );
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
fn regroup(
    r: &Ring,
    ka: &Term,
    aa: &Term,
    kb: &Term,
    bb: &Term,
) -> EqP {
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
            a: app(&app(&r.mul, &app(&app(&r.mul, ka), kb)), &app(&app(&r.mul, aa), bb)),
            b: app(&app(&r.mul, ka), &app(&app(&r.mul, kb), &app(&app(&r.mul, aa), bb))),
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
            let p = trp(r, &trp(r, &EqP { a: a.clone(), b: mid, p: p_assoc }, &p_ctx), &pf_i);
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
            let a = app(
                &app(&r.mul, t),
                &app(&app(&r.mul, &h), &c_rest),
            );
            let ka = term_ord(t);
            let kh = term_ord(&h);
            if ka < kh {
                let mut res = vec![t.clone()];
                res.extend(sorted.iter().cloned());
                (res, EqP { a: a.clone(), b: a.clone(), p: refl(&a) })
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
                (
                    res,
                    EqP {
                        a,
                        b,
                        p: p.p,
                    },
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Entry point called by the `Tactic::Ring` arm.
///
/// - `ctx` is the full context the goal lives in (tactic binders innermost).
/// - `goal_ty` is the normalized goal type.
/// - `num_tactic` is the number of binders `ctx` has beyond the outer context.
/// - `num_intro` is the number of names introduced by `intro`.
pub fn prove(
    dts: &[Datatype],
    ctx: &Ctx,
    goal_ty: &Term,
    _num_tactic: usize,
    _num_intro: usize,
) -> Result<Term, TypeError> {
    let ring = Ring::resolve(ctx)?;

    let (u, v) = {
        let goal_nf = nbe_eval_ctx(ctx.len(), goal_ty);
        match goal_nf {
            Term::TPath(a, u, v) => {
                let a_nf = nbe_eval_ctx(ctx.len(), &a);
                if !matches!(a_nf, Term::TData(ref d, ref p) if d == "Nat" && p.is_empty()) {
                    return Err(TypeError::Other(format!(
                        "ring: goal is not a path over Nat (got '{}')",
                        a_nf,
                    )));
                }
                (*u, *v)
            }
            other => {
                return Err(TypeError::Other(format!(
                    "ring: goal is not a path over Nat\n  goal: {}",
                    other,
                )))
            }
        }
    };

    let (pu, pfu) = decomp(&ring, &u)?;
    let (pv, pfv) = decomp(&ring, &v)?;

    let cu = canon_term(&ring, &pu);
    let cv = canon_term(&ring, &pv);
    if cu != cv {
        return Err(TypeError::Other(format!(
            "ring: unable to solve goal\n  goal : Path Nat {} {}\n  left  : {}\n  right : {}",
            u, v, cu, cv,
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
    let prev_skip = crate::cubical::typechecker::termination::should_skip_guard();
    crate::cubical::typechecker::termination::set_skip_guard(true);
    let check_res = check_dt(dts, ctx, &pf.p, goal_ty);
    crate::cubical::typechecker::termination::set_skip_guard(prev_skip);
    if let Err(e) = check_res {
        let detail = match &e {
            crate::cubical::typechecker::TypeError::TypeMismatch { expected, got, .. } => format!(
                "  expected : {}\n  got      : {}",
                crate::cubical::syntax::show_term(&ctx.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(), expected),
                crate::cubical::syntax::show_term(&ctx.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(), got),
            ),
            _ => format!("{:?}", e),
        };
        Err(TypeError::Other(format!(
            "ring: kernel rejected the constructed proof for\n  goal : Path Nat {} {}\n  error: {}",
            u, v, detail,
        )))
    } else {
        Ok(pf.p)
    }
}
