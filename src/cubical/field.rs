//! `by field` — field solver with inverse reasoning.
//!
//! Proves goals of the form `Path A u v` over an abstract `Field` record
//! bundled as `field with F` (building on H1's `by ring with C`).  Both sides
//! are reified to fractions `(N, D)` with a proof
//!
//! ```text
//!   t = mul (canon N) (inv (canon D))
//! ```
//!
//! where `D` is always a single monomial (a product of nonzero factors).
//! Add/mul of fractions combine through a common-denominator rewrite; `inv t`
//! swaps numerator and denominator (restricted to a single coefficient-1
//! monomial numerator — exactly the case that arises for products of atoms
//! and the demo theorems).  The final step proves
//!
//! ```text
//!   mul (canon N0) (inv (canon D0)) = mul (canon N1) (inv (canon D1))
//! ```
//!
//! from the ring-proved cross-multiplication
//! `mul (canon N0) (canon D1) = mul (canon N1) (canon D0)` via a scale lemma
//! that inserts `mul d (inv d) = one` and cancels.  Nonzero conditions
//! `(Path A zero x -> Empty)` are discharged structurally: strip canonical
//! `add _ zero` / `mul (numeral 1) _` wrappers, decompose products with
//! `nz_mul`, and match context hypotheses of shape `(Path A zero x -> Empty)`
//! (e.g. `hb : b != 0`).  The constructed proof is re-checked by the kernel,
//! so the tactic is sound by construction.

use crate::cubical::nbe::nbe_eval_ctx;
use crate::cubical::ring::{
    EqP, Mono, Ring, app, as_add, as_mul, canon_term, cong_add_l, cong_add_r, cong_mul_l,
    cong_mul_r, decomp, expand, inst, numeral_of, poly_merge, prod_term, regroup, sum_canon, syp,
    trp,
};
use crate::cubical::session::Session;
use crate::cubical::syntax::{Datatype, Term, shift};
use crate::cubical::typechecker::{Ctx, TypeError, check_dt, infer_dt};
use std::sync::Arc;

/// Resolved references to the field operations and the ring machinery.  The
/// ring laws are resolved by `Ring::resolve` on the bundled `Field` record
/// (its law fields carry the `CommRing` names); `inv` and the inverse/nonzero
/// laws are resolved here.
struct Field {
    ring: Ring,
    inv: Term,
    inv_mul: Term,
    inv_one: Term,
    inv_mul_dist: Term,
    inv_div: Term,
    cong_inv: Term,
    nz_one: Term,
    nz_mul: Term,
}

/// The `inv` operation of a `Field A add mul inv zero one` record: it is a
/// record *parameter*, extracted from the record type's parameter list.
fn field_inv_from_type(
    dts: &[Datatype],
    ctx: &Ctx,
    field_term: &Term,
    session: &mut Session,
) -> Result<Term, TypeError> {
    let inst_ty = infer_dt(dts, ctx, field_term, session)?;
    match nbe_eval_ctx(ctx.len(), &inst_ty, session) {
        Term::TData(dname, params) if dname == "Field" && params.len() == 6 => {
            Ok(params[3].clone())
        }
        other => Err(TypeError::Other(format!(
            "field: '{}' is not a Field record (its type is '{}')",
            field_term, other,
        ))),
    }
}

/// Search the context for a `Field A add mul inv zero one` record whose
/// carrier matches `carrier`, returning the `TVar` reference to it.
fn find_field_instance(ctx: &Ctx, carrier: &Term, session: &mut Session) -> Option<Term> {
    let car_nf = nbe_eval_ctx(ctx.len(), carrier, session);
    for (i, (_name, ty)) in ctx.iter().enumerate() {
        // Stored binder types are binder-relative; re-anchor as `lookup_ctx`
        // does before comparing the carrier.
        let ty_shifted = shift(i as i32 + 1, 0, ty);
        if let Term::TData(dname, params) = nbe_eval_ctx(ctx.len(), &ty_shifted, session) {
            if dname == "Field"
                && params.len() == 6
                && nbe_eval_ctx(ctx.len(), &params[0], session) == car_nf
            {
                return Some(Term::TVar(i as i32));
            }
        }
    }
    None
}

impl Field {
    fn resolve(
        dts: &[Datatype],
        ctx: &Ctx,
        field_term: &Term,
        session: &mut Session,
    ) -> Result<Field, TypeError> {
        let ring = Ring::resolve(dts, ctx, Some(field_term), session)?;
        let proj = |field: &str| -> Result<Term, TypeError> {
            Ok(Term::TProj(field.to_string(), Arc::new(field_term.clone())))
        };
        Ok(Field {
            ring,
            inv: field_inv_from_type(dts, ctx, field_term, session)?,
            inv_mul: proj("inv_mul")?,
            inv_one: proj("inv_one")?,
            inv_mul_dist: proj("inv_mul_dist")?,
            inv_div: proj("inv_div")?,
            cong_inv: proj("cong_inv")?,
            nz_one: proj("nz_one")?,
            nz_mul: proj("nz_mul")?,
        })
    }
}

/// A reified fraction: `pf : t = mul (canon num) (inv (canon den))`, where
/// `den` is always a single monomial with coefficient 1 (a product of
/// nonzero factors) and `num` is a sorted polynomial.
struct RF {
    num: Vec<Mono>,
    den: Vec<Mono>,
    pf: EqP,
}

// ---------------------------------------------------------------------------
// Term / proof plumbing
// ---------------------------------------------------------------------------

fn mul_term(r: &Ring, x: &Term, y: &Term) -> Term {
    crate::cubical::ring::app(&crate::cubical::ring::app(&r.mul, x), y)
}

fn inv_term(f: &Field, x: &Term) -> Term {
    crate::cubical::ring::app(&f.inv, x)
}

fn mul_assoc(r: &Ring, x: &Term, y: &Term, z: &Term) -> EqP {
    EqP {
        a: mul_term(r, &mul_term(r, x, y), z),
        b: mul_term(r, x, &mul_term(r, y, z)),
        p: inst(&r.mul_assoc, &[x, y, z]),
    }
}

fn mul_comm(r: &Ring, x: &Term, y: &Term) -> EqP {
    EqP {
        a: mul_term(r, x, y),
        b: mul_term(r, y, x),
        p: inst(&r.mul_comm, &[x, y]),
    }
}

fn mul_1_l(r: &Ring, x: &Term) -> EqP {
    EqP {
        a: mul_term(r, &r.one, x),
        b: x.clone(),
        p: inst(&r.mul_1_l, &[x]),
    }
}

#[allow(dead_code)]
fn mul_1_r(r: &Ring, x: &Term) -> EqP {
    EqP {
        a: mul_term(r, x, &r.one),
        b: x.clone(),
        p: inst(&r.mul_1_r, &[x]),
    }
}

#[allow(dead_code)]
fn inv_mul_eqp(f: &Field, x: &Term, nz: &Term) -> EqP {
    EqP {
        a: mul_term(&f.ring, x, &inv_term(f, x)),
        b: f.ring.one.clone(),
        p: inst(&f.inv_mul, &[x, nz]),
    }
}

#[allow(dead_code)]
fn inv_one_eqp(f: &Field) -> EqP {
    EqP {
        a: inv_term(f, &f.ring.one),
        b: f.ring.one.clone(),
        p: inst(&f.inv_one, &[]),
    }
}

fn inv_mul_dist_eqp(f: &Field, x: &Term, y: &Term, nzx: &Term, nzy: &Term) -> EqP {
    EqP {
        a: inv_term(f, &mul_term(&f.ring, x, y)),
        b: mul_term(&f.ring, &inv_term(f, x), &inv_term(f, y)),
        p: inst(&f.inv_mul_dist, &[x, y, nzx, nzy]),
    }
}

#[allow(dead_code)]
fn inv_div_eqp(f: &Field, x: &Term, y: &Term, nzx: &Term, nzy: &Term) -> EqP {
    EqP {
        a: inv_term(f, &mul_term(&f.ring, x, &inv_term(f, y))),
        b: mul_term(&f.ring, y, &inv_term(f, x)),
        p: inst(&f.inv_div, &[x, y, nzx, nzy]),
    }
}

fn cong_inv_eqp(f: &Field, x: &Term, y: &Term, p: &EqP) -> EqP {
    EqP {
        a: inv_term(f, x),
        b: inv_term(f, y),
        p: inst(&f.cong_inv, &[x, y, &p.p]),
    }
}

/// Sorted union of two atom lists (each already sorted by pretty-print).
fn merge_atoms(la: &[Term], lb: &[Term]) -> Vec<Term> {
    let mut out = Vec::new();
    let mut a = la.iter();
    let mut b = lb.iter();
    let mut x = a.next();
    let mut y = b.next();
    while x.is_some() || y.is_some() {
        match (x, y) {
            (Some(ta), Some(tb)) => {
                let ka = format!("{}", ta);
                let kb = format!("{}", tb);
                if ka < kb {
                    out.push(ta.clone());
                    x = a.next();
                } else if ka > kb {
                    out.push(tb.clone());
                    y = b.next();
                } else {
                    out.push(ta.clone());
                    x = a.next();
                    y = b.next();
                }
            }
            (Some(ta), None) => {
                out.push(ta.clone());
                x = a.next();
            }
            (None, Some(tb)) => {
                out.push(tb.clone());
                y = b.next();
            }
            (None, None) => {}
        }
    }
    out
}

/// A `Term` wrapper for the `inv` operation: `t ~ inv x` in Structured mode
/// when `t`'s normal form applies the resolved `inv` head to `x`.
fn as_inv(f: &Field, t: &Term, session: &mut Session) -> Option<Term> {
    let nf = nbe_eval_ctx(f.ring.ctx_len, t, session);
    match nf {
        Term::TApp(g, x) => {
            let inv_nf = nbe_eval_ctx(f.ring.ctx_len, &f.inv, session);
            if nbe_eval_ctx(f.ring.ctx_len, &g, session) == inv_nf {
                Some(x.as_ref().clone())
            } else {
                None
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Nonzero discharge
// ---------------------------------------------------------------------------

/// Discharge a nonzero obligation `(Path A zero t -> Empty)`.
///
/// Structural: normalize, reject `zero` outright, base case `one` via
/// `nz_one`, strip canonical `add _ zero` / `mul (numeral 1) _` wrappers,
/// decompose products with `nz_mul`, and finally match a context hypothesis
/// whose type normalizes to `(Path A zero x -> Empty)`.
fn discharge(f: &Field, ctx: &Ctx, t: &Term, session: &mut Session) -> Result<Term, TypeError> {
    let r = &f.ring;
    let nf = nbe_eval_ctx(ctx.len(), t, session);
    if nf == r.zero {
        return Err(TypeError::Other(format!(
            "field: division by zero in '{}'",
            t
        )));
    }
    if nf == r.one {
        return Ok(f.nz_one.clone());
    }
    if let Some((x, y)) = as_add(r, &nf, session) {
        if nbe_eval_ctx(ctx.len(), &y, session) == r.zero {
            return discharge(f, ctx, &x, session);
        }
        if nbe_eval_ctx(ctx.len(), &x, session) == r.zero {
            return discharge(f, ctx, &y, session);
        }
        return Err(TypeError::Other(format!(
            "field: cannot prove '{}' nonzero (sum of terms)",
            t
        )));
    }
    if let Some((x, y)) = as_mul(r, &nf, session) {
        match numeral_of(r, &x, session) {
            Some(1) => return discharge(f, ctx, &y, session),
            Some(_) => {
                return Err(TypeError::Other(format!(
                    "field: cannot prove '{}' nonzero (numeral multiple)",
                    t
                )));
            }
            None => {
                let nx = discharge(f, ctx, &x, session)?;
                let ny = discharge(f, ctx, &y, session)?;
                return Ok(inst(&f.nz_mul, &[&x, &y, &nx, &ny]));
            }
        }
    }
    if let Some(h) = nz_hypothesis(f, ctx, &nf, session) {
        return Ok(h);
    }
    Err(TypeError::Other(format!(
        "field: cannot prove '{}' nonzero; add a hypothesis of type (Path A zero {} -> Empty)",
        t, nf
    )))
}

/// Find a context hypothesis of type `(Path A zero x -> Empty)` whose domain
/// target normalizes to `nf`; returns the de Bruijn variable (index in `ctx`).
fn nz_hypothesis(f: &Field, ctx: &Ctx, nf: &Term, session: &mut Session) -> Option<Term> {
    let r = &f.ring;
    for (p, (_n, ty)) in ctx.iter().enumerate() {
        let shifted = shift(p as i32 + 1, 0, ty);
        let ty_nf = nbe_eval_ctx(ctx.len(), &shifted, session);
        if let Term::TPi(_, dom, codom, _) = ty_nf {
            let dom_nf = nbe_eval_ctx(ctx.len(), &dom, session);
            if let Term::TPath(_, z, x) = dom_nf {
                if nbe_eval_ctx(ctx.len(), &z, session) == r.zero
                    && nbe_eval_ctx(ctx.len(), &x, session) == *nf
                {
                    let codom_nf = nbe_eval_ctx(ctx.len(), &codom, session);
                    if matches!(codom_nf, Term::TData(d, p) if d == "Empty" && p.is_empty()) {
                        return Some(Term::TVar(p as i32));
                    }
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Ring-level equalities
// ---------------------------------------------------------------------------

/// Prove `u = v` by the ring solver (both sides canonicalized; must coincide).
fn ring_eq(r: &Ring, u: &Term, v: &Term, session: &mut Session) -> Result<EqP, TypeError> {
    let (pu, pfu) = decomp(r, u, session)?;
    let (pv, pfv) = decomp(r, v, session)?;
    let cu = canon_term(r, &pu);
    let cv = canon_term(r, &pv);
    if cu != cv {
        return Err(TypeError::Other(format!(
            "field: internal ring equality failed for\n  {} = {}\n  left  : {}\n  right : {}",
            u, v, cu, cv,
        )));
    }
    Ok(trp(r, &pfu, &syp(r, &pfv)))
}

/// `inv x = one` for `x = canon [one-monomial]` (i.e. `mul (numeral 1) one`).
fn inv_canon_one(f: &Field, x: &Term, session: &mut Session) -> Result<EqP, TypeError> {
    let r = &f.ring;
    let e1 = ring_eq(r, x, &r.one, session)?;
    let e2 = inst(&f.cong_inv, &[x, &r.one, &e1.p]);
    let e3 = inst(&f.inv_one, &[]);
    Ok(trp(
        r,
        &EqP {
            a: inv_term(f, x),
            b: inv_term(f, &r.one),
            p: e2,
        },
        &EqP {
            a: inv_term(f, &r.one),
            b: r.one.clone(),
            p: e3,
        },
    ))
}

// ---------------------------------------------------------------------------
// Fraction arithmetic
// ---------------------------------------------------------------------------

/// `mul (canon pa) (canon pb) = canon p_sum` where `p_sum = sum_canon (pa * pb)`
/// (distribute a polynomial over monomials, then sort).
fn expand_poly(r: &Ring, pa: &[Mono], pb: &[Mono]) -> Result<(Vec<Mono>, EqP), TypeError> {
    let (products, pf_exp) = expand(r, pa, pb);
    let (p_sum, pf_sum) = sum_canon(r, &products);
    let a = mul_term(r, &canon_term(r, pa), &canon_term(r, pb));
    let b = canon_term(r, &p_sum);
    let p = trp(r, &pf_exp, &pf_sum);
    Ok((p_sum, EqP { a, b, p: p.p }))
}

/// Scale a fraction `mul (canon num) (inv d1) = mul (canon num') (inv dd)`
/// to the common denominator `dd = d1 * d2`.
///
/// `e_num` is `mul (canon num) (canon [d2m]) = canon num'` (from `expand_poly`).
/// The proof inserts `mul d2 (inv d2) = one`, regroups, applies `inv_mul_dist`
/// and `cong_inv` (on `mul d1 d2 = dd`), and cancels.
fn scale_frac(
    f: &Field,
    ctx: &Ctx,
    num: &[Mono],
    d1m: &Mono,
    d2m: &Mono,
    num2: &[Mono],
    e_num: &EqP,
    session: &mut Session,
) -> Result<EqP, TypeError> {
    let r = &f.ring;
    let d1t = prod_term(r, &d1m.atoms);
    let d2t = prod_term(r, &d2m.atoms);
    let dd_mono = Mono {
        coeff: 1,
        atoms: merge_atoms(&d1m.atoms, &d2m.atoms),
    };
    let ddt = prod_term(r, &dd_mono.atoms);
    let n_term = canon_term(r, num);
    let n2_term = canon_term(r, num2);
    let inv_d1 = inv_term(f, &d1t);
    let inv_d2 = inv_term(f, &d2t);
    let inv_dd = inv_term(f, &ddt);
    let nz1 = discharge(f, ctx, &d1t, session)?;
    let nz2 = discharge(f, ctx, &d2t, session)?;
    let e_dd = ring_eq(r, &mul_term(r, &d1t, &d2t), &ddt, session)?;

    let m_d2_invd2 = mul_term(r, &d2t, &inv_d2);
    // e_insert : mul n_term inv_d1 = mul n_term (mul one inv_d1)
    let e_insert = cong_mul_r(
        r,
        &syp(
            r,
            &EqP {
                a: mul_term(r, &r.one, &inv_d1),
                b: inv_d1.clone(),
                p: inst(&r.mul_1_l, &[&inv_d1]),
            },
        ),
        &n_term,
    );
    // e_rep : mul n_term (mul one inv_d1) = mul n_term (mul (mul d2 inv_d2) inv_d1)
    let e_rep = cong_mul_r(
        r,
        &cong_mul_l(
            r,
            &syp(
                r,
                &EqP {
                    a: m_d2_invd2.clone(),
                    b: r.one.clone(),
                    p: inst(&f.inv_mul, &[&d2t, &nz2]),
                },
            ),
            &inv_d1,
        ),
        &n_term,
    );
    // e1 : mul n_term inv_d1 = mul n_term (mul (mul d2 inv_d2) inv_d1)
    let e1 = trp(r, &e_insert, &e_rep);
    // e2 : ... = mul (mul n_term (mul d2 inv_d2)) inv_d1
    let e2 = syp(r, &mul_assoc(r, &n_term, &m_d2_invd2, &inv_d1));
    // e3 : ... = mul (mul (mul n_term d2) inv_d2) inv_d1
    let e3 = syp(
        r,
        &cong_mul_l(r, &mul_assoc(r, &n_term, &d2t, &inv_d2), &inv_d1),
    );
    // e4 : ... = mul (mul n_term d2) (mul inv_d2 inv_d1)
    let m_n_d2 = mul_term(r, &n_term, &d2t);
    let e4 = mul_assoc(r, &m_n_d2, &inv_d2, &inv_d1);
    // e5 : ... = mul (mul n_term d2) (mul inv_d1 inv_d2)
    let e5 = cong_mul_r(r, &mul_comm(r, &inv_d2, &inv_d1), &m_n_d2);
    // e6 : ... = mul (mul n_term d2) (inv (mul d1 d2))
    let e6 = cong_mul_r(
        r,
        &syp(r, &inv_mul_dist_eqp(f, &d1t, &d2t, &nz1, &nz2)),
        &m_n_d2,
    );
    // e7 : ... = mul (mul n_term d2) inv_dd
    let e7 = cong_mul_r(
        r,
        &cong_inv_eqp(f, &mul_term(r, &d1t, &d2t), &ddt, &e_dd),
        &m_n_d2,
    );
    // e8 : ... = mul (canon num') inv_dd
    // e_num is `mul (canon num) (canon [d2m]) = canon num'`; the e-chain above
    // carries the *raw* denominator `d2t`, so bridge `d2t = canon [d2m]` first.
    let canon_d2 = canon_term(r, &[d2m.clone()]);
    let e_canon_d2 = ring_eq(r, &d2t, &canon_d2, session)?;
    let e8 = trp(
        r,
        &cong_mul_l(r, &cong_mul_r(r, &e_canon_d2, &n_term), &inv_dd),
        &cong_mul_l(r, e_num, &inv_dd),
    );
    let p = trp(
        r,
        &trp(
            r,
            &trp(
                r,
                &trp(r, &trp(r, &trp(r, &trp(r, &e1, &e2), &e3), &e4), &e5),
                &e6,
            ),
            &e7,
        ),
        &e8,
    );
    Ok(EqP {
        a: mul_term(r, &n_term, &inv_d1),
        b: mul_term(r, &n2_term, &inv_dd),
        p: p.p,
    })
}

/// Reify `t` as a fraction.  Base case (atom / numeral / opaque application):
/// `num` is the ring canonical form of `t` and `den` is `one`.
fn reify(f: &Field, ctx: &Ctx, t: &Term, session: &mut Session) -> Result<RF, TypeError> {
    let r = &f.ring;
    if let Some((s, z)) = as_add(r, t, session) {
        let rf1 = reify(f, ctx, &s, session)?;
        let rf2 = reify(f, ctx, &z, session)?;
        return reify_add(f, ctx, &s, &z, &rf1, &rf2, session);
    }
    if let Some(x) = as_inv(f, t, session) {
        return reify_inv(f, ctx, &x, session);
    }
    if let Some((s, a)) = as_mul(r, t, session) {
        let rf1 = reify(f, ctx, &s, session)?;
        let rf2 = reify(f, ctx, &a, session)?;
        return reify_mul(f, ctx, &s, &a, &rf1, &rf2, session);
    }
    let (num, pfn) = decomp(r, t, session)?;
    let den = vec![Mono {
        coeff: 1,
        atoms: Vec::new(),
    }];
    let d_term = prod_term(r, &den[0].atoms);
    let canon_num = canon_term(r, &num);
    let e_inv = inv_canon_one(f, &d_term, session)?;
    let e5 = cong_mul_r(r, &e_inv, &canon_num);
    let e6 = EqP {
        a: mul_term(r, &canon_num, &r.one),
        b: canon_num.clone(),
        p: inst(&r.mul_1_r, &[&canon_num]),
    };
    let e7 = trp(r, &e5, &e6);
    let pf = trp(r, &pfn, &syp(r, &e7));
    Ok(RF {
        num,
        den,
        pf: EqP {
            a: t.clone(),
            b: mul_term(r, &canon_num, &inv_term(f, &d_term)),
            p: pf.p,
        },
    })
}

/// Add of fractions: common denominator `dd = d1*d2`, numerators `num1*d2`
/// and `num2*d1` combined by `poly_merge`.
fn reify_add(
    f: &Field,
    ctx: &Ctx,
    s: &Term,
    z: &Term,
    rf1: &RF,
    rf2: &RF,
    session: &mut Session,
) -> Result<RF, TypeError> {
    let r = &f.ring;
    let dd_mono = Mono {
        coeff: 1,
        atoms: merge_atoms(&rf1.den[0].atoms, &rf2.den[0].atoms),
    };
    let ddt = prod_term(r, &dd_mono.atoms);
    let (n1, pf_n1) = expand_poly(r, &rf1.num, &rf2.den)?;
    let (n2, pf_n2) = expand_poly(r, &rf2.num, &rf1.den)?;
    let s1 = scale_frac(
        f,
        ctx,
        &rf1.num,
        &rf1.den[0],
        &rf2.den[0],
        &n1,
        &pf_n1,
        session,
    )?;
    let s2 = scale_frac(
        f,
        ctx,
        &rf2.num,
        &rf2.den[0],
        &rf1.den[0],
        &n2,
        &pf_n2,
        session,
    )?;
    let (num, _pf_m) = poly_merge(r, &n1, &n2);
    let n2t = canon_term(r, &rf2.num);
    let n1s = canon_term(r, &n1);
    let n2s = canon_term(r, &n2);
    let inv_dd = inv_term(f, &ddt);
    let inv_d2 = inv_term(f, &prod_term(r, &rf2.den[0].atoms));
    let e0 = trp(
        r,
        &cong_add_l(r, &rf1.pf, z),
        &cong_add_r(r, &rf2.pf, &rf1.pf.b),
    );
    // e1 : add (mul n1t inv_d1) (mul n2t inv_d2)
    //      = add (mul n1s inv_dd) (mul n2t inv_d2)
    let e1 = trp(r, &e0, &cong_add_l(r, &s1, &mul_term(r, &n2t, &inv_d2)));
    // e2 : ... = add (mul n1s inv_dd) (mul n2s inv_dd)
    let e2 = trp(r, &e1, &cong_add_r(r, &s2, &mul_term(r, &n1s, &inv_dd)));
    // e3 : ... = mul (canon num) inv_dd  (distribute via ring normalization)
    let num_t = canon_term(r, &num);
    let e3 = trp(
        r,
        &e2,
        &ring_eq(
            r,
            &app(
                &app(&r.add, &mul_term(r, &n1s, &inv_dd)),
                &mul_term(r, &n2s, &inv_dd),
            ),
            &mul_term(r, &num_t, &inv_dd),
            session,
        )?,
    );
    Ok(RF {
        num,
        den: vec![dd_mono],
        pf: EqP {
            a: app(&app(&r.add, s), z),
            b: mul_term(r, &num_t, &inv_dd),
            p: e3.p,
        },
    })
}

/// Mul of fractions: numerator `num1*num2`, denominator `dd = d1*d2`.  The
/// inverses are gathered with `regroup`, then `inv_mul_dist` merges them.
fn reify_mul(
    f: &Field,
    ctx: &Ctx,
    s: &Term,
    a: &Term,
    rf1: &RF,
    rf2: &RF,
    session: &mut Session,
) -> Result<RF, TypeError> {
    let r = &f.ring;
    let dd_mono = Mono {
        coeff: 1,
        atoms: merge_atoms(&rf1.den[0].atoms, &rf2.den[0].atoms),
    };
    let d1t = prod_term(r, &rf1.den[0].atoms);
    let d2t = prod_term(r, &rf2.den[0].atoms);
    let ddt = prod_term(r, &dd_mono.atoms);
    let n1t = canon_term(r, &rf1.num);
    let n2t = canon_term(r, &rf2.num);
    let inv_d1 = inv_term(f, &d1t);
    let inv_d2 = inv_term(f, &d2t);
    let inv_dd = inv_term(f, &ddt);
    let nz1 = discharge(f, ctx, &d1t, session)?;
    let nz2 = discharge(f, ctx, &d2t, session)?;
    let (num, pf_num) = expand_poly(r, &rf1.num, &rf2.num)?;
    let e_dd = ring_eq(r, &mul_term(r, &d1t, &d2t), &ddt, session)?;
    let m_n1n2 = mul_term(r, &n1t, &n2t);
    let e0 = trp(
        r,
        &cong_mul_l(r, &rf1.pf, a),
        &cong_mul_r(r, &rf2.pf, &rf1.pf.b),
    );
    let e1 = trp(r, &e0, &regroup(r, &n1t, &inv_d1, &n2t, &inv_d2));
    let e2 = trp(
        r,
        &e1,
        &cong_mul_r(
            r,
            &syp(
                r,
                &EqP {
                    a: inv_term(f, &mul_term(r, &d1t, &d2t)),
                    b: mul_term(r, &inv_d1, &inv_d2),
                    p: inst(&f.inv_mul_dist, &[&d1t, &d2t, &nz1, &nz2]),
                },
            ),
            &m_n1n2,
        ),
    );
    let e3 = trp(
        r,
        &e2,
        &cong_mul_r(
            r,
            &cong_inv_eqp(f, &mul_term(r, &d1t, &d2t), &ddt, &e_dd),
            &m_n1n2,
        ),
    );
    let e4 = trp(r, &e3, &cong_mul_l(r, &pf_num, &inv_dd));
    let num_t = canon_term(r, &num);
    Ok(RF {
        num,
        den: vec![dd_mono],
        pf: EqP {
            a: app(&app(&r.mul, s), a),
            b: mul_term(r, &num_t, &inv_dd),
            p: e4.p,
        },
    })
}

/// Inverse of a fraction whose numerator is a single coefficient-1 monomial:
/// swap numerator and denominator via `inv_div`.
fn reify_inv(f: &Field, ctx: &Ctx, x: &Term, session: &mut Session) -> Result<RF, TypeError> {
    let r = &f.ring;
    let rf = reify(f, ctx, x, session)?;
    match rf.num.as_slice() {
        [m] if m.coeff == 1 => {
            let m_term = prod_term(r, &m.atoms);
            let d_term = prod_term(r, &rf.den[0].atoms);
            let nz_m = discharge(f, ctx, &m_term, session)?;
            let nz_d = discharge(f, ctx, &d_term, session)?;
            let div_term = mul_term(r, &m_term, &inv_term(f, &d_term));
            let inv_div_term = inv_term(f, &div_term);
            // `rf.pf : x = mul (canon rf.num) (inv d_term)`; the swapped
            // fraction uses the raw numerator term `m_term`, so bridge
            // `mul m_term (inv d_term) = mul (canon rf.num) (inv d_term)`.
            let canon_num = canon_term(r, &rf.num);
            let e_canon_num = ring_eq(r, &m_term, &canon_num, session)?;
            let e_bridge = cong_mul_l(r, &e_canon_num, &inv_term(f, &d_term));
            let pf_div = trp(r, &rf.pf, &syp(r, &e_bridge));
            let e1 = inst(&f.cong_inv, &[x, &div_term, &pf_div.p]);
            let e2 = inst(&f.inv_div, &[&m_term, &d_term, &nz_m, &nz_d]);
            // The new fraction keeps `num = rf.den` (canonicalized) and
            // `den = [m]` (raw), so re-anchor the numerator side of the
            // swapped inverse `mul d_term (inv m_term)` onto `canon rf.den`.
            let canon_nd = canon_term(r, &rf.den);
            let e_canon = ring_eq(r, &d_term, &canon_nd, session)?;
            let e3 = cong_mul_l(r, &e_canon, &inv_term(f, &m_term));
            let target = mul_term(r, &canon_nd, &inv_term(f, &m_term));
            let p = trp(
                r,
                &trp(
                    r,
                    &EqP {
                        a: inv_term(f, x),
                        b: inv_div_term.clone(),
                        p: e1,
                    },
                    &EqP {
                        a: inv_div_term,
                        b: mul_term(r, &d_term, &inv_term(f, &m_term)),
                        p: e2,
                    },
                ),
                &e3,
            );
            Ok(RF {
                num: rf.den,
                den: vec![m.clone()],
                pf: EqP {
                    a: inv_term(f, x),
                    b: target,
                    p: p.p,
                },
            })
        }
        _ => Err(TypeError::Other(format!(
            "field: inverse of '{}' requires a numerator that is a single \
             product of variables (got a sum or a numeral multiple)",
            x
        ))),
    }
}

// ---------------------------------------------------------------------------
// Final step
// ---------------------------------------------------------------------------

/// From the ring-proved cross-multiplication `mul n0 d1 = mul n1 d0`, derive
/// `mul n0 (inv d0) = mul n1 (inv d1)` by inserting `mul d1 (inv d1) = one`,
/// regrouping, substituting the cross product, and cancelling `mul d0 (inv d0)`.
fn frac_eq(
    f: &Field,
    n0: &Term,
    d0: &Term,
    n1: &Term,
    d1: &Term,
    nz0: &Term,
    nz1: &Term,
    cross: &EqP,
) -> Result<EqP, TypeError> {
    let r = &f.ring;
    let inv_d0 = inv_term(f, d0);
    let inv_d1 = inv_term(f, d1);
    let a0 = mul_term(r, n0, &inv_d0);
    let a1 = mul_term(r, n1, &inv_d1);
    let m_d1_invd1 = mul_term(r, d1, &inv_d1);
    let m_d0_invd0 = mul_term(r, d0, &inv_d0);

    // s1 : a0 = mul a0 one
    let s1 = syp(
        r,
        &EqP {
            a: mul_term(r, &a0, &r.one),
            b: a0.clone(),
            p: inst(&r.mul_1_r, &[&a0]),
        },
    );
    // s2 : mul a0 one = mul a0 (mul d1 inv_d1)
    let s2 = syp(
        r,
        &cong_mul_r(
            r,
            &EqP {
                a: m_d1_invd1.clone(),
                b: r.one.clone(),
                p: inst(&f.inv_mul, &[d1, nz1]),
            },
            &a0,
        ),
    );
    // s3 : mul a0 (mul d1 inv_d1) = mul n0 (mul inv_d0 (mul d1 inv_d1))
    let s3 = mul_assoc(r, n0, &inv_d0, &m_d1_invd1);
    // s4 : ... = mul n0 (mul (mul inv_d0 d1) inv_d1)
    let s4 = syp(r, &cong_mul_r(r, &mul_assoc(r, &inv_d0, d1, &inv_d1), n0));
    // s5 : ... = mul n0 (mul (mul d1 inv_d0) inv_d1)
    let s5 = cong_mul_r(r, &cong_mul_l(r, &mul_comm(r, &inv_d0, d1), &inv_d1), n0);
    // s6 : ... = mul (mul n0 (mul d1 inv_d0)) inv_d1
    let s6 = syp(r, &mul_assoc(r, n0, &mul_term(r, d1, &inv_d0), &inv_d1));
    // s7 : ... = mul (mul (mul n0 d1) inv_d0) inv_d1
    let s7 = cong_mul_l(r, &syp(r, &mul_assoc(r, n0, d1, &inv_d0)), &inv_d1);
    // s8 : ... = mul (mul (mul n1 d0) inv_d0) inv_d1
    let s8 = cong_mul_l(r, &cong_mul_l(r, cross, &inv_d0), &inv_d1);
    // s9 : ... = mul (mul n1 (mul d0 inv_d0)) inv_d1
    let s9 = cong_mul_l(r, &mul_assoc(r, n1, d0, &inv_d0), &inv_d1);
    // s10 : ... = mul n1 (mul (mul d0 inv_d0) inv_d1)
    let s10 = mul_assoc(r, n1, &m_d0_invd0, &inv_d1);
    // s11 : ... = mul n1 (mul one inv_d1)
    let s11 = cong_mul_r(
        r,
        &cong_mul_l(
            r,
            &EqP {
                a: m_d0_invd0.clone(),
                b: r.one.clone(),
                p: inst(&f.inv_mul, &[d0, nz0]),
            },
            &inv_d1,
        ),
        n1,
    );
    // s12 : ... = mul n1 inv_d1
    let s12 = cong_mul_r(r, &mul_1_l(r, &inv_d1), n1);

    let p = trp(
        r,
        &trp(
            r,
            &trp(
                r,
                &trp(
                    r,
                    &trp(
                        r,
                        &trp(
                            r,
                            &trp(
                                r,
                                &trp(r, &trp(r, &trp(r, &trp(r, &s1, &s2), &s3), &s4), &s5),
                                &s6,
                            ),
                            &s7,
                        ),
                        &s8,
                    ),
                    &s9,
                ),
                &s10,
            ),
            &s11,
        ),
        &s12,
    );
    Ok(EqP {
        a: a0,
        b: a1,
        p: p.p,
    })
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Entry point called by the `Tactic::Field` arm.
///
/// - `ctx` is the full context the goal lives in (tactic binders innermost).
/// - `goal_ty` is the normalized goal type.
/// - `field_term` is the `F` in `field with F`; `None` triggers instance
///   search: the context is scanned for a `Field` record whose carrier matches
///   the goal, used as if the user had written `field with F`.
pub fn prove(
    dts: &[Datatype],
    ctx: &Ctx,
    goal_ty: &Term,
    _num_tactic: usize,
    _num_intro: usize,
    field_term: Option<&Term>,
    session: &mut Session,
) -> Result<Term, TypeError> {
    let (u, v, carrier) = {
        let goal_nf = nbe_eval_ctx(ctx.len(), goal_ty, session);
        match goal_nf {
            Term::TPath(a, u, v) => {
                let a_nf = nbe_eval_ctx(ctx.len(), &a, session);
                (u.as_ref().clone(), v.as_ref().clone(), a_nf)
            }
            other => {
                return Err(TypeError::Other(format!(
                    "field: goal is not a path (got '{}')",
                    other,
                )));
            }
        }
    };

    let field_term = match field_term {
        some @ Some(_) => some.cloned(),
        None => match find_field_instance(ctx, &carrier, session) {
            Some(inst) => Some(inst),
            None => {
                return Err(TypeError::Other(format!(
                    "field: no Field instance for '{}' in context; use `field with F`",
                    carrier,
                )));
            }
        },
    };
    let field_term = field_term.as_ref().ok_or_else(|| {
        TypeError::Other("field: internal error — no field term after instance search".into())
    })?;

    let f = Field::resolve(dts, ctx, field_term, session)?;
    let r = &f.ring;

    let rf0 = reify(&f, ctx, &u, session)?;
    let rf1 = reify(&f, ctx, &v, session)?;

    let n0 = canon_term(r, &rf0.num);
    let d0 = prod_term(r, &rf0.den[0].atoms);
    let n1 = canon_term(r, &rf1.num);
    let d1 = prod_term(r, &rf1.den[0].atoms);

    let nz0 = discharge(&f, ctx, &d0, session)?;
    let nz1 = discharge(&f, ctx, &d1, session)?;
    let cross = ring_eq(r, &mul_term(r, &n0, &d1), &mul_term(r, &n1, &d0), session)?;
    let scale = frac_eq(&f, &n0, &d0, &n1, &d1, &nz0, &nz1, &cross)?;

    let p = trp(r, &trp(r, &rf0.pf, &scale), &syp(r, &rf1.pf));

    let prev_skip = crate::cubical::typechecker::termination::should_skip_guard(session);
    crate::cubical::typechecker::termination::set_skip_guard(true, session);
    // Verify-once policy: `process_def` re-checks every resolved definition
    // body against its type (`check_with_full_env`) — that mandatory pass is
    // the soundness backstop. Re-checking here as well duplicates the entire
    // pass (~2x wall time on large proof trees, e.g. examples/field_demo.owl),
    // so this diagnostic check runs only under `--debug`, where the rich
    // "kernel rejected the constructed proof" message matters.
    let check_res = if crate::cubical::debug::is_active() {
        check_dt(dts, ctx, &p.p, goal_ty, session)
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
                    expected,
                ),
                crate::cubical::syntax::show_term(
                    &ctx.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(),
                    got,
                ),
                pos,
            ),
            _ => format!("{:?}", e),
        };
        Err(TypeError::Other(format!(
            "field: kernel rejected the constructed proof for\n  goal : Path _ {} {}\n  error: {}",
            u, v, detail,
        )))
    } else {
        Ok(p.p)
    }
}
