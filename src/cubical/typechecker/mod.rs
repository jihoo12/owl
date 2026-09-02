// Cubical TypeChecker — Rust port of typechecker.hs
//
// Depends on:
//   crate::interval::{I, DNF, Literal}
//   crate::syntax::{Term, Name, Level, shift, subst, beta, show_term}
//   crate::eval::{is_top_dnf, is_bot_dnf}
//   crate::equality::{definitionally_equal_ctx, definitionally_equal_ctx_r, EtaResult}

use std::collections::BTreeSet;
use std::sync::Arc;

pub mod errors;
pub mod termination;
pub use errors::{TypeError, err_pos};

use crate::cubical::equality::{EtaResult, definitionally_equal_ctx_r};
use crate::cubical::interval::{DNF, I, Literal, dnf_bot, dnf_leq, dnf_meet};
use crate::cubical::nbe::{nbe_eval, nbe_eval_ctx};
use crate::cubical::session::Session;
use crate::cubical::syntax::{
    Datatype, ElimCase, LevelExpr, Name, Term, beta, shift, show_term, subst,
};
use crate::cubical::syntax::{Variance, compute_param_variances};
use crate::cubical::syntax::{is_bot_dnf, is_top_dnf};

pub fn err_names(ctx: &Ctx) -> Vec<Name> {
    ctx.iter().map(|(n, _)| n.clone()).collect()
}

// Thread-local flag: when true, skip PLam boundary checks in check_dt.
// This is needed for HIT case bodies where the constructor variable is free
// and can't reduce — the boundary conditions are already encoded in the
// expected body type. (Now stored in Session.)

// ---------------------------------------------------------------------------
// Context
// ---------------------------------------------------------------------------

pub type Ctx = Vec<(Name, Term)>;

fn interval_ty() -> Term {
    Term::TIntervalTy
}

pub fn extend_ctx(x: Name, ty: Term, ctx: &Ctx) -> Ctx {
    let mut ctx2 = vec![(x, ty)];
    ctx2.extend_from_slice(ctx);
    ctx2
}

pub fn lookup_ctx(i: i32, ctx: &Ctx) -> Result<Term, TypeError> {
    if i < 0 || i as usize >= ctx.len() {
        Err(TypeError::UnboundVariable(format!("#{}", i)))
    } else {
        // Return the declared type unnormalized. Normalizing here bakes
        // quoted elim case bodies (whose global refs are re-anchored to
        // absolute frame positions) into the type; beta-substituting
        // arguments into that quoted normal form then leaves stale
        // re-anchored references that never re-resolve on the second pass.
        // Consumers normalize at the point of comparison, so a single
        // normalization pass from the raw type keeps both sides consistent.
        Ok(shift(i + 1, 0, &ctx[i as usize].1))
    }
}

/// Fallback used by `infer` on neutral-looking forms (application, fst,
/// snd, ...) whose immediate subterm isn't itself inferable — typically
/// because it's a bare, un-annotated introduction form (a `TAbs`/`PLam`
/// beta-redex or an un-annotated `TPair`). In that case `infer` on the
/// subterm alone can never succeed, but the *whole* term may still reduce
/// to something with an inferable type (e.g. `(\x. x) U0` reduces to `U0`,
/// and `fst (a, b)` reduces to `a`). We retry inference on the fully
/// reduced term, and only give up if reduction made no progress.
fn infer_via_reduction(
    dts: &[Datatype],
    ctx: &Ctx,
    t: &Term,
    original_err: TypeError,
    session: &mut Session,
) -> Result<Term, TypeError> {
    let reduced = nbe_eval_ctx(ctx.len(), t, session);
    if reduced == *t {
        Err(original_err)
    } else {
        infer_dt(dts, ctx, &reduced, session)
    }
}

// ---------------------------------------------------------------------------
// Require helpers
// ---------------------------------------------------------------------------

pub fn require_equal(
    ctx: &Ctx,
    expected: &Term,
    got: &Term,
    session: &mut Session,
) -> Result<(), TypeError> {
    let names: Vec<Name> = ctx.iter().map(|(n, _)| n.clone()).collect();
    crate::debug_log!(
        "require_equal: {} == {}",
        show_term(&names, expected),
        show_term(&names, got)
    );
    match definitionally_equal_ctx_r(ctx, expected, got, session) {
        EtaResult::Equal => Ok(()),
        EtaResult::NotEqual => Err(TypeError::TypeMismatch {
            expected: Box::new(nbe_eval_ctx(ctx.len(), expected, session)),
            got: Box::new(nbe_eval_ctx(ctx.len(), got, session)),
            names: err_names(ctx),
            pos: err_pos(ctx, got, session),
        }),
        EtaResult::Exhausted => Err(TypeError::EtaFuelExhausted {
            t1: Box::new(nbe_eval_ctx(ctx.len(), expected, session)),
            t2: Box::new(nbe_eval_ctx(ctx.len(), got, session)),
            names: err_names(ctx),
            pos: err_pos(ctx, got, session),
        }),
    }
}

pub fn require_equal_endpt(
    ctx: &Ctx,
    expected: &Term,
    got: &Term,
    session: &mut Session,
) -> Result<(), TypeError> {
    match definitionally_equal_ctx_r(ctx, expected, got, session) {
        EtaResult::Equal => Ok(()),
        EtaResult::NotEqual => {
            let ne1 = nbe_eval_ctx(ctx.len(), expected, session);
            let ne2 = nbe_eval_ctx(ctx.len(), got, session);
            Err(TypeError::TypeMismatch {
                expected: Box::new(ne1),
                got: Box::new(ne2),
                names: err_names(ctx),
                pos: err_pos(ctx, got, session),
            })
        }
        EtaResult::Exhausted => Err(TypeError::EtaFuelExhausted {
            t1: Box::new(nbe_eval_ctx(ctx.len(), expected, session)),
            t2: Box::new(nbe_eval_ctx(ctx.len(), got, session)),
            names: err_names(ctx),
            pos: err_pos(ctx, got, session),
        }),
    }
}

#[allow(dead_code)]
pub fn require_universe(
    ctx: &Ctx,
    t: &Term,
    session: &mut Session,
) -> Result<LevelExpr, TypeError> {
    require_universe_dt(&[], ctx, t, session)
}

#[allow(dead_code)]
fn require_universe_dt(
    dts: &[Datatype],
    ctx: &Ctx,
    t: &Term,
    session: &mut Session,
) -> Result<LevelExpr, TypeError> {
    let ty = infer_dt(dts, ctx, t, session)?;
    match nbe_eval_ctx(ctx.len(), &ty, session) {
        Term::TUniv(n) => Ok(n.clone()),
        other => Err(TypeError::ExpectedUniverse {
            ty: other.clone(),
            names: err_names(ctx),
            pos: err_pos(ctx, t, session),
        }),
    }
}

fn type_level_dt(
    dts: &[Datatype],
    ctx: &Ctx,
    t: &Term,
    session: &mut Session,
) -> Result<LevelExpr, TypeError> {
    // Match type formers structurally first. `nbe_eval` on a Π-type that still
    // mentions outer binders can collapse free de Bruijn indices and break
    // universe-level checking for dependent arrows like `(A : U0) -> A -> A`.
    match t {
        Term::TPi(x, a, b, _) => {
            let i = type_level_dt(dts, ctx, a, session)?;
            let ctx2 = extend_ctx(x.clone(), nbe_eval_ctx(ctx.len(), a, session), ctx);
            let j = type_level_dt(dts, &ctx2, b, session)?;
            Ok(LevelExpr::max(i, j))
        }
        Term::TPath(a, u, v) => {
            // For PathP-style dependent paths, a may be a PLam (type family).
            // In that case, check that the body of the PLam is well-typed,
            // and verify endpoints against the instantiated family.
            let n = match nbe_eval_ctx(ctx.len(), a, session) {
                Term::PLam(_, body) => {
                    // The type family body should be well-typed in a context
                    // with an interval variable. We check that the family
                    // returns values in some universe by checking at i0.
                    let ctx2 = extend_ctx("_i".to_string(), interval_ty(), ctx);
                    let a_at0 =
                        nbe_eval_ctx(ctx2.len(), &beta(&body, &Term::TInterval(I::I0)), session);
                    type_level_dt(dts, &ctx2, &a_at0, session)?
                }
                _ => type_level_dt(dts, ctx, a, session)?,
            };
            let a_ = nbe_eval_ctx(ctx.len(), a, session);
            let u_ty = match &a_ {
                Term::PLam(_, body) => {
                    nbe_eval_ctx(ctx.len(), &beta(body, &Term::TInterval(I::I0)), session)
                }
                p => p.clone(),
            };
            let v_ty = match &a_ {
                Term::PLam(_, body) => {
                    nbe_eval_ctx(ctx.len(), &beta(body, &Term::TInterval(I::I1)), session)
                }
                p => p.clone(),
            };
            check_dt(dts, ctx, u, &u_ty, session)?;
            check_dt(dts, ctx, v, &v_ty, session)?;
            Ok(n)
        }
        Term::Meta(_) => {
            // Metavariable holes are assumed to be types at some level;
            // they will be solved during checking and the real level checked then.
            Ok(LevelExpr::LConst(0))
        }
        Term::TEquiv(a, b) => {
            let n = type_level_dt(dts, ctx, a, session)?;
            let m = type_level_dt(dts, ctx, b, session)?;
            Ok(LevelExpr::max(n, m))
        }
        Term::TSigma(x, a, b) => {
            let i = type_level_dt(dts, ctx, a, session)?;
            let ctx2 = extend_ctx(x.clone(), nbe_eval_ctx(ctx.len(), a, session), ctx);
            let j = type_level_dt(dts, &ctx2, b, session)?;
            Ok(LevelExpr::max(i, j))
        }
        _ => match nbe_eval_ctx(ctx.len(), t, session) {
            Term::TProp => Ok(LevelExpr::LConst(0)), // Prop : U0
            Term::TSSet => Ok(LevelExpr::LConst(1)), // SSet : U1
            Term::TUniv(n) => Ok(n.clone()),
            Term::TData(d, _) => {
                let level = dts
                    .iter()
                    .find(|dt| dt.name == d)
                    .and_then(|dt| dt.universe_level.clone())
                    .unwrap_or(LevelExpr::LConst(0));
                Ok(level)
            }
            Term::TIntervalTy => Ok(LevelExpr::LConst(0)),
            _ => {
                let ty = infer_dt(dts, ctx, t, session)?;
                match nbe_eval_ctx(ctx.len(), &ty, session) {
                    Term::TUniv(n) => Ok(n.clone()),
                    other => Err(TypeError::ExpectedUniverse {
                        ty: other,
                        names: err_names(ctx),
                        pos: err_pos(ctx, t, session),
                    }),
                }
            }
        },
    }
}

pub fn check_interval(ctx: &Ctx, t: &Term, session: &mut Session) -> Result<(), TypeError> {
    check_interval_dt(&[], ctx, t, session)
}

fn check_interval_dt(
    dts: &[Datatype],
    ctx: &Ctx,
    t: &Term,
    session: &mut Session,
) -> Result<(), TypeError> {
    match t {
        Term::TInterval(_) | Term::TCube(_) => return Ok(()),
        _ => {}
    }
    let ty = infer_dt(dts, ctx, t, session)?;
    if ty == interval_ty() {
        Ok(())
    } else {
        Err(TypeError::NotAnInterval {
            t: t.clone(),
            names: err_names(ctx),
            pos: err_pos(ctx, t, session),
        })
    }
}

#[allow(dead_code)]
pub fn require_equiv(
    ctx: &Ctx,
    t: &Term,
    session: &mut Session,
) -> Result<(Term, Term), TypeError> {
    require_equiv_dt(&[], ctx, t, session)
}

fn require_equiv_dt(
    dts: &[Datatype],
    ctx: &Ctx,
    t: &Term,
    session: &mut Session,
) -> Result<(Term, Term), TypeError> {
    let ty = infer_dt(dts, ctx, t, session)?;
    match nbe_eval_ctx(ctx.len(), &ty, session) {
        Term::TEquiv(a, b) => Ok((
            nbe_eval_ctx(ctx.len(), &a, session),
            nbe_eval_ctx(ctx.len(), &b, session),
        )),
        other => Err(TypeError::ExpectedEquiv {
            ty: other,
            names: err_names(ctx),
            pos: err_pos(ctx, t, session),
        }),
    }
}

// ---------------------------------------------------------------------------
// Face-restriction helpers
// ---------------------------------------------------------------------------

/// Apply a single DNF literal as a substitution on a term.
/// `Pos n`    → iₙ = 1   (IVar n ↦ I1)
/// `NegVar n` → iₙ = 0   (IVar n ↦ I0)
pub fn apply_literal(lit: &Literal, t: &Term, session: &mut Session) -> Term {
    apply_literal_inner(lit, t, session)
}

fn apply_literal_inner(lit: &Literal, t: &Term, session: &mut Session) -> Term {
    let (n, val) = match lit {
        Literal::Pos(k) => (*k, I::I1),
        Literal::NegVar(k) => (*k, I::I0),
    };
    fn go_i(i: &I, n: i32, val: &I) -> I {
        match i {
            I::Var(k) if *k == n => val.clone(),
            I::Meet(a, b) => I::Meet(Arc::new(go_i(a, n, val)), Arc::new(go_i(b, n, val))),
            I::Join(a, b) => I::Join(Arc::new(go_i(a, n, val)), Arc::new(go_i(b, n, val))),
            I::Neg(a) => I::Neg(Arc::new(go_i(a, n, val))),
            other => other.clone(),
        }
    }

    fn go(t: &Term, n: i32, val: &I, session: &mut Session) -> Term {
        match t {
            Term::TInterval(i) => nbe_eval(&Term::TInterval(go_i(i, n, val)), session),

            Term::TCube(DNF { cubes }) => {
                // Substitute the literal into each cube then re-normalise.
                let subst_lit = |l: &Literal| -> I {
                    match l {
                        Literal::Pos(k) => go_i(&I::Var(*k), n, val),
                        Literal::NegVar(k) => I::Neg(Arc::new(go_i(&I::Var(*k), n, val))),
                    }
                };
                let subst_cube = |c: &BTreeSet<Literal>| -> I {
                    c.iter().fold(I::I1, |acc, l| {
                        I::Meet(Arc::new(subst_lit(l)), Arc::new(acc))
                    })
                };
                let combined = cubes.iter().fold(I::I0, |acc, c| {
                    I::Join(Arc::new(subst_cube(c)), Arc::new(acc))
                });
                nbe_eval(&Term::TInterval(combined), session)
            }

            Term::TApp(f, a) => nbe_eval(
                &Term::TApp(
                    Arc::new(go(f, n, val, session)),
                    Arc::new(go(a, n, val, session)),
                ),
                session,
            ),
            Term::TAbs(x, b) => Term::TAbs(x.clone(), Arc::new(go(b, n, val, session))),
            Term::TPi(x, a, b, implicit) => Term::TPi(
                x.clone(),
                Arc::new(go(a, n, val, session)),
                Arc::new(go(b, n, val, session)),
                *implicit,
            ),
            Term::TPath(a, u, v) => Term::TPath(
                Arc::new(go(a, n, val, session)),
                Arc::new(go(u, n, val, session)),
                Arc::new(go(v, n, val, session)),
            ),
            Term::PLam(i, b) => Term::PLam(i.clone(), Arc::new(go(b, n + 1, val, session))),
            Term::PApp(p, r) => nbe_eval(
                &Term::PApp(
                    Arc::new(go(p, n, val, session)),
                    Arc::new(go(r, n, val, session)),
                ),
                session,
            ),
            Term::THComp(a, sys, u0) => nbe_eval(
                &Term::THComp(
                    Arc::new(go(a, n, val, session)),
                    sys.iter()
                        .map(|(phi, t)| (go(phi, n, val, session), go(t, n, val, session)))
                        .collect(),
                    Arc::new(go(u0, n, val, session)),
                ),
                session,
            ),
            Term::TComp(a, sys, u0) => nbe_eval(
                &Term::TComp(
                    Arc::new(go(a, n, val, session)),
                    sys.iter()
                        .map(|(phi, t)| (go(phi, n, val, session), go(t, n, val, session)))
                        .collect(),
                    Arc::new(go(u0, n, val, session)),
                ),
                session,
            ),
            Term::TFill(a, sys, u0) => nbe_eval(
                &Term::TFill(
                    Arc::new(go(a, n, val, session)),
                    sys.iter()
                        .map(|(phi, t)| (go(phi, n, val, session), go(t, n, val, session)))
                        .collect(),
                    Arc::new(go(u0, n, val, session)),
                ),
                session,
            ),
            Term::THFill(a, sys, u0) => nbe_eval(
                &Term::THFill(
                    Arc::new(go(a, n, val, session)),
                    sys.iter()
                        .map(|(phi, t)| (go(phi, n, val, session), go(t, n, val, session)))
                        .collect(),
                    Arc::new(go(u0, n, val, session)),
                ),
                session,
            ),
            Term::TEquiv(a, b) => Term::TEquiv(
                Arc::new(go(a, n, val, session)),
                Arc::new(go(b, n, val, session)),
            ),
            Term::TMkEquiv(a, b, f, g, eta, eps) => Term::TMkEquiv(
                Arc::new(go(a, n, val, session)),
                Arc::new(go(b, n, val, session)),
                Arc::new(go(f, n, val, session)),
                Arc::new(go(g, n, val, session)),
                Arc::new(go(eta, n, val, session)),
                Arc::new(go(eps, n, val, session)),
            ),
            Term::TEquivFwd(e, x) => nbe_eval(
                &Term::TEquivFwd(
                    Arc::new(go(e, n, val, session)),
                    Arc::new(go(x, n, val, session)),
                ),
                session,
            ),
            Term::TUa(e) => Term::TUa(Arc::new(go(e, n, val, session))),
            Term::TTransport(p, x) => nbe_eval(
                &Term::TTransport(
                    Arc::new(go(p, n, val, session)),
                    Arc::new(go(x, n, val, session)),
                ),
                session,
            ),
            Term::TGlue(a, ph, te) => nbe_eval(
                &Term::TGlue(
                    Arc::new(go(a, n, val, session)),
                    Arc::new(go(ph, n, val, session)),
                    Arc::new(go(te, n, val, session)),
                ),
                session,
            ),
            Term::TGlueElem(ph, x, a) => nbe_eval(
                &Term::TGlueElem(
                    Arc::new(go(ph, n, val, session)),
                    Arc::new(go(x, n, val, session)),
                    Arc::new(go(a, n, val, session)),
                ),
                session,
            ),
            Term::TUnglue(ph, te, g) => nbe_eval(
                &Term::TUnglue(
                    Arc::new(go(ph, n, val, session)),
                    Arc::new(go(te, n, val, session)),
                    Arc::new(go(g, n, val, session)),
                ),
                session,
            ),
            Term::TPartial(ph, a) => nbe_eval(
                &Term::TPartial(
                    Arc::new(go(ph, n, val, session)),
                    Arc::new(go(a, n, val, session)),
                ),
                session,
            ),
            Term::TSigma(x, a, b) => Term::TSigma(
                x.clone(),
                Arc::new(go(a, n, val, session)),
                Arc::new(go(b, n, val, session)),
            ),
            Term::TPair(a, b) => Term::TPair(
                Arc::new(go(a, n, val, session)),
                Arc::new(go(b, n, val, session)),
            ),
            Term::TFst(p) => nbe_eval(&Term::TFst(Arc::new(go(p, n, val, session))), session),
            Term::TSnd(p) => nbe_eval(&Term::TSnd(Arc::new(go(p, n, val, session))), session),
            // Inductive types / HITs: recurse into all sub-terms.
            Term::TData(d, params) => nbe_eval(
                &Term::TData(
                    d.clone(),
                    params.iter().map(|a| go(a, n, val, session)).collect(),
                ),
                session,
            ),
            Term::TCon(data, con, args) => nbe_eval(
                &Term::TCon(
                    data.clone(),
                    con.clone(),
                    args.iter().map(|a| go(a, n, val, session)).collect(),
                ),
                session,
            ),
            Term::TPCon(data, con, args, r) => nbe_eval(
                &Term::TPCon(
                    data.clone(),
                    con.clone(),
                    args.iter().map(|a| go(a, n, val, session)).collect(),
                    Arc::new(go(r, n, val, session)),
                ),
                session,
            ),
            Term::TSqCon(data, con, args, r, s) => nbe_eval(
                &Term::TSqCon(
                    data.clone(),
                    con.clone(),
                    args.iter().map(|a| go(a, n, val, session)).collect(),
                    Arc::new(go(r, n, val, session)),
                    Arc::new(go(s, n, val, session)),
                ),
                session,
            ),
            Term::TCellCon(data, con, args, ivars) => nbe_eval(
                &Term::TCellCon(
                    data.clone(),
                    con.clone(),
                    args.iter().map(|a| go(a, n, val, session)).collect(),
                    ivars.iter().map(|a| go(a, n, val, session)).collect(),
                ),
                session,
            ),
            Term::TElim(motive, cases, scrut) => nbe_eval(
                &Term::TElim(
                    Arc::new(go(motive, n, val, session)),
                    cases
                        .iter()
                        .map(|c| ElimCase {
                            con: c.con.clone(),
                            binders: c.binders.clone(),
                            body: Box::new(go(&c.body, n, val, session)),
                            as_name: c.as_name.clone(),
                            record_bindings: c.record_bindings.clone(),
                            refinements: c.refinements.clone(),
                        })
                        .collect(),
                    Arc::new(go(scrut, n, val, session)),
                ),
                session,
            ),
            Term::Meta(_) => t.clone(),
            Term::TBy(tactics) => Term::TBy(
                tactics
                    .iter()
                    .map(|tac| match tac {
                        crate::cubical::syntax::Tactic::Exact(t) => {
                            crate::cubical::syntax::Tactic::Exact(go(t, n, val, session))
                        }
                        other => other.clone(),
                    })
                    .collect(),
            ),
            // TVar, TUniv, TIntervalTy: no interval vars
            other => other.clone(),
        }
    }

    go(t, n, &val, session)
}

/// Strip exactly `n` outer PLam layers from a term, returning the inner body.
/// Returns `Err` if the term doesn't have enough PLam layers.
fn strip_n_plams(t: &Term, n: usize) -> Result<&Term, ()> {
    let mut cur = t;
    for _ in 0..n {
        match cur {
            Term::PLam(_, b) => cur = b.as_ref(),
            _ => return Err(()),
        }
    }
    Ok(cur)
}

/// Check that `tube_at0 ≡ base` on every face of `phi`'s DNF.
fn check_faces(
    ctx: &Ctx,
    phi: &Term,
    tube_at0: &Term,
    base: &Term,
    session: &mut Session,
) -> Result<(), TypeError> {
    match phi {
        Term::TCube(DNF { cubes }) => {
            for cube in cubes {
                // Apply all literals in the cube as substitutions.
                let apply_all = |t: &Term, session: &mut Session| -> Term {
                    cube.iter()
                        .fold(t.clone(), |acc, lit| apply_literal(lit, &acc, session))
                };
                let lhs = nbe_eval(&apply_all(tube_at0, session), session);
                let rhs = nbe_eval(&apply_all(base, session), session);
                require_equal_endpt(ctx, &lhs, &rhs, session)?;
            }
            Ok(())
        }
        // Non-DNF phi: fall back to a direct equality check.
        _ => require_equal_endpt(ctx, tube_at0, base, session),
    }
}

fn shift_cases(cases: &[ElimCase], d: i32) -> Vec<ElimCase> {
    cases
        .iter()
        .map(|case| ElimCase {
            con: case.con.clone(),
            binders: case.binders.clone(),
            body: Box::new(shift(d, case.binders.len() as i32, &case.body)),
            as_name: case.as_name.clone(),
            record_bindings: case.record_bindings.clone(),
            refinements: case.refinements.clone(),
        })
        .collect()
}

/// Compute the expected endpoint for a path-constructor case in an eliminator.
///
/// The face term (e.g. `inc(trunc_0)`) is a constructor application whose
/// free variables are the case binders.  Instead of evaluating
/// `TElim(motive, cases, face)` through `nbe_eval` — which cannot reduce
/// when the scrutinee has free variables — we directly look up the matching
/// case body and apply it to the face's constructor arguments.
fn eval_elim_face(
    _motive: &Term,
    cases: &[ElimCase],
    face: &Term,
    _ord_vars: &[Term],
    _ambient_depth: i32,
    session: &mut Session,
) -> Term {
    // Peel apart the face to find (con_name, con_args).
    // The face is either:
    //   TCon(d, c, args)           — zero or more args in TCon
    //   TApp(TCon(d,c,base), ...)  — additional args wrapped in TApp
    fn extract_con(t: &Term) -> Option<(&str, Vec<Term>)> {
        match t {
            Term::TCon(_d, c, args) => Some((c, args.clone())),
            Term::TApp(f, a) | Term::PApp(f, a) => {
                if let Some((c, mut args)) = extract_con(f) {
                    args.push(a.as_ref().clone());
                    Some((c, args))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    if let Some((con_name, con_args)) = extract_con(face) {
        if let Some(case) = cases.iter().find(|c| c.con == con_name) {
            // Apply each constructor arg to the case body via beta.
            // The case body has `case.binders.len()` lambda binders;
            // each beta substitutes one binder with the corresponding arg.
            let mut result: Term = (*case.body).clone();
            for arg in &con_args {
                result = beta(&result, arg);
            }
            return nbe_eval(&result, session);
        }
    }

    // Fallback (shouldn't normally be reached): try the old TElim approach.
    nbe_eval(
        &Term::TElim(
            Arc::new(shift(_ambient_depth, 0, _motive)),
            shift_cases(cases, _ambient_depth),
            Arc::new(nbe_eval(face, session)),
        ),
        session,
    )
}

// ---------------------------------------------------------------------------
// Parameter inference + argument checking (shared by TCon/TPCon/TSqCon)
// ---------------------------------------------------------------------------

/// Two-phase helper for parameterized constructor checking:
///
/// 1. **Phase 1 — Infer params:** Walk the argument list; when the
///    (partially-substituted) expected type for an argument is a bare
///    `TVar(k)` with `k < num_params`, the argument *is* the parameter
///    value — infer its type from the context.
///
/// 2. **Phase 2 — Check args:** Walk again with fully-substituted arg_tys,
///    checking each argument against its expected type.
///
/// `initial_params` optionally pre-seeds some parameters (e.g. from an
/// expected type in bidirectional checking).  Its length must equal
/// `num_params`.
///
/// Returns `(param_terms, checked_args)` where `param_terms[i]` is
/// `Some(term)` if parameter `i` was inferred, `None` otherwise.
fn infer_and_check_params(
    dts: &[Datatype],
    ctx: &Ctx,
    sig_arg_tys: &[Term],
    args: &[Term],
    num_params: usize,
    session: &mut Session,
) -> Result<(Vec<Option<Term>>, Vec<Term>), TypeError> {
    infer_and_check_params_seeded(dts, ctx, sig_arg_tys, args, num_params, &[], session)
}

/// Like `infer_and_check_params` but accepts pre-seeded parameter values.
fn infer_and_check_params_seeded(
    dts: &[Datatype],
    ctx: &Ctx,
    sig_arg_tys: &[Term],
    args: &[Term],
    num_params: usize,
    initial_params: &[Option<Term>],
    session: &mut Session,
) -> Result<(Vec<Option<Term>>, Vec<Term>), TypeError> {
    debug_assert!(initial_params.len() <= num_params);
    // Phase 1: Infer parameter values from argument types.
    let mut param_terms: Vec<Option<Term>> = initial_params.to_vec();
    param_terms.resize(num_params, None);
    {
        let mut prev_args: Vec<Term> = Vec::new();
        for (k, arg) in args.iter().enumerate() {
            let mut arg_ty = sig_arg_tys[k].clone();
            // Substitute known params using plain subst (not beta).
            // Param i lives at de Bruijn (num_params - 1 - i) due to
            // insert(0,...) ordering. Process highest index first.
            for i in 0..num_params {
                let d = (num_params - 1 - i) as i32;
                if let Some(ref pv) = param_terms[i] {
                    arg_ty = subst(d, pv, &arg_ty);
                }
            }
            if let Term::TVar(idx) = &arg_ty {
                let i = *idx as usize;
                if i < num_params && param_terms[i].is_none() {
                    param_terms[i] = Some(infer_dt(dts, ctx, arg, session)?);
                    continue;
                }
            }
            prev_args.push(nbe_eval(arg, session));
        }
    }
    // Phase 2: Check args with fully-substituted arg_tys.
    let mut checked_args: Vec<Term> = Vec::with_capacity(args.len());
    for (k, arg) in args.iter().enumerate() {
        let mut arg_ty = sig_arg_tys[k].clone();
        // Substitute known params.
        for i in 0..num_params {
            let d = (num_params - 1 - i) as i32;
            if let Some(ref pv) = param_terms[i] {
                arg_ty = subst(d, pv, &arg_ty);
            }
        }
        // NOTE: We intentionally do NOT apply previous-arg substitution here.
        // The arg_tys telescope references only datatype parameters (via de Bruijn
        // indices), not previous constructor arguments.  Using `beta` would
        // incorrectly shift(-1,0,...) all free variables after substitution,
        // corrupting indices.  Dependent record fields (where a field type
        // references a previous field) are not yet supported.
        check_dt(dts, ctx, arg, &nbe_eval(&arg_ty, session), session)?;
        checked_args.push(nbe_eval(arg, session));
    }
    Ok((param_terms, checked_args))
}

/// Build the parameter list for a return type from inferred param terms.
/// Uninferred params default to `TVar(i)`.
fn build_params(param_terms: &[Option<Term>]) -> Vec<Term> {
    param_terms
        .iter()
        .enumerate()
        .map(|(i, p)| p.clone().unwrap_or_else(|| Term::TVar(i as i32)))
        .collect()
}

// ---------------------------------------------------------------------------
// Implicit argument resolution
// ---------------------------------------------------------------------------

/// Try to find a term in the context that matches the given type.
/// This is used for implicit argument resolution - when we have an implicit
/// binder `{x : A}`, we search the context for a term of type `A`.
fn find_implicit_arg(
    _dts: &[Datatype],
    ctx: &Ctx,
    target_ty: &Term,
    session: &mut Session,
) -> Option<Term> {
    let target_nf = nbe_eval_ctx(ctx.len(), target_ty, session);
    for (i, (_name, ty)) in ctx.iter().enumerate() {
        // Stored binder types are recorded relative to the binder's own frame
        // (binder at index 0); re-anchor with the same shift `lookup_ctx`
        // applies before comparing against the target.
        let ty_shifted = shift(i as i32 + 1, 0, ty);
        let ty_nf = nbe_eval_ctx(ctx.len(), &ty_shifted, session);
        if definitionally_equal_ctx_r(ctx, &ty_nf, &target_nf, session) == EtaResult::Equal {
            return Some(Term::TVar(i as i32));
        }
    }
    None
}

/// Fill in implicit Pi arguments in a function type.
/// Given a function type like `Π {x : A} (y : B) {z : C}. D`,
/// and a context, this searches for implicit arguments and applies them.
/// Returns the updated function term with implicit args applied, and the
/// remaining type after implicit args are filled.
fn fill_implicit_args(
    _dts: &[Datatype],
    ctx: &Ctx,
    mut f: Term,
    mut f_ty: Term,
    session: &mut Session,
) -> Result<(Term, Term), TypeError> {
    loop {
        let f_ty_nf = nbe_eval_ctx(ctx.len(), &f_ty, session);
        match f_ty_nf {
            Term::TPi(_x, a, b, implicit) if implicit => {
                // Search for an implicit argument of type `a`
                if let Some(arg) = find_implicit_arg(_dts, ctx, &a, session) {
                    let arg_clone = arg.clone();
                    // Apply the implicit argument
                    f = Term::TApp(Arc::new(f), Arc::new(arg));
                    // Update the type to the codomain with the argument substituted
                    f_ty = beta(&b, &arg_clone);
                    // Continue the loop in case there are more implicit args
                    continue;
                }
                // No implicit arg found - we'll need the user to provide it explicitly
                break;
            }
            _ => break,
        }
    }
    Ok((f, f_ty))
}

// ---------------------------------------------------------------------------
// Type Inference
// ---------------------------------------------------------------------------

pub fn infer(ctx: &Ctx, t: &Term, session: &mut Session) -> Result<Term, TypeError> {
    infer_dt(&[], ctx, t, session)
}

/// Like `infer` but with access to declared datatypes for checking
/// `TData`/`TCon`/`TPCon`/`TElim`.  Pass `&[]` when no datatypes are in scope.
pub fn infer_dt(
    dts: &[Datatype],
    ctx: &Ctx,
    t: &Term,
    session: &mut Session,
) -> Result<Term, TypeError> {
    const INFER_DT_MAX_DEPTH: usize = 2000;
    let d = session.infer_depth_enter();
    if d >= INFER_DT_MAX_DEPTH {
        session.infer_depth_restore(d);
        return Err(TypeError::Other(format!(
            "infer_dt depth exceeded ({INFER_DT_MAX_DEPTH})"
        )));
    }
    let result = infer_dt_inner(dts, ctx, t, session);
    session.infer_depth_restore(d);
    result
}

fn infer_dt_inner(
    dts: &[Datatype],
    ctx: &Ctx,
    t: &Term,
    session: &mut Session,
) -> Result<Term, TypeError> {
    let names: Vec<Name> = ctx.iter().map(|(n, _)| n.clone()).collect();
    crate::debug_scope!("infer {} : ctx[{}]", show_term(&names, t), ctx.len());
    session.set_current_dts(dts);
    match t {
        // Variable
        Term::TVar(i) => lookup_ctx(*i, ctx),

        // Universe: U_n : U_{n+1}
        Term::TUniv(n) => Ok(Term::TUniv(LevelExpr::suc(n.clone()))),

        // Subuniverses
        Term::TProp => Ok(Term::TUniv(LevelExpr::LConst(0))), // Prop : U0
        Term::TSSet => Ok(Term::TUniv(LevelExpr::LConst(1))), // SSet : U1

        // Universe lifting: lift A m : U_{max(n,m)} when A : U_n
        Term::TLift(a, m) => {
            let n = type_level_dt(dts, ctx, a, session)?;
            Ok(Term::TUniv(LevelExpr::max(n.clone(), m.clone())))
        }
        // Universe lowering: lower A : U_n when A : U_{n+1}
        Term::TLower(a) => match nbe_eval_ctx(ctx.len(), a, session) {
            Term::TLift(inner, _m) => {
                let lvl = type_level_dt(dts, ctx, &inner, session)?;
                Ok(Term::TUniv(lvl))
            }
            other => {
                let ty = type_level_dt(dts, ctx, &other, session)?;
                if ty.as_const().map_or(false, |c| c > 0) {
                    Ok(Term::TUniv(if let Some(c) = ty.as_const() {
                        LevelExpr::LConst(c - 1)
                    } else {
                        LevelExpr::LSuc(Box::new(ty))
                    }))
                } else {
                    Ok(Term::TUniv(LevelExpr::LConst(0)))
                }
            }
        },

        // Application: f a  where  f : Π(x:A).B
        Term::TApp(f, a) => match infer_dt(dts, ctx, f, session) {
            Ok(f_ty) => {
                // Fill in any implicit arguments before checking the explicit argument
                let (_f_filled, f_ty_filled) =
                    fill_implicit_args(dts, ctx, f.as_ref().clone(), f_ty, session)?;
                let (a_ty, b_ty) = match &f_ty_filled {
                    Term::TPi(_, a, b, _) => (a.as_ref().clone(), b.as_ref().clone()),
                    _ => match nbe_eval_ctx(ctx.len(), &f_ty_filled, session) {
                        Term::TPi(_, a, b, _) => (a.as_ref().clone(), b.as_ref().clone()),
                        other => {
                            return Err(TypeError::ExpectedPi {
                                ty: other,
                                names: err_names(ctx),
                                pos: err_pos(ctx, f, session),
                            });
                        }
                    },
                };
                check_dt(dts, ctx, a, &a_ty, session)?;
                // Keep the result unnormalized so that chains of applications
                // (e.g. a fully-applied law) beta-substitute into raw
                // codomains throughout, then normalize exactly once at the
                // comparison site. Normalizing here would beta-substitute the
                // outer argument into a codomain already baked into a quoted
                // normal form, leaving stale re-anchored global references in
                // elim case bodies.
                Ok(beta(&b_ty, a))
            }
            Err(e) => infer_via_reduction(dts, ctx, t, e, session),
        },

        // Pi formation: Π(x:A).B : U(max i j)
        Term::TPi(x, a_ty, b_ty, _) => {
            let i = type_level_dt(dts, ctx, a_ty, session)?;
            let ctx2 = extend_ctx(x.clone(), nbe_eval_ctx(ctx.len(), a_ty, session), ctx);
            let j = type_level_dt(dts, &ctx2, b_ty, session)?;
            Ok(Term::TUniv(LevelExpr::max(i, j)))
        }

        // Path type: Path A u v : U n
        Term::TPath(a_ty, u, v) => {
            let n = match nbe_eval_ctx(ctx.len(), a_ty, session) {
                Term::PLam(_, body) => {
                    let ctx2 = extend_ctx("_i".to_string(), interval_ty(), ctx);
                    let a_at0 =
                        nbe_eval_ctx(ctx2.len(), &beta(&body, &Term::TInterval(I::I0)), session);
                    type_level_dt(dts, &ctx2, &a_at0, session)?
                }
                _ => type_level_dt(dts, ctx, a_ty, session)?,
            };
            let a_ty_ = nbe_eval_ctx(ctx.len(), a_ty, session);
            let u_ty = match &a_ty_ {
                Term::PLam(_, body) => {
                    nbe_eval_ctx(ctx.len(), &beta(body, &Term::TInterval(I::I0)), session)
                }
                p => p.clone(),
            };
            let v_ty = match &a_ty_ {
                Term::PLam(_, body) => {
                    nbe_eval_ctx(ctx.len(), &beta(body, &Term::TInterval(I::I1)), session)
                }
                p => p.clone(),
            };
            check_dt(dts, ctx, u, &u_ty, session)?;
            check_dt(dts, ctx, v, &v_ty, session)?;
            Ok(Term::TUniv(n.clone()))
        }

        // Path application: p @ r
        Term::PApp(p, r) => match infer_dt(dts, ctx, p, session) {
            Ok(p_ty) => match nbe_eval_ctx(ctx.len(), &p_ty, session) {
                Term::TPath(a_ty, _, _) => {
                    check_interval_dt(dts, ctx, r, session)?;
                    let r_ = nbe_eval_ctx(ctx.len(), r, session);
                    Ok(match nbe_eval_ctx(ctx.len(), &a_ty, session) {
                        Term::PLam(_, body) => nbe_eval_ctx(ctx.len(), &beta(&body, &r_), session),
                        plain => plain,
                    })
                }
                other => Err(TypeError::ExpectedPath {
                    ty: other,
                    names: err_names(ctx),
                    pos: err_pos(ctx, p, session),
                }),
            },
            Err(e) => infer_via_reduction(dts, ctx, t, e, session),
        },

        // Interval atoms
        Term::TInterval(_) | Term::TCube(_) => Ok(interval_ty()),
        Term::TIntervalTy => Ok(Term::TUniv(LevelExpr::LConst(0))),
        Term::TLevelTy => Ok(Term::TUniv(LevelExpr::LConst(0))),

        // TId: Id A a b : U_n  when  A : U_n, a : A, b : A
        Term::TId(a, x, y) => {
            let n = type_level_dt(dts, ctx, a, session)?;
            let a_val = nbe_eval_ctx(ctx.len(), a, session);
            check_dt(dts, ctx, x, &a_val, session)?;
            check_dt(dts, ctx, y, &a_val, session)?;
            Ok(Term::TUniv(n.clone()))
        }

        // TRefl: Refl x : Id A x x  when  x : A
        Term::TRefl(x) => {
            let x_ty = infer_dt(dts, ctx, x, session)?;
            Ok(Term::TId(
                Arc::new(x_ty),
                Arc::new((**x).clone()),
                Arc::new((**x).clone()),
            ))
        }

        // J motive base p : B y p
        //
        // Requires:
        //   p   : Id A x y          (for some x, y)
        //   B   : (y : A) → Type   (the motive; simplified non-dependent version)
        //   d   : B x               (the reflexivity case)
        // Returns: B y
        Term::TJ(motive, base, p) => {
            // Infer the type of p — must be Id A x y.
            let p_ty = infer_dt(dts, ctx, p, session)?;
            let (a_ty, x_val, y_val) = match nbe_eval_ctx(ctx.len(), &p_ty, session) {
                Term::TId(a, x, y) => (a, x, y),
                other => {
                    return Err(TypeError::ExpectedPath {
                        // reuse ExpectedPath error for Id too
                        ty: other,
                        names: err_names(ctx),
                        pos: err_pos(ctx, p, session),
                    });
                }
            };

            // Infer the type of motive — must be (y : A) → Type.
            // Handle TAbs (no type annotation) by checking the body.
            match motive.as_ref() {
                Term::TAbs(y_name, body) => {
                    // Extend context with y : A, check body is a type
                    let ctx2 = extend_ctx(y_name.clone(), a_ty.as_ref().clone(), ctx);
                    type_level_dt(dts, &ctx2, body, session)?;
                }
                _ => {
                    let motive_ty = infer_dt(dts, ctx, motive, session)?;
                    match nbe_eval_ctx(ctx.len(), &motive_ty, session) {
                        Term::TPi(_y_name, dom, _cod, _) => {
                            let dom_val = nbe_eval_ctx(ctx.len(), &dom, session);
                            require_equal(ctx, &a_ty, &dom_val, session)?;
                        }
                        other => {
                            return Err(TypeError::ExpectedPi {
                                ty: other,
                                names: err_names(ctx),
                                pos: err_pos(ctx, motive, session),
                            });
                        }
                    }
                }
            }

            // Check that base : B x.
            let base_expected = nbe_eval_ctx(
                ctx.len(),
                &Term::TApp(motive.clone(), x_val.clone()),
                session,
            );
            check_dt(dts, ctx, base, &base_expected, session)?;

            // Return B y.
            Ok(nbe_eval_ctx(
                ctx.len(),
                &Term::TApp(motive.clone(), y_val.clone()),
                session,
            ))
        }

        // Lambdas cannot be inferred
        t @ Term::TAbs(_, _) | t @ Term::PLam(_, _) => Err(TypeError::CannotInfer {
            t: t.clone(),
            names: err_names(ctx),
            pos: err_pos(ctx, t, session),
        }),

        // Tactic blocks cannot be inferred (need type annotation)
        t @ Term::TBy(_) => Err(TypeError::CannotInfer {
            t: t.clone(),
            names: err_names(ctx),
            pos: err_pos(ctx, t, session),
        }),

        // Unresolved metavariable
        Term::Meta(id) => {
            let name = session
                .get_meta_name(*id)
                .map(|n| format!("?{}", n))
                .unwrap_or_else(|| format!("?_{}", id));
            let expected = session.get_meta_expected(*id);
            match expected {
                Some(ty) => Err(TypeError::Other(format!(
                    "cannot infer type of hole {}; expected type is {}\n  \
                     (Tip: fill the hole with a term, or place it where the \
                     expected type is known)",
                    name,
                    show_term(&err_names(ctx), &ty),
                ))),
                None => Err(TypeError::Other(format!(
                    "cannot infer type of hole {}; use a type annotation",
                    name,
                ))),
            }
        }

        // Equiv type
        Term::TEquiv(a, b) => {
            let n = type_level_dt(dts, ctx, a, session)?;
            let m = type_level_dt(dts, ctx, b, session)?;
            Ok(Term::TUniv(LevelExpr::max(n.clone(), m.clone())))
        }

        // mkEquiv: build an equivalence record
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            type_level_dt(dts, ctx, a, session)?;
            type_level_dt(dts, ctx, b, session)?;
            let a_ = nbe_eval_ctx(ctx.len(), a, session);
            let b_ = nbe_eval_ctx(ctx.len(), b, session);
            // f : A → B
            check(
                ctx,
                f,
                &Term::TPi(
                    "_".into(),
                    Arc::new(a_.clone()),
                    Arc::new(shift(1, 0, &b_)),
                    false,
                ),
                session,
            )?;
            // g : B → A
            check(
                ctx,
                g,
                &Term::TPi(
                    "_".into(),
                    Arc::new(b_.clone()),
                    Arc::new(shift(1, 0, &a_)),
                    false,
                ),
                session,
            )?;
            // eta : (a : A) → Path A a (g (f a))
            check(
                ctx,
                eta,
                &Term::TPi(
                    "a".into(),
                    Arc::new(a_.clone()),
                    Arc::new(Term::TPath(
                        Arc::new(shift(1, 0, &a_)),
                        Arc::new(Term::TVar(0)),
                        Arc::new(Term::TApp(
                            Arc::new(shift(1, 0, g)),
                            Arc::new(Term::TApp(
                                Arc::new(shift(1, 0, f)),
                                Arc::new(Term::TVar(0)),
                            )),
                        )),
                    )),
                    false,
                ),
                session,
            )?;
            // eps : (b : B) → Path B (f (g b)) b
            check(
                ctx,
                eps,
                &Term::TPi(
                    "b".into(),
                    Arc::new(b_.clone()),
                    Arc::new(Term::TPath(
                        Arc::new(shift(1, 0, &b_)),
                        Arc::new(Term::TApp(
                            Arc::new(shift(1, 0, f)),
                            Arc::new(Term::TApp(
                                Arc::new(shift(1, 0, g)),
                                Arc::new(Term::TVar(0)),
                            )),
                        )),
                        Arc::new(Term::TVar(0)),
                    )),
                    false,
                ),
                session,
            )?;
            Ok(Term::TEquiv(Arc::new(a_), Arc::new(b_)))
        }

        // equivFwd e x : B   where  e : Equiv A B,  x : A
        Term::TEquivFwd(e, x) => {
            let (a, b) = require_equiv_dt(dts, ctx, e, session)?;
            check_dt(dts, ctx, x, &a, session)?;
            Ok(b)
        }

        // ua e : Path U A B   where  e : Equiv A B
        Term::TUa(e) => {
            let (a, b) = require_equiv_dt(dts, ctx, e, session)?;
            let n = type_level_dt(dts, ctx, &a, session)?;
            Ok(Term::TPath(
                Arc::new(Term::TUniv(n)),
                Arc::new(a),
                Arc::new(b),
            ))
        }

        // transport p x : B   where  p : Path U A B,  x : A
        Term::TTransport(p, x) => {
            let p_ty = match p.as_ref() {
                // `p` is a literal path-lambda (an introduction form, not a
                // path-typed neutral) — `infer(p)` can never succeed on a
                // bare PLam, so derive its TPath type directly from the
                // body instead, the same way `infer` already does for
                // TAbs-applied-to-argument in TApp.
                Term::PLam(i, body) => {
                    // The body typically has the form PApp(path, IVar(0)),
                    // i.e. `<i> path @ i` which is equivalent to `path`.
                    // Infer the type of `path` directly to get the TPath,
                    // whose endpoints are the argument and return types.
                    let path = match body.as_ref() {
                        Term::PApp(path, _) => path.as_ref().clone(),
                        _ => body.as_ref().clone(),
                    };
                    let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
                    let path_ty = nbe_eval(&infer_dt(dts, &ctx2, &path, session)?, session);
                    // path_ty should be TPath(a_ty, u, v). The endpoints
                    // need to be shifted back to the outer context
                    // (removing the interval binder at index 0).
                    match path_ty {
                        Term::TPath(a_ty, u, v) => {
                            let u = shift(-1, 0, &u);
                            let v = shift(-1, 0, &v);
                            Term::TPath(a_ty, Arc::new(u), Arc::new(v))
                        }
                        _other => {
                            let a_ty = infer_dt(dts, &ctx2, body, session)?;
                            let u =
                                shift(-1, 0, &apply_literal(&Literal::NegVar(0), body, session));
                            let v = shift(-1, 0, &apply_literal(&Literal::Pos(0), body, session));
                            Term::TPath(Arc::new(a_ty), Arc::new(u), Arc::new(v))
                        }
                    }
                }
                _ => infer_dt(dts, ctx, p, session)?,
            };
            match nbe_eval(&p_ty, session) {
                Term::TPath(a_ty, u, v) => {
                    let (x_ty, ret_ty) = match nbe_eval(&a_ty, session) {
                        Term::PLam(_, body) => (
                            nbe_eval(&beta(&body, &Term::TInterval(I::I0)), session),
                            nbe_eval(&beta(&body, &Term::TInterval(I::I1)), session),
                        ),
                        _plain => (nbe_eval(&u, session), nbe_eval(&v, session)),
                    };
                    check_dt(dts, ctx, x, &x_ty, session)?;
                    Ok(ret_ty)
                }
                other => Err(TypeError::ExpectedPath {
                    ty: other,
                    names: err_names(ctx),
                    pos: err_pos(ctx, p, session),
                }),
            }
        }

        // transp A r x : A r   where  A : I → U,  r : I,  x : A i0
        Term::TTransp(a, r, x) => {
            // A should be a function from I to a universe (a type family).
            // Create a fresh interval variable to check A's domain.
            let ctx_a = extend_ctx("i_transp".to_string(), Term::TIntervalTy, ctx);
            let _a_body_ty = infer_dt(dts, &ctx_a, a, session)?;
            let r_ty = infer_dt(dts, ctx, r, session)?;
            check_interval_dt(dts, ctx, &r_ty, session)?;
            // x : A i0
            let x_ty = nbe_eval(
                &Term::TApp(Arc::new(shift(1, 0, a)), Arc::new(Term::TInterval(I::I0))),
                session,
            );
            check_dt(dts, ctx, x, &x_ty, session)?;
            // Result type: A r
            let result = nbe_eval(
                &Term::TApp(Arc::new(shift(1, 0, a)), Arc::new(shift(1, 0, r))),
                session,
            );
            Ok(result)
        }

        // Glue type formation
        Term::TGlue(a_ty, phi, te) => {
            let n = type_level_dt(dts, ctx, a_ty, session)?;
            let a_ty_ = nbe_eval(a_ty, session);
            check_interval_dt(dts, ctx, phi, session)?;
            let m = match te.as_ref() {
                // te = (A, e) : Σ(X : U). Equiv X a_ty_
                Term::TPair(te_a, _) => {
                    let sigma = Term::TSigma(
                        "X".to_string(),
                        Arc::new(Term::TUniv(n.clone())),
                        Arc::new(Term::TEquiv(
                            Arc::new(Term::TVar(0)),
                            Arc::new(shift(1, 0, &a_ty_)),
                        )),
                    );
                    check_dt(dts, ctx, te, &sigma, session)?;
                    type_level_dt(dts, ctx, te_a, session)?
                }
                // te = λ_. (A, e) — strip the lambda and check the body
                Term::TAbs(_, body) => {
                    let body_stripped = beta(body, &Term::TInterval(I::I1));
                    match &body_stripped {
                        Term::TPair(te_a, _) => {
                            let sigma = Term::TSigma(
                                "X".to_string(),
                                Arc::new(Term::TUniv(n.clone())),
                                Arc::new(Term::TEquiv(
                                    Arc::new(Term::TVar(0)),
                                    Arc::new(shift(1, 0, &a_ty_)),
                                )),
                            );
                            check_dt(dts, ctx, &body_stripped, &sigma, session)?;
                            type_level_dt(dts, ctx, te_a, session)?
                        }
                        other => {
                            return Err(TypeError::Other(format!(
                                "Glue: expected the lambda body to be a pair (type, equiv), got: {}",
                                other
                            )));
                        }
                    }
                }
                _ => {
                    let te_ty = infer_dt(dts, ctx, te, session)?;
                    match nbe_eval(&te_ty, session) {
                        Term::TUniv(k) => k.clone(),
                        Term::TEquiv(a, b) => {
                            let a_ = nbe_eval(&a, session);
                            let b_ = nbe_eval(&b, session);
                            require_equal(ctx, &b_, &a_ty_, session)?;
                            let p = type_level_dt(dts, ctx, &a_, session)?;
                            let q = type_level_dt(dts, ctx, &b_, session)?;
                            LevelExpr::max(p.clone(), q.clone())
                        }
                        Term::TMkEquiv(a, b, _, _, _, _) => {
                            let a_ = nbe_eval(&a, session);
                            let b_ = nbe_eval(&b, session);
                            require_equal(ctx, &b_, &a_ty_, session)?;
                            let p = type_level_dt(dts, ctx, &a_, session)?;
                            let q = type_level_dt(dts, ctx, &b_, session)?;
                            LevelExpr::max(p.clone(), q.clone())
                        }
                        other => {
                            return Err(TypeError::Other(format!(
                                "Glue: equivalence argument has unexpected type: {}",
                                other
                            )));
                        }
                    }
                }
            };
            Ok(Term::TUniv(LevelExpr::max(n.clone(), m.clone())))
        }

        // Partial type: [_ | phi] A — partial elements of A on face phi
        // Inference: TPartial(phi, A) : U_n where A : U_n
        Term::TPartial(phi, a) => {
            check_interval_dt(dts, ctx, phi, session)?;
            let n = type_level_dt(dts, ctx, a, session)?;
            Ok(Term::TUniv(n.clone()))
        }

        // System type: [phi => A, psi => B] — partial type families
        // Inference: TSystemType(sys) : U_n where each A_k : U_n
        // and system coherence is satisfied (overlapping faces agree).
        Term::TSystemType(sys) => {
            let mut level = LevelExpr::LConst(0);
            for (phi, a) in sys {
                check_interval_dt(dts, ctx, phi, session)?;
                let n = type_level_dt(dts, ctx, a, session)?;
                level = LevelExpr::max(level, n);
            }
            // Coherence check: for any two entries (phi, A) and (psi, B),
            // on their overlap (phi ∩ psi), A and B must agree.
            for i in 0..sys.len() {
                for j in (i + 1)..sys.len() {
                    let phi_i = nbe_eval(&sys[i].0, session);
                    let psi_j = nbe_eval(&sys[j].0, session);
                    let overlap =
                        dnf_meet(&term_to_dnf(&phi_i, session), &term_to_dnf(&psi_j, session));
                    if overlap != dnf_bot() {
                        let a_i = nbe_eval(&sys[i].1, session);
                        let a_j = nbe_eval(&sys[j].1, session);
                        if a_i != a_j {
                            return Err(TypeError::Other(format!(
                                "system type coherence: on overlap of {} and {}, types {} and {} disagree",
                                show_term(&[], &sys[i].0),
                                show_term(&[], &sys[j].0),
                                show_term(&[], &sys[i].1),
                                show_term(&[], &sys[j].1),
                            )));
                        }
                    }
                }
            }
            Ok(Term::TUniv(level))
        }

        // unglue phi te g
        Term::TUnglue(phi, te, g) => {
            check_interval_dt(dts, ctx, phi, session)?;
            let phi_ = nbe_eval(phi, session);
            if is_top_dnf(&phi_) {
                infer_dt(dts, ctx, &Term::TEquivFwd(te.clone(), g.clone()), session)
            } else if is_bot_dnf(&phi_) {
                infer_dt(dts, ctx, g, session)
            } else {
                let g_ty = infer_dt(dts, ctx, g, session)?;
                match nbe_eval(&g_ty, session) {
                    Term::TGlue(a_ty, _, _) => Ok(nbe_eval(&a_ty, session)),
                    other => Err(TypeError::Other(format!(
                        "unglue: expected argument of Glue type, got: {}",
                        other
                    ))),
                }
            }
        }

        // glue elem — can only infer in degenerate phi cases
        t @ Term::TGlueElem(phi, elm, a) => {
            let phi_ = nbe_eval(phi, session);
            if is_top_dnf(&phi_) {
                infer_dt(dts, ctx, elm, session)
            } else if is_bot_dnf(&phi_) {
                infer_dt(dts, ctx, a, session)
            } else {
                Err(TypeError::CannotInfer {
                    t: t.clone(),
                    names: err_names(ctx),
                    pos: err_pos(ctx, t, session),
                })
            }
        }

        // Sigma formation: Σ(x:A).B : U(max i j)
        Term::TSigma(x, a_ty, b_ty) => {
            let i = type_level_dt(dts, ctx, a_ty, session)?;
            let ctx2 = extend_ctx(x.clone(), nbe_eval(a_ty, session), ctx);
            let j = type_level_dt(dts, &ctx2, b_ty, session)?;
            Ok(Term::TUniv(LevelExpr::max(i, j)))
        }

        // fst p : A   where  p : Σ(x:A).B
        Term::TFst(p) => match infer_dt(dts, ctx, p, session) {
            Ok(p_ty) => match nbe_eval(&p_ty, session) {
                Term::TSigma(_, a_ty, _) => Ok(nbe_eval(&a_ty, session)),
                other => Err(TypeError::ExpectedSigma {
                    ty: other,
                    names: err_names(ctx),
                    pos: err_pos(ctx, p, session),
                }),
            },
            Err(e) => infer_via_reduction(dts, ctx, t, e, session),
        },

        // snd p : B[fst p / x]   where  p : Σ(x:A).B
        Term::TSnd(p) => match infer_dt(dts, ctx, p, session) {
            Ok(p_ty) => match nbe_eval(&p_ty, session) {
                Term::TSigma(_, _, b_ty) => {
                    Ok(nbe_eval(&beta(&b_ty, &Term::TFst(p.clone())), session))
                }
                other => Err(TypeError::ExpectedSigma {
                    ty: other,
                    names: err_names(ctx),
                    pos: err_pos(ctx, p, session),
                }),
            },
            Err(e) => infer_via_reduction(dts, ctx, t, e, session),
        },

        // r.field : field type   where  r : RecordType
        Term::TProj(field, r) => match infer_dt(dts, ctx, r, session) {
            Ok(r_ty) => match nbe_eval(&r_ty, session) {
                Term::TData(dname, params) => {
                    if let Some(dt) = dts.iter().find(|dt| dt.name == dname) {
                        if let Some(field_names) = &dt.field_names {
                            if let Some(con_sig) = dt.cons.first() {
                                if let Some(idx) = field_names.iter().position(|n| n == field) {
                                    if let Some(raw_ty) = con_sig.arg_tys.get(idx) {
                                        // Substitute param variables with concrete params.
                                        let mut result = raw_ty.clone();
                                        // Substitute param variables with concrete params.
                                        // In the record parser, params are inserted into
                                        // term_env via insert(0,...), so params[i] ends
                                        // up at de Bruijn index (num_params - 1 - i).
                                        let n = params.len() as i32;
                                        for (i, param_val) in params.iter().enumerate() {
                                            let db_idx = n - 1 - (i as i32);
                                            result = subst(db_idx, param_val, &result);
                                        }
                                        // Dependent records (fields referencing earlier fields)
                                        // are not yet supported. The loop below would substitute
                                        // earlier field projections for free-variable references,
                                        // but for non-dependent fields it corrupts de Bruijn
                                        // indices via unconditional shift(-1,0,...).
                                        return Ok(result);
                                    }
                                    return Err(TypeError::Other(format!(
                                        "field '{}' has no type in record '{}'",
                                        field, dname
                                    )));
                                }
                                return Err(TypeError::Other(format!(
                                    "field '{}' not found in record '{}'",
                                    field, dname
                                )));
                            }
                        }
                    }
                    Err(TypeError::Other(format!(
                        "cannot project '{}' from non-record type",
                        field
                    )))
                }
                other => Err(TypeError::Other(format!(
                    "cannot project '{}' from type {}",
                    field,
                    show_term(&names, &other)
                ))),
            },
            Err(e) => infer_via_reduction(dts, ctx, t, e, session),
        },

        // Record update: r { field1 = e1, field2 = e2 }
        Term::TRecordUpdate(r, updates) => {
            let r_ty = infer_dt(dts, ctx, r, session)?;
            match nbe_eval(&r_ty, session) {
                Term::TData(dname, params) => {
                    let dt = dts.iter().find(|dt| dt.name == dname).ok_or_else(|| {
                        TypeError::UnknownDatatype {
                            name: dname.clone(),
                            pos: err_pos(ctx, r, session),
                        }
                    })?;
                    let field_names = dt.field_names.as_ref().ok_or_else(|| {
                        TypeError::Other(format!("'{}' is not a record type", dname))
                    })?;
                    let con_sig = dt.cons.first().ok_or_else(|| {
                        TypeError::Other(format!("record '{}' has no constructor", dname))
                    })?;
                    let n = params.len() as i32;
                    for (field_name, new_val) in updates {
                        let idx = field_names
                            .iter()
                            .position(|f| f == field_name)
                            .ok_or_else(|| {
                                TypeError::Other(format!(
                                    "field '{}' not found in record '{}'",
                                    field_name, dname
                                ))
                            })?;
                        let mut field_ty = con_sig.arg_tys[idx].clone();
                        for (pi, param_val) in params.iter().enumerate() {
                            let db_idx = n - 1 - (pi as i32);
                            field_ty = subst(db_idx, param_val, &field_ty);
                        }
                        check_dt(dts, ctx, new_val, &nbe_eval(&field_ty, session), session)?;
                    }
                    Ok(r_ty)
                }
                other => Err(TypeError::Other(format!(
                    "record update expected a record type, got: {}",
                    show_term(&err_names(ctx), &other)
                ))),
            }
        }

        // Pairs cannot be inferred without annotation
        t @ Term::TPair(_, _) => Err(TypeError::CannotInfer {
            t: t.clone(),
            names: err_names(ctx),
            pos: err_pos(ctx, t, session),
        }),

        // hcomp A [phi -> tube, ...] base
        Term::THComp(a_ty, sys, base) => {
            type_level_dt(dts, ctx, a_ty, session)?;
            let a_ty_ = nbe_eval(a_ty, session);
            check_dt(dts, ctx, &base, &a_ty_, session)?;
            for (phi, tube) in sys {
                check_interval_dt(dts, ctx, &phi, session)?;
                let tube_val = nbe_eval(&tube, session);
                match tube_val {
                    Term::PLam(i, body) => {
                        let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
                        let a_ty_s = shift(1, 0, &a_ty_);
                        check_dt(dts, &ctx2, &body, &a_ty_s, session)?;
                        let tube_at0 = nbe_eval(&beta(&body, &Term::TInterval(I::I0)), session);
                        let phi_ = nbe_eval(&phi, session);
                        check_faces(ctx, &phi_, &tube_at0, &nbe_eval(&base, session), session)?;
                    }
                    tube_ => {
                        let tube_ty = infer_dt(dts, ctx, &tube_, session)?;
                        match nbe_eval(&tube_ty, session) {
                            Term::TPath(a, u, v) => {
                                if !definitionally_equal_ctx_r(
                                    ctx,
                                    &nbe_eval(&a, session),
                                    &a_ty_,
                                    session,
                                )
                                .is_equal()
                                {
                                    return Err(TypeError::TypeMismatch {
                                        expected: Box::new(nbe_eval(&a_ty_, session)),
                                        got: Box::new(nbe_eval(&a, session)),
                                        names: err_names(ctx),
                                        pos: err_pos(ctx, &tube, session),
                                    });
                                }
                                check_dt(dts, ctx, &nbe_eval(&u, session), &a_ty_, session)?;
                                check_dt(dts, ctx, &nbe_eval(&v, session), &a_ty_, session)?;
                                let phi_ = nbe_eval(&phi, session);
                                check_faces(
                                    ctx,
                                    &phi_,
                                    &nbe_eval(&u, session),
                                    &nbe_eval(&base, session),
                                    session,
                                )?;
                            }
                            other => {
                                return Err(TypeError::ExpectedPath {
                                    ty: other,
                                    names: err_names(ctx),
                                    pos: err_pos(ctx, &tube, session),
                                });
                            }
                        }
                    }
                }
            }
            Ok(a_ty_)
        }

        // comp A [phi -> tube, ...] base : A 1
        Term::TComp(a_fam, sys, base) => {
            let ctx_i = extend_ctx("i".to_string(), interval_ty(), ctx);
            let _a_fam_ty = type_level_dt(dts, &ctx_i, a_fam, session)?;
            let a_fam_ = nbe_eval(a_fam, session);
            let a_at0 = match &a_fam_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I0)), session),
                _ => a_fam_.clone(),
            };
            check_dt(dts, ctx, base, &a_at0, session)?;
            for (phi, tube) in sys {
                check_interval_dt(dts, ctx, &phi, session)?;
                match nbe_eval(&tube, session) {
                    Term::PLam(i, body) => {
                        let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
                        let a_fam_s = shift(1, 0, &a_fam_);
                        let body_ty = match &a_fam_s {
                            Term::PLam(_, b) => nbe_eval(&beta(b, &Term::TVar(0)), session),
                            _ => shift(1, 0, &a_at0),
                        };
                        check_dt(dts, &ctx2, &body, &body_ty, session)?;
                        let tube_at0 = nbe_eval(&beta(&body, &Term::TInterval(I::I0)), session);
                        let phi_ = nbe_eval(&phi, session);
                        check_faces(ctx, &phi_, &tube_at0, &nbe_eval(&base, session), session)?;
                    }
                    tube_ => {
                        let tube_ty = infer_dt(dts, ctx, &tube_, session)?;
                        match nbe_eval(&tube_ty, session) {
                            Term::TPath(_a, u, v) => {
                                check_dt(dts, ctx, &nbe_eval(&u, session), &a_at0, session)?;
                                check_dt(
                                    dts,
                                    ctx,
                                    &nbe_eval(&v, session),
                                    &nbe_eval(
                                        &Term::PApp(
                                            a_fam.clone(),
                                            Arc::new(Term::TInterval(I::I1)),
                                        ),
                                        session,
                                    ),
                                    session,
                                )?;
                                let phi_ = nbe_eval(&phi, session);
                                check_faces(
                                    ctx,
                                    &phi_,
                                    &nbe_eval(&u, session),
                                    &nbe_eval(&base, session),
                                    session,
                                )?;
                            }
                            other => {
                                return Err(TypeError::ExpectedPath {
                                    ty: other,
                                    names: err_names(ctx),
                                    pos: err_pos(ctx, &tube, session),
                                });
                            }
                        }
                    }
                }
            }
            let a_at1 = match &a_fam_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I1)), session),
                _ => a_fam_.clone(),
            };
            Ok(a_at1)
        }

        // fill A [phi -> tube, ...] base : (j : I) → A j
        Term::TFill(a_fam, sys, base) => {
            let ctx_i = extend_ctx("i".to_string(), interval_ty(), ctx);
            type_level_dt(dts, &ctx_i, a_fam, session)?;
            let a_fam_ = nbe_eval(a_fam, session);
            let a_at0 = match &a_fam_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I0)), session),
                _ => a_fam_.clone(),
            };
            check_dt(dts, ctx, base, &a_at0, session)?;
            for (phi, tube) in sys {
                check_interval_dt(dts, ctx, &phi, session)?;
                match nbe_eval(&tube, session) {
                    Term::PLam(i, body) => {
                        let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
                        let a_fam_s = shift(1, 0, &a_fam_);
                        let body_ty = match &a_fam_s {
                            Term::PLam(_, b) => nbe_eval(&beta(b, &Term::TVar(0)), session),
                            _ => shift(1, 0, &a_at0),
                        };
                        check_dt(dts, &ctx2, &body, &body_ty, session)?;
                        let tube_at0 = nbe_eval(&beta(&body, &Term::TInterval(I::I0)), session);
                        let phi_ = nbe_eval(&phi, session);
                        check_faces(ctx, &phi_, &tube_at0, &nbe_eval(&base, session), session)?;
                    }
                    tube_ => {
                        let tube_ty = infer_dt(dts, ctx, &tube_, session)?;
                        match nbe_eval(&tube_ty, session) {
                            Term::TPath(_a, u, v) => {
                                check_dt(dts, ctx, &nbe_eval(&u, session), &a_at0, session)?;
                                check_dt(
                                    dts,
                                    ctx,
                                    &nbe_eval(&v, session),
                                    &nbe_eval(
                                        &Term::PApp(
                                            a_fam.clone(),
                                            Arc::new(Term::TInterval(I::I1)),
                                        ),
                                        session,
                                    ),
                                    session,
                                )?;
                                let phi_ = nbe_eval(&phi, session);
                                check_faces(
                                    ctx,
                                    &phi_,
                                    &nbe_eval(&u, session),
                                    &nbe_eval(&base, session),
                                    session,
                                )?;
                            }
                            other => {
                                return Err(TypeError::ExpectedPath {
                                    ty: other,
                                    names: err_names(ctx),
                                    pos: err_pos(ctx, &tube, session),
                                });
                            }
                        }
                    }
                }
            }
            let comp_result = Term::TComp(a_fam.clone(), sys.clone(), base.clone());
            Ok(Term::TPath(
                Arc::new(shift(1, 0, &a_fam_)),
                Arc::new(nbe_eval(base, session)),
                Arc::new(nbe_eval(&comp_result, session)),
            ))
        }

        // hfill A [phi -> tube, ...] base : Path A base (hcomp A [phi -> tube, ...] base)
        Term::THFill(a_ty, sys, base) => {
            type_level_dt(dts, ctx, a_ty, session)?;
            let a_ty_ = nbe_eval(a_ty, session);
            check_dt(dts, ctx, base, &a_ty_, session)?;
            for (phi, tube) in sys {
                check_interval_dt(dts, ctx, &phi, session)?;
                match nbe_eval(&tube, session) {
                    Term::PLam(i, body) => {
                        let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
                        let a_ty_s = shift(1, 0, &a_ty_);
                        check_dt(dts, &ctx2, &body, &a_ty_s, session)?;
                        let tube_at0 = nbe_eval(&beta(&body, &Term::TInterval(I::I0)), session);
                        let phi_ = nbe_eval(&phi, session);
                        check_faces(ctx, &phi_, &tube_at0, &nbe_eval(&base, session), session)?;
                    }
                    tube_ => {
                        let tube_ty = infer_dt(dts, ctx, &tube_, session)?;
                        match nbe_eval(&tube_ty, session) {
                            Term::TPath(a, u, v) => {
                                if !definitionally_equal_ctx_r(
                                    ctx,
                                    &nbe_eval(&a, session),
                                    &a_ty_,
                                    session,
                                )
                                .is_equal()
                                {
                                    return Err(TypeError::TypeMismatch {
                                        expected: Box::new(nbe_eval(&a_ty_, session)),
                                        got: Box::new(nbe_eval(&a, session)),
                                        names: err_names(ctx),
                                        pos: err_pos(ctx, &tube, session),
                                    });
                                }
                                check_dt(dts, ctx, &nbe_eval(&u, session), &a_ty_, session)?;
                                check_dt(dts, ctx, &nbe_eval(&v, session), &a_ty_, session)?;
                                let phi_ = nbe_eval(&phi, session);
                                check_faces(
                                    ctx,
                                    &phi_,
                                    &nbe_eval(&u, session),
                                    &nbe_eval(&base, session),
                                    session,
                                )?;
                            }
                            other => {
                                return Err(TypeError::ExpectedPath {
                                    ty: other,
                                    names: err_names(ctx),
                                    pos: err_pos(ctx, &tube, session),
                                });
                            }
                        }
                    }
                }
            }
            let hcomp_result = Term::THComp(a_ty.clone(), sys.clone(), base.clone());
            Ok(Term::TPath(
                Arc::new(shift(1, 0, &a_ty_)),
                Arc::new(nbe_eval(base, session)),
                Arc::new(nbe_eval(&hcomp_result, session)),
            ))
        }

        // ------------------------------------------------------------------
        // Inductive types / HITs
        // ------------------------------------------------------------------

        // TData(d, args) : ...  where args are the parameter arguments.
        // If args fully apply all parameters (or there are no parameters),
        // the type is U_k. If args are fewer than parameters, we build
        // a Pi type for the remaining parameters.
        Term::TData(d, args) => {
            let dt =
                dts.iter()
                    .find(|dt| &dt.name == d)
                    .ok_or_else(|| TypeError::UnknownDatatype {
                        name: d.clone(),
                        pos: err_pos(ctx, t, session),
                    })?;

            // If the datatype has a universe-level annotation, use it directly
            // for the fully-applied case.
            if args.len() >= dt.params.len() {
                if let Some(level) = dt.universe_level.clone() {
                    return Ok(Term::TUniv(level));
                }
            }

            // Compute the maximum universe level over all constructor arg types.
            // For parameterized types, substitute provided parameter args into
            // the arg_tys before computing levels, so that TVar(0) etc.
            // referencing parameters get resolved.
            let num_params = dt.params.len();
            let mut max_level: LevelExpr = LevelExpr::LConst(0);

            // Ordinary constructors
            for con_sig in &dt.cons {
                let mut tel_ctx = ctx.clone();
                let mut prev_args: Vec<Term> = Vec::new();
                for (k, arg_ty) in con_sig.arg_tys.iter().enumerate() {
                    // Substitute provided parameters.  Param `i` (in parse
                    // order) lives at de Bruijn index `num_params - 1 - i`;
                    // record field types reference params under their own
                    // binders, so `subst` (which descends through binders) is
                    // required instead of head-`beta`, which would shift all
                    // free variables and corrupt those references.
                    let mut substituted = arg_ty.clone();
                    for i in 0..num_params.min(args.len()) {
                        let d = (num_params - 1 - i) as i32;
                        substituted = subst(d, &args[i], &substituted);
                    }
                    let arg_ty_inst = prev_args
                        .iter()
                        .rev()
                        .fold(substituted, |ty, a| beta(&ty, a));
                    let lvl = type_level_dt(dts, &tel_ctx, &arg_ty_inst, session)?;
                    max_level = LevelExpr::max(max_level, lvl);
                    // Record fields never reference earlier fields, and their
                    // types reference the datatype parameters at depths that
                    // include the field's own binders (handled by `subst`
                    // above and `type_level_dt`'s Pi recursion).  Building a
                    // dependent telescope context for them would shift the
                    // parameter references onto the wrong slots, so skip the
                    // accumulation for records.
                    if dt.field_names.is_none() {
                        let var_name = format!("_con_arg_{}", k);
                        let depth = k as i32;
                        prev_args.push(shift(depth + 1, 0, &Term::TVar(0)));
                        tel_ctx = extend_ctx(var_name, nbe_eval(&arg_ty_inst, session), &tel_ctx);
                    }
                }
            }

            // Path constructors (ordinary args only; interval arg is in 𝕀 ⊂ U_0)
            for pcon_sig in &dt.pcons {
                let mut tel_ctx = ctx.clone();
                let mut prev_args: Vec<Term> = Vec::new();
                for (k, arg_ty) in pcon_sig.arg_tys.iter().enumerate() {
                    let mut substituted = arg_ty.clone();
                    for i in 0..num_params.min(args.len()) {
                        let d = (num_params - 1 - i) as i32;
                        substituted = subst(d, &args[i], &substituted);
                    }
                    let arg_ty_inst = prev_args
                        .iter()
                        .rev()
                        .fold(substituted, |ty, a| beta(&ty, a));
                    let lvl = type_level_dt(dts, &tel_ctx, &arg_ty_inst, session)?;
                    max_level = LevelExpr::max(max_level, lvl);
                    let var_name = format!("_pcon_arg_{}", k);
                    let depth = k as i32;
                    prev_args.push(shift(depth + 1, 0, &Term::TVar(0)));
                    tel_ctx = extend_ctx(var_name, nbe_eval(&arg_ty_inst, session), &tel_ctx);
                }
            }

            // If args fully apply all params (or no params), return U_k.
            // If args are fewer than params, build a Pi type for remaining params.
            if args.len() >= dt.params.len() {
                Ok(Term::TUniv(max_level))
            } else {
                // Build a Pi type for the remaining parameters.
                // Each remaining param's type may reference earlier params via de Bruijn indices.
                // We substitute the provided args into the parameter telescope, then
                // wrap the result in Pi types for the remaining params.
                let provided = args.len();
                let remaining = &dt.params[provided..];
                let mut result = Term::TUniv(max_level);
                // Build from innermost to outermost (remaining params are later in the list)
                // The body references params via de Bruijn: param 0 is index 0, param 1 is index 1, etc.
                // After substituting provided args, remaining param 0 becomes index 0, etc.
                let mut offset = remaining.len() as i32;
                for (_i, (pname, pty)) in remaining.iter().enumerate().rev() {
                    // Shift the param type to account for the remaining binders
                    let shifted_pty = shift(offset, 0, pty);
                    result = Term::TPi(
                        pname.clone(),
                        Arc::new(shifted_pty),
                        Arc::new(result),
                        false,
                    );
                    offset -= 1;
                }
                // Substitute provided args for the outermost params
                let mut final_result = result;
                for (_i, arg) in args.iter().enumerate().rev() {
                    final_result = beta(&final_result, arg);
                }
                // The result still has free vars for remaining params (indices 0..remaining.len()-1),
                // so shift them down by `provided`
                let final_result = shift(-(provided as i32), 0, &final_result);
                Ok(final_result)
            }
        }

        // TCon(d, c, args) : TData(d, params)
        // Check each arg against the constructor's declared argument types,
        // substituting earlier args into later (dependent) argument types.
        // For parameterized types, arg_tys reference parameters via de Bruijn
        // indices (TVar(0) for first param). We infer parameter values from
        // argument types when they are free variables in the param range.
        Term::TCon(d, c, args) => {
            let dt =
                dts.iter()
                    .find(|dt| &dt.name == d)
                    .ok_or_else(|| TypeError::UnknownDatatype {
                        name: d.clone(),
                        pos: err_pos(ctx, t, session),
                    })?;
            // Check if this is an ordinary constructor.
            if let Some(sig) = dt.find_con(c) {
                let num_params = dt.params.len();
                let (param_terms, _checked_args) =
                    infer_and_check_params(dts, ctx, &sig.arg_tys, args, num_params, session)?;
                let params = build_params(&param_terms);
                Ok(Term::TData(d.clone(), params))
            // Path constructor used as a term (without explicit @).
            // Its type is Path (TData(d, params)) face0[args] face1[args].
            } else if let Some(sig) = dt.find_pcon(c) {
                let num_params = dt.params.len();
                let (param_terms, checked_args) =
                    infer_and_check_params(dts, ctx, &sig.arg_tys, args, num_params, session)?;
                let params = build_params(&param_terms);
                let face0 = checked_args
                    .iter()
                    .rev()
                    .fold(sig.face0.clone(), |ty, a| beta(&ty, a));
                let face1 = checked_args
                    .iter()
                    .rev()
                    .fold(sig.face1.clone(), |ty, a| beta(&ty, a));
                Ok(Term::TPath(
                    Arc::new(Term::TData(d.clone(), params.clone())),
                    Arc::new(nbe_eval(&face0, session)),
                    Arc::new(nbe_eval(&face1, session)),
                ))
            } else {
                Err(TypeError::UnknownConstructor {
                    datatype: d.clone(),
                    con: c.clone(),
                    pos: err_pos(ctx, t, session),
                })
            }
        }

        // TPCon(d, pc, args, r) : Path (TData(d, params)) face0[args] face1[args]
        Term::TPCon(d, pc, args, r) => {
            let dt =
                dts.iter()
                    .find(|dt| &dt.name == d)
                    .ok_or_else(|| TypeError::UnknownDatatype {
                        name: d.clone(),
                        pos: err_pos(ctx, t, session),
                    })?;
            let sig = dt
                .find_pcon(pc)
                .ok_or_else(|| TypeError::UnknownConstructor {
                    datatype: d.clone(),
                    con: pc.clone(),
                    pos: err_pos(ctx, t, session),
                })?;
            if args.len() != sig.arity() {
                return Err(TypeError::WrongNumberOfArgs {
                    con: pc.clone(),
                    expected: sig.arity(),
                    got: args.len(),
                    pos: err_pos(ctx, t, session),
                });
            }
            let num_params = dt.params.len();
            let (param_terms, _checked_args) =
                infer_and_check_params(dts, ctx, &sig.arg_tys, args, num_params, session)?;
            // Check interval argument.
            check_interval(ctx, r, session)?;
            let params = build_params(&param_terms);
            Ok(Term::TData(d.clone(), params))
        }

        // TSqCon(d, sc, args, r, s) :
        //   PathP (<i> PathP (<j> TData(d, params)) (face_i0 args j) (face_i1 args j))
        //               (face_j0 args i) (face_j1 args i)
        Term::TSqCon(d, sc, args, r, s) => {
            let dt =
                dts.iter()
                    .find(|dt| &dt.name == d)
                    .ok_or_else(|| TypeError::UnknownDatatype {
                        name: d.clone(),
                        pos: err_pos(ctx, t, session),
                    })?;
            let sig = dt
                .find_sqcon(sc)
                .ok_or_else(|| TypeError::UnknownConstructor {
                    datatype: d.clone(),
                    con: sc.clone(),
                    pos: err_pos(ctx, t, session),
                })?;
            if args.len() != sig.arity() {
                return Err(TypeError::WrongNumberOfArgs {
                    con: sc.clone(),
                    expected: sig.arity(),
                    got: args.len(),
                    pos: err_pos(ctx, t, session),
                });
            }
            let num_params = dt.params.len();
            let (param_terms, checked_args) =
                infer_and_check_params(dts, ctx, &sig.arg_tys, args, num_params, session)?;
            check_interval(ctx, r, session)?;
            check_interval(ctx, s, session)?;
            let params = build_params(&param_terms);
            let data_ty = Term::TData(d.clone(), params.clone());

            // Build the proper PathP type for the square constructor.
            // Face terms use de Bruijn indices: TVar(k) = arg_{num_args-1-k}.
            // We need to substitute checked args into face terms.
            let arity = sig.arity();
            let subst_face = |face: &Term| -> Term {
                let mut t = face.clone();
                for k in (0..arity).rev() {
                    t = subst(k as i32, &checked_args[arity - 1 - k], &t);
                }
                t
            };
            let face_i0_subst = subst_face(&sig.face_i0);
            let face_i1_subst = subst_face(&sig.face_i1);
            let face_j0_subst = subst_face(&sig.face_j0);
            let face_j1_subst = subst_face(&sig.face_j1);

            // Check if both interval args are concrete endpoints (i0 or i1).
            // If so, the square constructor is fully applied at a point
            // and its type is just TData(d, params).
            let mut is_endpoint = |t: &Term| -> bool {
                match nbe_eval(t, session) {
                    Term::TInterval(i) => {
                        let dnf = crate::cubical::interval::eval_interval(&i);
                        dnf == crate::cubical::interval::dnf_bot()
                            || dnf == crate::cubical::interval::dnf_top()
                    }
                    Term::TCube(d) => {
                        d == crate::cubical::interval::dnf_bot()
                            || d == crate::cubical::interval::dnf_top()
                    }
                    _ => false,
                }
            };
            if is_endpoint(r) && is_endpoint(s) {
                return Ok(data_ty);
            }
            // When only the first interval is an endpoint, return the inner path type.
            if is_endpoint(r) {
                // sq @ 0 or sq @ 1 has type Path (<j> Torus) (fi0 args) (fi1 args)
                return Ok(Term::TPath(
                    Arc::new(Term::PLam("j".to_string(), Arc::new(data_ty))),
                    Arc::new(face_i0_subst),
                    Arc::new(face_i1_subst),
                ));
            }

            // Outer type: PathP (<i> PathP (<j> A) (fi0 j) (fi1 j)) (fj0 i) (fj1 i)
            // In Owl AST: TPath(PLam("i", TPath(PLam("j", A), fi0, fi1)), fj0, fj1)
            let inner_path = Term::TPath(
                Arc::new(Term::PLam("j".to_string(), Arc::new(data_ty))),
                Arc::new(face_i0_subst),
                Arc::new(face_i1_subst),
            );
            let outer_type = Term::TPath(
                Arc::new(Term::PLam("i".to_string(), Arc::new(inner_path))),
                Arc::new(face_j0_subst),
                Arc::new(face_j1_subst),
            );
            Ok(outer_type)
        }

        // TCellCon(d, cc, args, ivars) :
        //   PathP (<i_1> PathP (<i_2> ... PathP (<i_n> TData(d, params)) face_0 face_1) ... face_{2n-4} face_{2n-3}) face_{2n-2} face_{2n-1}
        //
        // The cell constructor has dimension n = ivars.len().
        // faces are ordered: [face_0, face_1, face_2, face_3, ..., face_{2n-2}, face_{2n-1}]
        // where each consecutive pair (face_{2k}, face_{2k+1}) is the boundary
        // at interval variable i_{n-k} = 0 / i_{n-k} = 1.
        Term::TCellCon(d, cc, args, ivars) => {
            let dt =
                dts.iter()
                    .find(|dt| &dt.name == d)
                    .ok_or_else(|| TypeError::UnknownDatatype {
                        name: d.clone(),
                        pos: err_pos(ctx, t, session),
                    })?;
            let sig = dt
                .find_cellcon(cc)
                .ok_or_else(|| TypeError::UnknownConstructor {
                    datatype: d.clone(),
                    con: cc.clone(),
                    pos: err_pos(ctx, t, session),
                })?;
            if args.len() != sig.arity() {
                return Err(TypeError::WrongNumberOfArgs {
                    con: cc.clone(),
                    expected: sig.arity(),
                    got: args.len(),
                    pos: err_pos(ctx, t, session),
                });
            }
            let dim = ivars.len();
            if dim != sig.dimension() {
                return Err(TypeError::WrongNumberOfArgs {
                    con: cc.clone(),
                    expected: sig.dimension(),
                    got: dim,
                    pos: err_pos(ctx, t, session),
                });
            }
            let num_params = dt.params.len();
            let (param_terms, checked_args) =
                infer_and_check_params(dts, ctx, &sig.arg_tys, args, num_params, session)?;
            // Check all interval arguments.
            for iv in ivars {
                check_interval(ctx, iv, session)?;
            }
            let params = build_params(&param_terms);
            let data_ty = Term::TData(d.clone(), params.clone());

            if dim == 0 {
                return Ok(data_ty);
            }

            // Substitute constructor args into face terms.
            let arity = sig.arity();
            let subst_face = |face: &Term| -> Term {
                let mut t = face.clone();
                for k in (0..arity).rev() {
                    t = subst(k as i32, &checked_args[arity - 1 - k], &t);
                }
                t
            };

            let substituted_faces: Vec<Term> = sig.faces.iter().map(|f| subst_face(f)).collect();

            // Check if all interval args are concrete endpoints.
            let mut is_endpoint = |t: &Term| -> bool {
                match nbe_eval(t, session) {
                    Term::TInterval(i) => {
                        let dnf = crate::cubical::interval::eval_interval(&i);
                        dnf == crate::cubical::interval::dnf_bot()
                            || dnf == crate::cubical::interval::dnf_top()
                    }
                    Term::TCube(d) => {
                        d == crate::cubical::interval::dnf_bot()
                            || d == crate::cubical::interval::dnf_top()
                    }
                    _ => false,
                }
            };
            if ivars.iter().all(|iv| is_endpoint(iv)) {
                return Ok(data_ty);
            }

            // Build nested PathP type from innermost to outermost.
            // faces = [f_0, f_1, f_2, f_3, ..., f_{2n-2}, f_{2n-1}]
            // Type: PathP (<i_1> PathP (<i_2> ... PathP (<i_n> A) f_0 f_1) ... f_{2n-4} f_{2n-3}) f_{2n-2} f_{2n-1}
            //
            // Interval variable names: _i1, _i2, ..., _in (innermost to outermost)
            let ivar_names: Vec<String> = (0..dim).map(|k| format!("_i{}", k + 1)).collect();

            // Start with the innermost PathP using the last interval variable.
            let mut result_type = Term::TPath(
                Arc::new(Term::PLam(ivar_names[0].clone(), Arc::new(data_ty))),
                Arc::new(substituted_faces[0].clone()),
                Arc::new(substituted_faces[1].clone()),
            );

            // Wrap with PathPs for each subsequent interval variable (from inner to outer).
            for k in 1..dim {
                let body = result_type;
                result_type = Term::TPath(
                    Arc::new(Term::PLam(ivar_names[k].clone(), Arc::new(body))),
                    Arc::new(substituted_faces[2 * k].clone()),
                    Arc::new(substituted_faces[2 * k + 1].clone()),
                );
            }

            // If some outer interval args are at endpoints, peel those PathPs.
            // Peel off outermost PathPs where the interval arg is an endpoint.
            let mut current = result_type;
            for k in (0..dim).rev() {
                if is_endpoint(&ivars[k]) {
                    if let Term::TPath(_, inner, _) = current {
                        current = inner.as_ref().clone();
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }

            Ok(current)
        }

        // TElim(motive, cases, scrut)
        //
        // motive : TData(d, params) → U_n
        // scrut  : TData(d, params)
        // For each constructor  c  with args A₀…Aₖ:
        //   case body : motive (TCon(d, c, args))
        //   (under binders for the constructor args in context)
        // For each path constructor  pc  with args A₀…Aₖ  and boundary  f0/f1:
        //   case body : Path (motive ∘ pcon) (case_for_f0) (case_for_f1)
        //   body is PLam-shaped (see ElimCase docs in syntax.rs)
        // Returns: motive scrut
        Term::TElim(motive, cases, scrut) => {
            // Infer scrutinee — must be TData(d, params).
            let scrut_ty = infer_dt(dts, ctx, scrut, session)?;
            let (d, scrut_params) = match nbe_eval(&scrut_ty, session) {
                Term::TData(d, params) => (d, params),
                other => {
                    return Err(TypeError::ExpectedData {
                        ty: other,
                        names: err_names(ctx),
                        pos: err_pos(ctx, scrut, session),
                    });
                }
            };
            let dt =
                dts.iter()
                    .find(|dt| dt.name == d)
                    .ok_or_else(|| TypeError::UnknownDatatype {
                        name: d.clone(),
                        pos: err_pos(ctx, scrut, session),
                    })?;

            // Desugar record patterns: convert `{ field = binder }` to constructor pattern.
            let cases_owned: Vec<ElimCase> = {
                let mut buf = Vec::with_capacity(cases.len());
                for case in cases.iter() {
                    if let Some(ref bindings) = case.record_bindings {
                        if let Some(ref field_names) = dt.field_names {
                            let con_name = &dt.cons[0].name;
                            let binders: Vec<Name> = field_names
                                .iter()
                                .map(|f| {
                                    bindings
                                        .iter()
                                        .find(|(bf, _)| bf == f)
                                        .map(|(_, b)| b.clone())
                                        .unwrap_or_else(|| "_".to_string())
                                })
                                .collect();
                            buf.push(ElimCase {
                                con: con_name.clone(),
                                binders,
                                body: case.body.clone(),
                                as_name: case.as_name.clone(),
                                record_bindings: None,
                                refinements: None,
                            });
                        } else {
                            buf.push(case.clone());
                        }
                    } else {
                        buf.push(case.clone());
                    }
                }
                buf
            };
            let cases: &[ElimCase] = &cases_owned;

            // Verify motive has type Π(_:TData(d, params)).C where C is a well-formed type.
            let motive_dom = Term::TData(d.clone(), scrut_params.clone());
            match motive.as_ref() {
                Term::TAbs(x, body) => {
                    let motive_ctx = extend_ctx(x.clone(), nbe_eval(&motive_dom, session), ctx);
                    type_level_dt(dts, &motive_ctx, body, session)?;
                }
                _ => {
                    let motive_inferred = infer_dt(dts, ctx, motive, session)?;
                    match nbe_eval(&motive_inferred, session) {
                        Term::TPi(x, dom, cod, _) => {
                            require_equal(
                                ctx,
                                &nbe_eval(&dom, session),
                                &nbe_eval(&motive_dom, session),
                                session,
                            )?;
                            let cod_ctx = extend_ctx(x, nbe_eval(&dom, session), ctx);
                            type_level_dt(dts, &cod_ctx, &cod, session)?;
                        }
                        other => {
                            return Err(TypeError::ExpectedPi {
                                ty: other,
                                names: err_names(ctx),
                                pos: err_pos(ctx, motive, session),
                            });
                        }
                    }
                }
            }

            // Helper: substitute determined params into a constructor's arg_tys.
            // For parameterized types, arg_tys reference params via de Bruijn
            // indices.  In the datatype scope [B, A] (two params, B=TVar(0), A=TVar(1))
            // the first param A is at TVar(num_params-1) and the last param B at TVar(0).
            // We substitute the scrutinee's parameter values to get concrete arg types.
            fn subst_params(arg_tys: &[Term], params: &[Term]) -> Vec<Term> {
                let num_params = params.len();
                arg_tys
                    .iter()
                    .map(|ty| {
                        let mut t = ty.clone();
                        for (k, p) in params.iter().enumerate() {
                            let target = (num_params - 1 - k) as i32;
                            t = subst(target, p, &t);
                        }
                        t
                    })
                    .collect()
            }

            // Substitute params into pcon face terms.
            //
            // Face terms are parsed in a scope where constructor args occupy
            // indices 0..num_args-1 and datatype params occupy indices
            // num_args..num_args+num_params-1.  `beta` always targets
            // TVar(0) which would corrupt the constructor-arg references,
            // so we use `subst` at the correct param indices instead.
            fn subst_params_face(
                face: &Term,
                params: &[Term],
                num_args: usize,
                _session: &mut Session,
            ) -> Term {
                let mut t = face.clone();
                // Substitute from highest index to lowest so earlier
                // substitutions don't shift the indices we still need.
                for (k, p) in params.iter().enumerate().rev() {
                    t = subst((num_args + k) as i32, p, &t);
                }
                t
            }

            // Check all ordinary constructor cases.
            for con_sig in &dt.cons {
                let case = cases
                    .iter()
                    .find(|c| c.con == con_sig.name)
                    .ok_or_else(|| TypeError::MissingCase {
                        con: con_sig.name.clone(),
                        pos: err_pos(ctx, scrut, session),
                    })?;

                // Substitute params into arg_tys for this constructor.
                let subst_arg_tys = subst_params(&con_sig.arg_tys, &scrut_params);

                if case.binders.len() != subst_arg_tys.len() {
                    return Err(TypeError::BadElimCase {
                        con: con_sig.name.clone(),
                        msg: format!(
                            "expected {} binders, got {}",
                            subst_arg_tys.len(),
                            case.binders.len()
                        ),
                        pos: err_pos(ctx, scrut, session),
                    });
                }

                // Build extended context: push binders outermost-first,
                // last binder ends up at index 0.
                let mut case_ctx = ctx.clone();
                let mut con_args_in_ctx: Vec<Term> = Vec::new();
                for (k, binder_name) in case.binders.iter().enumerate() {
                    // Shift the arg type by k to account for previously pushed binders.
                    let mut arg_ty = shift(k as i32, 0, &subst_arg_tys[k]);
                    // Substitute previous constructor args into dependent arg types.
                    for a in con_args_in_ctx.iter().rev() {
                        arg_ty = subst(0, a, &arg_ty);
                    }
                    let arg_ty_ev = nbe_eval(&arg_ty, session);
                    let depth = k as i32;
                    con_args_in_ctx.push(shift(depth + 1, 0, &Term::TVar(0)));
                    case_ctx = extend_ctx(binder_name.clone(), arg_ty_ev, &case_ctx);
                }

                // As-pattern: bind the full constructor value to the as_name.
                let extra_shift = if case.as_name.is_some() { 1i32 } else { 0i32 };
                if let Some(ref as_n) = case.as_name {
                    let as_ty = nbe_eval(&Term::TData(d.clone(), scrut_params.clone()), session);
                    case_ctx = extend_ctx(as_n.clone(), as_ty, &case_ctx);
                }

                // Expected type: motive applied to TCon(d, c, params, all binders as vars).
                let arity = subst_arg_tys.len();
                let arity_i32 = arity as i32;
                let con_term_args: Vec<Term> = (0..arity)
                    .map(|k| Term::TVar((arity - 1 - k) as i32 + extra_shift))
                    .collect();
                let scrut_as_con = Term::TCon(d.clone(), con_sig.name.clone(), con_term_args);
                let shifted_motive = shift(arity_i32 + extra_shift, 0, motive);
                let expected_ty = nbe_eval(
                    &Term::TApp(Arc::new(shifted_motive), Arc::new(scrut_as_con)),
                    session,
                );
                check_dt(dts, &case_ctx, &case.body, &expected_ty, session)?;
            }

            // Check all path constructor cases.
            for pcon_sig in &dt.pcons {
                let case = cases
                    .iter()
                    .find(|c| c.con == pcon_sig.name)
                    .ok_or_else(|| TypeError::MissingCase {
                        con: pcon_sig.name.clone(),
                        pos: err_pos(ctx, scrut, session),
                    })?;

                let subst_arg_tys = subst_params(&pcon_sig.arg_tys, &scrut_params);

                // binders = arity ordinary args + 1 interval var (last).
                let expected_binders = subst_arg_tys.len() + 1;
                if case.binders.len() != expected_binders {
                    return Err(TypeError::BadElimCase {
                        con: pcon_sig.name.clone(),
                        msg: format!(
                            "expected {} binders ({} ordinary + 1 interval), got {}",
                            expected_binders,
                            subst_arg_tys.len(),
                            case.binders.len()
                        ),
                        pos: err_pos(ctx, scrut, session),
                    });
                }

                let ord_binders = &case.binders[..subst_arg_tys.len()];
                let i_name = &case.binders[subst_arg_tys.len()];

                // Build context for the ordinary args.
                let mut case_ctx = ctx.clone();
                let mut pcon_args_in_ctx: Vec<Term> = Vec::new();
                for (k, binder_name) in ord_binders.iter().enumerate() {
                    let arg_ty = pcon_args_in_ctx
                        .iter()
                        .rev()
                        .fold(subst_arg_tys[k].clone(), |ty, a| beta(&ty, a));
                    let depth = k as i32;
                    pcon_args_in_ctx.push(shift(depth + 1, 0, &Term::TVar(0)));
                    case_ctx =
                        extend_ctx(binder_name.clone(), nbe_eval(&arg_ty, session), &case_ctx);
                }

                let arity = subst_arg_tys.len();
                let _ord_case_ctx = case_ctx.clone();
                case_ctx = extend_ctx(i_name.clone(), interval_ty(), &case_ctx);

                let ord_var_no_i: Vec<Term> = (0..arity)
                    .map(|k| Term::TVar((arity - 1 - k) as i32))
                    .collect();
                let i_var = Term::TVar(0);
                let ord_var: Vec<Term> =
                    (0..arity).map(|k| Term::TVar((arity - k) as i32)).collect();

                let pcon_term = Term::TPCon(
                    d.clone(),
                    pcon_sig.name.clone(),
                    ord_var.clone(),
                    Arc::new(i_var.clone()),
                );
                let motive_shifted = shift((arity + 1) as i32, 0, motive);
                let motive_at_pcon = nbe_eval(
                    &Term::TApp(Arc::new(motive_shifted.clone()), Arc::new(pcon_term)),
                    session,
                );
                let face0_subst = subst_params_face(&pcon_sig.face0, &scrut_params, arity, session);
                let face1_subst = subst_params_face(&pcon_sig.face1, &scrut_params, arity, session);
                let face0_case = eval_elim_face(
                    motive,
                    cases,
                    &face0_subst,
                    &ord_var_no_i,
                    arity as i32,
                    session,
                );
                let face1_case = eval_elim_face(
                    motive,
                    cases,
                    &face1_subst,
                    &ord_var_no_i,
                    arity as i32,
                    session,
                );

                let expected_body_ty = Term::TPath(
                    Arc::new(Term::PLam(i_name.clone(), Arc::new(motive_at_pcon))),
                    Arc::new(shift(1, 0, &face0_case)),
                    Arc::new(shift(1, 0, &face1_case)),
                );
                if case.refinements.is_some() {
                    // Refined nested-pattern HIT case. The parser compiled the
                    // arm bodies into a nested `TElim` whose scrutinee is the
                    // case's ordinary-argument binder: the case interval binder
                    // sits at index 0 of `case_ctx`, so the elim's de Bruijn
                    // indices line up with the runtime evaluation environment.
                    // The parser cannot build the eliminator's motive itself —
                    // its codomain is the *path type* at the refined
                    // constructor, whose face endpoints come from the case
                    // bodies of the face constructors — so rebuild the motive
                    // from the expected body type computed above (which the
                    // flat path already derives from `eval_elim_face`). The
                    // typechecker then checks the rebuilt elim with the
                    // standard `PLam` rule and SKIP_PLAM_ENDPT off, so every
                    // leaf verifies that its own path endpoints agree with the
                    // faces at that leaf — exactly the boundary coherence the
                    // flat path checks by hand below.
                    let (elim_cases, slot) = match case.body.as_ref() {
                        Term::TElim(_, elim_cases, scrut) => match scrut.as_ref() {
                            Term::TVar(slot) => (elim_cases.clone(), *slot),
                            _ => {
                                return Err(TypeError::Other(format!(
                                    "refined HIT case '{}': nested eliminator has a non-variable scrutinee",
                                    case.con
                                )));
                            }
                        },
                        _ => {
                            return Err(TypeError::Other(format!(
                                "refined HIT case '{}': expected a nested eliminator body, \
                                 got a non-eliminator term",
                                case.con
                            )));
                        }
                    };
                    let correct_motive = Term::TAbs(
                        "z".to_string(),
                        Arc::new(subst(
                            slot + 1,
                            &Term::TVar(0),
                            &shift(1, 0, &expected_body_ty),
                        )),
                    );
                    let rebuilt = Term::TElim(
                        Arc::new(correct_motive),
                        elim_cases,
                        Arc::new(Term::TVar(slot)),
                    );
                    check_dt(dts, &case_ctx, &rebuilt, &expected_body_ty, session)?;
                } else {
                    session.set_skip_plam_endpt(true);
                    check_dt(dts, &case_ctx, &case.body, &expected_body_ty, session)?;
                    session.set_skip_plam_endpt(false);

                    let body_at0 = match case.body.as_ref() {
                        Term::PLam(_, inner) => {
                            let reduced = reduce_pcon_endpoints_dt(
                                dts,
                                &apply_literal(&Literal::NegVar(0), inner, session),
                                session,
                            );
                            nbe_eval(&shift(-1, 0, &reduced), session)
                        }
                        _ => {
                            let papp = Term::PApp(
                                Arc::new(case.body.as_ref().clone()),
                                Arc::new(Term::TInterval(I::I0)),
                            );
                            let reduced = reduce_pcon_endpoints_dt(dts, &papp, session);
                            nbe_eval(&reduced, session)
                        }
                    };
                    let body_at1 = match case.body.as_ref() {
                        Term::PLam(_, inner) => {
                            let reduced = reduce_pcon_endpoints_dt(
                                dts,
                                &apply_literal(&Literal::Pos(0), inner, session),
                                session,
                            );
                            nbe_eval(&shift(-1, 0, &reduced), session)
                        }
                        _ => {
                            let papp = Term::PApp(
                                Arc::new(case.body.as_ref().clone()),
                                Arc::new(Term::TInterval(I::I1)),
                            );
                            let reduced = reduce_pcon_endpoints_dt(dts, &papp, session);
                            nbe_eval(&reduced, session)
                        }
                    };
                    require_equal_endpt(&case_ctx, &shift(1, 0, &face0_case), &body_at0, session)?;
                    require_equal_endpt(&case_ctx, &shift(1, 0, &face1_case), &body_at1, session)?;
                }
            }

            // Check all square constructor cases.
            for sqcon_sig in &dt.sqcons {
                let case = cases
                    .iter()
                    .find(|c| c.con == sqcon_sig.name)
                    .ok_or_else(|| TypeError::MissingCase {
                        con: sqcon_sig.name.clone(),
                        pos: err_pos(ctx, scrut, session),
                    })?;

                let subst_arg_tys = subst_params(&sqcon_sig.arg_tys, &scrut_params);

                // binders = arity ordinary args + 2 interval vars (r, s).
                let expected_binders = subst_arg_tys.len() + 2;
                if case.binders.len() != expected_binders {
                    return Err(TypeError::BadElimCase {
                        con: sqcon_sig.name.clone(),
                        msg: format!(
                            "expected {} binders ({} ordinary + 2 interval), got {}",
                            expected_binders,
                            subst_arg_tys.len(),
                            case.binders.len()
                        ),
                        pos: err_pos(ctx, scrut, session),
                    });
                }

                let ord_binders_sq = &case.binders[..subst_arg_tys.len()];
                let r_name = &case.binders[subst_arg_tys.len()];
                let s_name = &case.binders[subst_arg_tys.len() + 1];

                let mut case_ctx_sq = ctx.clone();
                let mut sqcon_args_in_ctx: Vec<Term> = Vec::new();
                for (k, binder_name) in ord_binders_sq.iter().enumerate() {
                    let arg_ty = sqcon_args_in_ctx
                        .iter()
                        .rev()
                        .fold(subst_arg_tys[k].clone(), |ty, a| beta(&ty, a));
                    let depth = k as i32;
                    sqcon_args_in_ctx.push(shift(depth + 1, 0, &Term::TVar(0)));
                    case_ctx_sq = extend_ctx(
                        binder_name.clone(),
                        nbe_eval(&arg_ty, session),
                        &case_ctx_sq,
                    );
                }

                let arity_sq = subst_arg_tys.len();
                case_ctx_sq = extend_ctx(r_name.clone(), interval_ty(), &case_ctx_sq);
                case_ctx_sq = extend_ctx(s_name.clone(), interval_ty(), &case_ctx_sq);

                let ord_var_no_rs: Vec<Term> = (0..arity_sq)
                    .map(|k| Term::TVar((arity_sq - 1 - k) as i32))
                    .collect();
                let r_var = Term::TVar(1);
                let s_var = Term::TVar(0);
                let ord_var_sq: Vec<Term> = (0..arity_sq)
                    .map(|k| Term::TVar((arity_sq + 2 - k) as i32))
                    .collect();

                let sqcon_term = Term::TSqCon(
                    d.clone(),
                    sqcon_sig.name.clone(),
                    ord_var_sq.clone(),
                    Arc::new(r_var.clone()),
                    Arc::new(s_var.clone()),
                );
                let motive_shifted_sq = shift((arity_sq + 2) as i32, 0, motive);
                let motive_at_sqcon = nbe_eval(
                    &Term::TApp(Arc::new(motive_shifted_sq.clone()), Arc::new(sqcon_term)),
                    session,
                );

                let face_i0_subst =
                    subst_params_face(&sqcon_sig.face_i0, &scrut_params, arity_sq, session);
                let face_i1_subst =
                    subst_params_face(&sqcon_sig.face_i1, &scrut_params, arity_sq, session);
                let face_j0_subst =
                    subst_params_face(&sqcon_sig.face_j0, &scrut_params, arity_sq, session);
                let face_j1_subst =
                    subst_params_face(&sqcon_sig.face_j1, &scrut_params, arity_sq, session);

                let face_i0_case = eval_elim_face(
                    motive,
                    cases,
                    &face_i0_subst,
                    &ord_var_no_rs,
                    (arity_sq + 2) as i32,
                    session,
                );
                let face_i1_case = eval_elim_face(
                    motive,
                    cases,
                    &face_i1_subst,
                    &ord_var_no_rs,
                    (arity_sq + 2) as i32,
                    session,
                );
                let face_j0_case = eval_elim_face(
                    motive,
                    cases,
                    &face_j0_subst,
                    &ord_var_no_rs,
                    (arity_sq + 2) as i32,
                    session,
                );
                let face_j1_case = eval_elim_face(
                    motive,
                    cases,
                    &face_j1_subst,
                    &ord_var_no_rs,
                    (arity_sq + 2) as i32,
                    session,
                );

                let inner_path = Term::TPath(
                    Arc::new(Term::PLam(s_name.clone(), Arc::new(motive_at_sqcon))),
                    Arc::new(shift(1, 0, &face_i0_case)),
                    Arc::new(shift(1, 0, &face_i1_case)),
                );
                let expected_body_ty_sq = Term::TPath(
                    Arc::new(Term::PLam(r_name.clone(), Arc::new(inner_path))),
                    Arc::new(shift(2, 0, &face_j0_case)),
                    Arc::new(shift(2, 0, &face_j1_case)),
                );
                session.set_skip_plam_endpt(true);
                check_dt(dts, &case_ctx_sq, &case.body, &expected_body_ty_sq, session)?;
                session.set_skip_plam_endpt(false);

                // Boundary coherence for sqcon cases:
                // Strip the two PLam binders from the case body, then use
                // apply_literal to substitute concrete endpoints for each
                // interval variable.  Inside inner, IVar(0)=s (innermost)
                // and IVar(1)=r (outermost).
                if let Term::PLam(_, inner_box) = case.body.as_ref() {
                    if let Term::PLam(_, inner) = inner_box.as_ref() {
                        // body @ r0 @ s0
                        let body_r0_s0 = {
                            let t = apply_literal(&Literal::NegVar(1), inner, session);
                            let t = apply_literal(&Literal::NegVar(0), &t, session);
                            nbe_eval(
                                &shift(-2, 0, &reduce_pcon_endpoints_dt(dts, &t, session)),
                                session,
                            )
                        };
                        // body @ r0 @ s1
                        let body_r0_s1 = {
                            let t = apply_literal(&Literal::NegVar(1), inner, session);
                            let t = apply_literal(&Literal::Pos(0), &t, session);
                            nbe_eval(
                                &shift(-2, 0, &reduce_pcon_endpoints_dt(dts, &t, session)),
                                session,
                            )
                        };
                        // body @ r1 @ s0
                        let body_r1_s0 = {
                            let t = apply_literal(&Literal::Pos(1), inner, session);
                            let t = apply_literal(&Literal::NegVar(0), &t, session);
                            nbe_eval(
                                &shift(-2, 0, &reduce_pcon_endpoints_dt(dts, &t, session)),
                                session,
                            )
                        };
                        // body @ r1 @ s1
                        let body_r1_s1 = {
                            let t = apply_literal(&Literal::Pos(1), inner, session);
                            let t = apply_literal(&Literal::Pos(0), &t, session);
                            nbe_eval(
                                &shift(-2, 0, &reduce_pcon_endpoints_dt(dts, &t, session)),
                                session,
                            )
                        };
                        require_equal_endpt(
                            &case_ctx_sq,
                            &shift(2, 0, &face_i0_case),
                            &body_r0_s0,
                            session,
                        )?;
                        require_equal_endpt(
                            &case_ctx_sq,
                            &shift(2, 0, &face_i1_case),
                            &body_r0_s1,
                            session,
                        )?;
                        require_equal_endpt(
                            &case_ctx_sq,
                            &shift(2, 0, &face_i0_case),
                            &body_r1_s0,
                            session,
                        )?;
                        require_equal_endpt(
                            &case_ctx_sq,
                            &shift(2, 0, &face_i1_case),
                            &body_r1_s1,
                            session,
                        )?;
                    }
                }
            }

            // Check all n-dimensional cell constructor cases.
            for cellcon_sig in &dt.cellcons {
                let case = cases
                    .iter()
                    .find(|c| c.con == cellcon_sig.name)
                    .ok_or_else(|| TypeError::MissingCase {
                        con: cellcon_sig.name.clone(),
                        pos: err_pos(ctx, scrut, session),
                    })?;

                let subst_arg_tys = subst_params(&cellcon_sig.arg_tys, &scrut_params);
                let dim = cellcon_sig.dimension();

                // binders = arity ordinary args + dim interval vars.
                let expected_binders = subst_arg_tys.len() + dim;
                if case.binders.len() != expected_binders {
                    return Err(TypeError::BadElimCase {
                        con: cellcon_sig.name.clone(),
                        msg: format!(
                            "expected {} binders ({} ordinary + {} interval), got {}",
                            expected_binders,
                            subst_arg_tys.len(),
                            dim,
                            case.binders.len()
                        ),
                        pos: err_pos(ctx, scrut, session),
                    });
                }

                let ord_binders_cell = &case.binders[..subst_arg_tys.len()];
                let ivar_names: Vec<&String> = case.binders[subst_arg_tys.len()..].iter().collect();

                let mut case_ctx_cell = ctx.clone();
                let mut cellcon_args_in_ctx: Vec<Term> = Vec::new();
                for (k, binder_name) in ord_binders_cell.iter().enumerate() {
                    let arg_ty = cellcon_args_in_ctx
                        .iter()
                        .rev()
                        .fold(subst_arg_tys[k].clone(), |ty, a| beta(&ty, a));
                    let depth = k as i32;
                    cellcon_args_in_ctx.push(shift(depth + 1, 0, &Term::TVar(0)));
                    case_ctx_cell = extend_ctx(
                        binder_name.clone(),
                        nbe_eval(&arg_ty, session),
                        &case_ctx_cell,
                    );
                }

                let arity_cell = subst_arg_tys.len();
                // Extend context with interval variables (innermost first).
                for iv_name in ivar_names.iter().rev() {
                    case_ctx_cell = extend_ctx(iv_name.to_string(), interval_ty(), &case_ctx_cell);
                }

                // Build variable references for the constructor args and interval vars.
                let ord_var_no_ivars: Vec<Term> = (0..arity_cell)
                    .map(|k| Term::TVar((arity_cell - 1 - k) as i32))
                    .collect();
                // Interval variables: TVar(0) is the innermost, TVar(dim-1) is the outermost.
                let ivar_vars: Vec<Term> = (0..dim).map(|k| Term::TVar(k as i32)).collect();
                let ord_var_cell: Vec<Term> = (0..arity_cell)
                    .map(|k| Term::TVar((arity_cell + dim - k) as i32))
                    .collect();

                let cellcon_term = Term::TCellCon(
                    d.clone(),
                    cellcon_sig.name.clone(),
                    ord_var_cell.clone(),
                    ivar_vars.clone(),
                );
                let motive_shifted_cell = shift((arity_cell + dim) as i32, 0, motive);
                let motive_at_cellcon = nbe_eval(
                    &Term::TApp(
                        Arc::new(motive_shifted_cell.clone()),
                        Arc::new(cellcon_term),
                    ),
                    session,
                );

                // Build the expected body type as a nested PathP.
                // The body should be a PLam-shaped term over the dim interval variables,
                // with type PathP(<i_1> ... PathP(<i_dim> motive(cellcon_args @ ivars)) ... ) face_0 face_1.
                //
                // For each face pair, we compute the case body applied to the substituted face,
                // then build nested PathPs from innermost to outermost.

                // Substitute scrutinee params into each face.
                let substituted_faces: Vec<Term> = cellcon_sig
                    .faces
                    .iter()
                    .map(|f| subst_params_face(f, &scrut_params, arity_cell, session))
                    .collect();

                // For each face, compute the expected case body value at that face.
                let face_cases: Vec<Term> = substituted_faces
                    .iter()
                    .map(|f| {
                        eval_elim_face(
                            motive,
                            cases,
                            f,
                            &ord_var_no_ivars,
                            (arity_cell + dim) as i32,
                            session,
                        )
                    })
                    .collect();

                // Build nested PathP from innermost to outermost.
                // faces = [f_0, f_1, f_2, f_3, ..., f_{2n-2}, f_{2n-1}]
                // Type: PathP (<i_1> PathP (<i_2> ... PathP (<i_dim> motive_val) face_0 face_1) ... face_{2n-4} face_{2n-3}) face_{2n-2} face_{2n-1}
                // where i_1 is innermost and i_dim is outermost.

                // Start with the innermost PathP.
                let mut expected_body_ty = Term::TPath(
                    Arc::new(Term::PLam(
                        ivar_names[0].to_string(),
                        Arc::new(motive_at_cellcon),
                    )),
                    Arc::new(shift(1, 0, &face_cases[0])),
                    Arc::new(shift(1, 0, &face_cases[1])),
                );

                // Wrap with PathPs for each subsequent interval variable.
                for k in 1..dim {
                    let body = expected_body_ty;
                    expected_body_ty = Term::TPath(
                        Arc::new(Term::PLam(ivar_names[k].to_string(), Arc::new(body))),
                        Arc::new(shift((k + 1) as i32, 0, &face_cases[2 * k])),
                        Arc::new(shift((k + 1) as i32, 0, &face_cases[2 * k + 1])),
                    );
                }

                session.set_skip_plam_endpt(true);
                check_dt(dts, &case_ctx_cell, &case.body, &expected_body_ty, session)?;
                session.set_skip_plam_endpt(false);

                // Boundary coherence for cellcon cases:
                // For level k (0 = outermost), strip (k+1) outermost PLams
                // from the case body, substitute the exposed interval vars,
                // keep the remaining (dim-k-1) inner PLams, then compare
                // with face_cases[2*(dim-1-k)] shifted by (k+1).
                //
                // IMPORTANT: apply_literal uses a de Bruijn-level counter n
                // that increments under PLams. inner_at_k has `keep_count`
                // remaining PLams, so apply_literal(NegVar(v), inner_at_k)
                // would target index v+keep_count. We adjust by subtracting
                // keep_count from each index so the target is correct.
                for k in 0..dim {
                    let face_idx = 2 * (dim - 1 - k);
                    let strip_count = k + 1;
                    let keep_count = dim - strip_count;

                    if let Ok(inner_at_k) = strip_n_plams(&case.body, strip_count) {
                        // At this level, after stripping strip_count PLams:
                        // IVar(0..keep_count-1) are still bound by remaining PLams
                        // IVar(keep_count..dim-1) are free (the stripped vars)
                        // The free var for the current level is IVar(keep_count)
                        // (= dim - strip_count), and outer ones are IVar(keep_count+1..dim-1).
                        //
                        // adjust(v) = v - keep_count compensates for the keep_count
                        // remaining PLams that apply_literal will enter (incrementing n).

                        // at_i0: outer k free vars = I0, current var = I0
                        let mut t_i0 = inner_at_k.clone();
                        // Substitute outer free vars (keep_count+1 .. dim-1) → I0
                        for v in (keep_count + 1)..dim {
                            t_i0 = apply_literal(
                                &Literal::NegVar((v - keep_count) as i32),
                                &t_i0,
                                session,
                            );
                        }
                        // Current var (keep_count) → I0
                        t_i0 = apply_literal(&Literal::NegVar(0), &t_i0, session);
                        let at_i0 = nbe_eval(
                            &shift(
                                -(strip_count as i32),
                                0,
                                &reduce_pcon_endpoints_dt(dts, &t_i0, session),
                            ),
                            session,
                        );

                        // at_i1: outer k free vars = I0, current var = I1
                        let mut t_i1 = inner_at_k.clone();
                        for v in (keep_count + 1)..dim {
                            t_i1 = apply_literal(
                                &Literal::NegVar((v - keep_count) as i32),
                                &t_i1,
                                session,
                            );
                        }
                        t_i1 = apply_literal(&Literal::Pos(0), &t_i1, session);
                        let at_i1 = nbe_eval(
                            &shift(
                                -(strip_count as i32),
                                0,
                                &reduce_pcon_endpoints_dt(dts, &t_i1, session),
                            ),
                            session,
                        );

                        let expected_i0 = shift(strip_count as i32, 0, &face_cases[face_idx]);
                        let expected_i1 = shift(strip_count as i32, 0, &face_cases[face_idx + 1]);
                        require_equal_endpt(&case_ctx_cell, &expected_i0, &at_i0, session)?;
                        require_equal_endpt(&case_ctx_cell, &expected_i1, &at_i1, session)?;
                    }
                }
            }

            // Structural recursion guard check.
            if !crate::cubical::typechecker::termination::should_skip_guard(session) {
                // Index of the definition being checked in the current
                // context (without the eliminator's own case binders). Used
                // to detect recursive calls through the definition's name.
                let def_idx = crate::cubical::typechecker::termination::current_def(session)
                    .and_then(|dn| ctx.iter().position(|(n, _)| n == &dn).map(|p| p as i32));
                match crate::cubical::typechecker::termination::check_guard(&d, cases, def_idx) {
                    crate::cubical::typechecker::termination::GuardStatus::Ok => {}
                    crate::cubical::typechecker::termination::GuardStatus::Violation {
                        case,
                        msg,
                    } => {
                        return Err(TypeError::TerminationViolation {
                            datatype: d.clone(),
                            case,
                            msg,
                            pos: err_pos(ctx, scrut, session),
                        });
                    }
                }
            }

            // Return type: motive applied to the scrutinee.
            Ok(nbe_eval(
                &Term::TApp(motive.clone(), scrut.clone()),
                session,
            ))
        }

        // -- Coinduction ---------------------------------------------------------
        // Delay A : U_n when A : U_n
        Term::TDelay(a) => {
            let a_ty = infer_dt(dts, ctx, a, session)?;
            Ok(a_ty)
        }
        // Next : A -> Delay A
        Term::TNext(a) => {
            let a_ty = infer_dt(dts, ctx, a, session)?;
            Ok(Term::TDelay(Arc::new(a_ty)))
        }
        // Force : Delay A -> A
        Term::TForce(a) => {
            let delay_ty = infer_dt(dts, ctx, a, session)?;
            // delay_ty should be Delay B for some B
            match nbe_eval(&delay_ty, session) {
                Term::TDelay(b) => Ok(b.as_ref().clone()),
                other => Err(TypeError::Other(format!(
                    "Force expects a Delay type, but got: {}",
                    other
                ))),
            }
        }
    }
}

// HIT endpoint reduction (datatype-aware)
// ---------------------------------------------------------------------------
/// Reduce `TPCon(d, pc, args, r)` at endpoints `r=I0`/`r=I1` to the
/// corresponding declared face value, recursively.  This is needed because
/// `nbe_eval` doesn't carry datatype definitions, so it cannot reduce path
/// constructors at their boundaries without this extra pass.
fn reduce_pcon_endpoints_dt(dts: &[Datatype], t: &Term, session: &mut Session) -> Term {
    let t = nbe_eval(t, session);
    match &t {
        Term::TPCon(d, pc, args, r) => {
            let r_nf = nbe_eval(r, session);
            let (is_i0, is_i1) = match &r_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    (
                        dnf == crate::cubical::interval::dnf_bot(),
                        dnf == crate::cubical::interval::dnf_top(),
                    )
                }
                Term::TCube(d) => (
                    d == &crate::cubical::interval::dnf_bot(),
                    d == &crate::cubical::interval::dnf_top(),
                ),
                _ => (false, false),
            };
            if is_i0 || is_i1 {
                // Look up the face value from the PConSig.
                if let Some(dt) = dts.iter().find(|dt| &dt.name == d)
                    && let Some(sig) = dt.find_pcon(pc)
                {
                    // face0/face1 are in a scope of sig.arity() ordinary args.
                    // Substitute the checked args into the face term.
                    let reduced_args: Vec<Term> = args
                        .iter()
                        .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                        .collect();
                    let face = if is_i0 { &sig.face0 } else { &sig.face1 };
                    // Face parsing uses insert(0,...), so TVar(k) = arg_{num_args-1-k}.
                    // Substitute from highest face-var index to lowest.
                    let arity = reduced_args.len();
                    let mut face_inst = face.clone();
                    for k in (0..arity).rev() {
                        face_inst = subst(k as i32, &reduced_args[arity - 1 - k], &face_inst);
                    }
                    return reduce_pcon_endpoints_dt(dts, &nbe_eval(&face_inst, session), session);
                }
            }
            // Not at an endpoint (or datatype not found): reduce sub-terms.
            let reduced_args: Vec<Term> = args
                .iter()
                .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                .collect();
            nbe_eval(
                &Term::TPCon(d.clone(), pc.clone(), reduced_args, Arc::new(r_nf)),
                session,
            )
        }
        Term::TSqCon(d, sc, args, r, s) => {
            let r_nf = nbe_eval(r, session);
            let s_nf = nbe_eval(s, session);
            // Check if either interval is at an endpoint for boundary reduction.
            let (r_is_i0, r_is_i1) = match &r_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    (
                        dnf == crate::cubical::interval::dnf_bot(),
                        dnf == crate::cubical::interval::dnf_top(),
                    )
                }
                _ => (false, false),
            };
            let (s_is_i0, s_is_i1) = match &s_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    (
                        dnf == crate::cubical::interval::dnf_bot(),
                        dnf == crate::cubical::interval::dnf_top(),
                    )
                }
                _ => (false, false),
            };
            if let Some(dt) = dts.iter().find(|dt| &dt.name == d)
                && let Some(sig) = dt.find_sqcon(sc)
            {
                let arity = sig.arity();
                let reduced_args: Vec<Term> = args
                    .iter()
                    .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                    .collect();
                // Substitute args into face terms.
                let subst_face = |face: &Term| -> Term {
                    let mut t = face.clone();
                    for k in (0..arity).rev() {
                        t = subst(k as i32, &reduced_args[arity - 1 - k], &t);
                    }
                    t
                };
                if r_is_i0 {
                    // sq @ 0 @ s = face_j0 @ s (outer path at i=0 gives face_j0)
                    let face = subst_face(&sig.face_j0);
                    return reduce_pcon_endpoints_dt(
                        dts,
                        &nbe_eval(&Term::PApp(Arc::new(face), s.clone()), session),
                        session,
                    );
                }
                if r_is_i1 {
                    // sq @ 1 @ s = face_j1 @ s (outer path at i=1 gives face_j1)
                    let face = subst_face(&sig.face_j1);
                    return reduce_pcon_endpoints_dt(
                        dts,
                        &nbe_eval(&Term::PApp(Arc::new(face), s.clone()), session),
                        session,
                    );
                }
                if s_is_i0 {
                    // sq @ r @ 0 = face_i0 (inner path at j=0 gives face_i0, a point)
                    let face = subst_face(&sig.face_i0);
                    return reduce_pcon_endpoints_dt(dts, &nbe_eval(&face, session), session);
                }
                if s_is_i1 {
                    // sq @ r @ 1 = face_i1 (inner path at j=1 gives face_i1, a point)
                    let face = subst_face(&sig.face_i1);
                    return reduce_pcon_endpoints_dt(dts, &nbe_eval(&face, session), session);
                }
            }
            // Not at an endpoint: reduce sub-terms.
            nbe_eval(
                &Term::TSqCon(
                    d.clone(),
                    sc.clone(),
                    args.iter()
                        .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                        .collect(),
                    Arc::new(r_nf),
                    Arc::new(s_nf),
                ),
                session,
            )
        }
        Term::TCellCon(d, cc, args, ivars) => {
            let dim = ivars.len();
            let ivar_nfs: Vec<Term> = ivars.iter().map(|v| nbe_eval(v, session)).collect();
            // Check which interval args are at endpoints.
            let ivar_is_endpoint: Vec<(bool, bool)> = ivar_nfs
                .iter()
                .map(|v| match v {
                    Term::TInterval(i) => {
                        let dnf = crate::cubical::interval::eval_interval(i);
                        (
                            dnf == crate::cubical::interval::dnf_bot(),
                            dnf == crate::cubical::interval::dnf_top(),
                        )
                    }
                    Term::TCube(d) => (
                        d == &crate::cubical::interval::dnf_bot(),
                        d == &crate::cubical::interval::dnf_top(),
                    ),
                    _ => (false, false),
                })
                .collect();
            if let Some(dt) = dts.iter().find(|dt| &dt.name == d)
                && let Some(sig) = dt.find_cellcon(cc)
            {
                let arity = sig.arity();
                let reduced_args: Vec<Term> = args
                    .iter()
                    .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                    .collect();
                let subst_face = |face: &Term| -> Term {
                    let mut t = face.clone();
                    for k in (0..arity).rev() {
                        t = subst(k as i32, &reduced_args[arity - 1 - k], &t);
                    }
                    t
                };
                // Try outermost interval arg first (highest dimension).
                // cell @ r1 @ r2 @ ... @ rn: if r1 is endpoint, reduce via outer face pair.
                if ivar_is_endpoint[0].0 || ivar_is_endpoint[0].1 {
                    let face = if ivar_is_endpoint[0].0 {
                        &sig.faces[2 * dim - 2] // face at outermost=0
                    } else {
                        &sig.faces[2 * dim - 1] // face at outermost=1
                    };
                    let face_inst = subst_face(face);
                    // The face is a (dim-1)-dimensional term; apply to remaining ivars.
                    // ivar_nfs[0] is the consumed outermost endpoint; skip it.
                    // Apply remaining in outermost-first order (matching PApp apply order).
                    let mut result = nbe_eval(&face_inst, session);
                    for iv in ivar_nfs[1..].iter() {
                        result = reduce_pcon_endpoints_dt(
                            dts,
                            &Term::PApp(Arc::new(result), Arc::new(iv.clone())),
                            session,
                        );
                    }
                    return reduce_pcon_endpoints_dt(dts, &result, session);
                }
            }
            // Not at an endpoint: reduce sub-terms.
            nbe_eval(
                &Term::TCellCon(
                    d.clone(),
                    cc.clone(),
                    args.iter()
                        .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                        .collect(),
                    ivar_nfs,
                ),
                session,
            )
        }
        // Recurse into PApp so that e.g. `pcon @ (~ i0)` reduces too.
        Term::PApp(p, r) => {
            // If p is TCon(d, pc, args) referencing a path constructor, and r
            // is a concrete endpoint, reduce via the PConSig faces.
            let r_nf = nbe_eval(r, session);
            let r_is_endpoint = match &r_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    dnf == crate::cubical::interval::dnf_bot()
                        || dnf == crate::cubical::interval::dnf_top()
                }
                _ => false,
            };
            if r_is_endpoint {
                if let Term::TCon(ref d, ref pc, ref args) = **p {
                    if let Some(dt) = dts.iter().find(|dt| &dt.name == d) {
                        // Try pcon first
                        if let Some(sig) = dt.find_pcon(pc) {
                            let is_i0 = match &r_nf {
                                Term::TInterval(i) => {
                                    crate::cubical::interval::eval_interval(i)
                                        == crate::cubical::interval::dnf_bot()
                                }
                                _ => false,
                            };
                            let face = if is_i0 { &sig.face0 } else { &sig.face1 };
                            let arity = args.len();
                            let reduced_args: Vec<Term> = args
                                .iter()
                                .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                                .collect();
                            let mut face_inst = face.clone();
                            for k in (0..arity).rev() {
                                face_inst =
                                    subst(k as i32, &reduced_args[arity - 1 - k], &face_inst);
                            }
                            return reduce_pcon_endpoints_dt(
                                dts,
                                &nbe_eval(&face_inst, session),
                                session,
                            );
                        }
                        // Try sqcon: first PApp on a bare sqcon TCon
                        // applies to the r (outer) interval.
                        // sq @ 0 = face_j0, sq @ 1 = face_j1
                        if let Some(sig) = dt.sqcons.iter().find(|c| &c.name == pc) {
                            let is_i0 = match &r_nf {
                                Term::TInterval(i) => {
                                    crate::cubical::interval::eval_interval(i)
                                        == crate::cubical::interval::dnf_bot()
                                }
                                _ => false,
                            };
                            let face = if is_i0 { &sig.face_j0 } else { &sig.face_j1 };
                            let arity = args.len();
                            let reduced_args: Vec<Term> = args
                                .iter()
                                .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                                .collect();
                            let mut face_inst = face.clone();
                            for k in (0..arity).rev() {
                                face_inst =
                                    subst(k as i32, &reduced_args[arity - 1 - k], &face_inst);
                            }
                            return reduce_pcon_endpoints_dt(
                                dts,
                                &nbe_eval(&face_inst, session),
                                session,
                            );
                        }
                    }
                }
            }
            let p2 = reduce_pcon_endpoints_dt(dts, p, session);
            nbe_eval(&Term::PApp(Arc::new(p2), Arc::new(r_nf.clone())), session)
        }
        // Recurse into PLam so that e.g. `PLam(k, cube3 @ i0 @ j @ k)` reduces too.
        Term::PLam(name, body) => Term::PLam(
            name.clone(),
            Arc::new(reduce_pcon_endpoints_dt(dts, body, session)),
        ),
        _ => t,
    }
}

// ---------------------------------------------------------------------------
// Type Checking
// ---------------------------------------------------------------------------

pub fn check(ctx: &Ctx, t: &Term, ty: &Term, session: &mut Session) -> Result<(), TypeError> {
    check_dt(&[], ctx, t, ty, session)
}

/// Like `check` but with access to declared datatypes.
/// Pass `&[]` when no datatypes are in scope.
pub fn check_dt(
    dts: &[Datatype],
    ctx: &Ctx,
    t: &Term,
    ty: &Term,
    session: &mut Session,
) -> Result<(), TypeError> {
    const CHECK_DT_MAX_DEPTH: usize = 2000;
    let d = session.check_depth_enter();
    if d >= CHECK_DT_MAX_DEPTH {
        session.check_depth_restore(d);
        return Err(TypeError::Other(format!(
            "check_dt depth exceeded ({CHECK_DT_MAX_DEPTH})"
        )));
    }
    let result = check_dt_inner(dts, ctx, t, ty, session);
    session.check_depth_restore(d);
    result
}

fn check_dt_inner(
    dts: &[Datatype],
    ctx: &Ctx,
    t: &Term,
    ty: &Term,
    session: &mut Session,
) -> Result<(), TypeError> {
    let names: Vec<Name> = ctx.iter().map(|(n, _)| n.clone()).collect();
    crate::debug_scope!(
        "check {} : {} : ctx[{}]",
        show_term(&names, t),
        show_term(&names, ty),
        ctx.len()
    );
    session.set_current_dts(dts);
    match t {
        // Lambda introduction
        Term::TAbs(x, body) => {
            let (a_ty, b_ty) = match ty {
                Term::TPi(_, a, b, _) => (a.as_ref().clone(), b.as_ref().clone()),
                _ => match nbe_eval_ctx(ctx.len(), ty, session) {
                    Term::TPi(_, a, b, _) => (a.as_ref().clone(), b.as_ref().clone()),
                    other => {
                        return Err(TypeError::ExpectedPi {
                            ty: other,
                            names: err_names(ctx),
                            pos: err_pos(ctx, t, session),
                        });
                    }
                },
            };
            check_dt(
                dts,
                &extend_ctx(x.clone(), nbe_eval_ctx(ctx.len(), &a_ty, session), ctx),
                body,
                &b_ty,
                session,
            )
        }

        // Path-lambda introduction
        Term::PLam(i, body) => {
            let (a_ty, u, v) = match ty {
                Term::TPath(a, u, v) => {
                    (a.as_ref().clone(), u.as_ref().clone(), v.as_ref().clone())
                }
                _ => match nbe_eval_ctx(ctx.len(), ty, session) {
                    Term::TPath(a, u, v) => {
                        (a.as_ref().clone(), u.as_ref().clone(), v.as_ref().clone())
                    }
                    other => {
                        return Err(TypeError::ExpectedPath {
                            ty: other,
                            names: err_names(ctx),
                            pos: err_pos(ctx, t, session),
                        });
                    }
                },
            };
            let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
            let body_ty = match nbe_eval_ctx(ctx.len(), &a_ty, session) {
                // a_ty is a type family (PLam): apply it to the freshly-bound
                // interval variable TVar(0) to get the body's type.
                Term::PLam(_, b) => nbe_eval_ctx(ctx2.len(), &beta(&b, &Term::TVar(0)), session),
                // a_ty is a constant type: shift it into the extended context.
                plain => shift(1, 0, &plain),
            };
            // Instantiate the interval binder at each endpoint by substituting
            // IVar(0) → I0 / I1 via apply_literal. Unlike beta (which only
            // substitutes TVar), apply_literal correctly handles IVar inside
            // nested PLams by incrementing the target index.
            //
            // Skip boundary checks for HIT case bodies (SKIP_PLAM_ENDPT):
            // the constructor variable is free and can't reduce, so boundary
            // equality can't be verified. The expected body type already
            // encodes the correct faces from the constructor declaration.
            if !session.should_skip_plam_endpt() {
                let body_at0 = {
                    let reduced = reduce_pcon_endpoints_dt(
                        dts,
                        &apply_literal(&Literal::NegVar(0), body, session),
                        session,
                    );
                    nbe_eval_ctx(ctx.len(), &shift(-1, 0, &reduced), session)
                };
                let body_at1 = {
                    let reduced = reduce_pcon_endpoints_dt(
                        dts,
                        &apply_literal(&Literal::Pos(0), body, session),
                        session,
                    );
                    nbe_eval_ctx(ctx.len(), &shift(-1, 0, &reduced), session)
                };
                require_equal_endpt(
                    ctx,
                    &nbe_eval_ctx(ctx.len(), &u, session),
                    &body_at0,
                    session,
                )?;
                require_equal_endpt(
                    ctx,
                    &nbe_eval_ctx(ctx.len(), &v, session),
                    &body_at1,
                    session,
                )?;
            }
            check_dt(dts, &ctx2, body, &body_ty, session)
        }

        // GlueElem checking
        Term::TGlueElem(phi, t_inner, a) => {
            // Try to use the type as-is first (preserves Glue structure from
            // the annotation). Fall back to nbe_eval for neutral Glue types.
            let glue = match ty {
                Term::TGlue(_, _, _) => ty,
                _ => &nbe_eval(ty, session),
            };
            match glue {
                Term::TGlue(a_ty, phi_, te) => {
                    check_interval(ctx, phi, session)?;
                    require_equal(
                        ctx,
                        &nbe_eval(phi_, session),
                        &nbe_eval(phi, session),
                        session,
                    )?;
                    let t_ty = match nbe_eval(te, session) {
                        Term::TMkEquiv(dom_a, _, _, _, _, _) => nbe_eval(&dom_a, session),
                        Term::TEquiv(dom_a, _) => nbe_eval(&dom_a, session),
                        Term::TPair(te_a, _) => nbe_eval(&te_a, session),
                        Term::TAbs(_, body) => {
                            let body_at_1 = beta(&body, &Term::TInterval(I::I1));
                            match body_at_1 {
                                Term::TPair(ref te_a, _) => nbe_eval(te_a, session),
                                other => other,
                            }
                        }
                        other => other,
                    };
                    // The cap may be a trivial path (lambda over the interval) or a
                    // direct element — handle both by wrapping in I -> dom_ty when
                    // the cap is syntactically a lambda.
                    let cap_ty = match &**t_inner {
                        Term::TAbs(_, _) => {
                            // Shift t_ty up by 1 because the TPi binder will be
                            // pushed into the context during checking.
                            let shifted_t_ty = shift(1, 0, &t_ty);
                            Term::TPi(
                                "_".into(),
                                Arc::new(Term::TIntervalTy),
                                Arc::new(shifted_t_ty),
                                false,
                            )
                        }
                        _ => t_ty.clone(),
                    };
                    check_dt(dts, ctx, t_inner, &cap_ty, session)?;
                    check_dt(dts, ctx, a, &nbe_eval(a_ty, session), session)
                }
                other => Err(TypeError::Other(format!(
                    "glue: expected Glue type, got: {}",
                    other
                ))),
            }
        }

        // Pair introduction
        Term::TPair(a, b) => {
            let (a_ty, b_ty) = match ty {
                Term::TSigma(_, a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                _ => match nbe_eval(ty, session) {
                    Term::TSigma(_, a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                    other => {
                        return Err(TypeError::ExpectedSigma {
                            ty: other,
                            names: err_names(ctx),
                            pos: err_pos(ctx, t, session),
                        });
                    }
                },
            };
            check_dt(dts, ctx, a, &nbe_eval(&a_ty, session), session)?;
            check_dt(dts, ctx, b, &nbe_eval(&beta(&b_ty, a), session), session)
        }

        // Constructor introduction — checked bidirectionally.
        //
        // For TCon: the expected type must be TData(d). We use it to resolve
        // the datatype so argument checking can propagate the expected type
        // into dependent telescope positions, rather than inferring and
        // comparing afterward.
        //
        // For TPCon: similarly, the expected type should be
        // Path (λ_. TData(d)) face0 face1; we extract d from it and then
        // delegate to infer_dt (which checks args and verifies the path
        // endpoints). We still call require_equal at the end to catch any
        // endpoint mismatch the caller's annotation encodes.
        Term::TCon(d, c, args) => {
            let expected_ty_nf = nbe_eval(ty, session);
            let (expected_d, expected_params) = match &expected_ty_nf {
                Term::TData(ed, ep) => {
                    if ed != d {
                        return Err(TypeError::TypeMismatch {
                            expected: Box::new(expected_ty_nf.clone()),
                            got: Box::new(Term::TData(d.clone(), vec![])),
                            names: err_names(ctx),
                            pos: err_pos(ctx, t, session),
                        });
                    }
                    (ed.clone(), ep.clone())
                }
                _ => (d.clone(), vec![]),
            };
            let dt = dts.iter().find(|dt| dt.name == expected_d).ok_or_else(|| {
                TypeError::UnknownDatatype {
                    name: expected_d.clone(),
                    pos: err_pos(ctx, t, session),
                }
            })?;
            if let Some(sig) = dt.find_con(c) {
                if args.len() != sig.arity() {
                    return Err(TypeError::WrongNumberOfArgs {
                        con: c.clone(),
                        expected: sig.arity(),
                        got: args.len(),
                        pos: err_pos(ctx, t, session),
                    });
                }
                // Substitute known params from the expected type into arg_tys,
                // then use the same two-phase inference as infer_dt so that
                // parameters not provided by the expected type are inferred from
                // the arguments.
                let num_params = dt.params.len();
                let initial: Vec<Option<Term>> = (0..num_params)
                    .map(|i| expected_params.get(i).cloned())
                    .collect();
                let (param_terms, _checked_args) = infer_and_check_params_seeded(
                    dts,
                    ctx,
                    &sig.arg_tys,
                    args,
                    num_params,
                    &initial,
                    session,
                )?;
                let params = build_params(&param_terms);
                require_equal(
                    ctx,
                    &expected_ty_nf,
                    &Term::TData(d.clone(), params),
                    session,
                )
            } else if dt.find_pcon(c).is_some() {
                let inferred = infer_dt(
                    dts,
                    ctx,
                    &Term::TCon(d.clone(), c.clone(), args.clone()),
                    session,
                )?;
                require_equal(ctx, &expected_ty_nf, &nbe_eval(&inferred, session), session)
            } else {
                Err(TypeError::UnknownConstructor {
                    datatype: expected_d.clone(),
                    con: c.clone(),
                    pos: err_pos(ctx, t, session),
                })
            }
        }

        Term::TPCon(d, pc, args, r) => {
            // Infer the full path type from the constructor signature, then
            // unify with the expected type so endpoint annotations are checked.
            let inferred = infer_dt(
                dts,
                ctx,
                &Term::TPCon(d.clone(), pc.clone(), args.clone(), r.clone()),
                session,
            )?;
            require_equal(
                ctx,
                &nbe_eval(ty, session),
                &nbe_eval(&inferred, session),
                session,
            )
        }

        Term::TSqCon(d, sc, args, r, s) => {
            // When the expected type is TData(d), the PLam check has already
            // stripped the PathP layers. Just verify the data type matches and
            // check interval args are valid.
            let expected_nf = nbe_eval(ty, session);
            if let Term::TData(ed, _) = &expected_nf {
                if ed == d {
                    let dt_ = dts.iter().find(|dt| &dt.name == d).ok_or_else(|| {
                        TypeError::UnknownDatatype {
                            name: d.clone(),
                            pos: err_pos(ctx, t, session),
                        }
                    })?;
                    let sig = dt_
                        .find_sqcon(sc)
                        .ok_or_else(|| TypeError::UnknownConstructor {
                            datatype: d.clone(),
                            con: sc.clone(),
                            pos: err_pos(ctx, t, session),
                        })?;
                    if args.len() != sig.arity() {
                        return Err(TypeError::WrongNumberOfArgs {
                            con: sc.clone(),
                            expected: sig.arity(),
                            got: args.len(),
                            pos: err_pos(ctx, t, session),
                        });
                    }
                    check_interval(ctx, r, session)?;
                    check_interval(ctx, s, session)?;
                    return Ok(());
                }
            }
            let inferred = infer_dt(
                dts,
                ctx,
                &Term::TSqCon(d.clone(), sc.clone(), args.clone(), r.clone(), s.clone()),
                session,
            )?;
            require_equal(
                ctx,
                &nbe_eval(ty, session),
                &nbe_eval(&inferred, session),
                session,
            )
        }

        Term::TCellCon(d, cc, args, ivars) => {
            let expected_nf = nbe_eval(ty, session);
            if let Term::TData(ed, _) = &expected_nf {
                if ed == d {
                    let dt_ = dts.iter().find(|dt| &dt.name == d).ok_or_else(|| {
                        TypeError::UnknownDatatype {
                            name: d.clone(),
                            pos: err_pos(ctx, t, session),
                        }
                    })?;
                    let sig =
                        dt_.find_cellcon(cc)
                            .ok_or_else(|| TypeError::UnknownConstructor {
                                datatype: d.clone(),
                                con: cc.clone(),
                                pos: err_pos(ctx, t, session),
                            })?;
                    if args.len() != sig.arity() {
                        return Err(TypeError::WrongNumberOfArgs {
                            con: cc.clone(),
                            expected: sig.arity(),
                            got: args.len(),
                            pos: err_pos(ctx, t, session),
                        });
                    }
                    if ivars.len() != sig.dimension() {
                        return Err(TypeError::WrongNumberOfArgs {
                            con: cc.clone(),
                            expected: sig.dimension(),
                            got: ivars.len(),
                            pos: err_pos(ctx, t, session),
                        });
                    }
                    for iv in ivars {
                        check_interval(ctx, iv, session)?;
                    }
                    return Ok(());
                }
            }
            let inferred = infer_dt(
                dts,
                ctx,
                &Term::TCellCon(d.clone(), cc.clone(), args.clone(), ivars.clone()),
                session,
            )?;
            require_equal(
                ctx,
                &nbe_eval(ty, session),
                &nbe_eval(&inferred, session),
                session,
            )
        }

        // Tactic block: run tactics to produce a proof term, then check it
        Term::TBy(tactics) => {
            let goal_ty = nbe_eval(ty, session);
            let mut engine =
                crate::cubical::tactics::TacticEngine::new(dts, goal_ty.clone(), goal_ty);
            for tac in tactics {
                engine.run_tactic(tac, ctx, session)?;
            }
            let proof = engine.into_term(session)?;
            // The `ring` tactic returns a fully-normalized proof whose unfolded
            // law bodies contain elims on compound neutral scrutinees. The
            // structural-recursion guard cannot fire on a normal form (see the
            // comment at the fallback below), so skip it for this tactic's
            // output; every other tactic (e.g. `by exact`) keeps the guard.
            let prev = crate::cubical::typechecker::termination::should_skip_guard(session);
            if tactics
                .iter()
                .any(|t| matches!(t, crate::cubical::syntax::Tactic::Ring(_)))
            {
                crate::cubical::typechecker::termination::set_skip_guard(true, session);
            }
            let r = check_dt(dts, ctx, &proof, ty, session);
            crate::cubical::typechecker::termination::set_skip_guard(prev, session);
            r
        }

        // ------------------------------------------------------------------
        // Kan operations — check expected type first, then delegate to
        // infer_dt for sub-term checking.  On infer_dt failure, retry
        // with nbe_eval (the comp/hcomp may reduce and become well-typed).
        // ------------------------------------------------------------------

        // hcomp A [phi -> tube, ...] base : A
        Term::THComp(a_ty, _sys, _base) => {
            type_level_dt(dts, ctx, a_ty, session)?;
            let a_ty_ = nbe_eval(a_ty, session);
            let expected_nf = nbe_eval(ty, session);
            if !cumulativity_check(&expected_nf, &a_ty_, dts, session) {
                require_equal(ctx, &expected_nf, &a_ty_, session)?;
            }
            match infer_dt(dts, ctx, t, session) {
                Ok(_) => Ok(()),
                Err(e) => {
                    let reduced = nbe_eval(t, session);
                    if reduced == *t {
                        Err(e)
                    } else {
                        let nf = nbe_eval(&reduced, session);
                        if nf == *t {
                            Err(e)
                        } else {
                            check_dt(dts, ctx, &nf, ty, session)
                        }
                    }
                }
            }
        }

        // comp A [phi -> tube, ...] base : A 1
        Term::TComp(a_fam, _sys, _base) => {
            let ctx_i = extend_ctx("i".to_string(), interval_ty(), ctx);
            type_level_dt(dts, &ctx_i, a_fam, session)?;
            let a_fam_ = nbe_eval(a_fam, session);
            let a_at1 = match &a_fam_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I1)), session),
                _ => a_fam_.clone(),
            };
            let expected_nf = nbe_eval(ty, session);
            if !cumulativity_check(&expected_nf, &a_at1, dts, session) {
                require_equal(ctx, &expected_nf, &a_at1, session)?;
            }
            match infer_dt(dts, ctx, t, session) {
                Ok(_) => Ok(()),
                Err(e) => {
                    let reduced = nbe_eval(t, session);
                    if reduced == *t {
                        Err(e)
                    } else {
                        let nf = nbe_eval(&reduced, session);
                        if nf == *t {
                            Err(e)
                        } else {
                            check_dt(dts, ctx, &nf, ty, session)
                        }
                    }
                }
            }
        }

        // fill A [phi -> tube, ...] base : (j : I) -> A j
        // Inferred type is TPath(PLam j (A j), base, TComp A sys base), so
        // delegate to infer_dt for the full type, then check cumulativity.
        Term::TFill(_, _, _) | Term::THFill(_, _, _) => match infer_dt(dts, ctx, t, session) {
            Ok(inferred) => {
                let expected_nf = nbe_eval(ty, session);
                let inferred_nf = nbe_eval(&inferred, session);
                if cumulativity_check(&expected_nf, &inferred_nf, dts, session) {
                    Ok(())
                } else {
                    require_equal(ctx, &expected_nf, &inferred_nf, session)
                }
            }
            Err(e) => {
                let reduced = nbe_eval(t, session);
                if reduced == *t {
                    Err(e)
                } else {
                    let nf = nbe_eval(&reduced, session);
                    if nf == *t {
                        Err(e)
                    } else {
                        check_dt(dts, ctx, &nf, ty, session)
                    }
                }
            }
        },

        // Metavariable hole: the expected type is already known.
        Term::Meta(id) => {
            let expected_nf = nbe_eval(ty, session);
            session.set_meta_expected(*id, expected_nf.clone());
            let _ = type_level_dt(dts, ctx, ty, session)?;
            Ok(())
        }

        // Refl introduction: Refl x : Id A x x  when  x : A
        Term::TRefl(x) => {
            match nbe_eval_ctx(ctx.len(), ty, session) {
                Term::TId(a, _exp_x, _exp_y) => {
                    // Check that x : A (the type component of Id)
                    check_dt(dts, ctx, x, &nbe_eval_ctx(ctx.len(), &a, session), session)?;
                    Ok(())
                }
                other => {
                    return Err(TypeError::Other(format!(
                        "Refl must be checked against Id type, got {}",
                        show_term(&names, &other)
                    )));
                }
            }
        }

        // J elimination: infer and compare
        Term::TJ(_, _, _) => {
            let inferred = infer_dt(dts, ctx, t, session)?;
            require_equal(
                ctx,
                &nbe_eval_ctx(ctx.len(), ty, session),
                &nbe_eval_ctx(ctx.len(), &inferred, session),
                session,
            )
        }

        // Fall through to inference + cumulativity.
        t => match infer_dt(dts, ctx, t, session) {
            Ok(ty_) => {
                let expected_nf = nbe_eval(ty, session);
                let inferred_nf = nbe_eval(&ty_, session);
                if cumulativity_check(&expected_nf, &inferred_nf, dts, session) {
                    Ok(())
                } else {
                    require_equal(ctx, &expected_nf, &inferred_nf, session)
                }
            }
            Err(e) => {
                let reduced = nbe_eval_ctx(ctx.len(), t, session);
                if reduced == *t {
                    Err(e)
                } else {
                    let nf = nbe_eval_ctx(ctx.len(), &reduced, session);
                    if nf == *t {
                        Err(e)
                    } else {
                        // Re-check the fully-reduced term. Guard checking is a
                        // source-level structural-recursion check for
                        // definitions; the normal form only contains stuck
                        // elims (neutral scrutinees) that can never fire, so
                        // the guard is vacuous here. Without skipping it,
                        // legitimate normal forms built from checked
                        // definitions (e.g. the ring tactic's proof) would be
                        // rejected because unfolding inlines elims whose
                        // scrutinees are compound neutrals.
                        let prev =
                            crate::cubical::typechecker::termination::should_skip_guard(session);
                        crate::cubical::typechecker::termination::set_skip_guard(true, session);
                        let r = check_dt(dts, ctx, &nf, ty, session);
                        crate::cubical::typechecker::termination::set_skip_guard(prev, session);
                        r
                    }
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Universe cumulativity
// ---------------------------------------------------------------------------

/// Extract a DNF from a term that is known to represent a face (TCube or TInterval).
fn term_to_dnf(t: &Term, session: &mut Session) -> DNF {
    match nbe_eval(t, session) {
        Term::TCube(d) => d,
        Term::TInterval(i) => crate::cubical::interval::eval_interval(&i),
        _ => crate::cubical::interval::dnf_bot(),
    }
}

/// Check whether `inferred` is a subtype of `expected` under cumulativity.
///
/// Rules:
/// - `TUniv(n) ≤ TUniv(m)` when `n ≤ m` (cumulativity of universes)
/// - `TPi(x, A, B) ≤ TPi(x, A', B')` when `A' ≤ A` (contravariant domain)
///   and `B ≤ B'` (covariant codomain), checked recursively
/// - `TSigma(x, A, B) ≤ TSigma(x, A', B')` when `A ≤ A'` and `B ≤ B'`
///   (covariant in both), checked recursively
/// - `TData(d, ps) ≤ TData(d, ps')` with covariant parameters
///   (this covers desugared record types)
/// - `TPartial(phi, A) ≤ TPartial(psi, A)` when `phi ⇒ psi` (cofibration subtyping)
/// - Reflexive: identical (syntactically equal) terms are always subtypes,
///   so recursion through Π/Σ/record codomains and parameters that mention
///   bound variables succeeds.
fn cumulativity_check(
    expected: &Term,
    inferred: &Term,
    dts: &[Datatype],
    session: &mut Session,
) -> bool {
    match (expected, inferred) {
        // Prop ≤ U0 (cumulativity: Prop is a subuniverse of U0)
        (Term::TUniv(m), Term::TProp) if m.as_const().map_or(false, |c| c >= 0) => true,
        // SSet ≤ U1
        (Term::TUniv(m), Term::TSSet) if m.as_const().map_or(false, |c| c >= 1) => true,
        // Prop ≤ Prop
        (Term::TProp, Term::TProp) => true,
        // SSet ≤ SSet
        (Term::TSSet, Term::TSSet) => true,
        // Lift cumulativity: lift A m ≤ lift B m when A ≤ B
        (Term::TLift(a_exp, m1), Term::TLift(a_inf, m2)) if m1 == m2 => {
            cumulativity_check(a_exp, a_inf, dts, session)
        }
        // Lower cumulativity: lower A ≤ lower B when A ≤ B
        (Term::TLower(a_exp), Term::TLower(a_inf)) => {
            cumulativity_check(a_exp, a_inf, dts, session)
        }

        // Universe cumulativity: U_n is subtype of U_m when n ≤ m
        // When level expressions can't be evaluated (contain variables),
        // fall through to structural equality.
        (Term::TUniv(m), Term::TUniv(n)) => n.leq(m, &[]).unwrap_or_else(|| n == m),

        // Pi cumulativity: contravariant in domain, covariant in codomain
        (Term::TPi(_, a_exp, b_exp, _), Term::TPi(_, a_inf, b_inf, _)) => {
            cumulativity_check(a_inf, a_exp, dts, session)
                && cumulativity_check(b_exp, b_inf, dts, session)
        }

        // Sigma cumulativity: covariant in both components
        (Term::TSigma(_, a_exp, b_exp), Term::TSigma(_, a_inf, b_inf)) => {
            cumulativity_check(a_exp, a_inf, dts, session)
                && cumulativity_check(b_exp, b_inf, dts, session)
        }

        // Cofibration subtyping: [_ | phi] A ≤ [_ | psi] A when phi ⇒ psi
        (Term::TPartial(phi_exp, a_exp), Term::TPartial(phi_inf, a_inf)) => {
            let phi_exp_dnf = term_to_dnf(phi_exp, session);
            let phi_inf_dnf = term_to_dnf(phi_inf, session);
            // The inferred partial element has face phi_inf; the expected has phi_exp.
            // phi_inf ⇒ phi_exp means the inferred is defined on a "larger" face,
            // so it's a valid subtype.
            dnf_leq(&phi_inf_dnf, &phi_exp_dnf) && cumulativity_check(a_exp, a_inf, dts, session)
        }

        // Inductive type cumulativity: same datatype, parameters checked
        // according to their variance.
        //
        // Covariant-only checking of all parameters is UNSOUND: a datatype
        // whose parameters occur negatively (e.g. inside an arrow domain in a
        // constructor argument type) is contravariant, and one that occurs
        // both positively and negatively is invariant.  For such parameters
        // the comparison must be reversed or restricted to definitional
        // equality — otherwise `Bad U0 ≤ Bad U1` typechecks for a `Bad A`
        // that is not covariant in `A`.
        //
        // TData(d, ps) ≤ TData(d, ps') when, per parameter i with variance v:
        //   Covariant:     ps[i] ≤ ps'[i]
        //   Contravariant: ps'[i] ≤ ps[i]
        //   Invariant:     ps[i] == ps'[i]
        //   Unused:        any direction (treated as covariant)
        // Different datatypes are never subtypes of each other.
        (Term::TData(d_exp, ps_exp), Term::TData(d_inf, ps_inf)) => {
            if d_exp != d_inf || ps_exp.len() != ps_inf.len() {
                return false;
            }
            let variances: Vec<Variance> = if ps_exp.is_empty() {
                Vec::new()
            } else {
                dts.iter()
                    .position(|d| &d.name == d_exp)
                    .map(|i| {
                        compute_param_variances(dts)
                            .get(i)
                            .cloned()
                            .unwrap_or_default()
                    })
                    .unwrap_or_default()
            };
            ps_exp
                .iter()
                .zip(ps_inf.iter())
                .enumerate()
                .all(|(i, (a, b))| match variances.get(i) {
                    // Covariant or unused (and unregistered datatypes fall
                    // back to the historical covariant behavior): check b ≤ a.
                    Some(Variance::Covariant) | Some(Variance::Unused) | None => {
                        cumulativity_check(a, b, dts, session)
                    }
                    // Contravariant: check a ≤ b.
                    Some(Variance::Contravariant) => cumulativity_check(b, a, dts, session),
                    // Invariant: require definitional equality.
                    Some(Variance::Invariant) => a == b,
                })
        }

        // Path type cumulativity: Path A u v ≤ Path A' u' v' when A ≤ A' (covariant),
        // u ≤ u' and v ≤ v' (endpoints covariant).
        (Term::TPath(a_exp, u_exp, v_exp), Term::TPath(a_inf, u_inf, v_inf)) => {
            cumulativity_check(a_exp, a_inf, dts, session)
                && cumulativity_check(u_exp, u_inf, dts, session)
                && cumulativity_check(v_exp, v_inf, dts, session)
        }

        // Reflexivity: any term is a subtype of itself.  This is the
        // fallthrough for structurally-identical terms that the arms above
        // don't recurse into — most importantly de Bruijn variables
        // (TVar(i) ≤ TVar(i)) and neutral terms (TApp, TFst, ...) appearing
        // inside the covariant/contravariant positions of a Π, Σ, record, or
        // datatype comparison.  Without it, legal subtyping that only differs
        // in universe levels *inside* a dependent codomain or record parameter
        // is rejected, because the recursion bottoms out on an identical
        // bound-variable reference and falls through to `false`.
        //
        // Callers normalize both sides with `nbe_eval` first, so this
        // compares normal forms (syntactic equality there ≈ definitional
        // equality for closed terms).  Subtyping is reflexive, so this is
        // always sound.
        (a, b) => a == b,
    }
}

// ---------------------------------------------------------------------------
// EtaResult convenience
// ---------------------------------------------------------------------------

impl EtaResult {
    fn is_equal(&self) -> bool {
        *self == EtaResult::Equal
    }
}

// ---------------------------------------------------------------------------
// Top-level helpers
// ---------------------------------------------------------------------------

#[allow(dead_code)]
pub fn infer_closed(t: &Term, session: &mut Session) -> Result<Term, TypeError> {
    infer(&Vec::new(), t, session)
}

#[allow(dead_code)]
pub fn check_closed(t: &Term, ty: &Term, session: &mut Session) -> Result<(), TypeError> {
    check(&Vec::new(), t, ty, session)
}

#[allow(dead_code)]
pub fn infer_closed_dt(
    dts: &[Datatype],
    t: &Term,
    session: &mut Session,
) -> Result<Term, TypeError> {
    infer_dt(dts, &Vec::new(), t, session)
}

/// Check boundary coherence for all square constructors in a datatype.
///
/// For each SqConSig with faces `(face_i0, face_i1, face_j0, face_j1)`, verify:
///   - PApp(face_j0, I0) == face_i0   (face_j0 starts at face_i0)
///   - PApp(face_j0, I1) == face_i1   (face_j0 ends at face_i1)
///   - PApp(face_j1, I0) == face_i0   (face_j1 starts at face_i0)
///   - PApp(face_j1, I1) == face_i1   (face_j1 ends at face_i1)
pub fn check_sqcon_coherence(
    dts: &[Datatype],
    dt: &Datatype,
    session: &mut Session,
) -> Result<(), TypeError> {
    for sqcon in &dt.sqcons {
        let i0 = Term::TInterval(I::I0);
        let i1 = Term::TInterval(I::I1);

        // Use reduce_pcon_endpoints_dt to reduce terms that reference path
        // constructors at concrete interval endpoints. This is needed because
        // raw TCon references to path constructors don't reduce in NbE.

        // PApp(face_j0, I0) == face_i0
        let fj0_at_i0 = reduce_pcon_endpoints_dt(
            dts,
            &Term::PApp(Arc::new(sqcon.face_j0.clone()), Arc::new(i0.clone())),
            session,
        );
        let fi0_reduced = reduce_pcon_endpoints_dt(dts, &sqcon.face_i0, session);
        let empty_ctx: Ctx = Vec::new();
        let eq1 = definitionally_equal_ctx_r(&empty_ctx, &fi0_reduced, &fj0_at_i0, session);
        if let EtaResult::NotEqual = eq1 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 PApp(face_j0, i0) != face_i0\n  expected={}\n  got={}",
                sqcon.name,
                show_term(&[], &nbe_eval(&fi0_reduced, session)),
                show_term(&[], &nbe_eval(&fj0_at_i0, session)),
            )));
        }
        if let EtaResult::Exhausted = eq1 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 eta-check exhausted comparing PApp(face_j0, i0) with face_i0",
                sqcon.name,
            )));
        }

        // PApp(face_j0, I1) == face_i1
        let fj0_at_i1 = reduce_pcon_endpoints_dt(
            dts,
            &Term::PApp(Arc::new(sqcon.face_j0.clone()), Arc::new(i1.clone())),
            session,
        );
        let fi1_reduced = reduce_pcon_endpoints_dt(dts, &sqcon.face_i1, session);
        let eq2 = definitionally_equal_ctx_r(&empty_ctx, &fi1_reduced, &fj0_at_i1, session);
        if let EtaResult::NotEqual = eq2 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 PApp(face_j0, i1) != face_i1\n  expected={}\n  got={}",
                sqcon.name,
                show_term(&[], &nbe_eval(&fi1_reduced, session)),
                show_term(&[], &nbe_eval(&fj0_at_i1, session)),
            )));
        }
        if let EtaResult::Exhausted = eq2 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 eta-check exhausted comparing PApp(face_j0, i1) with face_i1",
                sqcon.name,
            )));
        }

        // PApp(face_j1, I0) == face_i0
        let fj1_at_i0 = reduce_pcon_endpoints_dt(
            dts,
            &Term::PApp(Arc::new(sqcon.face_j1.clone()), Arc::new(i0.clone())),
            session,
        );
        let eq3 = definitionally_equal_ctx_r(&empty_ctx, &fi0_reduced, &fj1_at_i0, session);
        if let EtaResult::NotEqual = eq3 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 PApp(face_j1, i0) != face_i0\n  expected={}\n  got={}",
                sqcon.name,
                show_term(&[], &nbe_eval(&fi0_reduced, session)),
                show_term(&[], &nbe_eval(&fj1_at_i0, session)),
            )));
        }
        if let EtaResult::Exhausted = eq3 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 eta-check exhausted comparing PApp(face_j1, i0) with face_i0",
                sqcon.name,
            )));
        }

        // PApp(face_j1, I1) == face_i1
        let fj1_at_i1 = reduce_pcon_endpoints_dt(
            dts,
            &Term::PApp(Arc::new(sqcon.face_j1.clone()), Arc::new(i1.clone())),
            session,
        );
        let eq4 = definitionally_equal_ctx_r(&empty_ctx, &fi1_reduced, &fj1_at_i1, session);
        if let EtaResult::NotEqual = eq4 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 PApp(face_j1, i1) != face_i1\n  expected={}\n  got={}",
                sqcon.name,
                show_term(&[], &nbe_eval(&fi1_reduced, session)),
                show_term(&[], &nbe_eval(&fj1_at_i1, session)),
            )));
        }
        if let EtaResult::Exhausted = eq4 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 eta-check exhausted comparing PApp(face_j1, i1) with face_i1",
                sqcon.name,
            )));
        }
    }
    Ok(())
}

pub fn check_closed_dt(
    dts: &[Datatype],
    t: &Term,
    ty: &Term,
    session: &mut Session,
) -> Result<(), TypeError> {
    check_dt(dts, &Vec::new(), t, ty, session)
}

#[allow(dead_code)]
pub fn report_infer(label: &str, t: &Term, session: &mut Session) {
    match infer_closed(t, session) {
        Ok(ty) => println!("  ✓  {}\n       : {}", label, ty),
        Err(e) => println!("  ✗  {}\n{}", label, e),
    }
}

#[allow(dead_code)]
pub fn report_check(label: &str, t: &Term, ty: &Term, session: &mut Session) {
    match check_closed(t, ty, session) {
        Ok(()) => println!("  ✓  {}\n       ⊢ {}\n       : {}", label, t, ty),
        Err(e) => println!("  ✗  {}\n{}", label, e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cubical::parser::parse_term;

    /// `cumulativity_check(expected, inferred)` returns whether `inferred ≤ expected`.
    fn sub(expected: &str, inferred: &str, session: &mut Session) -> bool {
        let e = nbe_eval(
            &parse_term(expected, session).expect("parse expected"),
            session,
        );
        let i = nbe_eval(
            &parse_term(inferred, session).expect("parse inferred"),
            session,
        );
        cumulativity_check(&e, &i, &[], session)
    }

    fn sub_t(expected: &Term, inferred: &Term, session: &mut Session) -> bool {
        cumulativity_check(
            &nbe_eval(expected, session),
            &nbe_eval(inferred, session),
            &[],
            session,
        )
    }

    /// Assert `inferred ≤ expected`.
    fn assert_sub(expected: &str, inferred: &str, session: &mut Session) {
        assert!(
            sub(expected, inferred, session),
            "expected `{} <= {}` to hold under cumulativity",
            inferred,
            expected
        );
    }

    /// Assert `inferred ≰ expected`.
    fn assert_not_sub(expected: &str, inferred: &str, session: &mut Session) {
        assert!(
            !sub(expected, inferred, session),
            "expected `{} <= {}` to FAIL under cumulativity",
            inferred,
            expected
        );
    }

    fn tdata(name: &str, params: Vec<Term>) -> Term {
        Term::TData(name.to_string(), params)
    }

    fn t_univ(n: i32) -> Term {
        Term::TUniv(LevelExpr::LConst(n))
    }

    /// `cumulativity_check` against a concrete datatype environment, so the
    /// `TData` arm can resolve parameter variance.
    fn cumul_dts(
        dts: &[Datatype],
        expected: &Term,
        inferred: &Term,
        session: &mut Session,
    ) -> bool {
        cumulativity_check(
            &nbe_eval(expected, session),
            &nbe_eval(inferred, session),
            dts,
            session,
        )
    }

    /// A single-parameter datatype `D (A : U0)` whose constructor arguments
    /// are `arg_tys` (referencing `A` as `TVar(0)`).
    fn dt_one_param(name: &str, arg_tys: Vec<Term>) -> Datatype {
        Datatype {
            name: name.to_string(),
            params: vec![("A".into(), Term::TUniv(LevelExpr::LConst(0)))],
            cons: vec![crate::cubical::syntax::ConSig {
                name: "mk".into(),
                arg_tys,
            }],
            pcons: vec![],
            sqcons: vec![],
            cellcons: vec![],
            universe_level: None,
            field_names: None,
        }
    }

    #[test]
    fn datatype_cumulativity_respects_contravariant_parameters() {
        crate::cubical::session::with_session_mut(|session| {
            // D (A) with `mk : (A -> U0) -> D A`: A occurs in an arrow domain,
            // so D is contravariant in A.  Under covariant-only checking this
            // would unsoundly accept `D U0 ≤ D U1`.
            let dts = vec![dt_one_param(
                "D",
                vec![Term::TPi(
                    "_".into(),
                    Arc::new(Term::TVar(0)),
                    Arc::new(Term::TUniv(LevelExpr::LConst(0))),
                    false,
                )],
            )];
            let d_u0 = tdata("D", vec![t_univ(0)]);
            let d_u1 = tdata("D", vec![t_univ(1)]);
            // Contravariance: D U0 ≤ D U1 requires U1 ≤ U0 (false) ...
            assert!(!cumul_dts(&dts, &d_u1, &d_u0, session));
            // ... and D U1 ≤ D U0 requires U0 ≤ U1 (true).
            assert!(cumul_dts(&dts, &d_u0, &d_u1, session));
        });
    }

    #[test]
    fn datatype_cumulativity_rejects_invariant_parameters() {
        crate::cubical::session::with_session_mut(|session| {
            // D (A) with `mk : A -> (A -> U0) -> D A`: A occurs both positively
            // and negatively, so D is invariant in A and neither subtyping
            // direction is allowed.
            let dts = vec![dt_one_param(
                "D",
                vec![
                    Term::TVar(0),
                    Term::TPi(
                        "_".into(),
                        Arc::new(Term::TVar(0)),
                        Arc::new(Term::TUniv(LevelExpr::LConst(0))),
                        false,
                    ),
                ],
            )];
            let d_u0 = tdata("D", vec![t_univ(0)]);
            let d_u1 = tdata("D", vec![t_univ(1)]);
            assert!(!cumul_dts(&dts, &d_u1, &d_u0, session));
            assert!(!cumul_dts(&dts, &d_u0, &d_u1, session));
            // Identical instantiations still compare fine.
            assert!(cumul_dts(&dts, &d_u0, &d_u0, session));
        });
    }

    #[test]
    fn datatype_cumulativity_keeps_covariant_records() {
        crate::cubical::session::with_session_mut(|session| {
            // R (A) with field `content : A`: A occurs positively (a record's
            // field is covariant), so the historical covariant behavior is kept.
            let dts = vec![dt_one_param("R", vec![Term::TVar(0)])];
            let r_u0 = tdata("R", vec![t_univ(0)]);
            let r_u1 = tdata("R", vec![t_univ(1)]);
            assert!(cumul_dts(&dts, &r_u1, &r_u0, session));
            assert!(!cumul_dts(&dts, &r_u0, &r_u1, session));
        });
    }

    #[test]
    fn datatype_cumulativity_propagates_variance_through_nested_types() {
        crate::cubical::session::with_session_mut(|session| {
            // Bar (A) with `b : (A -> U0) -> Bar A` (contravariant) and
            // Foo (A) with `mk : Bar A -> Foo A` — Foo's parameter inherits
            // Bar's contravariance through the nested application.
            let dts = vec![
                dt_one_param(
                    "Bar",
                    vec![Term::TPi(
                        "_".into(),
                        Arc::new(Term::TVar(0)),
                        Arc::new(Term::TUniv(LevelExpr::LConst(0))),
                        false,
                    )],
                ),
                dt_one_param("Foo", vec![tdata("Bar", vec![Term::TVar(0)])]),
            ];
            let foo_u0 = tdata("Foo", vec![t_univ(0)]);
            let foo_u1 = tdata("Foo", vec![t_univ(1)]);
            assert!(!cumul_dts(&dts, &foo_u1, &foo_u0, session));
            assert!(cumul_dts(&dts, &foo_u0, &foo_u1, session));
        });
    }

    #[test]
    fn universe_levels() {
        crate::cubical::session::with_session_mut(|session| {
            assert_sub("U1", "U0", session);
            assert_sub("U2", "U1", session);
            assert_sub("U0", "U0", session);
            assert_not_sub("U0", "U1", session);
            assert_not_sub("U1", "U2", session);
        });
    }

    #[test]
    fn pi_cumulativity() {
        crate::cubical::session::with_session_mut(|session| {
            // Contravariant domain: a function accepting a *larger* domain (U1) is
            // usable wherever a smaller domain (U0) is expected.
            assert_sub("∀ (A : U0), A -> A", "∀ (A : U1), A -> A", session);
            assert_not_sub("∀ (A : U1), A -> A", "∀ (A : U0), A -> A", session);
            // Covariant codomain: A -> U0 <= A -> U1.
            assert_sub("∀ (A : U0), A -> U1", "∀ (A : U0), A -> U0", session);
            assert_not_sub("∀ (A : U0), A -> U0", "∀ (A : U0), A -> U1", session);
            // Dependent codomain referencing the bound variable: reflexivity of
            // the variable is required for this comparison to close.
            assert_sub("∀ (A : U0), A -> U1", "∀ (A : U1), A -> U1", session);
            assert_not_sub("U1", "∀ (A : U0), A -> A", session);
        });
    }

    #[test]
    fn sigma_cumulativity() {
        crate::cubical::session::with_session_mut(|session| {
            // Covariant in both components.
            assert_sub("Σ (B : U1), B", "Σ (B : U0), B", session);
            assert_not_sub("Σ (B : U0), B", "Σ (B : U1), B", session);
            // Codomain mentioning the bound variable, differing only by universe.
            assert_sub("Σ (B : U0), B -> U1", "Σ (B : U0), B -> U0", session);
            assert_not_sub("Σ (B : U0), B -> U0", "Σ (B : U0), B -> U1", session);
        });
    }

    #[test]
    fn datatype_and_record_cumulativity() {
        crate::cubical::session::with_session_mut(|session| {
            // Identical datatypes are reflexive (empty parameters).
            assert!(sub_t(&tdata("Nat", vec![]), &tdata("Nat", vec![]), session));
            // Covariant datatype parameters (records desugar to TData).
            assert!(sub_t(
                &tdata("Pair", vec![t_univ(1), t_univ(1)]),
                &tdata("Pair", vec![t_univ(0), t_univ(0)]),
                session,
            ));
            assert!(sub_t(
                &tdata("Pair", vec![t_univ(1), tdata("Nat", vec![])]),
                &tdata("Pair", vec![t_univ(0), tdata("Nat", vec![])]),
                session,
            ));
            // Negative: parameters are covariant, not contravariant.
            assert!(!sub_t(
                &tdata("Pair", vec![t_univ(0), t_univ(0)]),
                &tdata("Pair", vec![t_univ(1), t_univ(1)]),
                session,
            ));
            // Negative: different datatypes are incomparable.
            assert!(!sub_t(
                &tdata("Bool", vec![]),
                &tdata("Nat", vec![]),
                session
            ));
            // Record params that are bound variables are reflexive.
            assert!(sub_t(
                &tdata("Pair", vec![Term::TVar(0), Term::TVar(1)]),
                &tdata("Pair", vec![Term::TVar(0), Term::TVar(1)]),
                session,
            ));
        });
    }

    #[test]
    fn bound_variables_are_reflexive() {
        crate::cubical::session::with_session_mut(|session| {
            // TVar(i) <= TVar(i) — required for recursion through dependent
            // codomains to succeed.
            assert_sub("∀ (x : U0), x -> x", "∀ (x : U0), x -> x", session);
            // A variable is not a subtype of a different term (here: U1).
            assert_not_sub("∀ (x : U0), x -> U1", "∀ (x : U0), x -> x", session);
            // Nor is a datatype a subtype of a universe (built directly, since
            // `Nat` is not registered in the standalone `parse_term` parser).
            // `∀ (x : U0), x -> Nat` vs `∀ (x : U0), x -> U1`.
            let pi_x_to = |cod: Term| {
                Term::TPi(
                    "x".into(),
                    Arc::new(Term::TUniv(LevelExpr::LConst(0))),
                    Arc::new(Term::TPi(
                        String::new(),
                        Arc::new(Term::TVar(1)),
                        Arc::new(cod),
                        false,
                    )),
                    false,
                )
            };
            assert!(!sub_t(
                &pi_x_to(t_univ(1)),
                &pi_x_to(tdata("Nat", vec![])),
                session
            ));
        });
    }

    #[test]
    fn path_and_partial_cumulativity() {
        crate::cubical::session::with_session_mut(|session| {
            // Path type component covariant (constant family).
            assert_sub("Path U1 i0 i0", "Path U0 i0 i0", session);
            // Partial: same (bottom) cofibration, body covariant.
            // The top face `i1` is avoided here: nbe_eval collapses `[_ | i1] A`
            // to `A` before the check runs, so the test would compare a `TPartial`
            // against a bare type instead of exercising the TPartial rule.
            assert_sub("[_ | i0] U1", "[_ | i0] U0", session);
            // Negative: body is covariant, not contravariant.
            assert_not_sub("[_ | i0] U0", "[_ | i0] U1", session);
        });
    }

    #[test]
    fn lift_and_lower_cumulativity() {
        crate::cubical::session::with_session_mut(|session| {
            assert!(sub_t(
                &Term::TLift(Arc::new(t_univ(1)), LevelExpr::LConst(1)),
                &Term::TLift(Arc::new(t_univ(0)), LevelExpr::LConst(1)),
                session,
            ));
            assert!(sub_t(
                &Term::TLower(Arc::new(t_univ(1))),
                &Term::TLower(Arc::new(t_univ(0))),
                session,
            ));
            assert!(!sub_t(
                &Term::TLift(Arc::new(t_univ(0)), LevelExpr::LConst(1)),
                &Term::TLift(Arc::new(t_univ(1)), LevelExpr::LConst(1)),
                session,
            ));
        });
    }
}
