// Cubical TypeChecker — Rust port of typechecker.hs
//
// Depends on:
//   crate::interval::{I, DNF, Literal}
//   crate::syntax::{Term, Name, Level, shift, subst, beta, show_term}
//   crate::eval::{is_top_dnf, is_bot_dnf}
//   crate::equality::{definitionally_equal_ctx, definitionally_equal_ctx_r, EtaResult}

use std::sync::Arc;

pub mod context;
pub mod cumulativity;
pub mod errors;
pub mod face;
pub mod implicit;
pub mod params;
pub mod reduce;
pub mod termination;

pub use context::{Ctx, err_names, extend_ctx, interval_ty, lookup_ctx};
pub use cumulativity::cumulativity_check;
pub use errors::{TypeError, err_pos};
pub use face::{apply_literal, check_faces, eval_elim_face, strip_n_plams};
pub use implicit::{fill_implicit_args, find_implicit_arg};
pub use params::{build_params, infer_and_check_params, infer_and_check_params_seeded};
pub use reduce::reduce_pcon_endpoints_dt;

use crate::cubical::equality::{EtaResult, definitionally_equal_ctx_r};
use crate::cubical::interval::{I, Literal};
use crate::cubical::nbe::{nbe_eval, nbe_eval_ctx};
use crate::cubical::session::Session;
use crate::cubical::syntax::{
    Datatype, ElimCase, LevelExpr, Name, Term, beta, shift, show_term, subst,
};
use crate::cubical::syntax::{is_bot_dnf, is_top_dnf};

// ---------------------------------------------------------------------------
// Require helpers (used by infer_dt_inner / check_dt_inner)
// ---------------------------------------------------------------------------

/// Look up a name in the context and return its de Bruijn index.
/// The context is ordered with locals first, then globals (newest-first).
/// De Bruijn index = position in the context list.
fn lookup_ctx_index(name: &str, ctx: &Ctx) -> i32 {
    for (i, (n, _)) in ctx.iter().enumerate() {
        if n == name {
            return i as i32;
        }
    }
    0
}

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

pub(crate) fn require_universe_dt(
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

pub(crate) fn type_level_dt(
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

pub(crate) fn check_interval_dt(
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

pub(crate) fn require_equiv_dt(
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
        Term::TJ(motive, base, p) => {
            let p_ty = infer_dt(dts, ctx, p, session)?;
            let (a_ty, x_val, y_val) = match nbe_eval_ctx(ctx.len(), &p_ty, session) {
                Term::TId(a, x, y) => (a, x, y),
                other => {
                    return Err(TypeError::ExpectedPath {
                        ty: other,
                        names: err_names(ctx),
                        pos: err_pos(ctx, p, session),
                    });
                }
            };
            match motive.as_ref() {
                Term::TAbs(y_name, body) => {
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
            let base_expected = nbe_eval_ctx(
                ctx.len(),
                &Term::TApp(motive.clone(), x_val.clone()),
                session,
            );
            check_dt(dts, ctx, base, &base_expected, session)?;
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
                Term::PLam(i, body) => {
                    let path = match body.as_ref() {
                        Term::PApp(path, _) => path.as_ref().clone(),
                        _ => body.as_ref().clone(),
                    };
                    let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
                    let path_ty = nbe_eval(&infer_dt(dts, &ctx2, &path, session)?, session);
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
            let ctx_a = extend_ctx("i_transp".to_string(), Term::TIntervalTy, ctx);
            let _a_body_ty = infer_dt(dts, &ctx_a, a, session)?;
            let r_ty = infer_dt(dts, ctx, r, session)?;
            check_interval_dt(dts, ctx, &r_ty, session)?;
            let x_ty = nbe_eval(
                &Term::TApp(Arc::new(shift(1, 0, a)), Arc::new(Term::TInterval(I::I0))),
                session,
            );
            check_dt(dts, ctx, x, &x_ty, session)?;
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
        Term::TPartial(phi, a) => {
            check_interval_dt(dts, ctx, phi, session)?;
            let n = type_level_dt(dts, ctx, a, session)?;
            Ok(Term::TUniv(n.clone()))
        }

        // System type: [phi => A, psi => B] — partial type families
        Term::TSystemType(sys) => {
            let mut level = LevelExpr::LConst(0);
            for (phi, a) in sys {
                check_interval_dt(dts, ctx, phi, session)?;
                let n = type_level_dt(dts, ctx, a, session)?;
                level = LevelExpr::max(level, n);
            }
            for i in 0..sys.len() {
                for j in (i + 1)..sys.len() {
                    let phi_i = nbe_eval(&sys[i].0, session);
                    let psi_j = nbe_eval(&sys[j].0, session);
                    let overlap = crate::cubical::interval::dnf_meet(
                        &cumulativity::term_to_dnf(&phi_i, session),
                        &cumulativity::term_to_dnf(&psi_j, session),
                    );
                    if overlap != crate::cubical::interval::dnf_bot() {
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
                                        let mut result = raw_ty.clone();
                                        let n = params.len() as i32;
                                        for (i, param_val) in params.iter().enumerate() {
                                            let db_idx = n - 1 - (i as i32);
                                            result = subst(db_idx, param_val, &result);
                                        }
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
        Term::TData(d, args) => {
            let dt =
                dts.iter()
                    .find(|dt| &dt.name == d)
                    .ok_or_else(|| TypeError::UnknownDatatype {
                        name: d.clone(),
                        pos: err_pos(ctx, t, session),
                    })?;
            if args.len() >= dt.params.len() {
                if let Some(level) = dt.universe_level.clone() {
                    return Ok(Term::TUniv(level));
                }
            }
            let num_params = dt.params.len();
            let mut max_level: LevelExpr = LevelExpr::LConst(0);
            for con_sig in &dt.cons {
                let mut tel_ctx = ctx.clone();
                let mut prev_args: Vec<Term> = Vec::new();
                for (k, arg_ty) in con_sig.arg_tys.iter().enumerate() {
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
                    if dt.field_names.is_none() {
                        let var_name = format!("_con_arg_{}", k);
                        let depth = k as i32;
                        prev_args.push(shift(depth + 1, 0, &Term::TVar(0)));
                        tel_ctx = extend_ctx(var_name, nbe_eval(&arg_ty_inst, session), &tel_ctx);
                    }
                }
            }
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
            if args.len() >= dt.params.len() {
                Ok(Term::TUniv(max_level))
            } else {
                let provided = args.len();
                let remaining = &dt.params[provided..];
                let mut result = Term::TUniv(max_level);
                let mut offset = remaining.len() as i32;
                for (_i, (pname, pty)) in remaining.iter().enumerate().rev() {
                    let shifted_pty = shift(offset, 0, pty);
                    result = Term::TPi(
                        pname.clone(),
                        Arc::new(shifted_pty),
                        Arc::new(result),
                        false,
                    );
                    offset -= 1;
                }
                let mut final_result = result;
                for (_i, arg) in args.iter().enumerate().rev() {
                    final_result = beta(&final_result, arg);
                }
                let final_result = shift(-(provided as i32), 0, &final_result);
                Ok(final_result)
            }
        }

        Term::TCon(d, c, args) => {
            let dt =
                dts.iter()
                    .find(|dt| &dt.name == d)
                    .ok_or_else(|| TypeError::UnknownDatatype {
                        name: d.clone(),
                        pos: err_pos(ctx, t, session),
                    })?;
            if let Some(sig) = dt.find_con(c) {
                let num_params = dt.params.len();
                let (param_terms, _checked_args) =
                    infer_and_check_params(dts, ctx, &sig.arg_tys, args, num_params, session)?;
                let params = build_params(&param_terms);
                Ok(Term::TData(d.clone(), params))
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
            check_interval(ctx, r, session)?;
            let params = build_params(&param_terms);
            Ok(Term::TData(d.clone(), params))
        }

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
            if is_endpoint(r) {
                return Ok(Term::TPath(
                    Arc::new(Term::PLam("j".to_string(), Arc::new(data_ty))),
                    Arc::new(face_i0_subst),
                    Arc::new(face_i1_subst),
                ));
            }
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
            for iv in ivars {
                check_interval(ctx, iv, session)?;
            }
            let params = build_params(&param_terms);
            let data_ty = Term::TData(d.clone(), params.clone());
            if dim == 0 {
                return Ok(data_ty);
            }
            let arity = sig.arity();
            let subst_face = |face: &Term| -> Term {
                let mut t = face.clone();
                for k in (0..arity).rev() {
                    t = subst(k as i32, &checked_args[arity - 1 - k], &t);
                }
                t
            };
            let substituted_faces: Vec<Term> = sig.faces.iter().map(|f| subst_face(f)).collect();
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
            let ivar_names: Vec<String> = (0..dim).map(|k| format!("_i{}", k + 1)).collect();
            let mut result_type = Term::TPath(
                Arc::new(Term::PLam(ivar_names[0].clone(), Arc::new(data_ty))),
                Arc::new(substituted_faces[0].clone()),
                Arc::new(substituted_faces[1].clone()),
            );
            for k in 1..dim {
                let body = result_type;
                result_type = Term::TPath(
                    Arc::new(Term::PLam(ivar_names[k].clone(), Arc::new(body))),
                    Arc::new(substituted_faces[2 * k].clone()),
                    Arc::new(substituted_faces[2 * k + 1].clone()),
                );
            }
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

        // TElim — the large eliminator checking block
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

            // Desugar record patterns
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
                                path_app_interval: None,
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

            // Verify motive
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
            fn subst_params_local(arg_tys: &[Term], params: &[Term]) -> Vec<Term> {
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

            fn subst_params_face_local(
                face: &Term,
                params: &[Term],
                num_args: usize,
                _session: &mut Session,
            ) -> Term {
                let mut t = face.clone();
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
                let subst_arg_tys = subst_params_local(&con_sig.arg_tys, &scrut_params);
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
                let mut case_ctx = ctx.clone();
                let mut con_args_in_ctx: Vec<Term> = Vec::new();
                for (k, binder_name) in case.binders.iter().enumerate() {
                    let mut arg_ty = shift(k as i32, 0, &subst_arg_tys[k]);
                    for a in con_args_in_ctx.iter().rev() {
                        arg_ty = subst(0, a, &arg_ty);
                    }
                    let arg_ty_ev = nbe_eval(&arg_ty, session);
                    let depth = k as i32;
                    con_args_in_ctx.push(shift(depth + 1, 0, &Term::TVar(0)));
                    case_ctx = extend_ctx(binder_name.clone(), arg_ty_ev, &case_ctx);
                }
                let extra_shift = if case.as_name.is_some() { 1i32 } else { 0i32 };
                if let Some(ref as_n) = case.as_name {
                    let as_ty = nbe_eval(&Term::TData(d.clone(), scrut_params.clone()), session);
                    case_ctx = extend_ctx(as_n.clone(), as_ty, &case_ctx);
                }
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
                let subst_arg_tys = subst_params_local(&pcon_sig.arg_tys, &scrut_params);
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
                let face0_subst =
                    subst_params_face_local(&pcon_sig.face0, &scrut_params, arity, session);
                let face1_subst =
                    subst_params_face_local(&pcon_sig.face1, &scrut_params, arity, session);
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
                let subst_arg_tys = subst_params_local(&sqcon_sig.arg_tys, &scrut_params);
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
                    subst_params_face_local(&sqcon_sig.face_i0, &scrut_params, arity_sq, session);
                let face_i1_subst =
                    subst_params_face_local(&sqcon_sig.face_i1, &scrut_params, arity_sq, session);
                let face_j0_subst =
                    subst_params_face_local(&sqcon_sig.face_j0, &scrut_params, arity_sq, session);
                let face_j1_subst =
                    subst_params_face_local(&sqcon_sig.face_j1, &scrut_params, arity_sq, session);
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

                if let Term::PLam(_, inner_box) = case.body.as_ref() {
                    if let Term::PLam(_, inner) = inner_box.as_ref() {
                        let body_r0_s0 = {
                            let t = apply_literal(&Literal::NegVar(1), inner, session);
                            let t = apply_literal(&Literal::NegVar(0), &t, session);
                            nbe_eval(
                                &shift(-2, 0, &reduce_pcon_endpoints_dt(dts, &t, session)),
                                session,
                            )
                        };
                        let body_r0_s1 = {
                            let t = apply_literal(&Literal::NegVar(1), inner, session);
                            let t = apply_literal(&Literal::Pos(0), &t, session);
                            nbe_eval(
                                &shift(-2, 0, &reduce_pcon_endpoints_dt(dts, &t, session)),
                                session,
                            )
                        };
                        let body_r1_s0 = {
                            let t = apply_literal(&Literal::Pos(1), inner, session);
                            let t = apply_literal(&Literal::NegVar(0), &t, session);
                            nbe_eval(
                                &shift(-2, 0, &reduce_pcon_endpoints_dt(dts, &t, session)),
                                session,
                            )
                        };
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
                let subst_arg_tys = subst_params_local(&cellcon_sig.arg_tys, &scrut_params);
                let dim = cellcon_sig.dimension();
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
                for iv_name in ivar_names.iter().rev() {
                    case_ctx_cell = extend_ctx(iv_name.to_string(), interval_ty(), &case_ctx_cell);
                }
                let ord_var_no_ivars: Vec<Term> = (0..arity_cell)
                    .map(|k| Term::TVar((arity_cell - 1 - k) as i32))
                    .collect();
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
                let substituted_faces: Vec<Term> = cellcon_sig
                    .faces
                    .iter()
                    .map(|f| subst_params_face_local(f, &scrut_params, arity_cell, session))
                    .collect();
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
                let mut expected_body_ty = Term::TPath(
                    Arc::new(Term::PLam(
                        ivar_names[0].to_string(),
                        Arc::new(motive_at_cellcon),
                    )),
                    Arc::new(shift(1, 0, &face_cases[0])),
                    Arc::new(shift(1, 0, &face_cases[1])),
                );
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

                // Boundary coherence for cellcon cases
                for k in 0..dim {
                    let face_idx = 2 * (dim - 1 - k);
                    let strip_count = k + 1;
                    let keep_count = dim - strip_count;
                    if let Ok(inner_at_k) = strip_n_plams(&case.body, strip_count) {
                        let mut t_i0 = inner_at_k.clone();
                        for v in (keep_count + 1)..dim {
                            t_i0 = apply_literal(
                                &Literal::NegVar((v - keep_count) as i32),
                                &t_i0,
                                session,
                            );
                        }
                        t_i0 = apply_literal(&Literal::NegVar(0), &t_i0, session);
                        let at_i0 = nbe_eval(
                            &shift(
                                -(strip_count as i32),
                                0,
                                &reduce_pcon_endpoints_dt(dts, &t_i0, session),
                            ),
                            session,
                        );
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
            Ok(nbe_eval(
                &Term::TApp(motive.clone(), scrut.clone()),
                session,
            ))
        }

        // -- Coinduction ---------------------------------------------------------
        Term::TDelay(a) => {
            let a_ty = infer_dt(dts, ctx, a, session)?;
            Ok(a_ty)
        }
        Term::TNext(a) => {
            let a_ty = infer_dt(dts, ctx, a, session)?;
            Ok(Term::TDelay(Arc::new(a_ty)))
        }
        Term::TForce(a) => {
            let delay_ty = infer_dt(dts, ctx, a, session)?;
            match nbe_eval(&delay_ty, session) {
                Term::TDelay(b) => Ok(b.as_ref().clone()),
                other => Err(TypeError::Other(format!(
                    "Force expects a Delay type, but got: {}",
                    other
                ))),
            }
        }

        // Reflection (E1): quote t : Term
        Term::TQuote(t) => {
            let _ty = infer_dt(dts, ctx, t, session)?;
            Ok(Term::TVar(lookup_ctx_index("OwlTerm", ctx)))
        }

        Term::TUnquote(_ast) => Err(TypeError::Other(
            "unquote requires a type annotation: use (unquote ast : A) or let x : A := unquote ast"
                .to_string(),
        )),

        Term::TGetContext => match session.reflection_ctx() {
            Some(_ctx) => Ok(Term::TVar(lookup_ctx_index("OwlTerm", ctx))),
            None => Err(TypeError::Other(
                "getContext: no reflection context in session".to_string(),
            )),
        },

        Term::TGetType(t) => {
            let ty = infer_dt(dts, ctx, t, session)?;
            let ty_normalized = nbe_eval(&ty, session);
            session.store_reflection_result(t.as_ref().clone(), ty_normalized);
            Ok(Term::TVar(lookup_ctx_index("OwlTerm", ctx)))
        }

        Term::TUnify(a, bx) => {
            let a_ty = infer_dt(dts, ctx, a, session)?;
            let bx_ty = infer_dt(dts, ctx, bx, session)?;
            let eq = definitionally_equal_ctx_r(ctx, &a_ty, &bx_ty, session);
            match eq {
                crate::cubical::equality::EtaResult::Equal => {
                    Ok(Term::TData("Unit".to_string(), vec![]))
                }
                _ => Err(TypeError::Other(format!(
                    "unify: terms are not definitionally equal"
                ))),
            }
        }
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
                Term::PLam(_, b) => nbe_eval_ctx(ctx2.len(), &beta(&b, &Term::TVar(0)), session),
                plain => shift(1, 0, &plain),
            };
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
                    let cap_ty = match &**t_inner {
                        Term::TAbs(_, _) => {
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

        // Constructor introduction
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
                // For zero-arity constructors with index constraints, verify
                // that the constructor's return-type constraints are consistent
                // with the expected type. Without this, refl : Eq A x x is
                // accepted against Eq Nat zero (suc zero) because the check is
                // circular (params are seeded from expected, then compared).
                //
                // We only apply this check when the return_args contain a
                // repeated de Bruijn variable at index positions — this
                // indicates the constructor constrains those indices to be
                // equal (like refl: Eq A x x where both indices reference x).
                // Constructors without repeated vars (like nil: Vec A zero)
                // have fixed indices that don't create this circularity.
                if args.is_empty() {
                    if let Some(ref return_args) = sig.return_args {
                        // Check if any de Bruijn var appears more than once
                        // in the return_args (skipping position 0 which is
                        // typically the type param).
                        let mut seen_vars: std::collections::HashSet<i32> =
                            std::collections::HashSet::new();
                        let mut has_repeated = false;
                        for ra in return_args.iter().skip(1) {
                            if let Term::TVar(k) = ra {
                                if !seen_vars.insert(*k) {
                                    has_repeated = true;
                                    break;
                                }
                            }
                        }
                        if has_repeated {
                            let substituted: Vec<Term> = return_args
                                .iter()
                                .map(|arg| {
                                    crate::cubical::syntax::subst_params(
                                        num_params,
                                        &param_terms,
                                        arg,
                                    )
                                })
                                .collect();
                            let inferred_ty = Term::TData(d.clone(), substituted);
                            return require_equal(ctx, &expected_ty_nf, &inferred_ty, session);
                        }
                    }
                }
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

        // Tactic block
        Term::TBy(tactics) => {
            let goal_ty = nbe_eval(ty, session);
            let mut engine =
                crate::cubical::tactics::TacticEngine::new(dts, goal_ty.clone(), goal_ty);
            for tac in tactics {
                engine.run_tactic(tac, ctx, session)?;
            }
            let proof = engine.into_term(session)?;
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

        // Kan operations
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

        Term::Meta(id) => {
            let expected_nf = nbe_eval(ty, session);
            session.set_meta_expected(*id, expected_nf.clone());
            let _ = type_level_dt(dts, ctx, ty, session)?;
            Ok(())
        }

        Term::TRefl(x) => match nbe_eval_ctx(ctx.len(), ty, session) {
            Term::TId(a, _exp_x, _exp_y) => {
                check_dt(dts, ctx, x, &nbe_eval_ctx(ctx.len(), &a, session), session)?;
                Ok(())
            }
            other => {
                return Err(TypeError::Other(format!(
                    "Refl must be checked against Id type, got {}",
                    show_term(&names, &other)
                )));
            }
        },

        Term::TJ(_, _, _) => {
            let inferred = infer_dt(dts, ctx, t, session)?;
            require_equal(
                ctx,
                &nbe_eval_ctx(ctx.len(), ty, session),
                &nbe_eval_ctx(ctx.len(), &inferred, session),
                session,
            )
        }

        Term::TUnquote(ast) => {
            let term_ty = Term::TData("OwlTerm".to_string(), Vec::new());
            check_dt(dts, ctx, ast, &term_ty, session)?;
            let ast_val = nbe_eval(ast, session);
            match ast_val {
                Term::TData(name, _) if name == "OwlTerm" => Ok(()),
                _ => check_dt(dts, ctx, &ast_val, ty, session),
            }
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
// Square constructor coherence check
// ---------------------------------------------------------------------------

/// Check boundary coherence for all square constructors in a datatype.
pub fn check_sqcon_coherence(
    dts: &[Datatype],
    dt: &Datatype,
    session: &mut Session,
) -> Result<(), TypeError> {
    use crate::cubical::interval::{I, dnf_bot};
    for sqcon in &dt.sqcons {
        let i0 = Term::TInterval(I::I0);
        let i1 = Term::TInterval(I::I1);
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

// ---------------------------------------------------------------------------
// Top-level helpers
// ---------------------------------------------------------------------------

pub fn check_closed_dt(
    dts: &[Datatype],
    t: &Term,
    ty: &Term,
    session: &mut Session,
) -> Result<(), TypeError> {
    check_dt(dts, &Vec::new(), t, ty, session)
}

#[allow(dead_code)]
pub fn infer_closed_dt(
    dts: &[Datatype],
    t: &Term,
    session: &mut Session,
) -> Result<Term, TypeError> {
    infer_dt(dts, &Vec::new(), t, session)
}

#[allow(dead_code)]
pub fn infer_closed(t: &Term, session: &mut Session) -> Result<Term, TypeError> {
    infer(&Vec::new(), t, session)
}

#[allow(dead_code)]
pub fn check_closed(t: &Term, ty: &Term, session: &mut Session) -> Result<(), TypeError> {
    check(&Vec::new(), t, ty, session)
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
