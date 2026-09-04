// Face-restriction helpers for the typechecker.
//
// Handles substitution of DNF literals into terms, boundary checking
// for face conditions, and evaluation of eliminator face cases.

use std::collections::BTreeSet;
use std::sync::Arc;

use crate::cubical::interval::{DNF, I, Literal};
use crate::cubical::nbe::nbe_eval;
use crate::cubical::session::Session;
use crate::cubical::syntax::{ElimCase, Term, beta, shift};

use super::context::Ctx;
use super::errors::TypeError;
use super::require_equal_endpt;

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
                            path_app_interval: c.path_app_interval.clone(),
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
pub fn strip_n_plams(t: &Term, n: usize) -> Result<&Term, ()> {
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
pub fn check_faces(
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

pub fn shift_cases(cases: &[ElimCase], d: i32) -> Vec<ElimCase> {
    cases
        .iter()
        .map(|case| ElimCase {
            con: case.con.clone(),
            binders: case.binders.clone(),
            body: Box::new(shift(d, case.binders.len() as i32, &case.body)),
            as_name: case.as_name.clone(),
            record_bindings: case.record_bindings.clone(),
            refinements: case.refinements.clone(),
            path_app_interval: case.path_app_interval.clone(),
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
pub fn eval_elim_face(
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
