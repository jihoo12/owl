// Cubical TypeChecker — Rust port of typechecker.hs
//
// Depends on:
//   crate::interval::{I, DNF, Literal}
//   crate::syntax::{Term, Name, Level, shift, subst, beta, show_term}
//   crate::eval::{is_top_dnf, is_bot_dnf}
//   crate::equality::{definitionally_equal_ctx, definitionally_equal_ctx_r, EtaResult}

use std::collections::BTreeSet;

mod errors;
pub use errors::TypeError;

use crate::cubical::equality::{EtaResult, definitionally_equal_ctx_r};
use crate::cubical::syntax::{is_bot_dnf, is_top_dnf};
use crate::cubical::interval::{DNF, I, Literal};
use crate::cubical::nbe::nbe_eval;
use crate::cubical::syntax::{Datatype, ElimCase, Level, Name, Term, beta, shift, show_term, subst};

use std::cell::Cell;

// Thread-local flag: when true, skip PLam boundary checks in check_dt.
// This is needed for HIT case bodies where the constructor variable is free
// and can't reduce — the boundary conditions are already encoded in the
// expected body type.
thread_local! {
    static SKIP_PLAM_ENDPT: Cell<bool> = Cell::new(false);
}

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
        Ok(nbe_eval(&shift(i + 1, 0, &ctx[i as usize].1)))
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
fn infer_via_reduction(dts: &[Datatype], ctx: &Ctx, t: &Term, original_err: TypeError) -> Result<Term, TypeError> {
    let reduced = nbe_eval(t);
    if reduced == *t {
        Err(original_err)
    } else {
        infer_dt(dts, ctx, &reduced)
    }
}

// ---------------------------------------------------------------------------
// Require helpers
// ---------------------------------------------------------------------------

pub fn require_equal(ctx: &Ctx, expected: &Term, got: &Term) -> Result<(), TypeError> {
    let names: Vec<Name> = ctx.iter().map(|(n, _)| n.clone()).collect();
    crate::debug_log!("require_equal: {} == {}", show_term(&names, expected), show_term(&names, got));
    match definitionally_equal_ctx_r(ctx, expected, got) {
        EtaResult::Equal => Ok(()),
        EtaResult::NotEqual => Err(TypeError::TypeMismatch(
            Box::new(nbe_eval(expected)),
            Box::new(nbe_eval(got)),
        )),
        EtaResult::Exhausted => Err(TypeError::EtaFuelExhausted(
            Box::new(nbe_eval(expected)),
            Box::new(nbe_eval(got)),
        )),
    }
}

pub fn require_equal_endpt(ctx: &Ctx, expected: &Term, got: &Term) -> Result<(), TypeError> {
    match definitionally_equal_ctx_r(ctx, expected, got) {
        EtaResult::Equal => Ok(()),
        EtaResult::NotEqual => {
            let names: Vec<Name> = ctx.iter().map(|(n, _)| n.clone()).collect();
            Err(TypeError::Other(format!(
                "endpoint mismatch (ctx_depth={}, ctx={:?})\
                 \n  expected={}  [raw={}]\
                 \n  got={}  [raw={}]",
                ctx.len(),
                ctx.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
                show_term(&names, &nbe_eval(expected)),
                nbe_eval(expected),
                show_term(&names, &nbe_eval(got)),
                nbe_eval(got),
            )))
        }
        EtaResult::Exhausted => Err(TypeError::EtaFuelExhausted(
            Box::new(nbe_eval(expected)),
            Box::new(nbe_eval(got)),
        )),
    }
}

#[allow(dead_code)]
pub fn require_universe(ctx: &Ctx, t: &Term) -> Result<Level, TypeError> {
    require_universe_dt(&[], ctx, t)
}

#[allow(dead_code)]
fn require_universe_dt(dts: &[Datatype], ctx: &Ctx, t: &Term) -> Result<Level, TypeError> {
    let ty = infer_dt(dts, ctx, t)?;
    match nbe_eval(&ty) {
        Term::TUniv(n) => Ok(n),
        other => Err(TypeError::ExpectedUniverse(other)),
    }
}

fn type_level_dt(dts: &[Datatype], ctx: &Ctx, t: &Term) -> Result<Level, TypeError> {
    // Match type formers structurally first. `nbe_eval` on a Π-type that still
    // mentions outer binders can collapse free de Bruijn indices and break
    // universe-level checking for dependent arrows like `(A : U0) -> A -> A`.
    match t {
        Term::TPi(x, a, b) => {
            let i = type_level_dt(dts, ctx, a)?;
            let ctx2 = extend_ctx(x.clone(), nbe_eval(a), ctx);
            let j = type_level_dt(dts, &ctx2, b)?;
            Ok(i.max(j))
        }
        Term::TPath(a, u, v) => {
            // For PathP-style dependent paths, a may be a PLam (type family).
            // In that case, check that the body of the PLam is well-typed,
            // and verify endpoints against the instantiated family.
            let n = match nbe_eval(a) {
                Term::PLam(_, body) => {
                    // The type family body should be well-typed in a context
                    // with an interval variable. We check that the family
                    // returns values in some universe by checking at i0.
                    let ctx2 = extend_ctx("_i".to_string(), interval_ty(), ctx);
                    let a_at0 = nbe_eval(&beta(&body, &Term::TInterval(I::I0)));
                    type_level_dt(dts, &ctx2, &a_at0)?
                }
                _ => type_level_dt(dts, ctx, a)?,
            };
            let a_ = nbe_eval(a);
            let u_ty = match &a_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I0))),
                p => p.clone(),
            };
            let v_ty = match &a_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I1))),
                p => p.clone(),
            };
            check_dt(dts, ctx, u, &u_ty)?;
            check_dt(dts, ctx, v, &v_ty)?;
            Ok(n)
        }
        Term::TEquiv(a, b) => {
            let n = type_level_dt(dts, ctx, a)?;
            let m = type_level_dt(dts, ctx, b)?;
            Ok(n.max(m))
        }
        Term::TSigma(x, a, b) => {
            let i = type_level_dt(dts, ctx, a)?;
            let ctx2 = extend_ctx(x.clone(), nbe_eval(a), ctx);
            let j = type_level_dt(dts, &ctx2, b)?;
            Ok(i.max(j))
        }
        _ => match nbe_eval(t) {
            Term::TUniv(n) => Ok(n),
            Term::TData(d, _) => {
                let level = dts.iter()
                    .find(|dt| dt.name == d)
                    .and_then(|dt| dt.universe_level)
                    .unwrap_or(0);
                Ok(level)
            }
            Term::TIntervalTy => Ok(0),
            _ => {
                let ty = infer_dt(dts, ctx, t)?;
                match nbe_eval(&ty) {
                    Term::TUniv(n) => Ok(n),
                    other => Err(TypeError::ExpectedUniverse(other)),
                }
            }
        },
    }
}

pub fn check_interval(ctx: &Ctx, t: &Term) -> Result<(), TypeError> {
    check_interval_dt(&[], ctx, t)
}

fn check_interval_dt(dts: &[Datatype], ctx: &Ctx, t: &Term) -> Result<(), TypeError> {
    match t {
        Term::TInterval(_) | Term::TCube(_) => return Ok(()),
        _ => {}
    }
    let ty = infer_dt(dts, ctx, t)?;
    if ty == interval_ty() {
        Ok(())
    } else {
        Err(TypeError::NotAnInterval(t.clone()))
    }
}

#[allow(dead_code)]
pub fn require_equiv(ctx: &Ctx, t: &Term) -> Result<(Term, Term), TypeError> {
    require_equiv_dt(&[], ctx, t)
}

fn require_equiv_dt(dts: &[Datatype], ctx: &Ctx, t: &Term) -> Result<(Term, Term), TypeError> {
    let ty = infer_dt(dts, ctx, t)?;
    match nbe_eval(&ty) {
        Term::TEquiv(a, b) => Ok((nbe_eval(&a), nbe_eval(&b))),
        other => Err(TypeError::ExpectedEquiv(other)),
    }
}

// ---------------------------------------------------------------------------
// Face-restriction helpers
// ---------------------------------------------------------------------------

/// Apply a single DNF literal as a substitution on a term.
/// `Pos n`    → iₙ = 1   (IVar n ↦ I1)
/// `NegVar n` → iₙ = 0   (IVar n ↦ I0)
pub fn apply_literal(lit: &Literal, t: &Term) -> Term {
    let (n, val) = match lit {
        Literal::Pos(k) => (*k, I::I1),
        Literal::NegVar(k) => (*k, I::I0),
    };

    fn go_i(i: &I, n: i32, val: &I) -> I {
        match i {
            I::Var(k) if *k == n => val.clone(),
            I::Meet(a, b) => I::Meet(Box::new(go_i(a, n, val)), Box::new(go_i(b, n, val))),
            I::Join(a, b) => I::Join(Box::new(go_i(a, n, val)), Box::new(go_i(b, n, val))),
            I::Neg(a) => I::Neg(Box::new(go_i(a, n, val))),
            other => other.clone(),
        }
    }

    fn go(t: &Term, n: i32, val: &I) -> Term {
        match t {
            Term::TInterval(i) => nbe_eval(&Term::TInterval(go_i(i, n, val))),

            Term::TCube(DNF { cubes }) => {
                // Substitute the literal into each cube then re-normalise.
                let subst_lit = |l: &Literal| -> I {
                    match l {
                        Literal::Pos(k) => go_i(&I::Var(*k), n, val),
                        Literal::NegVar(k) => I::Neg(Box::new(go_i(&I::Var(*k), n, val))),
                    }
                };
                let subst_cube = |c: &BTreeSet<Literal>| -> I {
                    c.iter().fold(I::I1, |acc, l| {
                        I::Meet(Box::new(subst_lit(l)), Box::new(acc))
                    })
                };
                let combined = cubes.iter().fold(I::I0, |acc, c| {
                    I::Join(Box::new(subst_cube(c)), Box::new(acc))
                });
                nbe_eval(&Term::TInterval(combined))
            }

            Term::TApp(f, a) => nbe_eval(&Term::TApp(
                Box::new(go(f, n, val)),
                Box::new(go(a, n, val)),
            )),
            Term::TAbs(x, b) => Term::TAbs(x.clone(), Box::new(go(b, n, val))),
            Term::TPi(x, a, b) => {
                Term::TPi(x.clone(), Box::new(go(a, n, val)), Box::new(go(b, n, val)))
            }
            Term::TPath(a, u, v) => Term::TPath(
                Box::new(go(a, n, val)),
                Box::new(go(u, n, val)),
                Box::new(go(v, n, val)),
            ),
            Term::PLam(i, b) => Term::PLam(i.clone(), Box::new(go(b, n + 1, val))),
            Term::PApp(p, r) => nbe_eval(&Term::PApp(
                Box::new(go(p, n, val)),
                Box::new(go(r, n, val)),
            )),
            Term::THComp(a, sys, u0) => nbe_eval(&Term::THComp(
                Box::new(go(a, n, val)),
                sys.iter().map(|(phi, t)| (go(phi, n, val), go(t, n, val))).collect(),
                Box::new(go(u0, n, val)),
            )),
            Term::TComp(a, sys, u0) => nbe_eval(&Term::TComp(
                Box::new(go(a, n, val)),
                sys.iter().map(|(phi, t)| (go(phi, n, val), go(t, n, val))).collect(),
                Box::new(go(u0, n, val)),
            )),
            Term::TFill(a, sys, u0) => nbe_eval(&Term::TFill(
                Box::new(go(a, n, val)),
                sys.iter().map(|(phi, t)| (go(phi, n, val), go(t, n, val))).collect(),
                Box::new(go(u0, n, val)),
            )),
            Term::THFill(a, sys, u0) => nbe_eval(&Term::THFill(
                Box::new(go(a, n, val)),
                sys.iter().map(|(phi, t)| (go(phi, n, val), go(t, n, val))).collect(),
                Box::new(go(u0, n, val)),
            )),
            Term::TEquiv(a, b) => Term::TEquiv(Box::new(go(a, n, val)), Box::new(go(b, n, val))),
            Term::TMkEquiv(a, b, f, g, eta, eps) => Term::TMkEquiv(
                Box::new(go(a, n, val)),
                Box::new(go(b, n, val)),
                Box::new(go(f, n, val)),
                Box::new(go(g, n, val)),
                Box::new(go(eta, n, val)),
                Box::new(go(eps, n, val)),
            ),
            Term::TEquivFwd(e, x) => nbe_eval(&Term::TEquivFwd(
                Box::new(go(e, n, val)),
                Box::new(go(x, n, val)),
            )),
            Term::TUa(e) => Term::TUa(Box::new(go(e, n, val))),
            Term::TTransport(p, x) => nbe_eval(&Term::TTransport(
                Box::new(go(p, n, val)),
                Box::new(go(x, n, val)),
            )),
            Term::TGlue(a, ph, te) => nbe_eval(&Term::TGlue(
                Box::new(go(a, n, val)),
                Box::new(go(ph, n, val)),
                Box::new(go(te, n, val)),
            )),
            Term::TGlueElem(ph, x, a) => nbe_eval(&Term::TGlueElem(
                Box::new(go(ph, n, val)),
                Box::new(go(x, n, val)),
                Box::new(go(a, n, val)),
            )),
            Term::TUnglue(ph, te, g) => nbe_eval(&Term::TUnglue(
                Box::new(go(ph, n, val)),
                Box::new(go(te, n, val)),
                Box::new(go(g, n, val)),
            )),
            Term::TSigma(x, a, b) => {
                Term::TSigma(x.clone(), Box::new(go(a, n, val)), Box::new(go(b, n, val)))
            }
            Term::TPair(a, b) => Term::TPair(Box::new(go(a, n, val)), Box::new(go(b, n, val))),
            Term::TFst(p) => nbe_eval(&Term::TFst(Box::new(go(p, n, val)))),
            Term::TSnd(p) => nbe_eval(&Term::TSnd(Box::new(go(p, n, val)))),
            // Inductive types / HITs: recurse into all sub-terms.
            Term::TData(d, params) => nbe_eval(&Term::TData(
                d.clone(),
                params.iter().map(|a| go(a, n, val)).collect(),
            )),
            Term::TCon(data, con, args) => nbe_eval(&Term::TCon(
                data.clone(),
                con.clone(),
                args.iter().map(|a| go(a, n, val)).collect(),
            )),
            Term::TPCon(data, con, args, r) => nbe_eval(&Term::TPCon(
                data.clone(),
                con.clone(),
                args.iter().map(|a| go(a, n, val)).collect(),
                Box::new(go(r, n, val)),
            )),
            Term::TSqCon(data, con, args, r, s) => nbe_eval(&Term::TSqCon(
                data.clone(),
                con.clone(),
                args.iter().map(|a| go(a, n, val)).collect(),
                Box::new(go(r, n, val)),
                Box::new(go(s, n, val)),
            )),
            Term::TElim(motive, cases, scrut) => nbe_eval(&Term::TElim(
                Box::new(go(motive, n, val)),
                cases
                    .iter()
                    .map(|c| ElimCase {
                        con: c.con.clone(),
                        binders: c.binders.clone(),
                        body: Box::new(go(&c.body, n, val)),
                    })
                    .collect(),
                Box::new(go(scrut, n, val)),
            )),
            Term::Meta(_) => t.clone(),
            Term::TBy(tactics) => Term::TBy(
                tactics
                    .iter()
                    .map(|tac| match tac {
                        crate::cubical::syntax::Tactic::Exact(t) => {
                            crate::cubical::syntax::Tactic::Exact(go(t, n, val))
                        }
                        other => other.clone(),
                    })
                    .collect(),
            ),
            // TVar, TUniv, TIntervalTy: no interval vars
            other => other.clone(),
        }
    }

    go(t, n, &val)
}

/// Check that `tube_at0 ≡ base` on every face of `phi`'s DNF.
fn check_faces(ctx: &Ctx, phi: &Term, tube_at0: &Term, base: &Term) -> Result<(), TypeError> {
    match phi {
        Term::TCube(DNF { cubes }) => {
            for cube in cubes {
                // Apply all literals in the cube as substitutions.
                let apply_all = |t: &Term| -> Term {
                    cube.iter()
                        .fold(t.clone(), |acc, lit| apply_literal(lit, &acc))
                };
                let lhs = nbe_eval(&apply_all(tube_at0));
                let rhs = nbe_eval(&apply_all(base));
                require_equal_endpt(ctx, &lhs, &rhs)?;
            }
            Ok(())
        }
        // Non-DNF phi: fall back to a direct equality check.
        _ => require_equal_endpt(ctx, tube_at0, base),
    }
}

fn shift_cases(cases: &[ElimCase], d: i32) -> Vec<ElimCase> {
    cases
        .iter()
        .map(|case| ElimCase {
            con: case.con.clone(),
            binders: case.binders.clone(),
            body: Box::new(shift(d, case.binders.len() as i32, &case.body)),
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
            return nbe_eval(&result);
        }
    }

    // Fallback (shouldn't normally be reached): try the old TElim approach.
    nbe_eval(&Term::TElim(
        Box::new(shift(_ambient_depth, 0, _motive)),
        shift_cases(cases, _ambient_depth),
        Box::new(nbe_eval(face)),
    ))
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
) -> Result<(Vec<Option<Term>>, Vec<Term>), TypeError> {
    infer_and_check_params_seeded(dts, ctx, sig_arg_tys, args, num_params, &[])
}

/// Like `infer_and_check_params` but accepts pre-seeded parameter values.
fn infer_and_check_params_seeded(
    dts: &[Datatype],
    ctx: &Ctx,
    sig_arg_tys: &[Term],
    args: &[Term],
    num_params: usize,
    initial_params: &[Option<Term>],
) -> Result<(Vec<Option<Term>>, Vec<Term>), TypeError> {
    debug_assert!(initial_params.len() <= num_params);
    // Phase 1: Infer parameter values from argument types.
    let mut param_terms: Vec<Option<Term>> = initial_params.to_vec();
    param_terms.resize(num_params, None);
    {
        let mut prev_args: Vec<Term> = Vec::new();
        for (k, arg) in args.iter().enumerate() {
            let mut arg_ty = sig_arg_tys[k].clone();
            for i in (0..num_params).rev() {
                if let Some(ref pv) = param_terms[i] {
                    arg_ty = beta(&arg_ty, pv);
                }
            }
            for prev in prev_args.iter().rev() {
                arg_ty = beta(&arg_ty, prev);
            }
            if let Term::TVar(idx) = &arg_ty {
                let i = *idx as usize;
                if i < num_params && param_terms[i].is_none() {
                    param_terms[i] = Some(infer_dt(dts, ctx, arg)?);
                    continue;
                }
            }
            prev_args.push(nbe_eval(arg));
        }
    }
    // Phase 2: Check args with fully-substituted arg_tys.
    let mut checked_args: Vec<Term> = Vec::with_capacity(args.len());
    for (k, arg) in args.iter().enumerate() {
        let mut arg_ty = sig_arg_tys[k].clone();
        for i in (0..num_params).rev() {
            if let Some(ref pv) = param_terms[i] {
                arg_ty = beta(&arg_ty, pv);
            }
        }
        for prev in checked_args.iter().rev() {
            arg_ty = beta(&arg_ty, prev);
        }
        check_dt(dts, ctx, arg, &nbe_eval(&arg_ty))?;
        checked_args.push(nbe_eval(arg));
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
// Type Inference
// ---------------------------------------------------------------------------

pub fn infer(ctx: &Ctx, t: &Term) -> Result<Term, TypeError> {
    infer_dt(&[], ctx, t)
}

/// Like `infer` but with access to declared datatypes for checking
/// `TData`/`TCon`/`TPCon`/`TElim`.  Pass `&[]` when no datatypes are in scope.
pub fn infer_dt(dts: &[Datatype], ctx: &Ctx, t: &Term) -> Result<Term, TypeError> {
    let names: Vec<Name> = ctx.iter().map(|(n, _)| n.clone()).collect();
    crate::debug_scope!("infer {} : ctx[{}]", show_term(&names, t), ctx.len());
    crate::cubical::nbe::set_current_dts(dts);
    match t {
        // Variable
        Term::TVar(i) => lookup_ctx(*i, ctx),

        // Universe: U_n : U_{n+1}
        Term::TUniv(n) => Ok(Term::TUniv(n + 1)),

        // Application: f a  where  f : Π(x:A).B
        Term::TApp(f, a) => match infer_dt(dts, ctx, f) {
            Ok(f_ty) => {
                let (a_ty, b_ty) = match &f_ty {
                    Term::TPi(_, a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                    _ => match nbe_eval(&f_ty) {
                        Term::TPi(_, a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                        other => return Err(TypeError::ExpectedPi(other)),
                    },
                };
                check_dt(dts, ctx, a, &a_ty)?;
                Ok(nbe_eval(&beta(&b_ty, a)))
            }
            Err(e) => infer_via_reduction(dts, ctx, t, e),
        },

        // Pi formation: Π(x:A).B : U(max i j)
        Term::TPi(x, a_ty, b_ty) => {
            let i = type_level_dt(dts, ctx, a_ty)?;
            let ctx2 = extend_ctx(x.clone(), nbe_eval(a_ty), ctx);
            let j = type_level_dt(dts, &ctx2, b_ty)?;
            Ok(Term::TUniv(i.max(j)))
        }

        // Path type: Path A u v : U n
        Term::TPath(a_ty, u, v) => {
            let n = match nbe_eval(a_ty) {
                Term::PLam(_, body) => {
                    let ctx2 = extend_ctx("_i".to_string(), interval_ty(), ctx);
                    let a_at0 = nbe_eval(&beta(&body, &Term::TInterval(I::I0)));
                    type_level_dt(dts, &ctx2, &a_at0)?
                }
                _ => type_level_dt(dts, ctx, a_ty)?,
            };
            let a_ty_ = nbe_eval(a_ty);
            let u_ty = match &a_ty_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I0))),
                p => p.clone(),
            };
            let v_ty = match &a_ty_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I1))),
                p => p.clone(),
            };
            check_dt(dts, ctx, u, &u_ty)?;
            check_dt(dts, ctx, v, &v_ty)?;
            Ok(Term::TUniv(n))
        }

        // Path application: p @ r
        Term::PApp(p, r) => match infer_dt(dts, ctx, p) {
            Ok(p_ty) => match nbe_eval(&p_ty) {
                Term::TPath(a_ty, _, _) => {
                    check_interval_dt(dts, ctx, r)?;
                    let r_ = nbe_eval(r);
                    Ok(match nbe_eval(&a_ty) {
                        Term::PLam(_, body) => nbe_eval(&beta(&body, &r_)),
                        plain => plain,
                    })
                }
                other => Err(TypeError::ExpectedPath(other)),
            },
            Err(e) => infer_via_reduction(dts, ctx, t, e),
        },

        // Interval atoms
        Term::TInterval(_) | Term::TCube(_) => Ok(interval_ty()),
        Term::TIntervalTy => Ok(Term::TUniv(0)),

        // Lambdas cannot be inferred
        t @ Term::TAbs(_, _) | t @ Term::PLam(_, _) => Err(TypeError::CannotInfer(t.clone())),

        // Tactic blocks cannot be inferred (need type annotation)
        t @ Term::TBy(_) => Err(TypeError::CannotInfer(t.clone())),

        // Unresolved metavariable
        t @ Term::Meta(_) => Err(TypeError::CannotInfer(t.clone())),

        // Equiv type
        Term::TEquiv(a, b) => {
            let n = type_level_dt(dts, ctx, a)?;
            let m = type_level_dt(dts, ctx, b)?;
            Ok(Term::TUniv(n.max(m)))
        }

        // mkEquiv: build an equivalence record
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            type_level_dt(dts, ctx, a)?;
            type_level_dt(dts, ctx, b)?;
            let a_ = nbe_eval(a);
            let b_ = nbe_eval(b);
            // f : A → B
            check(
                ctx,
                f,
                &Term::TPi("_".into(), Box::new(a_.clone()), Box::new(shift(1, 0, &b_))),
            )?;
            // g : B → A
            check(
                ctx,
                g,
                &Term::TPi("_".into(), Box::new(b_.clone()), Box::new(shift(1, 0, &a_))),
            )?;
            // eta : (a : A) → Path A a (g (f a))
            check(
                ctx,
                eta,
                &Term::TPi(
                    "a".into(),
                    Box::new(a_.clone()),
                    Box::new(Term::TPath(
                        Box::new(shift(1, 0, &a_)),
                        Box::new(Term::TVar(0)),
                        Box::new(Term::TApp(
                            Box::new(shift(1, 0, g)),
                            Box::new(Term::TApp(
                                Box::new(shift(1, 0, f)),
                                Box::new(Term::TVar(0)),
                            )),
                        )),
                    )),
                ),
            )?;
            // eps : (b : B) → Path B (f (g b)) b
            check(
                ctx,
                eps,
                &Term::TPi(
                    "b".into(),
                    Box::new(b_.clone()),
                    Box::new(Term::TPath(
                        Box::new(shift(1, 0, &b_)),
                        Box::new(Term::TApp(
                            Box::new(shift(1, 0, f)),
                            Box::new(Term::TApp(
                                Box::new(shift(1, 0, g)),
                                Box::new(Term::TVar(0)),
                            )),
                        )),
                        Box::new(Term::TVar(0)),
                    )),
                ),
            )?;
            Ok(Term::TEquiv(Box::new(a_), Box::new(b_)))
        }

        // equivFwd e x : B   where  e : Equiv A B,  x : A
        Term::TEquivFwd(e, x) => {
            let (a, b) = require_equiv_dt(dts, ctx, e)?;
            check_dt(dts, ctx, x, &a)?;
            Ok(b)
        }

        // ua e : Path U A B   where  e : Equiv A B
        Term::TUa(e) => {
            let (a, b) = require_equiv_dt(dts, ctx, e)?;
            let n = type_level_dt(dts, ctx, &a)?;
            Ok(Term::TPath(
                Box::new(Term::TUniv(n)),
                Box::new(a),
                Box::new(b),
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
                    let path_ty = nbe_eval(&infer_dt(dts, &ctx2, &path)?);
                    // path_ty should be TPath(a_ty, u, v). The endpoints
                    // need to be shifted back to the outer context
                    // (removing the interval binder at index 0).
                    match path_ty {
                        Term::TPath(a_ty, u, v) => {
                            let u = shift(-1, 0, &u);
                            let v = shift(-1, 0, &v);
                            Term::TPath(a_ty, Box::new(u), Box::new(v))
                        }
                        _other => {
                            let a_ty = infer_dt(dts, &ctx2, body)?;
                            let u = shift(-1, 0, &apply_literal(&Literal::NegVar(0), body));
                            let v = shift(-1, 0, &apply_literal(&Literal::Pos(0), body));
                            Term::TPath(Box::new(a_ty), Box::new(u), Box::new(v))
                        }
                    }
                }
                _ => infer_dt(dts, ctx, p)?,
            };
            match nbe_eval(&p_ty) {
                Term::TPath(a_ty, u, v) => {
                    let (x_ty, ret_ty) = match nbe_eval(&a_ty) {
                        Term::PLam(_, body) => (
                            nbe_eval(&beta(&body, &Term::TInterval(I::I0))),
                            nbe_eval(&beta(&body, &Term::TInterval(I::I1))),
                        ),
                        _plain => (nbe_eval(&u), nbe_eval(&v)),
                    };
                    check_dt(dts, ctx, x, &x_ty)?;
                    Ok(ret_ty)
                }
                other => Err(TypeError::ExpectedPath(other)),
            }
        }

        // Glue type formation
        Term::TGlue(a_ty, phi, te) => {
            let n = type_level_dt(dts, ctx, a_ty)?;
            let a_ty_ = nbe_eval(a_ty);
            check_interval_dt(dts, ctx, phi)?;
            let m = match te.as_ref() {
                // te = (A, e) : Σ(X : U). Equiv X a_ty_
                Term::TPair(te_a, _) => {
                    let sigma = Term::TSigma(
                        "X".to_string(),
                        Box::new(Term::TUniv(n)),
                        Box::new(Term::TEquiv(
                            Box::new(Term::TVar(0)),
                            Box::new(shift(1, 0, &a_ty_)),
                        )),
                    );
                    check_dt(dts, ctx, te, &sigma)?;
                    type_level_dt(dts, ctx, te_a)?
                }
                // te = λ_. (A, e) — strip the lambda and check the body
                Term::TAbs(_, body) => {
                    let body_stripped = beta(body, &Term::TInterval(I::I1));
                    match &body_stripped {
                        Term::TPair(te_a, _) => {
                            let sigma = Term::TSigma(
                                "X".to_string(),
                                Box::new(Term::TUniv(n)),
                                Box::new(Term::TEquiv(
                                    Box::new(Term::TVar(0)),
                                    Box::new(shift(1, 0, &a_ty_)),
                                )),
                            );
                            check_dt(dts, ctx, &body_stripped, &sigma)?;
                            type_level_dt(dts, ctx, te_a)?
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
                    let te_ty = infer_dt(dts, ctx, te)?;
                    match nbe_eval(&te_ty) {
                        Term::TUniv(k) => k,
                        Term::TEquiv(a, b) => {
                            let a_ = nbe_eval(&a);
                            let b_ = nbe_eval(&b);
                            require_equal(ctx, &b_, &a_ty_)?;
                            let p = type_level_dt(dts, ctx, &a_)?;
                            let q = type_level_dt(dts, ctx, &b_)?;
                            p.max(q)
                        }
                        Term::TMkEquiv(a, b, _, _, _, _) => {
                            let a_ = nbe_eval(&a);
                            let b_ = nbe_eval(&b);
                            require_equal(ctx, &b_, &a_ty_)?;
                            let p = type_level_dt(dts, ctx, &a_)?;
                            let q = type_level_dt(dts, ctx, &b_)?;
                            p.max(q)
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
            Ok(Term::TUniv(n.max(m)))
        }

        // unglue phi te g
        Term::TUnglue(phi, te, g) => {
            check_interval_dt(dts, ctx, phi)?;
            let phi_ = nbe_eval(phi);
            if is_top_dnf(&phi_) {
                infer_dt(dts, ctx, &Term::TEquivFwd(te.clone(), g.clone()))
            } else if is_bot_dnf(&phi_) {
                infer_dt(dts, ctx, g)
            } else {
                let g_ty = infer_dt(dts, ctx, g)?;
                match nbe_eval(&g_ty) {
                    Term::TGlue(a_ty, _, _) => Ok(nbe_eval(&a_ty)),
                    other => Err(TypeError::Other(format!(
                        "unglue: expected argument of Glue type, got: {}",
                        other
                    ))),
                }
            }
        }

        // glue elem — can only infer in degenerate phi cases
        t @ Term::TGlueElem(phi, elm, a) => {
            let phi_ = nbe_eval(phi);
            if is_top_dnf(&phi_) {
                infer_dt(dts, ctx, elm)
            } else if is_bot_dnf(&phi_) {
                infer_dt(dts, ctx, a)
            } else {
                Err(TypeError::CannotInfer(t.clone()))
            }
        }

        // Sigma formation: Σ(x:A).B : U(max i j)
        Term::TSigma(x, a_ty, b_ty) => {
            let i = type_level_dt(dts, ctx, a_ty)?;
            let ctx2 = extend_ctx(x.clone(), nbe_eval(a_ty), ctx);
            let j = type_level_dt(dts, &ctx2, b_ty)?;
            Ok(Term::TUniv(i.max(j)))
        }

        // fst p : A   where  p : Σ(x:A).B
        Term::TFst(p) => match infer_dt(dts, ctx, p) {
            Ok(p_ty) => match nbe_eval(&p_ty) {
                Term::TSigma(_, a_ty, _) => Ok(nbe_eval(&a_ty)),
                other => Err(TypeError::ExpectedSigma(other)),
            },
            Err(e) => infer_via_reduction(dts, ctx, t, e),
        },

        // snd p : B[fst p / x]   where  p : Σ(x:A).B
        Term::TSnd(p) => match infer_dt(dts, ctx, p) {
            Ok(p_ty) => match nbe_eval(&p_ty) {
                Term::TSigma(_, _, b_ty) => Ok(nbe_eval(&beta(&b_ty, &Term::TFst(p.clone())))),
                other => Err(TypeError::ExpectedSigma(other)),
            },
            Err(e) => infer_via_reduction(dts, ctx, t, e),
        },

        // Pairs cannot be inferred without annotation
        t @ Term::TPair(_, _) => Err(TypeError::CannotInfer(t.clone())),

        // hcomp A [phi -> tube, ...] base
        Term::THComp(a_ty, sys, base) => {
            type_level_dt(dts, ctx, a_ty)?;
            let a_ty_ = nbe_eval(a_ty);
            check_dt(dts, ctx, &base, &a_ty_)?;
            for (phi, tube) in sys {
                check_interval_dt(dts, ctx, &phi)?;
                let tube_val = nbe_eval(&tube);
                match tube_val {
                    Term::PLam(i, body) => {
                        let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
                        let a_ty_s = shift(1, 0, &a_ty_);
                        check_dt(dts, &ctx2, &body, &a_ty_s)?;
                        let tube_at0 = nbe_eval(&beta(&body, &Term::TInterval(I::I0)));
                        let phi_ = nbe_eval(&phi);
                        check_faces(ctx, &phi_, &tube_at0, &nbe_eval(&base))?;
                    }
                    tube_ => {
                        let tube_ty = infer_dt(dts, ctx, &tube_)?;
                        match nbe_eval(&tube_ty) {
                            Term::TPath(a, u, v) => {
                                if !definitionally_equal_ctx_r(ctx, &nbe_eval(&a), &a_ty_).is_equal() {
                                    return Err(TypeError::TypeMismatch(
                                        Box::new(nbe_eval(&a_ty_)),
                                        Box::new(nbe_eval(&a)),
                                    ));
                                }
                                check_dt(dts, ctx, &nbe_eval(&u), &a_ty_)?;
                                check_dt(dts, ctx, &nbe_eval(&v), &a_ty_)?;
                                let phi_ = nbe_eval(&phi);
                                check_faces(ctx, &phi_, &nbe_eval(&u), &nbe_eval(&base))?;
                            }
                            other => return Err(TypeError::ExpectedPath(other)),
                        }
                    }
                }
            }
            Ok(a_ty_)
        }

        // comp A [phi -> tube, ...] base : A 1
        Term::TComp(a_fam, sys, base) => {
            let ctx_i = extend_ctx("i".to_string(), interval_ty(), ctx);
            let _a_fam_ty = type_level_dt(dts, &ctx_i, a_fam)?;
            let a_fam_ = nbe_eval(a_fam);
            let a_at0 = match &a_fam_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I0))),
                _ => a_fam_.clone(),
            };
            check_dt(dts, ctx, base, &a_at0)?;
            for (phi, tube) in sys {
                check_interval_dt(dts, ctx, &phi)?;
                match nbe_eval(&tube) {
                    Term::PLam(i, body) => {
                        let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
                        let a_fam_s = shift(1, 0, &a_fam_);
                        let body_ty = match &a_fam_s {
                            Term::PLam(_, b) => nbe_eval(&beta(b, &Term::TVar(0))),
                            _ => shift(1, 0, &a_at0),
                        };
                        check_dt(dts, &ctx2, &body, &body_ty)?;
                        let tube_at0 = nbe_eval(&beta(&body, &Term::TInterval(I::I0)));
                        let phi_ = nbe_eval(&phi);
                        check_faces(ctx, &phi_, &tube_at0, &nbe_eval(&base))?;
                    }
                    tube_ => {
                        let tube_ty = infer_dt(dts, ctx, &tube_)?;
                        match nbe_eval(&tube_ty) {
                            Term::TPath(_a, u, v) => {
                                check_dt(dts, ctx, &nbe_eval(&u), &a_at0)?;
                                check_dt(dts, ctx, &nbe_eval(&v), &nbe_eval(&Term::PApp(a_fam.clone(), Box::new(Term::TInterval(I::I1)))))?;
                                let phi_ = nbe_eval(&phi);
                                check_faces(ctx, &phi_, &nbe_eval(&u), &nbe_eval(&base))?;
                            }
                            other => return Err(TypeError::ExpectedPath(other)),
                        }
                    }
                }
            }
            let a_at1 = match &a_fam_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I1))),
                _ => a_fam_.clone(),
            };
            Ok(a_at1)
        }

        // fill A [phi -> tube, ...] base : (j : I) → A j
        Term::TFill(a_fam, sys, base) => {
            let ctx_i = extend_ctx("i".to_string(), interval_ty(), ctx);
            type_level_dt(dts, &ctx_i, a_fam)?;
            let a_fam_ = nbe_eval(a_fam);
            let a_at0 = match &a_fam_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I0))),
                _ => a_fam_.clone(),
            };
            check_dt(dts, ctx, base, &a_at0)?;
            for (phi, tube) in sys {
                check_interval_dt(dts, ctx, &phi)?;
                match nbe_eval(&tube) {
                    Term::PLam(i, body) => {
                        let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
                        let a_fam_s = shift(1, 0, &a_fam_);
                        let body_ty = match &a_fam_s {
                            Term::PLam(_, b) => nbe_eval(&beta(b, &Term::TVar(0))),
                            _ => shift(1, 0, &a_at0),
                        };
                        check_dt(dts, &ctx2, &body, &body_ty)?;
                        let tube_at0 = nbe_eval(&beta(&body, &Term::TInterval(I::I0)));
                        let phi_ = nbe_eval(&phi);
                        check_faces(ctx, &phi_, &tube_at0, &nbe_eval(&base))?;
                    }
                    tube_ => {
                        let tube_ty = infer_dt(dts, ctx, &tube_)?;
                        match nbe_eval(&tube_ty) {
                            Term::TPath(_a, u, v) => {
                                check_dt(dts, ctx, &nbe_eval(&u), &a_at0)?;
                                check_dt(dts, ctx, &nbe_eval(&v), &nbe_eval(&Term::PApp(a_fam.clone(), Box::new(Term::TInterval(I::I1)))))?;
                                let phi_ = nbe_eval(&phi);
                                check_faces(ctx, &phi_, &nbe_eval(&u), &nbe_eval(&base))?;
                            }
                            other => return Err(TypeError::ExpectedPath(other)),
                        }
                    }
                }
            }
            let comp_result = Term::TComp(
                a_fam.clone(),
                sys.clone(),
                base.clone(),
            );
            let a_fam_s = shift(1, 0, a_fam);
            let body_ty = match &a_fam_s {
                Term::PLam(_, b) => nbe_eval(&beta(b, &Term::TVar(0))),
                _ => shift(1, 0, &a_at0),
            };
            Ok(Term::TPath(
                Box::new(Term::PLam("j".to_string(), Box::new(body_ty))),
                Box::new(nbe_eval(base)),
                Box::new(nbe_eval(&comp_result)),
            ))
        }

        // hfill A [phi -> tube, ...] base : Path A base (hcomp A [phi -> tube, ...] base)
        Term::THFill(a_ty, sys, base) => {
            type_level_dt(dts, ctx, a_ty)?;
            let a_ty_ = nbe_eval(a_ty);
            check_dt(dts, ctx, base, &a_ty_)?;
            for (phi, tube) in sys {
                check_interval_dt(dts, ctx, &phi)?;
                match nbe_eval(&tube) {
                    Term::PLam(i, body) => {
                        let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
                        let a_ty_s = shift(1, 0, &a_ty_);
                        check_dt(dts, &ctx2, &body, &a_ty_s)?;
                        let tube_at0 = nbe_eval(&beta(&body, &Term::TInterval(I::I0)));
                        let phi_ = nbe_eval(&phi);
                        check_faces(ctx, &phi_, &tube_at0, &nbe_eval(&base))?;
                    }
                    tube_ => {
                        let tube_ty = infer_dt(dts, ctx, &tube_)?;
                        match nbe_eval(&tube_ty) {
                            Term::TPath(a, u, v) => {
                                if !definitionally_equal_ctx_r(ctx, &nbe_eval(&a), &a_ty_).is_equal() {
                                    return Err(TypeError::TypeMismatch(
                                        Box::new(nbe_eval(&a_ty_)),
                                        Box::new(nbe_eval(&a)),
                                    ));
                                }
                                check_dt(dts, ctx, &nbe_eval(&u), &a_ty_)?;
                                check_dt(dts, ctx, &nbe_eval(&v), &a_ty_)?;
                                let phi_ = nbe_eval(&phi);
                                check_faces(ctx, &phi_, &nbe_eval(&u), &nbe_eval(&base))?;
                            }
                            other => return Err(TypeError::ExpectedPath(other)),
                        }
                    }
                }
            }
            let hcomp_result = Term::THComp(
                a_ty.clone(),
                sys.clone(),
                base.clone(),
            );
            Ok(Term::TPath(
                Box::new(shift(1, 0, &a_ty_)),
                Box::new(nbe_eval(base)),
                Box::new(nbe_eval(&hcomp_result)),
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
            let dt = dts
                .iter()
                .find(|dt| &dt.name == d)
                .ok_or_else(|| TypeError::UnknownDatatype(d.clone()))?;

            // If the datatype has a universe-level annotation, use it directly
            // for the fully-applied case.
            if args.len() >= dt.params.len() {
                if let Some(level) = dt.universe_level {
                    return Ok(Term::TUniv(level));
                }
            }

            // Compute the maximum universe level over all constructor arg types.
            // For parameterized types, substitute provided parameter args into
            // the arg_tys before computing levels, so that TVar(0) etc.
            // referencing parameters get resolved.
            let num_params = dt.params.len();
            let mut max_level: Level = 0;

            // Ordinary constructors
            for con_sig in &dt.cons {
                let mut tel_ctx = ctx.clone();
                let mut prev_args: Vec<Term> = Vec::new();
                for (k, arg_ty) in con_sig.arg_tys.iter().enumerate() {
                    // Substitute provided parameters (reverse order for de Bruijn).
                    let mut substituted = arg_ty.clone();
                    for i in (0..num_params.min(args.len())).rev() {
                        substituted = beta(&substituted, &args[i]);
                    }
                    let arg_ty_inst = prev_args
                        .iter()
                        .rev()
                        .fold(substituted, |ty, a| beta(&ty, a));
                    let lvl = type_level_dt(dts, &tel_ctx, &arg_ty_inst)?;
                    max_level = max_level.max(lvl);
                    let var_name = format!("_con_arg_{}", k);
                    let depth = k as i32;
                    prev_args.push(shift(depth + 1, 0, &Term::TVar(0)));
                    tel_ctx = extend_ctx(var_name, nbe_eval(&arg_ty_inst), &tel_ctx);
                }
            }

            // Path constructors (ordinary args only; interval arg is in 𝕀 ⊂ U_0)
            for pcon_sig in &dt.pcons {
                let mut tel_ctx = ctx.clone();
                let mut prev_args: Vec<Term> = Vec::new();
                for (k, arg_ty) in pcon_sig.arg_tys.iter().enumerate() {
                    let mut substituted = arg_ty.clone();
                    for i in (0..num_params.min(args.len())).rev() {
                        substituted = beta(&substituted, &args[i]);
                    }
                    let arg_ty_inst = prev_args
                        .iter()
                        .rev()
                        .fold(substituted, |ty, a| beta(&ty, a));
                    let lvl = type_level_dt(dts, &tel_ctx, &arg_ty_inst)?;
                    max_level = max_level.max(lvl);
                    let var_name = format!("_pcon_arg_{}", k);
                    let depth = k as i32;
                    prev_args.push(shift(depth + 1, 0, &Term::TVar(0)));
                    tel_ctx = extend_ctx(var_name, nbe_eval(&arg_ty_inst), &tel_ctx);
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
                        Box::new(shifted_pty),
                        Box::new(result),
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
            let dt = dts
                .iter()
                .find(|dt| &dt.name == d)
                .ok_or_else(|| TypeError::UnknownDatatype(d.clone()))?;
            // Check if this is an ordinary constructor.
            if let Some(sig) = dt.find_con(c) {
                let num_params = dt.params.len();
                let (param_terms, _checked_args) = infer_and_check_params(
                    dts, ctx, &sig.arg_tys, args, num_params,
                )?;
                let params = build_params(&param_terms);
                Ok(Term::TData(d.clone(), params))
            // Path constructor used as a term (without explicit @).
            // Its type is Path (TData(d, params)) face0[args] face1[args].
            } else if let Some(sig) = dt.find_pcon(c) {
                let num_params = dt.params.len();
                let (param_terms, checked_args) = infer_and_check_params(
                    dts, ctx, &sig.arg_tys, args, num_params,
                )?;
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
                    Box::new(Term::TData(d.clone(), params.clone())),
                    Box::new(nbe_eval(&face0)),
                    Box::new(nbe_eval(&face1)),
                ))
            } else {
                Err(TypeError::UnknownConstructor(d.clone(), c.clone()))
            }
        }

        // TPCon(d, pc, args, r) : Path (TData(d, params)) face0[args] face1[args]
        Term::TPCon(d, pc, args, r) => {
            let dt = dts
                .iter()
                .find(|dt| &dt.name == d)
                .ok_or_else(|| TypeError::UnknownDatatype(d.clone()))?;
            let sig = dt
                .find_pcon(pc)
                .ok_or_else(|| TypeError::UnknownConstructor(d.clone(), pc.clone()))?;
            if args.len() != sig.arity() {
                return Err(TypeError::WrongNumberOfArgs {
                    con: pc.clone(),
                    expected: sig.arity(),
                    got: args.len(),
                });
            }
            let num_params = dt.params.len();
            let (param_terms, _checked_args) = infer_and_check_params(
                dts, ctx, &sig.arg_tys, args, num_params,
            )?;
            // Check interval argument.
            check_interval(ctx, r)?;
            let params = build_params(&param_terms);
            Ok(Term::TData(d.clone(), params))
        }

        // TSqCon(d, sc, args, r, s) :
        //   PathP (<i> PathP (<j> TData(d, params)) (face_i0 args j) (face_i1 args j))
        //               (face_j0 args i) (face_j1 args i)
        Term::TSqCon(d, sc, args, r, s) => {
            let dt = dts
                .iter()
                .find(|dt| &dt.name == d)
                .ok_or_else(|| TypeError::UnknownDatatype(d.clone()))?;
            let sig = dt
                .find_sqcon(sc)
                .ok_or_else(|| TypeError::UnknownConstructor(d.clone(), sc.clone()))?;
            if args.len() != sig.arity() {
                return Err(TypeError::WrongNumberOfArgs {
                    con: sc.clone(),
                    expected: sig.arity(),
                    got: args.len(),
                });
            }
            let num_params = dt.params.len();
            let (param_terms, checked_args) = infer_and_check_params(
                dts, ctx, &sig.arg_tys, args, num_params,
            )?;
            check_interval(ctx, r)?;
            check_interval(ctx, s)?;
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
            let is_endpoint = |t: &Term| -> bool {
                match nbe_eval(t) {
                    Term::TInterval(i) => {
                        let dnf = crate::cubical::interval::eval_interval(&i);
                        dnf == crate::cubical::interval::dnf_bot() || dnf == crate::cubical::interval::dnf_top()
                    }
                    Term::TCube(d) => {
                        d == crate::cubical::interval::dnf_bot() || d == crate::cubical::interval::dnf_top()
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
                    Box::new(Term::PLam("j".to_string(), Box::new(data_ty))),
                    Box::new(face_i0_subst),
                    Box::new(face_i1_subst),
                ));
            }

            // Outer type: PathP (<i> PathP (<j> A) (fi0 j) (fi1 j)) (fj0 i) (fj1 i)
            // In Owl AST: TPath(PLam("i", TPath(PLam("j", A), fi0, fi1)), fj0, fj1)
            let inner_path = Term::TPath(
                Box::new(Term::PLam("j".to_string(), Box::new(data_ty))),
                Box::new(face_i0_subst),
                Box::new(face_i1_subst),
            );
            let outer_type = Term::TPath(
                Box::new(Term::PLam("i".to_string(), Box::new(inner_path))),
                Box::new(face_j0_subst),
                Box::new(face_j1_subst),
            );
            Ok(outer_type)
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
            let scrut_ty = infer_dt(dts, ctx, scrut)?;
            let (d, scrut_params) = match nbe_eval(&scrut_ty) {
                Term::TData(d, params) => (d, params),
                other => return Err(TypeError::ExpectedData(other)),
            };
            let dt = dts
                .iter()
                .find(|dt| dt.name == d)
                .ok_or_else(|| TypeError::UnknownDatatype(d.clone()))?;

            // Verify motive has type Π(_:TData(d, params)).C where C is a well-formed type.
            let motive_dom = Term::TData(d.clone(), scrut_params.clone());
            match motive.as_ref() {
                Term::TAbs(x, body) => {
                    let motive_ctx =
                        extend_ctx(x.clone(), nbe_eval(&motive_dom), ctx);
                    type_level_dt(dts, &motive_ctx, body)?;
                }
                _ => {
                    let motive_inferred = infer_dt(dts, ctx, motive)?;
                    match nbe_eval(&motive_inferred) {
                        Term::TPi(x, dom, cod) => {
                            require_equal(ctx, &nbe_eval(&dom), &nbe_eval(&motive_dom))?;
                            let cod_ctx = extend_ctx(x, nbe_eval(&dom), ctx);
                            type_level_dt(dts, &cod_ctx, &cod)?;
                        }
                        other => return Err(TypeError::ExpectedPi(other)),
                    }
                }
            }

            // Helper: substitute determined params into a constructor's arg_tys.
            // For parameterized types, arg_tys reference params via de Bruijn
            // indices (TVar(0) for first param). We substitute the scrutinee's
            // parameter values to get concrete arg types.
            fn subst_params(arg_tys: &[Term], params: &[Term]) -> Vec<Term> {
                arg_tys
                    .iter()
                    .map(|ty| {
                        let mut t = ty.clone();
                        for p in params.iter().rev() {
                            t = beta(&t, p);
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
            fn subst_params_face(face: &Term, params: &[Term], num_args: usize) -> Term {
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
                    .ok_or_else(|| TypeError::MissingCase(con_sig.name.clone()))?;

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
                    });
                }

                // Build extended context: push binders outermost-first,
                // last binder ends up at index 0.
                let mut case_ctx = ctx.clone();
                let mut con_args_in_ctx: Vec<Term> = Vec::new();
                for (k, binder_name) in case.binders.iter().enumerate() {
                    let arg_ty = con_args_in_ctx
                        .iter()
                        .rev()
                        .fold(subst_arg_tys[k].clone(), |ty, a| beta(&ty, a));
                    let arg_ty_ev = nbe_eval(&arg_ty);
                    let depth = k as i32;
                    con_args_in_ctx.push(shift(depth + 1, 0, &Term::TVar(0)));
                    case_ctx = extend_ctx(binder_name.clone(), arg_ty_ev, &case_ctx);
                }

                // Expected type: motive applied to TCon(d, c, params, all binders as vars).
                let arity = subst_arg_tys.len();
                let con_term_args: Vec<Term> = (0..arity)
                    .map(|k| Term::TVar((arity - 1 - k) as i32))
                    .collect();
                let scrut_as_con = Term::TCon(d.clone(), con_sig.name.clone(), con_term_args);
                let shifted_motive = shift((arity) as i32, 0, motive);
                let expected_ty = nbe_eval(&Term::TApp(
                    Box::new(shifted_motive),
                    Box::new(scrut_as_con),
                ));
                check_dt(dts, &case_ctx, &case.body, &expected_ty)?;
            }

            // Check all path constructor cases.
            for pcon_sig in &dt.pcons {
                let case = cases
                    .iter()
                    .find(|c| c.con == pcon_sig.name)
                    .ok_or_else(|| TypeError::MissingCase(pcon_sig.name.clone()))?;

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
                    case_ctx = extend_ctx(binder_name.clone(), nbe_eval(&arg_ty), &case_ctx);
                }

                let arity = subst_arg_tys.len();
                let _ord_case_ctx = case_ctx.clone();
                case_ctx = extend_ctx(i_name.clone(), interval_ty(), &case_ctx);

                let ord_var_no_i: Vec<Term> = (0..arity)
                    .map(|k| Term::TVar((arity - 1 - k) as i32))
                    .collect();
                let i_var = Term::TVar(0);
                let ord_var: Vec<Term> = (0..arity)
                    .map(|k| Term::TVar((arity - k) as i32))
                    .collect();

                let pcon_term = Term::TPCon(
                    d.clone(),
                    pcon_sig.name.clone(),
                    ord_var.clone(),
                    Box::new(i_var.clone()),
                );
                let motive_shifted = shift((arity + 1) as i32, 0, motive);
                let motive_at_pcon = nbe_eval(&Term::TApp(
                    Box::new(motive_shifted.clone()),
                    Box::new(pcon_term),
                ));
                let face0_subst = subst_params_face(&pcon_sig.face0, &scrut_params, arity);
                let face1_subst = subst_params_face(&pcon_sig.face1, &scrut_params, arity);
                let face0_case =
                    eval_elim_face(motive, cases, &face0_subst, &ord_var_no_i, arity as i32);
                let face1_case =
                    eval_elim_face(motive, cases, &face1_subst, &ord_var_no_i, arity as i32);

                let expected_body_ty = Term::TPath(
                    Box::new(Term::PLam(i_name.clone(), Box::new(motive_at_pcon))),
                    Box::new(shift(1, 0, &face0_case)),
                    Box::new(shift(1, 0, &face1_case)),
                );
                SKIP_PLAM_ENDPT.with(|c| c.set(true));
                check_dt(dts, &case_ctx, &case.body, &expected_body_ty)?;
                SKIP_PLAM_ENDPT.with(|c| c.set(false));

                let body_at0 = match case.body.as_ref() {
                    Term::PLam(_, inner) => {
                        let reduced = reduce_pcon_endpoints_dt(
                            dts,
                            &apply_literal(&Literal::NegVar(0), inner),
                        );
                        nbe_eval(&shift(-1, 0, &reduced))
                    }
                    _ => {
                        let papp = Term::PApp(
                            case.body.clone(),
                            Box::new(Term::TInterval(I::I0)),
                        );
                        let reduced = reduce_pcon_endpoints_dt(dts, &papp);
                        nbe_eval(&reduced)
                    }
                };
                let body_at1 = match case.body.as_ref() {
                    Term::PLam(_, inner) => {
                        let reduced = reduce_pcon_endpoints_dt(
                            dts,
                            &apply_literal(&Literal::Pos(0), inner),
                        );
                        nbe_eval(&shift(-1, 0, &reduced))
                    }
                    _ => {
                        let papp = Term::PApp(
                            case.body.clone(),
                            Box::new(Term::TInterval(I::I1)),
                        );
                        let reduced = reduce_pcon_endpoints_dt(dts, &papp);
                        nbe_eval(&reduced)
                    }
                };
                require_equal_endpt(&case_ctx, &shift(1, 0, &face0_case), &body_at0)?;
                require_equal_endpt(&case_ctx, &shift(1, 0, &face1_case), &body_at1)?;
            }

            // Check all square constructor cases.
            for sqcon_sig in &dt.sqcons {
                let case = cases
                    .iter()
                    .find(|c| c.con == sqcon_sig.name)
                    .ok_or_else(|| TypeError::MissingCase(sqcon_sig.name.clone()))?;

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
                    case_ctx_sq = extend_ctx(binder_name.clone(), nbe_eval(&arg_ty), &case_ctx_sq);
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
                    Box::new(r_var.clone()),
                    Box::new(s_var.clone()),
                );
                let motive_shifted_sq = shift((arity_sq + 2) as i32, 0, motive);
                let motive_at_sqcon = nbe_eval(&Term::TApp(
                    Box::new(motive_shifted_sq.clone()),
                    Box::new(sqcon_term),
                ));

                let face_i0_subst = subst_params_face(&sqcon_sig.face_i0, &scrut_params, arity_sq);
                let face_i1_subst = subst_params_face(&sqcon_sig.face_i1, &scrut_params, arity_sq);
                let face_j0_subst = subst_params_face(&sqcon_sig.face_j0, &scrut_params, arity_sq);
                let face_j1_subst = subst_params_face(&sqcon_sig.face_j1, &scrut_params, arity_sq);

                let face_i0_case =
                    eval_elim_face(motive, cases, &face_i0_subst, &ord_var_no_rs, (arity_sq + 2) as i32);
                let face_i1_case =
                    eval_elim_face(motive, cases, &face_i1_subst, &ord_var_no_rs, (arity_sq + 2) as i32);
                let face_j0_case =
                    eval_elim_face(motive, cases, &face_j0_subst, &ord_var_no_rs, (arity_sq + 2) as i32);
                let face_j1_case =
                    eval_elim_face(motive, cases, &face_j1_subst, &ord_var_no_rs, (arity_sq + 2) as i32);

                let inner_path = Term::TPath(
                    Box::new(Term::PLam(s_name.clone(), Box::new(motive_at_sqcon))),
                    Box::new(shift(1, 0, &face_i0_case)),
                    Box::new(shift(1, 0, &face_i1_case)),
                );
                let expected_body_ty_sq = Term::TPath(
                    Box::new(Term::PLam(r_name.clone(), Box::new(inner_path))),
                    Box::new(shift(2, 0, &face_j0_case)),
                    Box::new(shift(2, 0, &face_j1_case)),
                );
                SKIP_PLAM_ENDPT.with(|c| c.set(true));
                check_dt(dts, &case_ctx_sq, &case.body, &expected_body_ty_sq)?;
                SKIP_PLAM_ENDPT.with(|c| c.set(false));
            }

            // Return type: motive applied to the scrutinee.
            Ok(nbe_eval(&Term::TApp(
                motive.clone(),
                scrut.clone(),
            )))
        }
    }
}

// HIT endpoint reduction (datatype-aware)
// ---------------------------------------------------------------------------
/// Reduce `TPCon(d, pc, args, r)` at endpoints `r=I0`/`r=I1` to the
/// corresponding declared face value, recursively.  This is needed because
/// `nbe_eval` doesn't carry datatype definitions, so it cannot reduce path
/// constructors at their boundaries without this extra pass.
fn reduce_pcon_endpoints_dt(dts: &[Datatype], t: &Term) -> Term {
    let t = nbe_eval(t);
    match &t {
        Term::TPCon(d, pc, args, r) => {
            let r_nf = nbe_eval(r);
            let (is_i0, is_i1) = match &r_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    (dnf == crate::cubical::interval::dnf_bot(), dnf == crate::cubical::interval::dnf_top())
                }
                Term::TCube(d) => {
                    (d == &crate::cubical::interval::dnf_bot(), d == &crate::cubical::interval::dnf_top())
                }
                _ => (false, false),
            };
            if is_i0 || is_i1 {
                // Look up the face value from the PConSig.
                if let Some(dt) = dts.iter().find(|dt| &dt.name == d)
                    && let Some(sig) = dt.find_pcon(pc) {
                        // face0/face1 are in a scope of sig.arity() ordinary args.
                        // Substitute the checked args into the face term.
                        let reduced_args: Vec<Term> =
                            args.iter().map(|a| reduce_pcon_endpoints_dt(dts, a)).collect();
                        let face = if is_i0 { &sig.face0 } else { &sig.face1 };
                        // Face parsing uses insert(0,...), so TVar(k) = arg_{num_args-1-k}.
                        // Substitute from highest face-var index to lowest.
                        let arity = reduced_args.len();
                        let mut face_inst = face.clone();
                        for k in (0..arity).rev() {
                            face_inst = subst(k as i32, &reduced_args[arity - 1 - k], &face_inst);
                        }
                        return reduce_pcon_endpoints_dt(dts, &nbe_eval(&face_inst));
                    }
            }
            // Not at an endpoint (or datatype not found): reduce sub-terms.
            let reduced_args: Vec<Term> =
                args.iter().map(|a| reduce_pcon_endpoints_dt(dts, a)).collect();
            nbe_eval(&Term::TPCon(
                d.clone(),
                pc.clone(),
                reduced_args,
                Box::new(r_nf),
            ))
        }
        Term::TSqCon(d, sc, args, r, s) => {
            let r_nf = nbe_eval(r);
            let s_nf = nbe_eval(s);
            // Check if either interval is at an endpoint for boundary reduction.
            let (r_is_i0, r_is_i1) = match &r_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    (dnf == crate::cubical::interval::dnf_bot(), dnf == crate::cubical::interval::dnf_top())
                }
                _ => (false, false),
            };
            let (s_is_i0, s_is_i1) = match &s_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    (dnf == crate::cubical::interval::dnf_bot(), dnf == crate::cubical::interval::dnf_top())
                }
                _ => (false, false),
            };
            if let Some(dt) = dts.iter().find(|dt| &dt.name == d)
                && let Some(sig) = dt.find_sqcon(sc) {
                    let arity = sig.arity();
                    let reduced_args: Vec<Term> =
                        args.iter().map(|a| reduce_pcon_endpoints_dt(dts, a)).collect();
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
                        return reduce_pcon_endpoints_dt(dts, &nbe_eval(&Term::PApp(Box::new(face), s.clone())));
                    }
                    if r_is_i1 {
                        // sq @ 1 @ s = face_j1 @ s (outer path at i=1 gives face_j1)
                        let face = subst_face(&sig.face_j1);
                        return reduce_pcon_endpoints_dt(dts, &nbe_eval(&Term::PApp(Box::new(face), s.clone())));
                    }
                    if s_is_i0 {
                        // sq @ r @ 0 = face_i0 (inner path at j=0 gives face_i0, a point)
                        let face = subst_face(&sig.face_i0);
                        return reduce_pcon_endpoints_dt(dts, &nbe_eval(&face));
                    }
                    if s_is_i1 {
                        // sq @ r @ 1 = face_i1 (inner path at j=1 gives face_i1, a point)
                        let face = subst_face(&sig.face_i1);
                        return reduce_pcon_endpoints_dt(dts, &nbe_eval(&face));
                    }
                }
            // Not at an endpoint: reduce sub-terms.
            nbe_eval(&Term::TSqCon(
                d.clone(),
                sc.clone(),
                args.iter().map(|a| reduce_pcon_endpoints_dt(dts, a)).collect(),
                Box::new(r_nf),
                Box::new(s_nf),
            ))
        }
        // Recurse into PApp so that e.g. `pcon @ (~ i0)` reduces too.
        Term::PApp(p, r) => {
            // If p is TCon(d, pc, args) referencing a path constructor, and r
            // is a concrete endpoint, reduce via the PConSig faces.
            let r_nf = nbe_eval(r);
            let r_is_endpoint = match &r_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    dnf == crate::cubical::interval::dnf_bot() || dnf == crate::cubical::interval::dnf_top()
                }
                _ => false,
            };
            if r_is_endpoint {
                if let Term::TCon(ref d, ref pc, ref args) = **p {
                    if let Some(dt) = dts.iter().find(|dt| &dt.name == d)
                        && let Some(sig) = dt.find_pcon(pc) {
                            let is_i0 = match &r_nf {
                                Term::TInterval(i) => crate::cubical::interval::eval_interval(i) == crate::cubical::interval::dnf_bot(),
                                _ => false,
                            };
                            let face = if is_i0 { &sig.face0 } else { &sig.face1 };
                            let arity = args.len();
                            let reduced_args: Vec<Term> =
                                args.iter().map(|a| reduce_pcon_endpoints_dt(dts, a)).collect();
                            let mut face_inst = face.clone();
                            for k in (0..arity).rev() {
                                face_inst = subst(k as i32, &reduced_args[arity - 1 - k], &face_inst);
                            }
                            return reduce_pcon_endpoints_dt(dts, &nbe_eval(&face_inst));
                        }
                }
            }
            let p2 = reduce_pcon_endpoints_dt(dts, p);
            nbe_eval(&Term::PApp(Box::new(p2), Box::new(r_nf)))
        }
        _ => t,
    }
}


// ---------------------------------------------------------------------------
// Type Checking
// ---------------------------------------------------------------------------

pub fn check(ctx: &Ctx, t: &Term, ty: &Term) -> Result<(), TypeError> {
    check_dt(&[], ctx, t, ty)
}

/// Like `check` but with access to declared datatypes.
/// Pass `&[]` when no datatypes are in scope.
pub fn check_dt(dts: &[Datatype], ctx: &Ctx, t: &Term, ty: &Term) -> Result<(), TypeError> {
    let names: Vec<Name> = ctx.iter().map(|(n, _)| n.clone()).collect();
    crate::debug_scope!("check {} : {} : ctx[{}]", show_term(&names, t), show_term(&names, ty), ctx.len());
    crate::cubical::nbe::set_current_dts(dts);
    match t {
        // Lambda introduction
        Term::TAbs(x, body) => {
            let (a_ty, b_ty) = match ty {
                Term::TPi(_, a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                _ => match nbe_eval(ty) {
                    Term::TPi(_, a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                    other => return Err(TypeError::ExpectedPi(other)),
                },
            };
            check_dt(
                dts,
                &extend_ctx(x.clone(), nbe_eval(&a_ty), ctx),
                body,
                &b_ty,
            )
        }

        // Path-lambda introduction
        Term::PLam(i, body) => {
            let (a_ty, u, v) = match ty {
                Term::TPath(a, u, v) => (a.as_ref().clone(), u.as_ref().clone(), v.as_ref().clone()),
                _ => match nbe_eval(ty) {
                    Term::TPath(a, u, v) => {
                        (a.as_ref().clone(), u.as_ref().clone(), v.as_ref().clone())
                    }
                    other => return Err(TypeError::ExpectedPath(other)),
                },
            };
            let ctx2 = extend_ctx(i.clone(), interval_ty(), ctx);
            let body_ty = match nbe_eval(&a_ty) {
                // a_ty is a type family (PLam): apply it to the freshly-bound
                // interval variable TVar(0) to get the body's type.
                Term::PLam(_, b) => nbe_eval(&beta(&b, &Term::TVar(0))),
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
            if !SKIP_PLAM_ENDPT.with(|c| c.get()) {
                let body_at0 = reduce_pcon_endpoints_dt(
                    dts,
                    &apply_literal(&Literal::NegVar(0), body),
                );
                let body_at1 = reduce_pcon_endpoints_dt(
                    dts,
                    &apply_literal(&Literal::Pos(0), body),
                );
                require_equal_endpt(ctx, &nbe_eval(&u), &body_at0)?;
                require_equal_endpt(ctx, &nbe_eval(&v), &body_at1)?;
            }
            check_dt(dts, &ctx2, body, &body_ty)
        }

        // GlueElem checking
        Term::TGlueElem(phi, t_inner, a) => {
            // Try to use the type as-is first (preserves Glue structure from
            // the annotation). Fall back to nbe_eval for neutral Glue types.
            let glue = match ty {
                Term::TGlue(_, _, _) => ty,
                _ => &nbe_eval(ty),
            };
            match glue {
            Term::TGlue(a_ty, phi_, te) => {
                check_interval(ctx, phi)?;
                require_equal(ctx, &nbe_eval(phi_), &nbe_eval(phi))?;
                let t_ty = match nbe_eval(te) {
                    Term::TMkEquiv(dom_a, _, _, _, _, _) => nbe_eval(&dom_a),
                    Term::TEquiv(dom_a, _) => nbe_eval(&dom_a),
                    Term::TPair(te_a, _) => nbe_eval(&te_a),
                    Term::TAbs(_, body) => {
                        let body_at_1 = beta(&body, &Term::TInterval(I::I1));
                        match body_at_1 {
                            Term::TPair(ref te_a, _) => nbe_eval(te_a),
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
                        Term::TPi("_".into(), Box::new(Term::TIntervalTy), Box::new(shifted_t_ty))
                    }
                    _ => t_ty.clone(),
                };
                check_dt(dts, ctx, t_inner, &cap_ty)?;
                check_dt(dts, ctx, a, &nbe_eval(a_ty))
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
                _ => match nbe_eval(ty) {
                    Term::TSigma(_, a, b) => (a.as_ref().clone(), b.as_ref().clone()),
                    other => return Err(TypeError::ExpectedSigma(other)),
                },
            };
                            check_dt(dts, ctx, a, &nbe_eval(&a_ty))?;
            check_dt(dts, ctx, b, &nbe_eval(&beta(&b_ty, a)))
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
            let expected_ty_nf = nbe_eval(ty);
            let (expected_d, expected_params) = match &expected_ty_nf {
                Term::TData(ed, ep) => {
                    if ed != d {
                        return Err(TypeError::TypeMismatch(
                            Box::new(expected_ty_nf.clone()),
                            Box::new(Term::TData(d.clone(), vec![])),
                        ));
                    }
                    (ed.clone(), ep.clone())
                }
                _ => (d.clone(), vec![]),
            };
            let dt = dts
                .iter()
                .find(|dt| dt.name == expected_d)
                .ok_or_else(|| TypeError::UnknownDatatype(expected_d.clone()))?;
            if let Some(sig) = dt.find_con(c) {
                if args.len() != sig.arity() {
                    return Err(TypeError::WrongNumberOfArgs {
                        con: c.clone(),
                        expected: sig.arity(),
                        got: args.len(),
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
                    dts, ctx, &sig.arg_tys, args, num_params, &initial,
                )?;
                let params = build_params(&param_terms);
                require_equal(ctx, &expected_ty_nf, &Term::TData(d.clone(), params))
            } else if dt.find_pcon(c).is_some() {
                let inferred = infer_dt(dts, ctx, &Term::TCon(d.clone(), c.clone(), args.clone()))?;
                require_equal(ctx, &expected_ty_nf, &nbe_eval(&inferred))
            } else {
                Err(TypeError::UnknownConstructor(expected_d.clone(), c.clone()))
            }
        }

        Term::TPCon(d, pc, args, r) => {
            // Infer the full path type from the constructor signature, then
            // unify with the expected type so endpoint annotations are checked.
            let inferred = infer_dt(dts, ctx, &Term::TPCon(d.clone(), pc.clone(), args.clone(), r.clone()))?;
            require_equal(ctx, &nbe_eval(ty), &nbe_eval(&inferred))
        }

        Term::TSqCon(d, sc, args, r, s) => {
            // When the expected type is TData(d), the PLam check has already
            // stripped the PathP layers. Just verify the data type matches and
            // check interval args are valid.
            let expected_nf = nbe_eval(ty);
            if let Term::TData(ed, _) = &expected_nf {
                if ed == d {
                    let dt_ = dts.iter().find(|dt| &dt.name == d)
                        .ok_or_else(|| TypeError::UnknownDatatype(d.clone()))?;
                    let sig = dt_.find_sqcon(sc)
                        .ok_or_else(|| TypeError::UnknownConstructor(d.clone(), sc.clone()))?;
                    if args.len() != sig.arity() {
                        return Err(TypeError::WrongNumberOfArgs {
                            con: sc.clone(),
                            expected: sig.arity(),
                            got: args.len(),
                        });
                    }
                    check_interval(ctx, r)?;
                    check_interval(ctx, s)?;
                    return Ok(());
                }
            }
            let inferred = infer_dt(dts, ctx, &Term::TSqCon(d.clone(), sc.clone(), args.clone(), r.clone(), s.clone()))?;
            require_equal(ctx, &nbe_eval(ty), &nbe_eval(&inferred))
        }

        // Tactic block: run tactics to produce a proof term, then check it
        Term::TBy(tactics) => {
            let goal_ty = nbe_eval(ty);
            let mut engine = crate::cubical::tactics::TacticEngine::new(dts, goal_ty);
            for tac in tactics {
                engine.run_tactic(tac, ctx)?;
            }
            let proof = engine.into_term()?;
            check_dt(dts, ctx, &proof, ty)
        }

        // ------------------------------------------------------------------
        // Kan operations — check expected type first, then delegate to
        // infer_dt for sub-term checking.  On infer_dt failure, retry
        // with nbe_eval (the comp/hcomp may reduce and become well-typed).
        // ------------------------------------------------------------------

        // hcomp A [phi -> tube, ...] base : A
        Term::THComp(a_ty, _sys, _base) => {
            type_level_dt(dts, ctx, a_ty)?;
            let a_ty_ = nbe_eval(a_ty);
            let expected_nf = nbe_eval(ty);
            if !cumulativity_check(&expected_nf, &a_ty_) {
                require_equal(ctx, &expected_nf, &a_ty_)?;
            }
            match infer_dt(dts, ctx, t) {
                Ok(_) => Ok(()),
                Err(e) => {
                    let reduced = nbe_eval(t);
                    if reduced == *t { Err(e) }
                    else { check_dt(dts, ctx, &reduced, ty) }
                }
            }
        }

        // comp A [phi -> tube, ...] base : A 1
        Term::TComp(a_fam, _sys, _base) => {
            let ctx_i = extend_ctx("i".to_string(), interval_ty(), ctx);
            type_level_dt(dts, &ctx_i, a_fam)?;
            let a_fam_ = nbe_eval(a_fam);
            let a_at1 = match &a_fam_ {
                Term::PLam(_, body) => nbe_eval(&beta(body, &Term::TInterval(I::I1))),
                _ => a_fam_.clone(),
            };
            let expected_nf = nbe_eval(ty);
            if !cumulativity_check(&expected_nf, &a_at1) {
                require_equal(ctx, &expected_nf, &a_at1)?;
            }
            match infer_dt(dts, ctx, t) {
                Ok(_) => Ok(()),
                Err(e) => {
                    let reduced = nbe_eval(t);
                    if reduced == *t { Err(e) }
                    else { check_dt(dts, ctx, &reduced, ty) }
                }
            }
        }

        // fill A [phi -> tube, ...] base : (j : I) -> A j
        // Inferred type is TPath(PLam j (A j), base, TComp A sys base), so
        // delegate to infer_dt for the full type, then check cumulativity.
        Term::TFill(_, _, _) | Term::THFill(_, _, _) => {
            match infer_dt(dts, ctx, t) {
                Ok(inferred) => {
                    let expected_nf = nbe_eval(ty);
                    let inferred_nf = nbe_eval(&inferred);
                    if cumulativity_check(&expected_nf, &inferred_nf) {
                        Ok(())
                    } else {
                        require_equal(ctx, &expected_nf, &inferred_nf)
                    }
                }
                Err(e) => {
                    let reduced = nbe_eval(t);
                    if reduced == *t { Err(e) }
                    else { check_dt(dts, ctx, &reduced, ty) }
                }
            }
        }

        // Fall through to inference + cumulativity.
        t => match infer_dt(dts, ctx, t) {
            Ok(ty_) => {
                let expected_nf = nbe_eval(ty);
                let inferred_nf = nbe_eval(&ty_);
                if cumulativity_check(&expected_nf, &inferred_nf) {
                    Ok(())
                } else {
                    require_equal(ctx, &expected_nf, &inferred_nf)
                }
            }
            Err(e) => {
                let reduced = nbe_eval(t);
                if reduced == *t {
                    Err(e)
                } else {
                    check_dt(dts, ctx, &reduced, ty)
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Universe cumulativity
// ---------------------------------------------------------------------------

/// Check whether `inferred` is a subtype of `expected` under cumulativity.
///
/// Rules:
/// - `TUniv(n) ≤ TUniv(m)` when `n ≤ m` (cumulativity of universes)
/// - `TPi(x, A, B) ≤ TPi(x, A', B')` when `A' ≤ A` (contravariant domain)
///   and `B ≤ B'` (covariant codomain), checked recursively
/// - `TSigma(x, A, B) ≤ TSigma(x, A', B')` when `A ≤ A'` and `B ≤ B'`
///   (covariant in both), checked recursively
fn cumulativity_check(expected: &Term, inferred: &Term) -> bool {
    match (expected, inferred) {
        // Universe cumulativity: U_n is subtype of U_m when n ≤ m
        (Term::TUniv(m), Term::TUniv(n)) => n <= m,

        // Pi cumulativity: contravariant in domain, covariant in codomain
        (Term::TPi(_, a_exp, b_exp), Term::TPi(_, a_inf, b_inf)) => {
            cumulativity_check(a_inf, a_exp) && cumulativity_check(b_exp, b_inf)
        }

        // Sigma cumulativity: covariant in both components
        (Term::TSigma(_, a_exp, b_exp), Term::TSigma(_, a_inf, b_inf)) => {
            cumulativity_check(a_exp, a_inf) && cumulativity_check(b_exp, b_inf)
        }

        _ => false,
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
pub fn infer_closed(t: &Term) -> Result<Term, TypeError> {
    infer(&Vec::new(), t)
}

#[allow(dead_code)]
pub fn check_closed(t: &Term, ty: &Term) -> Result<(), TypeError> {
    check(&Vec::new(), t, ty)
}

#[allow(dead_code)]
pub fn infer_closed_dt(dts: &[Datatype], t: &Term) -> Result<Term, TypeError> {
    infer_dt(dts, &Vec::new(), t)
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
) -> Result<(), TypeError> {
    for sqcon in &dt.sqcons {
        let i0 = Term::TInterval(I::I0);
        let i1 = Term::TInterval(I::I1);

        // Use reduce_pcon_endpoints_dt to reduce terms that reference path
        // constructors at concrete interval endpoints. This is needed because
        // raw TCon references to path constructors don't reduce in NbE.
        let reduce = |t: &Term| -> Term { reduce_pcon_endpoints_dt(dts, t) };

        // PApp(face_j0, I0) == face_i0
        let fj0_at_i0 = reduce(&Term::PApp(
            Box::new(sqcon.face_j0.clone()),
            Box::new(i0.clone()),
        ));
        let fi0_reduced = reduce(&sqcon.face_i0);
        let empty_ctx: Ctx = Vec::new();
        let eq1 = definitionally_equal_ctx_r(&empty_ctx, &fi0_reduced, &fj0_at_i0);
        if let EtaResult::NotEqual = eq1 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 PApp(face_j0, i0) != face_i0\n  expected={}\n  got={}",
                sqcon.name,
                show_term(&[], &nbe_eval(&fi0_reduced)),
                show_term(&[], &nbe_eval(&fj0_at_i0)),
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
        let fj0_at_i1 = reduce(&Term::PApp(
            Box::new(sqcon.face_j0.clone()),
            Box::new(i1.clone()),
        ));
        let fi1_reduced = reduce(&sqcon.face_i1);
        let eq2 = definitionally_equal_ctx_r(&empty_ctx, &fi1_reduced, &fj0_at_i1);
        if let EtaResult::NotEqual = eq2 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 PApp(face_j0, i1) != face_i1\n  expected={}\n  got={}",
                sqcon.name,
                show_term(&[], &nbe_eval(&fi1_reduced)),
                show_term(&[], &nbe_eval(&fj0_at_i1)),
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
        let fj1_at_i0 = reduce(&Term::PApp(
            Box::new(sqcon.face_j1.clone()),
            Box::new(i0.clone()),
        ));
        let eq3 = definitionally_equal_ctx_r(&empty_ctx, &fi0_reduced, &fj1_at_i0);
        if let EtaResult::NotEqual = eq3 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 PApp(face_j1, i0) != face_i0\n  expected={}\n  got={}",
                sqcon.name,
                show_term(&[], &nbe_eval(&fi0_reduced)),
                show_term(&[], &nbe_eval(&fj1_at_i0)),
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
        let fj1_at_i1 = reduce(&Term::PApp(
            Box::new(sqcon.face_j1.clone()),
            Box::new(i1.clone()),
        ));
        let eq4 = definitionally_equal_ctx_r(&empty_ctx, &fi1_reduced, &fj1_at_i1);
        if let EtaResult::NotEqual = eq4 {
            return Err(TypeError::Other(format!(
                "square constructor '{}' boundary coherence: \
                 PApp(face_j1, i1) != face_i1\n  expected={}\n  got={}",
                sqcon.name,
                show_term(&[], &nbe_eval(&fi1_reduced)),
                show_term(&[], &nbe_eval(&fj1_at_i1)),
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

pub fn check_closed_dt(dts: &[Datatype], t: &Term, ty: &Term) -> Result<(), TypeError> {
    check_dt(dts, &Vec::new(), t, ty)
}

#[allow(dead_code)]
pub fn report_infer(label: &str, t: &Term) {
    match infer_closed(t) {
        Ok(ty) => println!("  ✓  {}\n       : {}", label, ty),
        Err(e) => println!("  ✗  {}\n{}", label, e),
    }
}

#[allow(dead_code)]
pub fn report_check(label: &str, t: &Term, ty: &Term) {
    match check_closed(t, ty) {
        Ok(()) => println!("  ✓  {}\n       ⊢ {}\n       : {}", label, t, ty),
        Err(e) => println!("  ✗  {}\n{}", label, e),
    }
}