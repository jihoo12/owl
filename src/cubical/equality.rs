// Cubical Equality — Rust port of Equality.hs
//
// Depends on:
//   crate::interval::I
//   crate::syntax::{Term, Name, shift, beta}
//   crate::eval::{is_top_dnf, is_bot_dnf}

use std::collections::HashMap;

use crate::cubical::nbe::{meta_mentions, nbe_eval, nbe_eval_ctx, try_solve_meta};
use crate::cubical::session::Session;
use crate::cubical::syntax::{Name, Term, beta, shift};
use crate::cubical::typechecker::Ctx;

// ---------------------------------------------------------------------------
// Term size (fuel derivation)
// ---------------------------------------------------------------------------

/// Structural node count of a term. Used to derive the initial fuel for
/// `eta_eq`; see `initial_fuel` for the termination argument.
pub fn term_size(t: &Term) -> usize {
    match t {
        Term::TVar(_)
        | Term::TUniv(_)
        | Term::TIntervalTy
        | Term::TInterval(_)
        | Term::TCube(_)
        | Term::TProp
        | Term::TSSet => 1,

        Term::TAbs(_, b) | Term::PLam(_, b) | Term::TUa(b) | Term::TFst(b) | Term::TSnd(b) => {
            1 + term_size(b)
        }

        Term::TLift(a, _) | Term::TLower(a) => 1 + term_size(a),

        Term::TApp(f, a)
        | Term::PApp(f, a)
        | Term::TEquiv(f, a)
        | Term::TEquivFwd(f, a)
        | Term::TTransport(f, a)
        | Term::TPair(f, a) => 1 + term_size(f) + term_size(a),

        Term::TTransp(a, r, x) => 1 + term_size(a) + term_size(r) + term_size(x),

        Term::TPi(_, a, b, _) | Term::TSigma(_, a, b) => 1 + term_size(a) + term_size(b),

        Term::TPath(a, u, v)
        | Term::TGlue(a, u, v)
        | Term::TGlueElem(a, u, v)
        | Term::TUnglue(a, u, v) => 1 + term_size(a) + term_size(u) + term_size(v),

        Term::TPartial(a, u) => 1 + term_size(a) + term_size(u),

        Term::TSystemType(sys) => {
            1 + sys
                .iter()
                .map(|(phi, a)| term_size(phi) + term_size(a))
                .sum::<usize>()
        }

        Term::THComp(a, sys, u0) => {
            let mut s = 1 + term_size(a) + term_size(u0);
            for (phi, t) in sys {
                s += term_size(phi) + term_size(t);
            }
            s
        }

        Term::TComp(a, sys, u0) => {
            let mut s = 1 + term_size(a) + term_size(u0);
            for (phi, t) in sys {
                s += term_size(phi) + term_size(t);
            }
            s
        }

        Term::TFill(a, sys, u0) => {
            let mut s = 1 + term_size(a) + term_size(u0);
            for (phi, t) in sys {
                s += term_size(phi) + term_size(t);
            }
            s
        }

        Term::THFill(a, sys, u0) => {
            let mut s = 1 + term_size(a) + term_size(u0);
            for (phi, t) in sys {
                s += term_size(phi) + term_size(t);
            }
            s
        }

        Term::TMkEquiv(a, b, f, g, e, s) => {
            1 + term_size(a)
                + term_size(b)
                + term_size(f)
                + term_size(g)
                + term_size(e)
                + term_size(s)
        }

        // Inductive types / HITs
        Term::TData(_, params) => 1 + params.iter().map(term_size).sum::<usize>(),

        Term::TCon(_, _, args) => 1 + args.iter().map(term_size).sum::<usize>(),

        Term::TPCon(_, _, args, r) => 1 + args.iter().map(term_size).sum::<usize>() + term_size(r),

        Term::TElim(motive, cases, scrut) => {
            1 + term_size(motive)
                + cases.iter().map(|c| term_size(&c.body)).sum::<usize>()
                + term_size(scrut)
        }

        Term::Meta(_) | Term::TBy(_) => 1,
        Term::TSqCon(_, _, args, r, s) => {
            1 + args.iter().map(|a| term_size(a)).sum::<usize>() + term_size(r) + term_size(s)
        }
        Term::TProj(_, r) => 1 + term_size(r),
        Term::TRecordUpdate(r, updates) => {
            1 + term_size(r) + updates.iter().map(|(_, e)| term_size(e)).sum::<usize>()
        }
        Term::TDelay(a) | Term::TNext(a) | Term::TForce(a) => 1 + term_size(a),
        Term::TCellCon(_, _, args, ivars) => {
            1 + args.iter().map(term_size).sum::<usize>()
                + ivars.iter().map(term_size).sum::<usize>()
        }
    }
}

/// Starting fuel for an eta-equality check.
/// Floor of 16 ensures small terms get reasonable headroom.
pub fn initial_fuel(t1: &Term, t2: &Term) -> usize {
    (term_size(t1) + term_size(t2)).max(16)
}

// ---------------------------------------------------------------------------
// Eta-equality result
// ---------------------------------------------------------------------------

/// Three-valued result of an eta-equality check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EtaResult {
    /// The two terms are definitionally equal.
    Equal,
    /// The two terms are definitionally distinct.
    NotEqual,
    /// Fuel ran out before a verdict was reached (inconclusive).
    Exhausted,
}

/// Conjunctive combination: both sides must be `Equal`.
/// `Exhausted` is infectious; `NotEqual` beats `Equal` but loses to `Exhausted`.
pub fn and_result(a: EtaResult, b: EtaResult) -> EtaResult {
    use EtaResult::*;
    match (a, b) {
        (Equal, r) => r,
        (r, Equal) => r,
        (Exhausted, _) => Exhausted,
        (_, Exhausted) => Exhausted,
        (NotEqual, NotEqual) => NotEqual,
    }
}

// ---------------------------------------------------------------------------
// Context-free definitional equality
// ---------------------------------------------------------------------------

#[allow(dead_code)]
pub fn definitionally_equal(t1: &Term, t2: &Term, session: &mut Session) -> bool {
    let v1 = nbe_eval(t1, session);
    let v2 = nbe_eval(t2, session);
    v1 == v2 || eta_eq(initial_fuel(&v1, &v2), &Vec::new(), &v1, &v2, session) == EtaResult::Equal
}

#[allow(dead_code)]
pub fn definitionally_equal_ctx(ctx: &Ctx, t1: &Term, t2: &Term, session: &mut Session) -> bool {
    let v1 = nbe_eval_ctx(ctx.len(), t1, session);
    let v2 = nbe_eval_ctx(ctx.len(), t2, session);
    v1 == v2 || eta_eq(initial_fuel(&v1, &v2), ctx, &v1, &v2, session) == EtaResult::Equal
}

/// Like `definitionally_equal_ctx` but surfaces fuel exhaustion as a distinct
/// `EtaResult` so callers can emit a proper error.
pub fn definitionally_equal_ctx_r(
    ctx: &Ctx,
    t1: &Term,
    t2: &Term,
    session: &mut Session,
) -> EtaResult {
    let v1 = nbe_eval_ctx(ctx.len(), t1, session);
    let v2 = nbe_eval_ctx(ctx.len(), t2, session);
    if v1 == v2 {
        EtaResult::Equal
    } else {
        eta_eq(initial_fuel(&v1, &v2), ctx, &v1, &v2, session)
    }
}

// ---------------------------------------------------------------------------
// Path boundary reduction
// ---------------------------------------------------------------------------

/// If `p : Path A u v` and `r` is `I0` / `I1`, return the endpoint.
pub fn reduce_papp_by_type(ctx: &Ctx, p: &Term, r: &Term, session: &mut Session) -> Option<Term> {
    match infer_ty(ctx, p, session) {
        Some(Term::TPath(_, u, v)) => {
            let r_ = nbe_eval_ctx(ctx.len(), r, session);
            let d = match &r_ {
                Term::TCube(d) => d.clone(),
                Term::TInterval(i) => crate::cubical::interval::eval_interval(i),
                _ => return None,
            };
            if d == crate::cubical::interval::dnf_bot() {
                Some(nbe_eval_ctx(ctx.len(), &u, session))
            } else if d == crate::cubical::interval::dnf_top() {
                Some(nbe_eval_ctx(ctx.len(), &v, session))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn infer_ty(ctx: &Ctx, t: &Term, session: &mut Session) -> Option<Term> {
    match t {
        Term::TVar(i) => {
            let i = *i as usize;
            if i < ctx.len() {
                Some(nbe_eval_ctx(
                    ctx.len(),
                    &shift((i + 1) as i32, 0, &ctx[i].1),
                    session,
                ))
            } else {
                None
            }
        }
        Term::TApp(f, a) => match infer_ty(ctx, f, session) {
            Some(Term::TPi(_, _, b_ty, _)) => {
                Some(nbe_eval_ctx(ctx.len(), &beta(&b_ty, a), session))
            }
            _ => None,
        },
        Term::TElim(motive, _, scrut) => Some(nbe_eval_ctx(
            ctx.len(),
            &Term::TApp(Box::new((**motive).clone()), Box::new((**scrut).clone())),
            session,
        )),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Lightweight neutral type inference
// ---------------------------------------------------------------------------

fn infer_neutral_ty(ctx: &Ctx, t: &Term, session: &mut Session) -> Option<Term> {
    match t {
        Term::TVar(i) => {
            let i = *i as usize;
            if i < ctx.len() {
                Some(nbe_eval_ctx(
                    ctx.len(),
                    &shift((i + 1) as i32, 0, &ctx[i].1),
                    session,
                ))
            } else {
                None
            }
        }
        Term::TApp(f, a) => match infer_neutral_ty(ctx, f, session) {
            Some(Term::TPi(_, _, b_ty, _)) => {
                Some(nbe_eval_ctx(ctx.len(), &beta(&b_ty, a), session))
            }
            _ => None,
        },
        Term::TElim(motive, _, scrut) => Some(nbe_eval_ctx(
            ctx.len(),
            &Term::TApp(Box::new((**motive).clone()), Box::new((**scrut).clone())),
            session,
        )),
        _ => None,
    }
}

/// Try to infer the Pi domain of `neutral` from the context, to use as the
/// type of the fresh variable introduced when eta-expanding `neutral` against
/// a lambda. Returns `None` when the type cannot be determined.
pub fn infer_lam_dom(ctx: &Ctx, neutral: &Term, session: &mut Session) -> Option<Term> {
    match infer_neutral_ty(ctx, neutral, session) {
        Some(Term::TPi(_, dom_ty, _, _)) => Some(nbe_eval_ctx(ctx.len(), &dom_ty, session)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Core eta-equality
// ---------------------------------------------------------------------------

/// Build `PApp(...PApp(TCon(d,c,args), arg1)..., argN)` from a TCon base
/// and optional first interval argument.
fn build_papp_chain(d: &str, c: &str, args: &[Term], first_ivar: Option<&Term>) -> Term {
    let base = Term::TCon(d.to_string(), c.to_string(), args.to_vec());
    match first_ivar {
        Some(r) => Term::PApp(Box::new(base), Box::new(r.clone())),
        None => base,
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct EtaMemoKey {
    fuel: usize,
    ctx: Ctx,
    left: Term,
    right: Term,
}

type EtaMemo = HashMap<EtaMemoKey, EtaResult>;

/// `eta_eq(fuel, ctx, t1, t2)` checks whether `t1` and `t2` are
/// definitionally equal under `ctx`, consuming `fuel` for eta-expansion steps.
pub fn eta_eq(fuel: usize, ctx: &Ctx, t1: &Term, t2: &Term, session: &mut Session) -> EtaResult {
    let mut memo = EtaMemo::new();
    eta_eq_memo(fuel, ctx, t1, t2, &mut memo, session)
}

fn eta_eq_memo(
    fuel: usize,
    ctx: &Ctx,
    t1: &Term,
    t2: &Term,
    memo: &mut EtaMemo,
    session: &mut Session,
) -> EtaResult {
    let key = EtaMemoKey {
        fuel,
        ctx: ctx.clone(),
        left: t1.clone(),
        right: t2.clone(),
    };

    if let Some(result) = memo.get(&key) {
        return *result;
    }

    let result = eta_eq_uncached(fuel, ctx, t1, t2, memo, session);
    memo.insert(key, result);
    result
}

fn eta_eq_uncached(
    fuel: usize,
    ctx: &Ctx,
    t1: &Term,
    t2: &Term,
    memo: &mut EtaMemo,
    session: &mut Session,
) -> EtaResult {
    use EtaResult::*;

    if fuel == 0 {
        return Exhausted;
    }

    if t1 == t2 {
        return Equal;
    }

    // ------------------------------------------------------------------
    // Metavariable unification
    // ------------------------------------------------------------------
    if let Term::Meta(i) = t1 {
        // Check if already solved
        if let Some(solution) = session.get_meta_solution(*i) {
            return eta_eq_memo(fuel, ctx, &solution, t2, memo, session);
        }
        if !meta_mentions(*i, t2) {
            try_solve_meta(*i, t2, session);
            return Equal;
        }
        // occurs check failed — can't solve
        return NotEqual;
    }
    if let Term::Meta(i) = t2 {
        if let Some(solution) = session.get_meta_solution(*i) {
            return eta_eq_memo(fuel, ctx, t1, &solution, memo, session);
        }
        if !meta_mentions(*i, t1) {
            try_solve_meta(*i, t1, session);
            return Equal;
        }
        return NotEqual;
    }

    // ------------------------------------------------------------------
    // Path boundary reduction (consumes fuel)
    // ------------------------------------------------------------------
    if let Term::PApp(p, r) = t1
        && let Some(u) = reduce_papp_by_type(ctx, p, r, session)
    {
        return eta_eq_memo(fuel - 1, ctx, &u, t2, memo, session);
    }
    if let Term::PApp(p, r) = t2
        && let Some(u) = reduce_papp_by_type(ctx, p, r, session)
    {
        return eta_eq_memo(fuel - 1, ctx, t1, &u, memo, session);
    }

    // ------------------------------------------------------------------
    // Lambda eta (consumes fuel)
    // ------------------------------------------------------------------

    // Both sides are lambdas.
    if let (Term::TAbs(x, b1), Term::TAbs(_, b2)) = (t1, t2) {
        let dom = infer_lam_dom(ctx, t1, session)
            .or_else(|| infer_lam_dom(ctx, t2, session))
            .unwrap_or(Term::TUniv(0));
        let mut ctx2 = vec![(x.clone(), dom)];
        ctx2.extend_from_slice(ctx);
        return eta_eq_memo(
            fuel - 1,
            &ctx2,
            &nbe_eval_ctx(ctx2.len(), b1, session),
            &nbe_eval_ctx(ctx2.len(), b2, session),
            memo,
            session,
        );
    }

    // Only RHS is a lambda — eta-expand neutral LHS.
    if let Term::TAbs(x, b2) = t2 {
        return match infer_lam_dom(ctx, t1, session) {
            None => Exhausted,
            Some(dom) => {
                let mut ctx2 = vec![(x.clone(), dom)];
                ctx2.extend_from_slice(ctx);
                eta_eq_memo(
                    fuel - 1,
                    &ctx2,
                    &nbe_eval_ctx(
                        ctx2.len(),
                        &Term::TApp(Box::new(shift(1, 0, t1)), Box::new(Term::TVar(0))),
                        session,
                    ),
                    &nbe_eval_ctx(ctx2.len(), b2, session),
                    memo,
                    session,
                )
            }
        };
    }

    // Only LHS is a lambda — eta-expand neutral RHS.
    if let Term::TAbs(x, b1) = t1 {
        return match infer_lam_dom(ctx, t2, session) {
            None => Exhausted,
            Some(dom) => {
                let mut ctx2 = vec![(x.clone(), dom)];
                ctx2.extend_from_slice(ctx);
                eta_eq_memo(
                    fuel - 1,
                    &ctx2,
                    &nbe_eval_ctx(ctx2.len(), b1, session),
                    &nbe_eval_ctx(
                        ctx2.len(),
                        &Term::TApp(Box::new(shift(1, 0, t2)), Box::new(Term::TVar(0))),
                        session,
                    ),
                    memo,
                    session,
                )
            }
        };
    }

    // ------------------------------------------------------------------
    // Path-lambda eta (consumes fuel)
    // ------------------------------------------------------------------

    // Both sides are path-lambdas.
    if let (Term::PLam(i, b1), Term::PLam(_, b2)) = (t1, t2) {
        let mut ctx2 = vec![(i.clone(), Term::TIntervalTy)];
        ctx2.extend_from_slice(ctx);
        return eta_eq_memo(
            fuel - 1,
            &ctx2,
            &nbe_eval_ctx(ctx2.len(), b1, session),
            &nbe_eval_ctx(ctx2.len(), b2, session),
            memo,
            session,
        );
    }

    // Only RHS is a path-lambda.
    if let Term::PLam(i, b2) = t2 {
        let mut ctx2 = vec![(i.clone(), Term::TIntervalTy)];
        ctx2.extend_from_slice(ctx);
        return eta_eq_memo(
            fuel - 1,
            &ctx2,
            &nbe_eval_ctx(
                ctx2.len(),
                &Term::PApp(Box::new(shift(1, 0, t1)), Box::new(Term::TVar(0))),
                session,
            ),
            &nbe_eval_ctx(ctx2.len(), b2, session),
            memo,
            session,
        );
    }

    // Only LHS is a path-lambda.
    if let Term::PLam(i, b1) = t1 {
        let mut ctx2 = vec![(i.clone(), Term::TIntervalTy)];
        ctx2.extend_from_slice(ctx);
        return eta_eq_memo(
            fuel - 1,
            &ctx2,
            &nbe_eval_ctx(ctx2.len(), b1, session),
            &nbe_eval_ctx(
                ctx2.len(),
                &Term::PApp(Box::new(shift(1, 0, t2)), Box::new(Term::TVar(0))),
                session,
            ),
            memo,
            session,
        );
    }

    // ------------------------------------------------------------------
    // Congruence on neutral spines (structural: no fuel consumed)
    // ------------------------------------------------------------------
    if let (Term::TApp(f1, a1), Term::TApp(f2, a2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, f1, f2, memo, session),
            eta_eq_memo(fuel, ctx, a1, a2, memo, session),
        );
    }
    if let (Term::PApp(p1, r1), Term::PApp(p2, r2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, p1, p2, memo, session),
            eta_eq_memo(fuel, ctx, r1, r2, memo, session),
        );
    }

    // ------------------------------------------------------------------
    // TPCon / TSqCon / TCellCon ↔ TCon + PApp structural equivalence.
    // These are different AST representations of the same thing:
    //   TPCon(d,c,args,r) ≡ PApp(TCon(d,c,args), r)
    //   TSqCon(d,c,args,r,s) ≡ PApp(PApp(TCon(d,c,args), r), s)
    //   TCellCon(d,c,args,[r1..rn]) ≡ PApp(...PApp(TCon(d,c,args),r1)...rn)
    // ------------------------------------------------------------------
    if let (Term::TPCon(d1, c1, args1, r1), _) = (t1, t2) {
        let papp_form = build_papp_chain(d1, c1, args1, Some(r1));
        return eta_eq_memo(fuel, ctx, &papp_form, t2, memo, session);
    }
    if let (_, Term::TPCon(d2, c2, args2, r2)) = (t1, t2) {
        let papp_form = build_papp_chain(d2, c2, args2, Some(r2));
        return eta_eq_memo(fuel, ctx, t1, &papp_form, memo, session);
    }
    if let (Term::TSqCon(d1, c1, args1, r1, s1), _) = (t1, t2) {
        let papp_form = build_papp_chain(d1, c1, args1, Some(r1));
        let papp_form = Term::PApp(Box::new(papp_form), Box::new((**s1).clone()));
        return eta_eq_memo(fuel, ctx, &papp_form, t2, memo, session);
    }
    if let (_, Term::TSqCon(d2, c2, args2, r2, s2)) = (t1, t2) {
        let papp_form = build_papp_chain(d2, c2, args2, Some(r2));
        let papp_form = Term::PApp(Box::new(papp_form), Box::new((**s2).clone()));
        return eta_eq_memo(fuel, ctx, t1, &papp_form, memo, session);
    }
    if let (Term::TCellCon(d1, c1, args1, ivars1), _) = (t1, t2) {
        let papp_form = build_papp_chain(d1, c1, args1, None);
        let papp_form = ivars1.iter().fold(papp_form, |f, iv| {
            Term::PApp(Box::new(f), Box::new(iv.clone()))
        });
        return eta_eq_memo(fuel, ctx, &papp_form, t2, memo, session);
    }
    if let (_, Term::TCellCon(d2, c2, args2, ivars2)) = (t1, t2) {
        let papp_form = build_papp_chain(d2, c2, args2, None);
        let papp_form = ivars2.iter().fold(papp_form, |f, iv| {
            Term::PApp(Box::new(f), Box::new(iv.clone()))
        });
        return eta_eq_memo(fuel, ctx, t1, &papp_form, memo, session);
    }

    // ------------------------------------------------------------------
    // Type congruence (structural: no fuel consumed)
    // ------------------------------------------------------------------
    if let (Term::TPi(_, a1, b1, _), Term::TPi(_, a2, b2, _)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo, session),
            eta_eq_memo(fuel, ctx, b1, b2, memo, session),
        );
    }
    if let (Term::TPath(ty1, u1, v1), Term::TPath(ty2, u2, v2)) = (t1, t2) {
        // Normalize type families: if one is PLam and the other isn't,
        // wrap the non-PLam side in a constant PLam so they structurally match.
        let (ty1_eff, ty2_eff): (Box<Term>, Box<Term>) = match (ty1.as_ref(), ty2.as_ref()) {
            (Term::PLam(_, _), Term::PLam(_, _)) => ((*ty1).clone(), (*ty2).clone()),
            (Term::PLam(_, _), _) => (
                (*ty1).clone(),
                Box::new(Term::PLam("_".to_string(), Box::new((**ty2).clone()))),
            ),
            (_, Term::PLam(_, _)) => (
                Box::new(Term::PLam("_".to_string(), Box::new((**ty1).clone()))),
                (*ty2).clone(),
            ),
            _ => ((*ty1).clone(), (*ty2).clone()),
        };
        return and_result(
            and_result(
                eta_eq_memo(fuel, ctx, &ty1_eff, &ty2_eff, memo, session),
                eta_eq_memo(fuel, ctx, u1, u2, memo, session),
            ),
            eta_eq_memo(fuel, ctx, v1, v2, memo, session),
        );
    }
    if let (Term::TSigma(_, a1, b1), Term::TSigma(_, a2, b2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo, session),
            eta_eq_memo(fuel, ctx, b1, b2, memo, session),
        );
    }

    // ------------------------------------------------------------------
    // Pair congruence (structural)
    // ------------------------------------------------------------------
    if let (Term::TPair(a1, b1), Term::TPair(a2, b2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo, session),
            eta_eq_memo(fuel, ctx, b1, b2, memo, session),
        );
    }

    // ------------------------------------------------------------------
    // Sigma eta: one side is a pair, the other is neutral (consumes fuel)
    // ------------------------------------------------------------------
    if let Term::TPair(a1, b1) = t1 {
        return and_result(
            eta_eq_memo(
                fuel - 1,
                ctx,
                a1,
                &nbe_eval_ctx(ctx.len(), &Term::TFst(Box::new(t2.clone())), session),
                memo,
                session,
            ),
            eta_eq_memo(
                fuel - 1,
                ctx,
                b1,
                &nbe_eval_ctx(ctx.len(), &Term::TSnd(Box::new(t2.clone())), session),
                memo,
                session,
            ),
        );
    }
    if let Term::TPair(a2, b2) = t2 {
        return and_result(
            eta_eq_memo(
                fuel - 1,
                ctx,
                &nbe_eval_ctx(ctx.len(), &Term::TFst(Box::new(t1.clone())), session),
                a2,
                memo,
                session,
            ),
            eta_eq_memo(
                fuel - 1,
                ctx,
                &nbe_eval_ctx(ctx.len(), &Term::TSnd(Box::new(t1.clone())), session),
                b2,
                memo,
                session,
            ),
        );
    }

    // ------------------------------------------------------------------
    // Projection congruence on neutral spines (structural)
    // ------------------------------------------------------------------
    if let (Term::TFst(p1), Term::TFst(p2)) = (t1, t2) {
        return eta_eq_memo(fuel, ctx, p1, p2, memo, session);
    }
    if let (Term::TSnd(p1), Term::TSnd(p2)) = (t1, t2) {
        return eta_eq_memo(fuel, ctx, p1, p2, memo, session);
    }
    if let (Term::TProj(f1, r1), Term::TProj(f2, r2)) = (t1, t2) {
        if f1 != f2 {
            return NotEqual;
        }
        return eta_eq_memo(fuel, ctx, r1, r2, memo, session);
    }

    if let (Term::TRecordUpdate(r1, u1), Term::TRecordUpdate(r2, u2)) = (t1, t2) {
        if u1.len() != u2.len() {
            return NotEqual;
        }
        let mut result = eta_eq_memo(fuel, ctx, r1, r2, memo, session);
        for ((f1, e1), (f2, e2)) in u1.iter().zip(u2.iter()) {
            if f1 != f2 {
                return NotEqual;
            }
            result = and_result(result, eta_eq_memo(fuel, ctx, e1, e2, memo, session));
        }
        return result;
    }

    // ------------------------------------------------------------------
    // Inductive types / HITs (structural: no fuel consumed)
    // ------------------------------------------------------------------

    // TData is an atom — equality is already handled by the `t1 == t2`
    // check at the top (same name ↔ equal), so reaching here means
    // different names → NotEqual.  No extra arm needed; the fall-through
    // at the end handles it.

    // Constructor congruence: same datatype, same constructor, check args.
    if let (Term::TCon(d1, c1, args1), Term::TCon(d2, c2, args2)) = (t1, t2) {
        if d1 != d2 || c1 != c2 || args1.len() != args2.len() {
            return NotEqual;
        }
        return args1.iter().zip(args2.iter()).fold(Equal, |acc, (a1, a2)| {
            and_result(acc, eta_eq_memo(fuel, ctx, a1, a2, memo, session))
        });
    }

    // Path-constructor congruence: same datatype, same path-constructor,
    // check ordinary args and then the interval argument.
    if let (Term::TPCon(d1, c1, args1, r1), Term::TPCon(d2, c2, args2, r2)) = (t1, t2) {
        if d1 != d2 || c1 != c2 || args1.len() != args2.len() {
            return NotEqual;
        }
        let args_eq = args1.iter().zip(args2.iter()).fold(Equal, |acc, (a1, a2)| {
            and_result(acc, eta_eq_memo(fuel, ctx, a1, a2, memo, session))
        });
        return and_result(args_eq, eta_eq_memo(fuel, ctx, r1, r2, memo, session));
    }

    // Cell-constructor congruence: same datatype, same cell-constructor,
    // check ordinary args and then each interval argument.
    if let (Term::TCellCon(d1, c1, args1, ivars1), Term::TCellCon(d2, c2, args2, ivars2)) = (t1, t2)
    {
        if d1 != d2 || c1 != c2 || args1.len() != args2.len() || ivars1.len() != ivars2.len() {
            return NotEqual;
        }
        let args_eq = args1.iter().zip(args2.iter()).fold(Equal, |acc, (a1, a2)| {
            and_result(acc, eta_eq_memo(fuel, ctx, a1, a2, memo, session))
        });
        let ivars_eq = ivars1
            .iter()
            .zip(ivars2.iter())
            .fold(Equal, |acc, (i1, i2)| {
                and_result(acc, eta_eq_memo(fuel, ctx, i1, i2, memo, session))
            });
        return and_result(args_eq, ivars_eq);
    }

    // Eliminator congruence: check motive, each matching case body
    // (case order and constructor names must agree), and the scrutinee.
    // This only fires when both sides are stuck TElim neutrals, which
    // requires the scrutinees to be neutral — so this is genuinely the
    // structural congruence on eliminators, not a reduction step.
    if let (Term::TElim(m1, cases1, s1), Term::TElim(m2, cases2, s2)) = (t1, t2) {
        if cases1.len() != cases2.len() {
            return NotEqual;
        }
        let cases_eq = cases1
            .iter()
            .zip(cases2.iter())
            .fold(Equal, |acc, (c1, c2)| {
                if c1.con != c2.con || c1.binders.len() != c2.binders.len() {
                    return NotEqual;
                }
                // Build the extended context for this case's binders.
                // binders is outermost-first; we push them innermost-first
                // so the last binder ends up at index 0, matching the de Bruijn
                // convention used everywhere else in this file.
                let mut case_ctx: Vec<(Name, Term)> = c1
                    .binders
                    .iter()
                    .rev()
                    .map(|b| (b.clone(), Term::TUniv(0)))
                    .collect();
                case_ctx.extend_from_slice(ctx);
                // A stuck elim suspends its case bodies, so a reducible
                // global application (e.g. `mul b c`) that entered a case
                // body via substitution is never reduced by whole-term
                // normalization — leaving `(mul b) c` in the normal form
                // while the same value, entered as an eagerly-evaluated
                // function argument, appears folded. Normalize each body
                // *once* in isolation (terminating: a single top-level
                // evaluation pass) and, if both sides converge to the same
                // normal form, accept. Do NOT recurse on the normalized
                // bodies: re-normalizing a stuck elim's case bodies unfolds
                // recursive definitions one level per pass and never reaches
                // a fixed point. If the single pass does not converge,
                // fall back to the raw structural comparison, which is what
                // this code did before.
                let n1 = nbe_eval_ctx(case_ctx.len(), &c1.body, session);
                let n2 = nbe_eval_ctx(case_ctx.len(), &c2.body, session);
                if n1 == n2 {
                    acc
                } else if c1.body == c2.body {
                    acc
                } else {
                    // Bounded fallback: recursing into the raw bodies lets
                    // proofs that need a couple of unfolds go through, but an
                    // unbounded fallback re-normalizes a stuck elim's case
                    // bodies one definitional level per pass and never reaches
                    // a fixed point on recursive definitions (see the comment
                    // above). Cap the number of nested fallbacks so recursive
                    // definitions like nat_add/nat_mul terminate instead of
                    // overflowing the stack.
                    const ELIM_RECURSE_CAP: usize = 6;
                    let depth = session.elim_depth_enter();
                    if depth >= ELIM_RECURSE_CAP {
                        session.elim_depth_restore(depth);
                        NotEqual
                    } else {
                        let r = and_result(
                            acc,
                            eta_eq_memo(fuel, &case_ctx, &c1.body, &c2.body, memo, session),
                        );
                        session.elim_depth_restore(depth);
                        r
                    }
                }
            });
        return and_result(
            and_result(cases_eq, eta_eq_memo(fuel, ctx, m1, m2, memo, session)),
            eta_eq_memo(fuel, ctx, s1, s2, memo, session),
        );
    }

    // ------------------------------------------------------------------
    // Cubical form congruence (structural: no fuel consumed)
    // ------------------------------------------------------------------
    if let (Term::THComp(a1, sys1, u01), Term::THComp(a2, sys2, u02)) = (t1, t2) {
        if sys1.len() != sys2.len() {
            return NotEqual;
        }
        let mut result = and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo, session),
            eta_eq_memo(fuel, ctx, u01, u02, memo, session),
        );
        for ((phi1, t1), (phi2, t2)) in sys1.iter().zip(sys2.iter()) {
            result = and_result(
                result,
                and_result(
                    eta_eq_memo(fuel, ctx, phi1, phi2, memo, session),
                    eta_eq_memo(fuel, ctx, t1, t2, memo, session),
                ),
            );
        }
        return result;
    }
    if let (Term::TComp(a1, sys1, u01), Term::TComp(a2, sys2, u02)) = (t1, t2) {
        if sys1.len() != sys2.len() {
            return NotEqual;
        }
        let mut result = and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo, session),
            eta_eq_memo(fuel, ctx, u01, u02, memo, session),
        );
        for ((phi1, t1), (phi2, t2)) in sys1.iter().zip(sys2.iter()) {
            result = and_result(
                result,
                and_result(
                    eta_eq_memo(fuel, ctx, phi1, phi2, memo, session),
                    eta_eq_memo(fuel, ctx, t1, t2, memo, session),
                ),
            );
        }
        return result;
    }
    if let (Term::TFill(a1, sys1, u01), Term::TFill(a2, sys2, u02)) = (t1, t2) {
        if sys1.len() != sys2.len() {
            return NotEqual;
        }
        let mut result = and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo, session),
            eta_eq_memo(fuel, ctx, u01, u02, memo, session),
        );
        for ((phi1, t1), (phi2, t2)) in sys1.iter().zip(sys2.iter()) {
            result = and_result(
                result,
                and_result(
                    eta_eq_memo(fuel, ctx, phi1, phi2, memo, session),
                    eta_eq_memo(fuel, ctx, t1, t2, memo, session),
                ),
            );
        }
        return result;
    }
    if let (Term::THFill(a1, sys1, u01), Term::THFill(a2, sys2, u02)) = (t1, t2) {
        if sys1.len() != sys2.len() {
            return NotEqual;
        }
        let mut result = and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo, session),
            eta_eq_memo(fuel, ctx, u01, u02, memo, session),
        );
        for ((phi1, t1), (phi2, t2)) in sys1.iter().zip(sys2.iter()) {
            result = and_result(
                result,
                and_result(
                    eta_eq_memo(fuel, ctx, phi1, phi2, memo, session),
                    eta_eq_memo(fuel, ctx, t1, t2, memo, session),
                ),
            );
        }
        return result;
    }
    if let (Term::TGlue(a1, phi1, te1), Term::TGlue(a2, phi2, te2)) = (t1, t2) {
        return and_result(
            and_result(
                eta_eq_memo(fuel, ctx, a1, a2, memo, session),
                eta_eq_memo(fuel, ctx, phi1, phi2, memo, session),
            ),
            eta_eq_memo(fuel, ctx, te1, te2, memo, session),
        );
    }
    if let (Term::TGlueElem(phi1, t1v, a1), Term::TGlueElem(phi2, t2v, a2)) = (t1, t2) {
        return and_result(
            and_result(
                eta_eq_memo(fuel, ctx, phi1, phi2, memo, session),
                eta_eq_memo(fuel, ctx, t1v, t2v, memo, session),
            ),
            eta_eq_memo(fuel, ctx, a1, a2, memo, session),
        );
    }
    if let (Term::TUnglue(phi1, te1, g1), Term::TUnglue(phi2, te2, g2)) = (t1, t2) {
        return and_result(
            and_result(
                eta_eq_memo(fuel, ctx, phi1, phi2, memo, session),
                eta_eq_memo(fuel, ctx, te1, te2, memo, session),
            ),
            eta_eq_memo(fuel, ctx, g1, g2, memo, session),
        );
    }
    if let (Term::TPartial(phi1, a1), Term::TPartial(phi2, a2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, phi1, phi2, memo, session),
            eta_eq_memo(fuel, ctx, a1, a2, memo, session),
        );
    }
    if let (Term::TTransport(p1, x1), Term::TTransport(p2, x2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, p1, p2, memo, session),
            eta_eq_memo(fuel, ctx, x1, x2, memo, session),
        );
    }
    if let (Term::TTransp(a1, r1, x1), Term::TTransp(a2, r2, x2)) = (t1, t2) {
        return and_result(
            and_result(
                eta_eq_memo(fuel, ctx, a1, a2, memo, session),
                eta_eq_memo(fuel, ctx, r1, r2, memo, session),
            ),
            eta_eq_memo(fuel, ctx, x1, x2, memo, session),
        );
    }
    if let (Term::TUa(e1), Term::TUa(e2)) = (t1, t2) {
        return eta_eq_memo(fuel, ctx, e1, e2, memo, session);
    }
    if let (Term::TEquiv(a1, b1), Term::TEquiv(a2, b2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo, session),
            eta_eq_memo(fuel, ctx, b1, b2, memo, session),
        );
    }

    NotEqual
}
