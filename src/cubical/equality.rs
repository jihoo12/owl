// Cubical Equality — Rust port of Equality.hs
//
// Depends on:
//   crate::interval::I
//   crate::syntax::{Term, Name, shift, beta}
//   crate::eval::{is_top_dnf, is_bot_dnf}

use std::collections::HashMap;

use crate::cubical::nbe::nbe_eval;
use crate::cubical::syntax::{Name, Term, beta, shift};

/// A context maps de Bruijn names to their types.
pub type Ctx = Vec<(Name, Term)>;

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
        | Term::TCube(_) => 1,

        Term::TAbs(_, b) | Term::PLam(_, b) | Term::TUa(b) | Term::TFst(b) | Term::TSnd(b) => {
            1 + term_size(b)
        }

        Term::TApp(f, a)
        | Term::PApp(f, a)
        | Term::TEquiv(f, a)
        | Term::TEquivFwd(f, a)
        | Term::TTransport(f, a)
        | Term::TPair(f, a) => 1 + term_size(f) + term_size(a),

        Term::TPi(_, a, b) | Term::TSigma(_, a, b) => 1 + term_size(a) + term_size(b),

        Term::TPath(a, u, v)
        | Term::TGlue(a, u, v)
        | Term::TGlueElem(a, u, v)
        | Term::TUnglue(a, u, v) => 1 + term_size(a) + term_size(u) + term_size(v),

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
pub fn definitionally_equal(t1: &Term, t2: &Term) -> bool {
    let v1 = nbe_eval(t1);
    let v2 = nbe_eval(t2);
    v1 == v2 || eta_eq(initial_fuel(&v1, &v2), &Vec::new(), &v1, &v2) == EtaResult::Equal
}

#[allow(dead_code)]
pub fn definitionally_equal_ctx(ctx: &Ctx, t1: &Term, t2: &Term) -> bool {
    let v1 = nbe_eval(t1);
    let v2 = nbe_eval(t2);
    v1 == v2 || eta_eq(initial_fuel(&v1, &v2), ctx, &v1, &v2) == EtaResult::Equal
}

/// Like `definitionally_equal_ctx` but surfaces fuel exhaustion as a distinct
/// `EtaResult` so callers can emit a proper error.
pub fn definitionally_equal_ctx_r(ctx: &Ctx, t1: &Term, t2: &Term) -> EtaResult {
    let v1 = nbe_eval(t1);
    let v2 = nbe_eval(t2);
    if v1 == v2 {
        EtaResult::Equal
    } else {
        eta_eq(initial_fuel(&v1, &v2), ctx, &v1, &v2)
    }
}

// ---------------------------------------------------------------------------
// Path boundary reduction
// ---------------------------------------------------------------------------

/// If `p : Path A u v` and `r` is `I0` / `I1`, return the endpoint.
pub fn reduce_papp_by_type(ctx: &Ctx, p: &Term, r: &Term) -> Option<Term> {
    match infer_ty(ctx, p) {
        Some(Term::TPath(_, u, v)) => {
            let r_ = nbe_eval(r);
            let d = match &r_ {
                Term::TCube(d) => d.clone(),
                Term::TInterval(i) => crate::cubical::interval::eval_interval(i),
                _ => return None,
            };
            if d == crate::cubical::interval::dnf_bot() {
                Some(nbe_eval(&u))
            } else if d == crate::cubical::interval::dnf_top() {
                Some(nbe_eval(&v))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn infer_ty(ctx: &Ctx, t: &Term) -> Option<Term> {
    match t {
        Term::TVar(i) => {
            let i = *i as usize;
            if i < ctx.len() {
                Some(nbe_eval(&shift((i + 1) as i32, 0, &ctx[i].1)))
            } else {
                None
            }
        }
        Term::TApp(f, a) => match infer_ty(ctx, f) {
            Some(Term::TPi(_, _, b_ty)) => Some(nbe_eval(&beta(&b_ty, a))),
            _ => None,
        },
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Lightweight neutral type inference
// ---------------------------------------------------------------------------

fn infer_neutral_ty(ctx: &Ctx, t: &Term) -> Option<Term> {
    match t {
        Term::TVar(i) => {
            let i = *i as usize;
            if i < ctx.len() {
                Some(nbe_eval(&shift((i + 1) as i32, 0, &ctx[i].1)))
            } else {
                None
            }
        }
        Term::TApp(f, a) => match infer_neutral_ty(ctx, f) {
            Some(Term::TPi(_, _, b_ty)) => Some(nbe_eval(&beta(&b_ty, a))),
            _ => None,
        },
        _ => None,
    }
}

/// Try to infer the Pi domain of `neutral` from the context, to use as the
/// type of the fresh variable introduced when eta-expanding `neutral` against
/// a lambda. Returns `None` when the type cannot be determined.
pub fn infer_lam_dom(ctx: &Ctx, neutral: &Term) -> Option<Term> {
    match infer_neutral_ty(ctx, neutral) {
        Some(Term::TPi(_, dom_ty, _)) => Some(nbe_eval(&dom_ty)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Core eta-equality
// ---------------------------------------------------------------------------

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
pub fn eta_eq(fuel: usize, ctx: &Ctx, t1: &Term, t2: &Term) -> EtaResult {
    let mut memo = EtaMemo::new();
    eta_eq_memo(fuel, ctx, t1, t2, &mut memo)
}

fn eta_eq_memo(fuel: usize, ctx: &Ctx, t1: &Term, t2: &Term, memo: &mut EtaMemo) -> EtaResult {
    let key = EtaMemoKey {
        fuel,
        ctx: ctx.clone(),
        left: t1.clone(),
        right: t2.clone(),
    };

    if let Some(result) = memo.get(&key) {
        return *result;
    }

    let result = eta_eq_uncached(fuel, ctx, t1, t2, memo);
    memo.insert(key, result);
    result
}

fn eta_eq_uncached(fuel: usize, ctx: &Ctx, t1: &Term, t2: &Term, memo: &mut EtaMemo) -> EtaResult {
    use EtaResult::*;

    if fuel == 0 {
        return Exhausted;
    }

    if t1 == t2 {
        return Equal;
    }

    // ------------------------------------------------------------------
    // Path boundary reduction (consumes fuel)
    // ------------------------------------------------------------------
    if let Term::PApp(p, r) = t1
        && let Some(u) = reduce_papp_by_type(ctx, p, r) {
            return eta_eq_memo(fuel - 1, ctx, &u, t2, memo);
        }
    if let Term::PApp(p, r) = t2
        && let Some(u) = reduce_papp_by_type(ctx, p, r) {
            return eta_eq_memo(fuel - 1, ctx, t1, &u, memo);
        }

    // ------------------------------------------------------------------
    // Lambda eta (consumes fuel)
    // ------------------------------------------------------------------

    // Both sides are lambdas.
    if let (Term::TAbs(x, b1), Term::TAbs(_, b2)) = (t1, t2) {
        let dom = infer_lam_dom(ctx, t1)
            .or_else(|| infer_lam_dom(ctx, t2))
            .unwrap_or(Term::TUniv(0));
        let mut ctx2 = vec![(x.clone(), dom)];
        ctx2.extend_from_slice(ctx);
        return eta_eq_memo(fuel - 1, &ctx2, &nbe_eval(b1), &nbe_eval(b2), memo);
    }

    // Only RHS is a lambda — eta-expand neutral LHS.
    if let Term::TAbs(x, b2) = t2 {
        return match infer_lam_dom(ctx, t1) {
            None => Exhausted,
            Some(dom) => {
                let mut ctx2 = vec![(x.clone(), dom)];
                ctx2.extend_from_slice(ctx);
                eta_eq_memo(
                    fuel - 1,
                    &ctx2,
                    &nbe_eval(&Term::TApp(
                        Box::new(shift(1, 0, t1)),
                        Box::new(Term::TVar(0)),
                    )),
                    &nbe_eval(b2),
                    memo,
                )
            }
        };
    }

    // Only LHS is a lambda — eta-expand neutral RHS.
    if let Term::TAbs(x, b1) = t1 {
        return match infer_lam_dom(ctx, t2) {
            None => Exhausted,
            Some(dom) => {
                let mut ctx2 = vec![(x.clone(), dom)];
                ctx2.extend_from_slice(ctx);
                eta_eq_memo(
                    fuel - 1,
                    &ctx2,
                    &nbe_eval(b1),
                    &nbe_eval(&Term::TApp(
                        Box::new(shift(1, 0, t2)),
                        Box::new(Term::TVar(0)),
                    )),
                    memo,
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
        return eta_eq_memo(fuel - 1, &ctx2, &nbe_eval(b1), &nbe_eval(b2), memo);
    }

    // Only RHS is a path-lambda.
    if let Term::PLam(i, b2) = t2 {
        let mut ctx2 = vec![(i.clone(), Term::TIntervalTy)];
        ctx2.extend_from_slice(ctx);
        return eta_eq_memo(
            fuel - 1,
            &ctx2,
            &nbe_eval(&Term::PApp(
                Box::new(shift(1, 0, t1)),
                Box::new(Term::TVar(0)),
            )),
            &nbe_eval(b2),
            memo,
        );
    }

    // Only LHS is a path-lambda.
    if let Term::PLam(i, b1) = t1 {
        let mut ctx2 = vec![(i.clone(), Term::TIntervalTy)];
        ctx2.extend_from_slice(ctx);
        return eta_eq_memo(
            fuel - 1,
            &ctx2,
            &nbe_eval(b1),
            &nbe_eval(&Term::PApp(
                Box::new(shift(1, 0, t2)),
                Box::new(Term::TVar(0)),
            )),
            memo,
        );
    }

    // ------------------------------------------------------------------
    // Congruence on neutral spines (structural: no fuel consumed)
    // ------------------------------------------------------------------
    if let (Term::TApp(f1, a1), Term::TApp(f2, a2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, f1, f2, memo),
            eta_eq_memo(fuel, ctx, a1, a2, memo),
        );
    }
    if let (Term::PApp(p1, r1), Term::PApp(p2, r2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, p1, p2, memo),
            eta_eq_memo(fuel, ctx, r1, r2, memo),
        );
    }

    // ------------------------------------------------------------------
    // Type congruence (structural: no fuel consumed)
    // ------------------------------------------------------------------
    if let (Term::TPi(_, a1, b1), Term::TPi(_, a2, b2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo),
            eta_eq_memo(fuel, ctx, b1, b2, memo),
        );
    }
    if let (Term::TPath(ty1, u1, v1), Term::TPath(ty2, u2, v2)) = (t1, t2) {
        return and_result(
            and_result(
                eta_eq_memo(fuel, ctx, ty1, ty2, memo),
                eta_eq_memo(fuel, ctx, u1, u2, memo),
            ),
            eta_eq_memo(fuel, ctx, v1, v2, memo),
        );
    }
    if let (Term::TSigma(_, a1, b1), Term::TSigma(_, a2, b2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo),
            eta_eq_memo(fuel, ctx, b1, b2, memo),
        );
    }

    // ------------------------------------------------------------------
    // Pair congruence (structural)
    // ------------------------------------------------------------------
    if let (Term::TPair(a1, b1), Term::TPair(a2, b2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo),
            eta_eq_memo(fuel, ctx, b1, b2, memo),
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
                &nbe_eval(&Term::TFst(Box::new(t2.clone()))),
                memo,
            ),
            eta_eq_memo(
                fuel - 1,
                ctx,
                b1,
                &nbe_eval(&Term::TSnd(Box::new(t2.clone()))),
                memo,
            ),
        );
    }
    if let Term::TPair(a2, b2) = t2 {
        return and_result(
            eta_eq_memo(
                fuel - 1,
                ctx,
                &nbe_eval(&Term::TFst(Box::new(t1.clone()))),
                a2,
                memo,
            ),
            eta_eq_memo(
                fuel - 1,
                ctx,
                &nbe_eval(&Term::TSnd(Box::new(t1.clone()))),
                b2,
                memo,
            ),
        );
    }

    // ------------------------------------------------------------------
    // Projection congruence on neutral spines (structural)
    // ------------------------------------------------------------------
    if let (Term::TFst(p1), Term::TFst(p2)) = (t1, t2) {
        return eta_eq_memo(fuel, ctx, p1, p2, memo);
    }
    if let (Term::TSnd(p1), Term::TSnd(p2)) = (t1, t2) {
        return eta_eq_memo(fuel, ctx, p1, p2, memo);
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
            and_result(acc, eta_eq_memo(fuel, ctx, a1, a2, memo))
        });
    }

    // Path-constructor congruence: same datatype, same path-constructor,
    // check ordinary args and then the interval argument.
    if let (Term::TPCon(d1, c1, args1, r1), Term::TPCon(d2, c2, args2, r2)) = (t1, t2) {
        if d1 != d2 || c1 != c2 || args1.len() != args2.len() {
            return NotEqual;
        }
        let args_eq = args1.iter().zip(args2.iter()).fold(Equal, |acc, (a1, a2)| {
            and_result(acc, eta_eq_memo(fuel, ctx, a1, a2, memo))
        });
        return and_result(args_eq, eta_eq_memo(fuel, ctx, r1, r2, memo));
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
                and_result(acc, eta_eq_memo(fuel, &case_ctx, &c1.body, &c2.body, memo))
            });
        return and_result(
            and_result(cases_eq, eta_eq_memo(fuel, ctx, m1, m2, memo)),
            eta_eq_memo(fuel, ctx, s1, s2, memo),
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
            eta_eq_memo(fuel, ctx, a1, a2, memo),
            eta_eq_memo(fuel, ctx, u01, u02, memo),
        );
        for ((phi1, t1), (phi2, t2)) in sys1.iter().zip(sys2.iter()) {
            result = and_result(
                result,
                and_result(
                    eta_eq_memo(fuel, ctx, phi1, phi2, memo),
                    eta_eq_memo(fuel, ctx, t1, t2, memo),
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
            eta_eq_memo(fuel, ctx, a1, a2, memo),
            eta_eq_memo(fuel, ctx, u01, u02, memo),
        );
        for ((phi1, t1), (phi2, t2)) in sys1.iter().zip(sys2.iter()) {
            result = and_result(
                result,
                and_result(
                    eta_eq_memo(fuel, ctx, phi1, phi2, memo),
                    eta_eq_memo(fuel, ctx, t1, t2, memo),
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
            eta_eq_memo(fuel, ctx, a1, a2, memo),
            eta_eq_memo(fuel, ctx, u01, u02, memo),
        );
        for ((phi1, t1), (phi2, t2)) in sys1.iter().zip(sys2.iter()) {
            result = and_result(
                result,
                and_result(
                    eta_eq_memo(fuel, ctx, phi1, phi2, memo),
                    eta_eq_memo(fuel, ctx, t1, t2, memo),
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
            eta_eq_memo(fuel, ctx, a1, a2, memo),
            eta_eq_memo(fuel, ctx, u01, u02, memo),
        );
        for ((phi1, t1), (phi2, t2)) in sys1.iter().zip(sys2.iter()) {
            result = and_result(
                result,
                and_result(
                    eta_eq_memo(fuel, ctx, phi1, phi2, memo),
                    eta_eq_memo(fuel, ctx, t1, t2, memo),
                ),
            );
        }
        return result;
    }
    if let (Term::TGlue(a1, phi1, te1), Term::TGlue(a2, phi2, te2)) = (t1, t2) {
        return and_result(
            and_result(
                eta_eq_memo(fuel, ctx, a1, a2, memo),
                eta_eq_memo(fuel, ctx, phi1, phi2, memo),
            ),
            eta_eq_memo(fuel, ctx, te1, te2, memo),
        );
    }
    if let (Term::TGlueElem(phi1, t1v, a1), Term::TGlueElem(phi2, t2v, a2)) = (t1, t2) {
        return and_result(
            and_result(
                eta_eq_memo(fuel, ctx, phi1, phi2, memo),
                eta_eq_memo(fuel, ctx, t1v, t2v, memo),
            ),
            eta_eq_memo(fuel, ctx, a1, a2, memo),
        );
    }
    if let (Term::TUnglue(phi1, te1, g1), Term::TUnglue(phi2, te2, g2)) = (t1, t2) {
        return and_result(
            and_result(
                eta_eq_memo(fuel, ctx, phi1, phi2, memo),
                eta_eq_memo(fuel, ctx, te1, te2, memo),
            ),
            eta_eq_memo(fuel, ctx, g1, g2, memo),
        );
    }
    if let (Term::TTransport(p1, x1), Term::TTransport(p2, x2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, p1, p2, memo),
            eta_eq_memo(fuel, ctx, x1, x2, memo),
        );
    }
    if let (Term::TUa(e1), Term::TUa(e2)) = (t1, t2) {
        return eta_eq_memo(fuel, ctx, e1, e2, memo);
    }
    if let (Term::TEquiv(a1, b1), Term::TEquiv(a2, b2)) = (t1, t2) {
        return and_result(
            eta_eq_memo(fuel, ctx, a1, a2, memo),
            eta_eq_memo(fuel, ctx, b1, b2, memo),
        );
    }

    NotEqual
}