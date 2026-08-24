//! `by omega` — linear arithmetic over `Nat` and `Int`.
//!
//! Proves goals of the form `Path C u v` where `C` is one of the supported
//! concrete carriers (`Nat`, `Int` from lib/ring_laws.owl) and `u`/`v` are
//! expressions over the context's variables of that type (for `Nat`: built
//! with `add`, `suc`, `zero`; for `Int`: with `int_add`, `int_neg`,
//! `int_sub`, `pos`, `negsuc`).  The proof term is constructed from
//! kernel-verified lemmas and re-checked by the typechecker:
//!
//! 1. **Reflexivity** — when the two sides are definitionally equal after
//!    normalization (which unfolds global definitions such as `add` or
//!    `int_add` applied to constructor-headed arguments).
//! 2. **Lemma matching** — when the goal is a direct instance of a previously
//!    verified global lemma (`forall ... Path C L R`), omega applies it to
//!    the context's variables in every order and re-checks the result.
//!
//! Goals requiring induction (e.g. commutativity without a pre-proved lemma)
//! are not yet synthesized; see `TODO.md` §B.1/§H3.

use crate::cubical::equality::{EtaResult, definitionally_equal_ctx_r};
use crate::cubical::nbe::nbe_eval_ctx;
use crate::cubical::session::Session;
use crate::cubical::syntax::{Datatype, Term, shift};
use crate::cubical::typechecker::{Ctx, TypeError, check_dt};

/// The carriers `by omega` supports, recognized by their datatype head.
fn supported_carrier(a_nf: &Term) -> Option<&'static str> {
    match a_nf {
        Term::TData(d, p) if p.is_empty() => match d.as_str() {
            "Nat" => Some("Nat"),
            "Int" => Some("Int"),
            _ => None,
        },
        _ => None,
    }
}

/// Entry point called by the `Tactic::Omega` arm.
///
/// - `ctx` is the full context the goal lives in (tactic binders innermost).
/// - `goal_ty` is the normalized goal type.
/// - `num_tactic` is the number of binders `ctx` has beyond the outer context.
/// - `num_intro` is the number of names introduced by `intro`.
pub fn prove(
    dts: &[Datatype],
    ctx: &Ctx,
    goal_ty: &Term,
    num_tactic: usize,
    _num_intro: usize,
    session: &mut Session,
) -> Result<Term, TypeError> {
    // The goal must be a path over a supported carrier.
    let (a, u, v) = {
        let goal_nf = nbe_eval_ctx(ctx.len(), goal_ty, session);
        match goal_nf {
            Term::TPath(a, u, v) => (*a, *u, *v),
            other => {
                return Err(TypeError::Other(format!(
                    "omega: goal is not a path\n  goal: {}",
                    other,
                )));
            }
        }
    };
    let a_nf = nbe_eval_ctx(ctx.len(), &a, session);
    let carrier = supported_carrier(&a_nf).ok_or_else(|| {
        TypeError::Other(format!(
            "omega: goal is not a path over a supported carrier (Nat, Int); got '{}'",
            a_nf,
        ))
    })?;

    // 1. Reflexivity after normalization (definitional equality).
    let u_nf = nbe_eval_ctx(ctx.len(), &u, session);
    let v_nf = nbe_eval_ctx(ctx.len(), &v, session);
    if definitionally_equal_ctx_r(ctx, &u_nf, &v_nf, session) == EtaResult::Equal {
        return Ok(Term::PLam("_i".into(), Box::new(shift(1, 0, &u))));
    }

    // 2. Direct instance of a previously defined global lemma.
    //
    //    In `ctx` the tactic binders occupy indices `0..num_tactic`, the
    //    definition being proved sits at `num_tactic`, and the previously
    //    defined globals follow at `num_tactic + 1..`. We skip the current
    //    definition to avoid self-reference (the kernel would reject a
    //    non-structural use of it, but there is no reason to attempt it).
    for gi in (num_tactic + 1)..ctx.len() {
        let arity = pi_arity(&ctx[gi].1);
        if arity > num_tactic {
            continue;
        }
        for args in arg_permutations(num_tactic, arity) {
            let mut cand = Term::TVar(gi as i32);
            for i in args {
                cand = Term::TApp(Box::new(cand), Box::new(Term::TVar(i)));
            }
            if check_dt(dts, ctx, &cand, goal_ty, session).is_ok() {
                return Ok(cand);
            }
        }
    }

    Err(TypeError::Other(format!(
        "omega: unable to solve goal over {}\n  goal : Path {} {} {}\n  left  : {}\n  right : {}",
        carrier, a, u, v, u_nf, v_nf,
    )))
}

/// Number of `Pi` binders at the head of `ty` (the lemma's argument count).
fn pi_arity(ty: &Term) -> usize {
    let mut t = ty;
    let mut n = 0;
    while let Term::TPi(_, _, b) = t {
        n += 1;
        t = b;
    }
    n
}

/// All ordered `k`-element selections of distinct indices in `0..n`.
fn arg_permutations(n: usize, k: usize) -> Vec<Vec<i32>> {
    let mut out = Vec::new();
    fn rec(n: usize, k: usize, used: &mut Vec<bool>, cur: &mut Vec<i32>, out: &mut Vec<Vec<i32>>) {
        if cur.len() == k {
            out.push(cur.clone());
            return;
        }
        for i in 0..n {
            if !used[i] {
                used[i] = true;
                cur.push(i as i32);
                rec(n, k, used, cur, out);
                cur.pop();
                used[i] = false;
            }
        }
    }
    rec(n, k, &mut vec![false; n], &mut Vec::new(), &mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pi_arity_counts_pi_chain() {
        use crate::cubical::syntax::Term;
        let nat = || Term::TData("Nat".into(), vec![]);
        let t = Term::TPi(
            "m".into(),
            Box::new(nat()),
            Box::new(Term::TPi(
                "n".into(),
                Box::new(nat()),
                Box::new(Term::TPath(
                    Box::new(nat()),
                    Box::new(Term::TVar(0)),
                    Box::new(Term::TVar(0)),
                )),
            )),
        );
        assert_eq!(pi_arity(&t), 2);
        assert_eq!(pi_arity(&nat()), 0);
    }

    #[test]
    fn arg_permutations_enumerates_ordered_selections() {
        assert_eq!(arg_permutations(0, 0), vec![Vec::<i32>::new()]);
        assert_eq!(arg_permutations(2, 1), vec![vec![0], vec![1]]);
        assert_eq!(arg_permutations(2, 2), vec![vec![0, 1], vec![1, 0]]);
        assert_eq!(arg_permutations(2, 3), Vec::<Vec<i32>>::new());
    }
}
