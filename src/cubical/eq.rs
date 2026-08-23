//! Propositional-equality chaining — `by eq`.
//!
//! Closes goals of the form `Path A u v` by searching the context for path
//! hypotheses and composing them into a chain `u -> ... -> v`:
//!
//! * reflexivity: if `u` and `v` are definitionally equal, return `<i> u`;
//! * otherwise run a breadth-first search over an undirected graph whose
//!   nodes are endpoint terms (matched up to normalization) and whose edges
//!   are context hypotheses of path type;
//! * forward edges use the hypothesis as-is, backward edges wrap it in an
//!   inline symmetry (`<i> p @ ~i`);
//! * adjacent proofs compose with the standard cubical transitivity
//!   combinator (`<i> hcomp A [~i => <j> x, i => q] (p @ i)`), mirroring
//!   `_owl_trans` from lib/ring_laws.owl.
//!
//! Hypotheses are used monomorphically — no quantifier instantiation.  As
//! always, the kernel re-checks the assembled proof.

use crate::cubical::interval::I;
use crate::cubical::nbe::nbe_eval_ctx;
use crate::cubical::ring::inst;
use crate::cubical::session::Session;
use crate::cubical::syntax::{Term, shift};
use crate::cubical::typechecker::{Ctx, TypeError};

/// Path reflection: `<i> x`.
fn pref(x: &Term) -> Term {
    Term::PLam("_i".into(), Box::new(shift(1, 0, x)))
}

/// Inline path symmetry: `p : Path X x y` gives `<i> p @ ~i : Path X y x`.
fn psym(p: &Term) -> Term {
    // Under the new binder the hypothesis reference shifts by one; the
    // interval argument is its negation.
    Term::PLam(
        "_i".into(),
        Box::new(Term::PApp(
            Box::new(shift(1, 0, p)),
            Box::new(Term::TInterval(I::Neg(Box::new(I::Var(0))))),
        )),
    )
}

/// An edge of the hypothesis graph: witness term plus endpoints (raw).
struct Edge {
    hyp: Term,
    from: Term,
    to: Term,
}

/// Node identity: normalization-normalized term equality.
fn same(ctx_len: usize, a: &Term, b: &Term, session: &mut Session) -> bool {
    nbe_eval_ctx(ctx_len, a, session) == nbe_eval_ctx(ctx_len, b, session)
}

/// Collect path-typed hypotheses from the context.
fn collect_edges(ctx: &Ctx, session: &mut Session) -> Vec<Edge> {
    let mut edges = Vec::new();
    for (i, (_name, ty)) in ctx.iter().enumerate() {
        // Stored binder types are recorded relative to the binder's own
        // frame (binder at index 0); re-anchor before normalizing.
        let ty_shifted = shift(i as i32 + 1, 0, ty);
        if let Term::TPath(_carrier, x, y) = nbe_eval_ctx(ctx.len(), &ty_shifted, session) {
            edges.push(Edge {
                hyp: Term::TVar(i as i32),
                from: *x,
                to: *y,
            });
        }
    }
    edges
}

/// Breadth-first search from `u` to `v` over undirected hypothesis edges.
/// Returns the chain of edges as `(index, traversed_forward)` pairs.
fn bfs(
    ctx_len: usize,
    edges: &[Edge],
    u: &Term,
    v: &Term,
    session: &mut Session,
) -> Option<Vec<(usize, bool)>> {
    use std::collections::VecDeque;

    let mut prev: Vec<Option<(usize, bool)>> = vec![None; edges.len()];
    let mut queue = VecDeque::new();

    // Seed: every edge incident to u.
    for (k, e) in edges.iter().enumerate() {
        let dir = if same(ctx_len, u, &e.from, session) {
            true
        } else if same(ctx_len, u, &e.to, session) {
            false
        } else {
            continue;
        };
        prev[k] = Some((usize::MAX, dir));
        queue.push_back(k);
    }

    while let Some(k) = queue.pop_front() {
        let e = &edges[k];
        let fwd = prev[k].unwrap().1;
        let head = if fwd { &e.to } else { &e.from };
        if same(ctx_len, head, v, session) {
            // Reconstruct the chain back to the seed.
            let mut chain = Vec::new();
            let mut cur = Some(k);
            while let Some(idx) = cur {
                let (pred, d) = prev[idx].unwrap();
                chain.push((idx, d));
                cur = if pred == usize::MAX { None } else { Some(pred) };
            }
            chain.reverse();
            return Some(chain);
        }
        for (j, e2) in edges.iter().enumerate() {
            if prev[j].is_some() {
                continue;
            }
            let reach_fwd = same(ctx_len, head, &e2.from, session);
            let reach_bwd = same(ctx_len, head, &e2.to, session);
            if reach_fwd || reach_bwd {
                prev[j] = Some((k, reach_fwd));
                queue.push_back(j);
            }
        }
    }
    None
}

/// Prove a path goal by reflexivity or context chaining.
pub fn prove(
    _dts: &[crate::cubical::syntax::Datatype],
    ctx: &Ctx,
    goal_ty: &Term,
    _num_tactic: usize,
    _num_intro: usize,
    session: &mut Session,
) -> Result<Term, TypeError> {
    let (u, v, _carrier) = match nbe_eval_ctx(ctx.len(), goal_ty, session) {
        Term::TPath(a, x, y) => (*x, *y, *a),
        other => {
            return Err(TypeError::Other(format!(
                "eq: goal is not a path (got '{}')",
                other,
            )));
        }
    };

    // Reflexivity.
    if same(ctx.len(), &u, &v, session) {
        return Ok(pref(&u));
    }

    let edges = collect_edges(ctx, session);

    // Direct hypothesis (either orientation), skipping the search.
    for e in &edges {
        if same(ctx.len(), &e.from, &u, session) && same(ctx.len(), &e.to, &v, session) {
            return Ok(e.hyp.clone());
        }
        if same(ctx.len(), &e.from, &v, session) && same(ctx.len(), &e.to, &u, session) {
            return Ok(psym(&e.hyp));
        }
    }

    let chain = bfs(ctx.len(), &edges, &u, &v, session).ok_or_else(|| {
        TypeError::Other(format!(
            "eq: no chain of context paths connects '{}' to '{}'",
            crate::cubical::syntax::pretty::show_term(&[], &u),
            crate::cubical::syntax::pretty::show_term(&[], &v),
        ))
    })?;

    // Compose the chain left-to-right through a context-provided
    // transitivity lemma (`trans` / `_owl_trans`).  Hand-rolling the hcomp
    // combinator would duplicate `_owl_trans`; composing through a context
    // lemma keeps the generated term an ordinary application spine and lets
    // the kernel re-check every hop.
    let (tr_lemma, leading) = find_trans(ctx).ok_or_else(|| {
        TypeError::Other(
            "eq: multi-step chaining needs a transitivity lemma named 'trans' or \
             '_owl_trans' in context (import lib/ring_laws.owl or bundle one)"
                .to_string(),
        )
    })?;

    let mut acc: Option<Term> = None;
    let acc_left = u.clone();
    let mut cur_right: Option<Term> = None;
    for (idx, fwd) in &chain {
        let e = &edges[*idx];
        let step = if *fwd { e.hyp.clone() } else { psym(&e.hyp) };
        let step_right = if *fwd { e.to.clone() } else { e.from.clone() };
        match &acc {
            None => {
                acc = Some(step);
            }
            Some(ap) => {
                let mid = cur_right.clone().ok_or_else(|| {
                    TypeError::Other("eq: internal error — missing midpoint".into())
                })?;
                let applied = if leading >= 2 {
                    // e.g. `_owl_trans : forall x y z, Path x y -> Path y z ->
                    // Path x z` — endpoints supplied explicitly.
                    inst(&tr_lemma, &[&acc_left, &mid, &step_right, ap, &step])
                } else {
                    inst(&tr_lemma, &[ap, &step])
                };
                acc = Some(applied);
            }
        }
        cur_right = Some(step_right);
    }

    acc.ok_or_else(|| TypeError::Other("eq: internal error — empty chain".into()))
}

/// Find a context lemma whose type matches the path-transitivity shape
/// `Path A x y -> Path A y z -> Path A x z` (under any number of leading
/// explicit arguments, e.g. endpoints made explicit).  Candidates are looked
/// up by the conventional names `trans` and `_owl_trans`.
fn find_trans(ctx: &Ctx) -> Option<(Term, usize)> {
    for candidate in ["_owl_trans", "trans"] {
        for (i, (name, ty)) in ctx.iter().enumerate() {
            if name != candidate {
                continue;
            }
            if let Some(leading) = is_trans_shape(ty) {
                return Some((Term::TVar(i as i32), leading));
            }
        }
    }
    None
}

/// Recognize the transitivity shape and report how many *leading explicit*
/// arguments precede the two path arguments.  After any leading arguments,
/// the type must continue `Path A x y -> Path A y z -> Path A x z` with the
/// shared middle endpoint.
fn is_trans_shape(ty: &Term) -> Option<usize> {
    // Pass 1: strip Pis, recording each path-typed domain together with its
    // binder depth and the running leading-argument count.
    let mut cur = ty.clone();
    let mut depth = 0usize;
    let mut leading = 0usize;
    let mut captures: Vec<(usize, Term, Term)> = Vec::new();
    loop {
        match cur {
            Term::TPi(_, d, body) => {
                if let Term::TPath(_, x, y) = *d.clone() {
                    captures.push((depth, *x, *y));
                } else if captures.is_empty() {
                    leading += 1;
                }
                depth += 1;
                cur = *body;
            }
            other => {
                if captures.len() != 2 {
                    return None;
                }
                // Pass 2: lift every capture into the full-depth frame so
                // endpoints captured under different binders compare
                // syntactically.
                let lifted: Vec<(Term, Term)> = captures
                    .iter()
                    .map(|(d, x, y)| {
                        let sx = shift((depth - d) as i32, 0, x);
                        let sy = shift((depth - d) as i32, 0, y);
                        (sx, sy)
                    })
                    .collect();
                let (x0, y0) = (&lifted[0].0, &lifted[0].1);
                let (x1, z1) = (&lifted[1].0, &lifted[1].1);
                if let Term::TPath(_carrier, ref mid, ref z) = other {
                    // The codomain `Path A x z` must start at the first
                    // path's left endpoint and conclude at the second path's
                    // right endpoint (all endpoints lifted to a common
                    // binder depth before comparing).
                    if same_nf(x0, mid) && same_nf(y0, x1) && same_nf(z, z1) {
                        return Some(leading);
                    }
                }
                return None;
            }
        }
    }
}

/// Normalized terms compare syntactically.
fn same_nf(a: &Term, b: &Term) -> bool {
    a == b
}
