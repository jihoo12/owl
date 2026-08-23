//! Group solver — `by group with G`.
//!
//! Proves goals of the form `Path A u v` where `u`/`v` are built from the
//! operations of an abstract `Group A mul inv one` record (multiplication,
//! inverse, unit): both sides are parsed into signed-generator words, the
//! word problem is decided by free reduction, and — when the reduced words
//! agree — a proof tree is assembled from the record's law fields.  As
//! everywhere else, the constructed proof is re-checked by the kernel, which
//! is the soundness backstop.
//!
//! Rendering conventions (load-bearing for the proof generators):
//!
//! * every `gen` proof *endpoint* renders its word **right-associated**
//!   (`R([l1..lk]) = l1 · R([l2..])`, singleton bare, empty = unit);
//! * distributing an inverse through a product swaps the factors, so the
//!   inversion lemma [`finisher_inv`] naturally reads the inverted word
//!   **left-associated**; [`conv_lr`] bridges that back to the canonical
//!   rendering with iterated associativity.
//!
//! The law set required from the record is deliberately pragmatic (the same
//! choice `Field` makes with `inv_mul_dist`): besides associativity, the two
//! unit laws and the two cancellation laws it carries `inv_one`, `inv_inv`
//! and the *swapping* distributivity `inv (mul a b) = mul (inv b) (inv a)`
//! as primitive fields rather than deriving them.

use crate::cubical::nbe::nbe_eval_ctx;
use crate::cubical::ring::{EqP, app, inst, refl2};
use crate::cubical::session::Session;
use crate::cubical::syntax::{Datatype, Term, shift};
use crate::cubical::typechecker::{Ctx, TypeError, check_dt, infer_dt};

/// A letter of a word: a generator (`neg = false`) or its formal inverse.
/// Atoms are kept in normal form so equality checks stay syntactic.
#[derive(Clone, Debug)]
struct Letter {
    neg: bool,
    atom: Term,
}

/// A (reduced) word over the group generators.
type Word = Vec<Letter>;

/// Resolved references to the group operations and law fields.
struct Group {
    ctx_len: usize,
    mul: Term,
    inv: Term,
    one: Term,
    // Structural glue.
    trans: Term,
    sym: Term,
    cong_mul_l: Term,
    cong_mul_r: Term,
    cong_inv: Term,
    // Laws.
    mul_assoc: Term, // mul (mul a b) c   = mul a (mul b c)
    one_mul: Term,   // mul one a         = a
    mul_one: Term,   // mul a one         = a
    inv_l: Term,     // mul (inv a) a     = one
    inv_r: Term,     // mul a (inv a)     = one
    inv_one: Term,   // inv one           = one
    inv_inv: Term,   // inv (inv a)       = a
    inv_mul: Term,   // inv (mul a b)     = mul (inv b) (inv a)
}

impl Group {
    fn mul_t(&self, x: &Term, y: &Term) -> Term {
        app(&app(&self.mul, x), y)
    }

    /// Resolve the record's operations and laws (structured mode only).
    ///
    /// Operations come from the record type's parameter list (`Group A mul
    /// inv one`); laws are record projections of `g`.
    fn resolve(
        dts: &[Datatype],
        ctx: &Ctx,
        carrier: &Term,
        group_term: Option<&Term>,
        session: &mut Session,
    ) -> Result<Group, TypeError> {
        let group_term = match group_term {
            some @ Some(_) => some.cloned(),
            None => match find_group_instance(ctx, carrier, session) {
                Some(found) => Some(found),
                None => {
                    return Err(TypeError::Other(format!(
                        "group: no Group instance for '{}' in context; use `group with G`",
                        carrier,
                    )));
                }
            },
        };
        let g = group_term.as_ref().ok_or_else(|| {
            TypeError::Other("group: internal error — no group term after search".into())
        })?;

        let inst_ty = infer_dt(dts, ctx, g, session)?;
        let (mul, inv, one) = match nbe_eval_ctx(ctx.len(), &inst_ty, session) {
            Term::TData(dname, params) if dname == "Group" && params.len() == 4 => {
                (params[1].clone(), params[2].clone(), params[3].clone())
            }
            other => {
                return Err(TypeError::Other(format!(
                    "group: '{}' is not a Group record (its type is '{}')",
                    g, other,
                )));
            }
        };

        let proj = |field: &str| -> Result<Term, TypeError> {
            Ok(Term::TProj(field.to_string(), Box::new(g.clone())))
        };
        Ok(Group {
            ctx_len: ctx.len(),
            mul,
            inv,
            one,
            trans: proj("trans")?,
            sym: proj("sym")?,
            cong_mul_l: proj("cong_mul_l")?,
            cong_mul_r: proj("cong_mul_r")?,
            cong_inv: proj("cong_inv")?,
            mul_assoc: proj("mul_assoc")?,
            one_mul: proj("one_mul")?,
            mul_one: proj("mul_one")?,
            inv_l: proj("inv_l")?,
            inv_r: proj("inv_r")?,
            inv_one: proj("inv_one")?,
            inv_inv: proj("inv_inv")?,
            inv_mul: proj("inv_mul")?,
        })
    }
}

/// Search the context for a bundled `Group` record instance whose carrier
/// matches `carrier` (mirrors ring's instance search).
fn find_group_instance(ctx: &Ctx, carrier: &Term, session: &mut Session) -> Option<Term> {
    let car_nf = nbe_eval_ctx(ctx.len(), carrier, session);
    for (i, (_name, ty)) in ctx.iter().enumerate() {
        // Stored binder types are recorded relative to the binder's own frame
        // (binder at index 0); re-anchor before comparing against the carrier.
        let ty_shifted = shift(i as i32 + 1, 0, ty);
        if let Term::TData(dname, params) = nbe_eval_ctx(ctx.len(), &ty_shifted, session) {
            if dname == "Group" && params.len() == 4 {
                if nbe_eval_ctx(ctx.len(), &params[0], session) == car_nf {
                    return Some(Term::TVar(i as i32));
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Structure tree
// ---------------------------------------------------------------------------

/// The structure of a goal-side term, with inverses kept explicit so proofs
/// can be generated structurally.
enum GT {
    Atom(Term),
    One(Term),
    /// `orig` is the whole `inv u` application: generated proofs must start
    /// exactly there, not at the child's endpoint.
    Inv(Term, Box<GT>),
    /// `orig` is the whole `mul x y` application.
    Mul(Term, Box<GT>, Box<GT>),
}

/// Peel an application spine `(f a1 .. an)` into head + args (normal form).
fn spine(t: &Term) -> (Term, Vec<Term>) {
    let mut args = Vec::new();
    let mut cur = t;
    while let Term::TApp(f, a) = cur {
        args.push((**a).clone());
        cur = f;
    }
    args.reverse();
    (cur.clone(), args)
}

/// Classify a normalized term into the structure tree.
fn classify(g: &Group, t: &Term, session: &mut Session) -> GT {
    let nf = nbe_eval_ctx(g.ctx_len, t, session);
    if nf == g.one {
        return GT::One(nf);
    }
    let (head, args) = spine(&nf);
    if head == g.mul && args.len() == 2 {
        return GT::Mul(
            nf.clone(),
            Box::new(classify(g, &args[0], session)),
            Box::new(classify(g, &args[1], session)),
        );
    }
    if head == g.inv && args.len() == 1 {
        return GT::Inv(nf.clone(), Box::new(classify(g, &args[0], session)));
    }
    GT::Atom(nf)
}

// ---------------------------------------------------------------------------
// Words and renderings
// ---------------------------------------------------------------------------

/// The term denoted by one letter.
fn letter_term(inv_t: &Term, l: &Letter) -> Term {
    if l.neg {
        app(inv_t, &l.atom)
    } else {
        l.atom.clone()
    }
}

/// Render a word right-associated: `R([l1..lk]) = l1 · R([l2..])`, singleton
/// letters render bare, the empty word renders as the unit.  This is the
/// canonical rendering of every `gen` endpoint.
fn render_r(g: &Group, w: &[Letter]) -> Term {
    match w.split_first() {
        None => g.one.clone(),
        Some((first, rest)) => {
            let first_t = letter_term(&g.inv, first);
            if rest.is_empty() {
                first_t
            } else {
                g.mul_t(&first_t, &render_r(g, &rest.to_vec()))
            }
        }
    }
}

/// Render a word left-associated.  Only appears inside the inversion lemma.
fn render_l(g: &Group, w: &[Letter]) -> Term {
    if w.is_empty() {
        return g.one.clone();
    }
    let mut acc = letter_term(&g.inv, &w[0]);
    for l in &w[1..] {
        acc = g.mul_t(&acc, &letter_term(&g.inv, l));
    }
    acc
}

/// Reverse and flip a word (its group-theoretic inverse as a word).
fn flip(w: &[Letter]) -> Word {
    w.iter()
        .rev()
        .map(|l| Letter {
            neg: !l.neg,
            atom: l.atom.clone(),
        })
        .collect()
}

/// Free reduction of the concatenation `a ++ b`: push letters onto a stack,
/// cancelling adjacent opposite letters with definitionally equal atoms.
fn reduce_concat(g: &Group, a: &[Letter], b: &[Letter], session: &mut Session) -> Word {
    let mut stack: Vec<Letter> = Vec::new();
    for l in a.iter().chain(b.iter()) {
        if let Some(top) = stack.last() {
            if top.neg != l.neg {
                let top_nf = nbe_eval_ctx(g.ctx_len, &top.atom, session);
                let l_nf = nbe_eval_ctx(g.ctx_len, &l.atom, session);
                if top_nf == l_nf {
                    stack.pop();
                    continue;
                }
            }
        }
        stack.push(l.clone());
    }
    stack
}

// ---------------------------------------------------------------------------
// Equation plumbing
// ---------------------------------------------------------------------------

/// Transitivity.
fn tr(g: &Group, p: &EqP, q: &EqP) -> EqP {
    if p.b != q.a {
        crate::debug_log!(
            "group: trans mismatch:\n  p.b={}\n  q.a={}",
            crate::cubical::syntax::pretty::show_term(&[], &p.b),
            crate::cubical::syntax::pretty::show_term(&[], &q.a)
        );
    }
    debug_assert!(p.b == q.a, "trans endpoints must line up");
    EqP {
        a: p.a.clone(),
        b: q.b.clone(),
        p: inst(&g.trans, &[&p.a, &p.b, &q.b, &p.p, &q.p]),
    }
}

/// Symmetry.
fn sy(g: &Group, p: &EqP) -> EqP {
    EqP {
        a: p.b.clone(),
        b: p.a.clone(),
        p: inst(&g.sym, &[&p.b, &p.a, &p.p]),
    }
}

/// Fixed context on the left: `p : x = y` gives `m · x = m · y`.
/// (The record's `cong_mul_r` field carries this orientation — its naming
/// follows ring_laws/field_laws, where `_l`/`_r` name the *varying* side.)
fn cmul_l(g: &Group, p: &EqP, m: &Term) -> EqP {
    EqP {
        a: g.mul_t(m, &p.a),
        b: g.mul_t(m, &p.b),
        p: inst(&g.cong_mul_r, &[&p.a, &p.b, m, &p.p]),
    }
}

/// Fixed context on the right: `p : x = y` gives `x · m = y · m`.
fn cmul_r(g: &Group, p: &EqP, m: &Term) -> EqP {
    EqP {
        a: g.mul_t(&p.a, m),
        b: g.mul_t(&p.b, m),
        p: inst(&g.cong_mul_l, &[&p.a, &p.b, m, &p.p]),
    }
}

/// Congruence of inverse: `p : x = y` gives `inv x = inv y`.
fn cinv(g: &Group, p: &EqP) -> EqP {
    EqP {
        a: app(&g.inv, &p.a),
        b: app(&g.inv, &p.b),
        p: inst(&g.cong_inv, &[&p.a, &p.b, &p.p]),
    }
}

/// Combine two congruences: `pa : a = a'`, `pb : b = b'` gives
/// `a · b = a' · b'`.
fn cmul2(g: &Group, pa: &EqP, pb: &EqP) -> EqP {
    let left_fixed = cmul_l(g, pb, &pa.a); // a · b  = a · b'
    let right_fixed = cmul_r(g, pa, &pb.b); // a · b' = a' · b'
    tr(g, &left_fixed, &right_fixed)
}

/// Reflexivity between two terms that are already definitionally (here:
/// syntactically) equal.
fn rfl2(a: &Term, b: &Term) -> EqP {
    refl2(a, b)
}

// ---------------------------------------------------------------------------
// Proof generation
// ---------------------------------------------------------------------------

/// Prove `inv (render_r w) = render_l (flip w)`.
///
/// Distribution swaps factors, so the inverted word reads left-associated;
/// this lemma makes that orientation change explicit.  Peel the first letter
/// (right-associated products expose their head):
///
/// ```text
/// inv (l · R ls) --inv_mul--> (inv (R ls)) · (inv l)
///     --cong_mul_l(F ls)------> (L (flip ls)) · (inv l)
///     --sign fix on inv l------> L (flip ls ++ [flip l]) = L (flip w)
/// ```
fn finisher_inv(g: &Group, w: &[Letter]) -> EqP {
    match w.split_first() {
        None => EqP {
            a: app(&g.inv, &g.one),
            b: g.one.clone(),
            p: g.inv_one.clone(),
        },
        Some((first, rest)) if rest.is_empty() => {
            // Single letter: inv l = flip-rendered l.
            let flipped = Letter {
                neg: !first.neg,
                atom: first.atom.clone(),
            };
            let lhs = app(&g.inv, &letter_term(&g.inv, first));
            let rhs = letter_term(&g.inv, &flipped);
            if !first.neg {
                // inv x = inv x
                rfl2(&lhs, &rhs)
            } else {
                // inv (inv x) = x
                EqP {
                    a: lhs,
                    b: rhs,
                    p: inst(&g.inv_inv, &[&first.atom]),
                }
            }
        }
        Some((first, rest)) => {
            let l_t = letter_term(&g.inv, first);
            let ls_rr = render_r(g, rest);
            // step1: inv (mul l (R ls)) = (inv (R ls)) · (inv l)
            let step1 = EqP {
                a: app(&g.inv, &g.mul_t(&l_t, &ls_rr)),
                b: g.mul_t(&app(&g.inv, &ls_rr), &app(&g.inv, &l_t)),
                p: inst(&g.inv_mul, &[&l_t, &ls_rr]),
            };
            // step2: (inv (R ls)) · (inv l) = (L (flip ls)) · (inv l)
            let inner = finisher_inv(g, rest);
            let step2 = cmul_r(g, &inner, &app(&g.inv, &l_t));
            // step3: sign fix on the right slot — only needed when l is
            // itself negative (inv (inv x) = x); otherwise `inv l` already
            // equals the flip-rendered letter syntactically.
            if first.neg {
                let x = &first.atom;
                let fls_l = render_l(g, &flip(rest));
                // inv l = inv (inv x); rewrite it to x with the context
                // L (flip ls) fixed on the left.
                let invinv = EqP {
                    a: app(&g.inv, &app(&g.inv, x)),
                    b: x.clone(),
                    p: inst(&g.inv_inv, &[x]),
                };
                let step3 = cmul_l(g, &invinv, &fls_l);
                tr(g, &tr(g, &step1, &step2), &step3)
            } else {
                // step2's right side is already render_l(flip w).
                tr(g, &step1, &step2)
            }
        }
    }
}

/// Prove `render_l w = render_r w` by rotating the association spine.
///
/// Peel the last letter (left-associated products expose their last letter
/// at the right of the root), re-associate once with `mul_assoc`, convert
/// the shorter prefix by induction, and fix the right component with
/// `cong_mul_r`.  Words of length ≤ 2 render identically both ways.
fn conv_lr(g: &Group, w: &[Letter]) -> EqP {
    if w.len() <= 2 {
        return rfl2(&render_l(g, w), &render_r(g, w));
    }
    let (init, last) = (&w[..w.len() - 1], &w[w.len() - 1]);
    // L(w) = mul (L init) last; unfold L(init) once more when it is a product.
    let last_t = letter_term(&g.inv, last);
    let (inner_init, second_last) = (&init[..init.len() - 1], &init[init.len() - 1]);
    let second_last_t = letter_term(&g.inv, second_last);
    let l_inner = render_l(g, inner_init);
    // step1: mul (mul (L ii) sl) last = mul (L ii) (mul sl last)   [assoc]
    let step1 = EqP {
        a: g.mul_t(&g.mul_t(&l_inner, &second_last_t), &last_t),
        b: g.mul_t(&l_inner, &g.mul_t(&second_last_t, &last_t)),
        p: inst(&g.mul_assoc, &[&l_inner, &second_last_t, &last_t]),
    };
    // step2: convert the prefix by induction: L(ii) = R(ii)
    let rec = conv_lr(g, inner_init);
    let step2 = cmul_l(g, &rec, &g.mul_t(&second_last_t, &last_t));
    // Now at: mul (R ii) (mul sl last).
    // step3: rotate the remainder: mul (R ii) (mul sl last)
    //        = mul l1 (…)? — instead recurse on the whole suffix via bridge:
    // R(w) = mul (head) (R(tail)); bridge grows R from the back:
    //   mul (R ii) (mul sl last) = R(ii ++ [sl, last]) = R(w)   by bridge.
    let bridged = bridge(g, inner_init, &[second_last.clone(), last.clone()]);
    tr(g, &tr(g, &step1, &step2), &bridged)
}

/// Prove `mul (render_r xs) (render_r ys) = render_r (xs ++ ys)` for a
/// non-empty `ys`, growing the right-associated rendering from the back.
fn bridge(g: &Group, xs: &[Letter], ys: &[Letter]) -> EqP {
    match xs.split_first() {
        // mul one (R ys) = R ys
        None => {
            let ys_r = render_r(g, ys);
            EqP {
                a: g.mul_t(&g.one, &ys_r),
                b: ys_r,
                p: inst(&g.one_mul, &[&render_r(g, ys)]),
            }
        }
        Some((_h, t)) if t.is_empty() => {
            // xs = [h]: mul h (R ys) = R([h] ++ ys) — identical by definition.
            let lhs = g.mul_t(&render_r(g, xs), &render_r(g, ys));
            let joined = xs.iter().chain(ys.iter()).cloned().collect::<Vec<_>>();
            rfl2(&lhs, &render_r(g, &joined))
        }
        Some((h, t)) => {
            let h_t = letter_term(&g.inv, h);
            let rt = render_r(g, t);
            let ys_r = render_r(g, ys);
            // R(xs) = mul h (R t) syntactically.
            let e1 = EqP {
                a: g.mul_t(&g.mul_t(&h_t, &rt), &ys_r),
                b: g.mul_t(&h_t, &g.mul_t(&rt, &ys_r)),
                p: inst(&g.mul_assoc, &[&h_t, &rt, &ys_r]),
            };
            let inner = bridge(g, t, ys);
            let e2 = cmul_l(g, &inner, &h_t);
            tr(g, &e1, &e2)
        }
    }
}

/// Prove `mul (render_r wa) (render_r wb) = render_r (reduce_concat wa wb)`
/// for already-reduced `wa`/`wb`.  Peels `wa` from the front; the junction
/// cancellation surfaces exactly when the peeled prefix is a single letter.
fn concat_pf(g: &Group, wa: &[Letter], wb: &[Letter], session: &mut Session) -> EqP {
    match wa.split_first() {
        // mul one Wb = Wb
        None => {
            let wb_r = render_r(g, wb);
            EqP {
                a: g.mul_t(&g.one, &wb_r),
                b: wb_r,
                p: inst(&g.one_mul, &[&render_r(g, wb)]),
            }
        }
        Some((first, rest)) if rest.is_empty() => {
            let l_t = letter_term(&g.inv, first);
            match wb.split_first() {
                // mul l one = l
                None => EqP {
                    a: g.mul_t(&l_t, &g.one),
                    b: l_t.clone(),
                    p: inst(&g.mul_one, &[&l_t]),
                },
                Some((m, wb_rest)) => {
                    let m_t = letter_term(&g.inv, m);
                    let cancel = first.neg != m.neg && {
                        let a_nf = nbe_eval_ctx(g.ctx_len, &first.atom, session);
                        let b_nf = nbe_eval_ctx(g.ctx_len, &m.atom, session);
                        a_nf == b_nf
                    };
                    if !cancel {
                        return wrfl_concat(g, wa, wb);
                    }
                    let pair = if first.neg {
                        inst(&g.inv_l, &[&first.atom])
                    } else {
                        inst(&g.inv_r, &[&first.atom])
                    };
                    if wb_rest.is_empty() {
                        // mul l m = one
                        EqP {
                            a: g.mul_t(&l_t, &m_t),
                            b: g.one.clone(),
                            p: pair,
                        }
                    } else {
                        let wbr = render_r(g, wb_rest);
                        // s1: mul l (mul m W') = mul (mul l m) W'
                        let fwd = EqP {
                            a: g.mul_t(&g.mul_t(&l_t, &m_t), &wbr),
                            b: g.mul_t(&l_t, &g.mul_t(&m_t, &wbr)),
                            p: inst(&g.mul_assoc, &[&l_t, &m_t, &wbr]),
                        };
                        let s1 = sy(g, &fwd);
                        // s2: mul (mul l m) W' = mul one W'
                        //     (the cancelling pair varies; W' is fixed)
                        let pair_eq = EqP {
                            a: g.mul_t(&l_t, &m_t),
                            b: g.one.clone(),
                            p: pair,
                        };
                        let s2 = cmul_r(g, &pair_eq, &wbr);
                        // s3: mul one W' = W'
                        let s3 = EqP {
                            a: g.mul_t(&g.one, &wbr),
                            b: wbr.clone(),
                            p: inst(&g.one_mul, &[&wbr]),
                        };
                        tr(g, &tr(g, &s1, &s2), &s3)
                    }
                }
            }
        }
        Some((first, rest)) => {
            let l_t = letter_term(&g.inv, first);
            let ls_r = render_r(g, rest);
            let wb_r = render_r(g, wb);
            // e1: mul (mul l (R ls)) (R wb) = mul l (mul (R ls) (R wb))
            let e1 = EqP {
                a: g.mul_t(&g.mul_t(&l_t, &ls_r), &wb_r),
                b: g.mul_t(&l_t, &g.mul_t(&ls_r, &wb_r)),
                p: inst(&g.mul_assoc, &[&l_t, &ls_r, &wb_r]),
            };
            let inner = concat_pf(g, rest, wb, session);
            let mut e2 = cmul_l(g, &inner, &l_t);
            // When the whole suffix reduces to nothing, e2 ends at
            // `mul l one`; drop the unit so the endpoint matches R(w).
            if e2.b == g.mul_t(&l_t, &g.one) {
                let drop = EqP {
                    a: g.mul_t(&l_t, &g.one),
                    b: l_t.clone(),
                    p: inst(&g.mul_one, &[&l_t]),
                };
                e2 = tr(g, &e2, &drop);
            }
            tr(g, &e1, &e2)
        }
    }
}

/// No-cancellation case: both sides are literally the same term.
fn wrfl_concat(g: &Group, wa: &[Letter], wb: &[Letter]) -> EqP {
    let lhs = g.mul_t(&render_r(g, wa), &render_r(g, wb));
    let joined = wa.iter().chain(wb.iter()).cloned().collect::<Vec<_>>();
    rfl2(&lhs, &render_r(g, &joined))
}

/// Generate a proof that `t` equals its fully reduced word (canonical
/// right-associated rendering).
fn gen_side(g: &Group, t: &GT, session: &mut Session) -> (Word, EqP) {
    match t {
        GT::One(orig) => (Vec::new(), rfl2(orig, &g.one)),
        GT::Atom(x) => {
            let w = vec![Letter {
                neg: false,
                atom: x.clone(),
            }];
            let r = render_r(g, &w);
            (w, rfl2(x, &r))
        }
        GT::Inv(_, u) => {
            let (wu, pu) = gen_side(g, u, session);
            // pu : u = R(wu); invert the whole equation.
            let s0 = cinv(g, &pu); // inv u = inv (R wu)
            let fin = finisher_inv(g, &wu); // inv (R wu) = L (flip wu)
            let inv_word = flip(&wu);
            let inv_word_r = render_r(g, &inv_word);
            let to_l = tr(g, &s0, &fin); // inv u = L (flip wu)
            // Bridge back to the canonical right-associated rendering.
            let reassoc = conv_lr(g, &inv_word); // L (flip wu) = R (flip wu)
            let p = tr(g, &to_l, &reassoc);
            let orig = match t {
                GT::Inv(orig, _) => orig.clone(),
                _ => unreachable!("Inv arm"),
            };
            (
                inv_word,
                EqP {
                    a: orig,
                    b: inv_word_r,
                    p: p.p,
                },
            )
        }
        GT::Mul(_, a, b) => {
            let (wa, pa) = gen_side(g, a, session);
            let (wb, pb) = gen_side(g, b, session);
            let w = reduce_concat(g, &wa, &wb, session);
            let p0 = cmul2(g, &pa, &pb);
            let pc = concat_pf(g, &wa, &wb, session);
            let p = tr(g, &p0, &pc);
            let w_r = render_r(g, &w);
            let orig = match t {
                GT::Mul(orig, _, _) => orig.clone(),
                _ => unreachable!("Mul arm"),
            };
            (
                w,
                EqP {
                    a: orig,
                    b: w_r,
                    p: p.p,
                },
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Prove a path goal over an abstract group.
pub fn prove(
    dts: &[Datatype],
    ctx: &Ctx,
    goal_ty: &Term,
    _num_tactic: usize,
    _num_intro: usize,
    group_term: Option<&Term>,
    session: &mut Session,
) -> Result<Term, TypeError> {
    let (u, v, carrier) = {
        let goal_nf = nbe_eval_ctx(ctx.len(), goal_ty, session);
        match goal_nf {
            Term::TPath(a, u, v) => {
                let a_nf = nbe_eval_ctx(ctx.len(), &a, session);
                (*u, *v, a_nf)
            }
            other => {
                return Err(TypeError::Other(format!(
                    "group: goal is not a path (got '{}')",
                    other,
                )));
            }
        }
    };

    let grp = Group::resolve(dts, ctx, &carrier, group_term, session)?;

    let tu = classify(&grp, &u, session);
    let tv = classify(&grp, &v, session);

    let (wu, pu) = gen_side(&grp, &tu, session);
    let (wv, pv) = gen_side(&grp, &tv, session);

    // Decide: reduced words must agree letter-by-letter (defeq atoms).
    let agree = wu.len() == wv.len()
        && wu.iter().zip(wv.iter()).all(|(a, b)| {
            a.neg == b.neg
                && nbe_eval_ctx(grp.ctx_len, &a.atom, session)
                    == nbe_eval_ctx(grp.ctx_len, &b.atom, session)
        });
    if !agree {
        return Err(TypeError::Other(format!(
            "group: cannot prove '{}' = '{}': the words do not match \
             (reduced forms differ)",
            show_side(&u),
            show_side(&v),
        )));
    }

    // Per-side diagnostics: check each half independently first.
    {
        let goal_l = Term::TPath(
            Box::new(carrier.clone()),
            Box::new(u.clone()),
            Box::new(pu.b.clone()),
        );
        let prev_skip = crate::cubical::typechecker::termination::should_skip_guard(session);
        crate::cubical::typechecker::termination::set_skip_guard(true, session);
        let r = check_dt(dts, ctx, &pu.p, &goal_l, session);
        crate::cubical::typechecker::termination::set_skip_guard(prev_skip, session);
        if let Err(e) = r {
            crate::debug_log!(
                "group: LEFT proof term: {}",
                crate::cubical::syntax::pretty::show_term(&[], &pu.p)
            );
            return Err(TypeError::Other(format!(
                "group: LEFT side proof failed ({} = {}): {}",
                show_side(&u),
                show_side_term(&pu.b),
                e
            )));
        }
        let goal_r = Term::TPath(
            Box::new(carrier.clone()),
            Box::new(v.clone()),
            Box::new(pv.b.clone()),
        );
        let prev_skip = crate::cubical::typechecker::termination::should_skip_guard(session);
        crate::cubical::typechecker::termination::set_skip_guard(true, session);
        let r = check_dt(dts, ctx, &pv.p, &goal_r, session);
        crate::cubical::typechecker::termination::set_skip_guard(prev_skip, session);
        if let Err(e) = r {
            return Err(TypeError::Other(format!(
                "group: RIGHT side proof failed ({} = {}): {}",
                show_side(&v),
                show_side_term(&pv.b),
                e
            )));
        }
    }

    let pf = tr(&grp, &pu, &sy(&grp, &pv));

    // Hand the proof to the kernel — the soundness backstop.
    let prev_skip = crate::cubical::typechecker::termination::should_skip_guard(session);
    crate::cubical::typechecker::termination::set_skip_guard(true, session);
    let check_res = check_dt(dts, ctx, &pf.p, goal_ty, session);
    crate::cubical::typechecker::termination::set_skip_guard(prev_skip, session);
    if let Err(_e) = &check_res {
        crate::debug_log!(
            "group: generated proof for goal '{}':\n  {}",
            crate::cubical::syntax::pretty::show_term(&[], goal_ty),
            crate::cubical::syntax::pretty::show_term(&[], &pf.p)
        );
    }
    check_res.map_err(|e| TypeError::Other(format!("group: kernel rejected the proof: {}", e)))?;
    Ok(pf.p)
}

fn show_side(t: &Term) -> String {
    crate::cubical::syntax::pretty::show_term(&[], t)
}

fn show_side_term(t: &Term) -> String {
    crate::cubical::syntax::pretty::show_term(&[], t)
}
