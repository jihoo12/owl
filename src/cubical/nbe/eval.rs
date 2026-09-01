//! Term evaluation: NbE from `Term`s to `Value`s.

use std::collections::BTreeSet;

use super::elim::{do_apply, do_elim, do_force, do_fst, do_papp, do_proj, do_snd};
use super::hcomp::{do_comp, do_fill, do_hcomp, do_hfill};
use super::quote::quote;
use super::trace::record_step;
use super::transport::{do_transp, do_transport, transport_term_fallback};
use super::util::{do_equiv_fwd, equiv_dom_value, value_to_dnf, value_to_endpoint};
use super::value::{
    Closure, DNFSystem, Globals, IClosure, Neutral, NeutralInner, Scope, Value, value_str,
};
use crate::cubical::interval::{DNF, I, Literal, dnf_bot, dnf_top};
use crate::cubical::session::Session;
use crate::cubical::syntax::{ElimCase, Name, System, Tactic, Term, max_var, subst};

/// Structurally substitute interval variable `Var(target)` (the closure's
/// bound interval variable, incremented under nested PLams) with `val` in a
/// term. Pure traversal — no re-normalisation; the caller evaluates the result.
pub(super) fn subst_interval_var(t: &Term, target: i32, val: &I) -> Term {
    fn go_i(i: &I, target: i32, val: &I) -> I {
        match i {
            I::Var(k) if *k == target => val.clone(),
            I::Meet(a, b) => I::Meet(
                Box::new(go_i(a, target, val)),
                Box::new(go_i(b, target, val)),
            ),
            I::Join(a, b) => I::Join(
                Box::new(go_i(a, target, val)),
                Box::new(go_i(b, target, val)),
            ),
            I::Neg(a) => I::Neg(Box::new(go_i(a, target, val))),
            other => other.clone(),
        }
    }

    fn go(t: &Term, target: i32, val: &I) -> Term {
        match t {
            Term::TInterval(i) => Term::TInterval(go_i(i, target, val)),
            Term::TCube(DNF { cubes }) => {
                let subst_lit = |l: &Literal| -> I {
                    match l {
                        Literal::Pos(k) => go_i(&I::Var(*k), target, val),
                        Literal::NegVar(k) => I::Neg(Box::new(go_i(&I::Var(*k), target, val))),
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
                Term::TInterval(combined)
            }
            Term::TApp(f, a) => {
                Term::TApp(Box::new(go(f, target, val)), Box::new(go(a, target, val)))
            }
            Term::TAbs(x, b) => Term::TAbs(x.clone(), Box::new(go(b, target, val))),
            Term::TPi(x, a, b, implicit) => Term::TPi(
                x.clone(),
                Box::new(go(a, target, val)),
                Box::new(go(b, target, val)),
                *implicit,
            ),
            Term::TPath(a, u, v) => Term::TPath(
                Box::new(go(a, target, val)),
                Box::new(go(u, target, val)),
                Box::new(go(v, target, val)),
            ),
            Term::PLam(x, b) => Term::PLam(x.clone(), Box::new(go(b, target + 1, val))),
            Term::PApp(p, r) => {
                Term::PApp(Box::new(go(p, target, val)), Box::new(go(r, target, val)))
            }
            Term::THComp(a, sys, base) => Term::THComp(
                Box::new(go(a, target, val)),
                sys.iter()
                    .map(|(phi, t)| (go(phi, target, val), go(t, target, val)))
                    .collect(),
                Box::new(go(base, target, val)),
            ),
            Term::TComp(a, sys, base) => Term::TComp(
                Box::new(go(a, target, val)),
                sys.iter()
                    .map(|(phi, t)| (go(phi, target, val), go(t, target, val)))
                    .collect(),
                Box::new(go(base, target, val)),
            ),
            Term::TFill(a, sys, base) => Term::TFill(
                Box::new(go(a, target, val)),
                sys.iter()
                    .map(|(phi, t)| (go(phi, target, val), go(t, target, val)))
                    .collect(),
                Box::new(go(base, target, val)),
            ),
            Term::THFill(a, sys, base) => Term::THFill(
                Box::new(go(a, target, val)),
                sys.iter()
                    .map(|(phi, t)| (go(phi, target, val), go(t, target, val)))
                    .collect(),
                Box::new(go(base, target, val)),
            ),
            Term::TEquiv(a, b) => {
                Term::TEquiv(Box::new(go(a, target, val)), Box::new(go(b, target, val)))
            }
            Term::TMkEquiv(a, b, f, g, eta, eps) => Term::TMkEquiv(
                Box::new(go(a, target, val)),
                Box::new(go(b, target, val)),
                Box::new(go(f, target, val)),
                Box::new(go(g, target, val)),
                Box::new(go(eta, target, val)),
                Box::new(go(eps, target, val)),
            ),
            Term::TEquivFwd(e, x) => {
                Term::TEquivFwd(Box::new(go(e, target, val)), Box::new(go(x, target, val)))
            }
            Term::TUa(e) => Term::TUa(Box::new(go(e, target, val))),
            Term::TTransport(p, x) => {
                Term::TTransport(Box::new(go(p, target, val)), Box::new(go(x, target, val)))
            }
            Term::TGlue(a, ph, te) => Term::TGlue(
                Box::new(go(a, target, val)),
                Box::new(go(ph, target, val)),
                Box::new(go(te, target, val)),
            ),
            Term::TGlueElem(ph, x, a) => Term::TGlueElem(
                Box::new(go(ph, target, val)),
                Box::new(go(x, target, val)),
                Box::new(go(a, target, val)),
            ),
            Term::TUnglue(ph, te, g) => Term::TUnglue(
                Box::new(go(ph, target, val)),
                Box::new(go(te, target, val)),
                Box::new(go(g, target, val)),
            ),
            Term::TPartial(ph, a) => {
                Term::TPartial(Box::new(go(ph, target, val)), Box::new(go(a, target, val)))
            }
            Term::TSystemType(sys) => Term::TSystemType(
                sys.iter()
                    .map(|(phi, a)| (go(phi, target, val), go(a, target, val)))
                    .collect(),
            ),
            Term::TSigma(x, a, b) => Term::TSigma(
                x.clone(),
                Box::new(go(a, target, val)),
                Box::new(go(b, target, val)),
            ),
            Term::TPair(a, b) => {
                Term::TPair(Box::new(go(a, target, val)), Box::new(go(b, target, val)))
            }
            Term::TFst(p) => Term::TFst(Box::new(go(p, target, val))),
            Term::TSnd(p) => Term::TSnd(Box::new(go(p, target, val))),
            Term::TData(d, params) => Term::TData(
                d.clone(),
                params.iter().map(|a| go(a, target, val)).collect(),
            ),
            Term::TCon(data, con, args) => Term::TCon(
                data.clone(),
                con.clone(),
                args.iter().map(|a| go(a, target, val)).collect(),
            ),
            Term::TPCon(data, con, args, r) => Term::TPCon(
                data.clone(),
                con.clone(),
                args.iter().map(|a| go(a, target, val)).collect(),
                Box::new(go(r, target, val)),
            ),
            Term::TSqCon(data, con, args, r, s) => Term::TSqCon(
                data.clone(),
                con.clone(),
                args.iter().map(|a| go(a, target, val)).collect(),
                Box::new(go(r, target, val)),
                Box::new(go(s, target, val)),
            ),
            Term::TCellCon(data, con, args, ivars) => Term::TCellCon(
                data.clone(),
                con.clone(),
                args.iter().map(|a| go(a, target, val)).collect(),
                ivars.iter().map(|a| go(a, target, val)).collect(),
            ),
            Term::TElim(motive, cases, scrut) => Term::TElim(
                Box::new(go(motive, target, val)),
                cases
                    .iter()
                    .map(|c| ElimCase {
                        con: c.con.clone(),
                        binders: c.binders.clone(),
                        body: Box::new(go(&c.body, target, val)),
                        as_name: c.as_name.clone(),
                        record_bindings: c.record_bindings.clone(),
                        refinements: c.refinements.clone(),
                    })
                    .collect(),
                Box::new(go(scrut, target, val)),
            ),
            Term::TProj(field, record) => {
                Term::TProj(field.clone(), Box::new(go(record, target, val)))
            }
            Term::TRecordUpdate(record, fields) => Term::TRecordUpdate(
                Box::new(go(record, target, val)),
                fields
                    .iter()
                    .map(|(f, t)| (f.clone(), go(t, target, val)))
                    .collect(),
            ),
            Term::TDelay(a) => Term::TDelay(Box::new(go(a, target, val))),
            Term::TNext(a) => Term::TNext(Box::new(go(a, target, val))),
            Term::TForce(a) => Term::TForce(Box::new(go(a, target, val))),
            Term::TBy(tactics) => Term::TBy(
                tactics
                    .iter()
                    .map(|tac| match tac {
                        Tactic::Exact(t) => Tactic::Exact(go(t, target, val)),
                        other => other.clone(),
                    })
                    .collect(),
            ),
            other => other.clone(),
        }
    }

    go(t, target, val)
}

/// Evaluate a term with local variables in `env` and global definitions in `globals`.
///
/// `global_offset` is the index into `globals` (in env.defs order, most-recent-first)
/// corresponding to the definition whose body is being evaluated.
/// A TVar(k) where k >= env.len() is a global reference:
///   globals[global_offset + (k - env.len())]
/// UNLESS that is also out of bounds — in which case we create a neutral.
///
/// Normalization can diverge on definitions that reference themselves directly
/// (e.g. `def f : Nat -> Nat := fun n => f n`): evaluating the global value
/// re-resolves the self-reference to the same lambda forever, growing the
/// recursion unboundedly. Cap the evaluation depth so such inputs produce a
/// Maximum eval depth before returning a stuck neutral. This prevents stack
/// overflow on divergent terms (self-application, infinite recursions) while
/// allowing legitimate deep normal forms. The cap is generous (2000) to avoid
/// truncating real proofs; the 256 MiB CLI stack and 64 MiB test stacks
/// provide additional headroom.
const EVAL_NBE_MAX_DEPTH: usize = 2000;

pub fn eval_nbe(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    t: &Term,
    session: &mut Session,
) -> Value {
    let depth = session.eval_depth_enter();
    if depth >= EVAL_NBE_MAX_DEPTH {
        session.eval_depth_restore(depth);
        return Value::VNeutral(Neutral::nvar(depth));
    }
    let result = eval_nbe_inner(env, globals, global_offset, t, session);
    session.eval_depth_restore(depth);
    result
}

fn eval_nbe_inner(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    t: &Term,
    session: &mut Session,
) -> Value {
    match t {
        Term::TVar(i) => {
            let i = *i as usize;
            if i < env.len() {
                env.lookup(i).clone()
            } else {
                let g = globals.borrow();
                let global_idx = global_offset + (i - env.len());
                if global_idx < g.len() {
                    g[global_idx].clone()
                } else {
                    Value::VNeutral(Neutral::nvar(global_idx - g.len()))
                }
            }
        }
        Term::TApp(f, a) => do_apply(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, f, session),
            eval_nbe(env, globals, global_offset, a, session),
            session,
        ),
        Term::TAbs(x, b) => Value::VLam(
            x.clone(),
            Closure {
                env: env.clone(),
                globals: globals.clone(),
                global_offset,
                body: (**b).clone(),
            },
        ),
        Term::TUniv(n) => Value::VUniv(*n),
        Term::TProp => Value::VProp,
        Term::TSSet => Value::VSSet,
        Term::TLift(a, lvl) => Value::VLift(
            Box::new(eval_nbe(env, globals, global_offset, a, session)),
            *lvl,
        ),
        Term::TLower(a) => {
            Value::VLower(Box::new(eval_nbe(env, globals, global_offset, a, session)))
        }
        Term::TIntervalTy => Value::VIntervalTy,
        Term::TPi(x, a, b, implicit) => Value::VPi(
            x.clone(),
            Box::new(eval_nbe(env, globals, global_offset, a, session)),
            Closure {
                env: env.clone(),
                globals: globals.clone(),
                global_offset,
                body: (**b).clone(),
            },
            *implicit,
        ),
        Term::TInterval(i) => Value::VInterval(i.clone()),
        Term::TCube(c) => Value::VCube(c.clone()),
        Term::TPath(a, u, v) => Value::VPath(
            Box::new(eval_nbe(env, globals, global_offset, a, session)),
            Box::new(eval_nbe(env, globals, global_offset, u, session)),
            Box::new(eval_nbe(env, globals, global_offset, v, session)),
        ),
        Term::PLam(x, b) => Value::VPLam(
            x.clone(),
            IClosure {
                env: env.clone(),
                globals: globals.clone(),
                global_offset,
                body: (**b).clone(),
            },
        ),
        Term::PApp(p, r) => do_papp(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, p, session),
            eval_nbe(env, globals, global_offset, r, session),
            session,
        ),
        Term::THComp(a, sys, base) => do_hcomp(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, a, session),
            eval_system(env, globals, global_offset, sys, session),
            eval_nbe(env, globals, global_offset, base, session),
            session,
        ),
        Term::TComp(a, sys, base) => do_comp(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, a, session),
            eval_system(env, globals, global_offset, sys, session),
            eval_nbe(env, globals, global_offset, base, session),
            session,
        ),
        Term::TFill(a, sys, base) => do_fill(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, a, session),
            eval_system(env, globals, global_offset, sys, session),
            eval_nbe(env, globals, global_offset, base, session),
            session,
        ),
        Term::THFill(a, sys, base) => do_hfill(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, a, session),
            eval_system(env, globals, global_offset, sys, session),
            eval_nbe(env, globals, global_offset, base, session),
            session,
        ),
        Term::TEquiv(a, b) => Value::VEquiv(
            Box::new(eval_nbe(env, globals, global_offset, a, session)),
            Box::new(eval_nbe(env, globals, global_offset, b, session)),
        ),
        Term::TMkEquiv(a, b, f, g, eta, eps) => Value::VMkEquiv(
            Box::new(eval_nbe(env, globals, global_offset, a, session)),
            Box::new(eval_nbe(env, globals, global_offset, b, session)),
            Box::new(eval_nbe(env, globals, global_offset, f, session)),
            Box::new(eval_nbe(env, globals, global_offset, g, session)),
            Box::new(eval_nbe(env, globals, global_offset, eta, session)),
            Box::new(eval_nbe(env, globals, global_offset, eps, session)),
        ),
        Term::TEquivFwd(e, x) => do_equiv_fwd(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, e, session),
            eval_nbe(env, globals, global_offset, x, session),
            session,
        ),
        Term::TUa(e) => Value::VUa(Box::new(eval_nbe(env, globals, global_offset, e, session))),
        Term::TTransport(p, x) => {
            let p_val = eval_nbe(env, globals, global_offset, p, session);
            let x_val = eval_nbe(env, globals, global_offset, x, session);
            let res = do_transport(
                env,
                globals,
                global_offset,
                p_val.clone(),
                x_val.clone(),
                session,
            );
            match &res {
                Value::VTransport(_, _) => {
                    let p_term = quote(env.len(), globals, global_offset, p_val, session);
                    let x_term = quote(env.len(), globals, global_offset, x_val, session);
                    let reduced = transport_term_fallback(p_term, x_term, session);
                    match reduced {
                        Term::TTransport(_, _) => res,
                        _ => eval_nbe(env, globals, global_offset, &reduced, session),
                    }
                }
                Value::VNeutral(n) if matches!(n.inner(), NeutralInner::NTransport(_, _)) => {
                    let p_term = quote(env.len(), globals, global_offset, p_val, session);
                    let x_term = quote(env.len(), globals, global_offset, x_val, session);
                    let reduced = transport_term_fallback(p_term, x_term, session);
                    match reduced {
                        Term::TTransport(_, _) => res,
                        _ => eval_nbe(env, globals, global_offset, &reduced, session),
                    }
                }
                _ => res,
            }
        }
        Term::TTransp(a, r, x) => {
            let a_val = eval_nbe(env, globals, global_offset, a, session);
            let r_val = eval_nbe(env, globals, global_offset, r, session);
            let x_val = eval_nbe(env, globals, global_offset, x, session);
            do_transp(env, globals, global_offset, a_val, r_val, x_val, session)
        }
        Term::TGlue(a, phi, te) => {
            let phi = value_to_dnf(eval_nbe(env, globals, global_offset, phi, session), session);
            let te = eval_nbe(env, globals, global_offset, te, session);
            if phi == dnf_top() {
                match te {
                    Value::VLam(_, clos) => {
                        let body = clos.apply(Value::VInterval(I::I1), session);
                        equiv_dom_value(body)
                    }
                    other => equiv_dom_value(other),
                }
            } else if phi == dnf_bot() {
                eval_nbe(env, globals, global_offset, a, session)
            } else {
                Value::VGlue(
                    Box::new(eval_nbe(env, globals, global_offset, a, session)),
                    phi,
                    Box::new(te),
                )
            }
        }
        Term::TPartial(phi, a) => {
            let phi_val = eval_nbe(env, globals, global_offset, phi, session);
            let a_val = eval_nbe(env, globals, global_offset, a, session);
            let phi_dnf = value_to_dnf(phi_val, session);
            if phi_dnf == dnf_top() {
                a_val
            } else {
                Value::VPartial(Box::new(a_val), Box::new(Value::VCube(phi_dnf)))
            }
        }
        Term::TSystemType(sys) => {
            let mut entries: DNFSystem = Vec::new();
            for (phi, a) in sys {
                let phi_val = eval_nbe(env, globals, global_offset, phi, session);
                let a_val = eval_nbe(env, globals, global_offset, a, session);
                let phi_dnf = value_to_dnf(phi_val, session);
                entries.push((phi_dnf, a_val));
            }
            Value::VSystemType(entries)
        }
        Term::TGlueElem(phi, t, a) => {
            let phi_dnf =
                value_to_dnf(eval_nbe(env, globals, global_offset, phi, session), session);
            let a_val = eval_nbe(env, globals, global_offset, a, session);
            if phi_dnf == dnf_top() {
                // phi=1: glue [1, t, a] = t
                // But if t = unglue(te, a), then unglue(glue [1, unglue(te, a), a]) = a
                // (Glue/unglue β for top face).
                eval_nbe(env, globals, global_offset, t, session)
            } else if phi_dnf == dnf_bot() {
                a_val
            } else {
                Value::VGlueElem(
                    phi_dnf,
                    Box::new(eval_nbe(env, globals, global_offset, t, session)),
                    Box::new(a_val),
                )
            }
        }
        Term::TUnglue(phi, te, g) => {
            let phi = value_to_dnf(eval_nbe(env, globals, global_offset, phi, session), session);
            let te = eval_nbe(env, globals, global_offset, te, session);
            let g_val = eval_nbe(env, globals, global_offset, g, session);
            if phi == dnf_top() {
                do_equiv_fwd(globals, global_offset, te, g_val, session)
            } else if phi == dnf_bot() {
                g_val
            } else {
                match &g_val {
                    Value::VGlueElem(g_phi, _, a) if *g_phi == phi => *a.clone(),
                    _ => Value::VUnglue(phi, Box::new(te), Box::new(g_val)),
                }
            }
        }
        Term::TSigma(x, a, b) => Value::VSigma(
            x.clone(),
            Box::new(eval_nbe(env, globals, global_offset, a, session)),
            Closure {
                env: env.clone(),
                globals: globals.clone(),
                global_offset,
                body: (**b).clone(),
            },
        ),
        Term::TPair(a, b) => Value::VPair(
            Box::new(eval_nbe(env, globals, global_offset, a, session)),
            Box::new(eval_nbe(env, globals, global_offset, b, session)),
        ),
        Term::TFst(p) => do_fst(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, p, session),
            session,
        ),
        Term::TSnd(p) => do_snd(
            globals,
            global_offset,
            eval_nbe(env, globals, global_offset, p, session),
            session,
        ),
        Term::TProj(field, r) => do_proj(
            field,
            eval_nbe(env, globals, global_offset, r, session),
            session,
        ),
        Term::TRecordUpdate(r, updates) => {
            let r_val = eval_nbe(env, globals, global_offset, r, session);
            let updates_val: Vec<(Name, Value)> = updates
                .iter()
                .map(|(f, e)| (f.clone(), eval_nbe(env, globals, global_offset, e, session)))
                .collect();
            // Eagerly desugar when the record evaluates to a VCon.
            if let Value::VCon(ref dt, ref con, ref args) = r_val {
                let dts = session.current_dts();
                if let Some(dt_sig) = dts.iter().find(|d| &d.name == dt) {
                    if let Some(field_names) = &dt_sig.field_names {
                        let mut new_args = args.clone();
                        for (field, val) in &updates_val {
                            if let Some(idx) = field_names.iter().position(|f| f == field) {
                                if idx < new_args.len() {
                                    new_args[idx] = val.clone();
                                }
                            }
                        }
                        return Value::VCon(dt.clone(), con.clone(), new_args);
                    }
                }
            }
            Value::VRecordUpdate(Box::new(r_val), updates_val)
        }
        Term::TData(d, params) => Value::VData(
            d.clone(),
            params
                .iter()
                .map(|p| eval_nbe(env, globals, global_offset, p, session))
                .collect(),
        ),
        Term::TCon(data, con, args) => Value::VCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| eval_nbe(env, globals, global_offset, a, session))
                .collect(),
        ),
        Term::TPCon(data, con, args, r) => {
            let r_v = eval_nbe(env, globals, global_offset, r, session);
            // A path constructor applied at a concrete endpoint is
            // definitionally its face (c args @ i0 = face0, c args @ i1 =
            // face1), so reduce instead of leaving a stuck VPCon normal form.
            // The face is substituted with the *original* args and evaluated
            // in the *same* env (mirroring the typechecker's
            // reduce_pcon_endpoints_dt), so open args keep their levels —
            // only faces that reference the datatype's parameters (levels
            // >= arity in the face scope, which have no counterpart in the
            // eval env) are left neutral.
            let mut reduced: Option<Term> = None;
            if let Some(endpoint) = value_to_endpoint(&r_v)
                && let Some(dt) = session.current_dts().iter().find(|dt| &dt.name == data)
                && let Some(sig) = dt.pcons.iter().find(|c| &c.name == con)
            {
                let arity = args.len();
                let face = if endpoint == I::I0 {
                    &sig.face0
                } else {
                    &sig.face1
                };
                if max_var(face) < arity as i32 {
                    let mut face_inst = face.clone();
                    for k in (0..arity).rev() {
                        face_inst = subst(k as i32, &args[arity - 1 - k], &face_inst);
                    }
                    reduced = Some(face_inst);
                }
            }
            if let Some(face_inst) = reduced {
                let face_val = eval_nbe(env, globals, global_offset, &face_inst, session);
                record_step(
                    "pcon-endpoint".into(),
                    format!(
                        "{} @ {}",
                        con,
                        if value_to_endpoint(&r_v) == Some(I::I0) {
                            "0"
                        } else {
                            "1"
                        }
                    ),
                    value_str(globals, global_offset, &face_val, session),
                );
                face_val
            } else {
                let args_v: Vec<Value> = args
                    .iter()
                    .map(|a| eval_nbe(env, globals, global_offset, a, session))
                    .collect();
                Value::VPCon(data.clone(), con.clone(), args_v, Box::new(r_v))
            }
        }
        Term::TSqCon(data, con, args, r, s) => {
            let r_v = eval_nbe(env, globals, global_offset, r, session);
            let s_v = eval_nbe(env, globals, global_offset, s, session);
            // Square-constructor boundary reduction, mirroring the
            // typechecker's reduce_pcon_endpoints_dt:
            //   sq @ 0 @ s = face_j0 @ s   (outer path at r=0 is face_j0)
            //   sq @ 1 @ s = face_j1 @ s
            //   sq @ r @ 0 = face_i0       (inner path at s=0 is a point)
            //   sq @ r @ 1 = face_i1
            // Faces are substituted with the original args and the resulting
            // term is evaluated in the same env, so open args keep their
            // levels; faces referencing the datatype's parameters (levels
            // >= arity in the face scope) are left neutral.
            let mut reduced: Option<Term> = None;
            if let Some(dt) = session.current_dts().iter().find(|dt| &dt.name == data)
                && let Some(sig) = dt.sqcons.iter().find(|c| &c.name == con)
            {
                let arity = args.len();
                if [&sig.face_i0, &sig.face_i1, &sig.face_j0, &sig.face_j1]
                    .iter()
                    .all(|f| max_var(f) < arity as i32)
                {
                    let subst_args = |face: &Term| {
                        let mut t = face.clone();
                        for k in (0..arity).rev() {
                            t = subst(k as i32, &args[arity - 1 - k], &t);
                        }
                        t
                    };
                    if let Some(endpoint) = value_to_endpoint(&r_v) {
                        let face = if endpoint == I::I0 {
                            &sig.face_j0
                        } else {
                            &sig.face_j1
                        };
                        let face_inst = subst_args(face);
                        reduced = Some(Term::PApp(Box::new(face_inst), s.clone()));
                    } else if let Some(endpoint) = value_to_endpoint(&s_v) {
                        let face = if endpoint == I::I0 {
                            &sig.face_i0
                        } else {
                            &sig.face_i1
                        };
                        reduced = Some(subst_args(face));
                    }
                }
            }
            if let Some(reduced) = reduced {
                let face_val = eval_nbe(env, globals, global_offset, &reduced, session);
                record_step(
                    "sqcon-endpoint".into(),
                    format!("{} @ ...", con),
                    value_str(globals, global_offset, &face_val, session),
                );
                face_val
            } else {
                Value::VSqCon(
                    data.clone(),
                    con.clone(),
                    args.iter()
                        .map(|a| eval_nbe(env, globals, global_offset, a, session))
                        .collect(),
                    Box::new(r_v),
                    Box::new(s_v),
                )
            }
        }
        Term::TCellCon(data, con, args, ivars) => {
            let ivars_v: Vec<Value> = ivars
                .iter()
                .map(|v| eval_nbe(env, globals, global_offset, v, session))
                .collect();
            // Cell-constructor boundary reduction, mirroring the typechecker's
            // reduce_pcon_endpoints_dt. When the *outermost* interval arg is a
            // concrete endpoint, the outermost face pair is the value at that
            // endpoint:
            //   cell @ 0 @ r2 .. = faces[2n-2] @ r2 ..   (an (n-1)-cell)
            //   cell @ 1 @ r2 .. = faces[2n-1] @ r2 ..
            // and the remaining interval args are applied outermost-first
            // (r2, r3, ...). Faces are substituted with the original args and
            // the resulting PApp chain is evaluated in the same env, so open
            // args keep their levels; faces referencing the datatype's
            // parameters (levels >= arity in the face scope) are left neutral.
            let mut reduced: Option<Term> = None;
            if !ivars.is_empty()
                && let Some(dt) = session.current_dts().iter().find(|dt| &dt.name == data)
                && let Some(sig) = dt.cellcons.iter().find(|c| &c.name == con)
                && ivars.len() == sig.dimension()
            {
                let arity = args.len();
                let dim = sig.dimension();
                if sig.faces.iter().all(|f| max_var(f) < arity as i32)
                    && let Some(endpoint) = value_to_endpoint(&ivars_v[0])
                {
                    let face = if endpoint == I::I0 {
                        &sig.faces[2 * dim - 2]
                    } else {
                        &sig.faces[2 * dim - 1]
                    };
                    let mut t = face.clone();
                    for k in (0..arity).rev() {
                        t = subst(k as i32, &args[arity - 1 - k], &t);
                    }
                    for iv in &ivars[1..] {
                        t = Term::PApp(Box::new(t), Box::new(iv.clone()));
                    }
                    reduced = Some(t);
                }
            }
            if let Some(reduced) = reduced {
                let face_val = eval_nbe(env, globals, global_offset, &reduced, session);
                record_step(
                    "cellcon-endpoint".into(),
                    format!("{} @ ...", con),
                    value_str(globals, global_offset, &face_val, session),
                );
                face_val
            } else {
                Value::VCellCon(
                    data.clone(),
                    con.clone(),
                    args.iter()
                        .map(|a| eval_nbe(env, globals, global_offset, a, session))
                        .collect(),
                    ivars_v,
                )
            }
        }
        Term::TElim(motive, cases, scrut) => do_elim(
            eval_nbe(env, globals, global_offset, motive, session),
            cases,
            eval_nbe(env, globals, global_offset, scrut, session),
            env,
            globals,
            global_offset,
            session,
        ),
        Term::Meta(i) => {
            if *i >= 0 {
                if let Some(solution) = session.get_meta_solution(*i) {
                    return eval_nbe(env, globals, global_offset, &solution, session);
                }
            }
            Value::VNeutral(Neutral::nmeta(*i))
        }
        Term::TBy(_) => panic!("TBy should be resolved before NbE"),
        Term::TDelay(a) => {
            Value::VDelay(Box::new(eval_nbe(env, globals, global_offset, a, session)))
        }
        Term::TNext(a) => Value::VNext(Box::new(eval_nbe(env, globals, global_offset, a, session))),
        Term::TForce(a) => do_force(
            eval_nbe(env, globals, global_offset, a, session),
            globals,
            global_offset,
            session,
        ),
    }
}

/// Evaluate a term-level system into a DNFSystem.
pub fn eval_system(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    sys: &System,
    session: &mut Session,
) -> DNFSystem {
    sys.iter()
        .map(|(phi, t)| {
            let phi_val = eval_nbe(env, globals, global_offset, phi, session);
            let phi_dnf = value_to_dnf(phi_val, session);
            let t_val = eval_nbe(env, globals, global_offset, t, session);
            (phi_dnf, t_val)
        })
        .collect()
}
