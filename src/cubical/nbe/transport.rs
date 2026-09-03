//! Transport along type families: the cubical transport operation, its
//! per-type-shape specialisations and the term-level fallback.

use super::eval::eval_nbe;
use super::hcomp::do_hcomp;
use super::nbe_eval;
use super::quote::quote;
use super::trace::record_step;
use super::util::{do_equiv_fwd, equiv_dom_value};
use super::value::{Closure, DNFSystem, Globals, IClosure, Neutral, Scope, Value, value_str};
use crate::cubical::interval::{DNF, I, dnf_bot, dnf_top};
use crate::cubical::session::Session;
use crate::cubical::syntax::{
    LevelExpr, Term, beta, equiv_dom, is_bot_dnf, is_top_dnf, max_var, shift, subst,
};
use std::sync::Arc;

pub fn do_transp(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    a: Value,
    r: Value,
    x: Value,
    session: &mut Session,
) -> Value {
    use super::value::Neutral;

    match r {
        Value::VInterval(I::I0) => x,
        Value::VInterval(I::I1) => {
            // If the family is already a VPLam, do_transport handles it directly.
            // If not (e.g. VAbs from `fun (i : I) => ...`, or a stuck neutral),
            // eta-expand into a synthetic VPLam: λi. a(i) so do_transport can
            // inspect the type structure at i0 and i1.
            match &a {
                Value::VPLam(_, _) | Value::VUa(_) => {
                    do_transport(env, globals, global_offset, a, x, session)
                }
                _ => {
                    let a_term = quote(env.len(), globals, global_offset, a, session);
                    let fam = Term::PLam(
                        "_transp_i".to_string(),
                        Arc::new(Term::TApp(
                            Arc::new(shift(1, 0, &a_term)),
                            Arc::new(Term::TVar(0)),
                        )),
                    );
                    let fam_val = eval_nbe(env, globals, global_offset, &fam, session);
                    do_transport(env, globals, global_offset, fam_val, x, session)
                }
            }
        }
        _ => {
            if let Value::VNeutral(n) = r {
                let a_term = quote(env.len(), globals, global_offset, a, session);
                let r_term = quote(
                    env.len(),
                    globals,
                    global_offset,
                    Value::VNeutral(n),
                    session,
                );
                let x_term = quote(env.len(), globals, global_offset, x, session);
                Value::VNeutral(Neutral::ntransp(
                    eval_nbe(env, globals, global_offset, &a_term, session),
                    eval_nbe(env, globals, global_offset, &r_term, session),
                    eval_nbe(env, globals, global_offset, &x_term, session),
                ))
            } else {
                let a_term = quote(env.len(), globals, global_offset, a, session);
                let r_term = quote(env.len(), globals, global_offset, r, session);
                let x_term = quote(env.len(), globals, global_offset, x, session);
                Value::VNeutral(Neutral::ntransp(
                    eval_nbe(env, globals, global_offset, &a_term, session),
                    eval_nbe(env, globals, global_offset, &r_term, session),
                    eval_nbe(env, globals, global_offset, &x_term, session),
                ))
            }
        }
    }
}

pub fn do_transport(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    p: Value,
    x: Value,
    session: &mut Session,
) -> Value {
    match p {
        Value::VUa(e) => {
            let result = do_equiv_fwd(globals, global_offset, e.as_ref().clone(), x, session);
            record_step(
                "transport-ua".into(),
                "transport (ua _) _".into(),
                value_str(globals, global_offset, &result, session),
            );
            result
        }
        Value::VPLam(ref i_name, ref clos) => {
            let b0 = clos.apply_i(I::I0, session);
            let b1 = clos.apply_i(I::I1, session);
            if quote(0, globals, global_offset, b0.clone(), session)
                == quote(0, globals, global_offset, b1.clone(), session)
            {
                record_step(
                    "transport-const".into(),
                    "transport (λi. A) x [A constant]".into(),
                    value_str(globals, global_offset, &x, session),
                );
                return x;
            }

            match (&b0, &b1) {
                (Value::VUniv(_), Value::VUniv(_)) => {
                    record_step(
                        "transport-univ".into(),
                        "transport (λi. Univ) _".into(),
                        value_str(globals, global_offset, &x, session),
                    );
                    x
                }

                // Prop/SSet transport (constant type families, same as Univ)
                (Value::VProp, Value::VProp) | (Value::VSSet, Value::VSSet) => {
                    record_step(
                        "transport-prop-ss".into(),
                        "transport (λi. Prop/SSet) _".into(),
                        value_str(globals, global_offset, &x, session),
                    );
                    x
                }

                // Lift transport: transport (λi. Lift (A i) lvl) x
                (Value::VLift(_, _), Value::VLift(_, _)) => Value::VTransport(
                    Arc::new(Value::VPLam(i_name.to_string(), clos.clone())),
                    Arc::new(x),
                ),

                // Lower transport: same fallback
                (Value::VLower(_), Value::VLower(_)) => Value::VTransport(
                    Arc::new(Value::VPLam(i_name.to_string(), clos.clone())),
                    Arc::new(x),
                ),

                // Pi transport (non-dependent codomain only)
                (Value::VPi(arg_name, _, _, _), Value::VPi(_, _, _, _)) => {
                    let result = transport_pi(
                        env,
                        globals,
                        global_offset,
                        i_name,
                        clos,
                        arg_name,
                        x,
                        session,
                    );
                    record_step(
                        "transport-pi".into(),
                        "transport (λi. Π _ _) _".into(),
                        value_str(globals, global_offset, &result, session),
                    );
                    result
                }

                // Path transport
                (Value::VPath(_, _, _), Value::VPath(_, _, _)) => {
                    let result =
                        transport_path(env, globals, global_offset, i_name, clos, x, session);
                    record_step(
                        "transport-path".into(),
                        "transport (λi. Path _ _ _) _".into(),
                        value_str(globals, global_offset, &result, session),
                    );
                    result
                }

                // Sigma transport (pair only)
                (Value::VSigma(_, _, _), Value::VSigma(_, _, _)) => match x {
                    Value::VPair(ref a, ref b) => {
                        let result = transport_sigma_pair(
                            env,
                            globals,
                            global_offset,
                            i_name,
                            clos,
                            a,
                            b,
                            session,
                        );
                        record_step(
                            "transport-sigma".into(),
                            "transport (λi. Σ _ _) (_, _)".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        result
                    }
                    _ => Value::VTransport(
                        Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                        Arc::new(x),
                    ),
                },

                // Glue transport (phi=bot or phi=top)
                (Value::VGlue(_, phi0, _), Value::VGlue(_, _, _)) => {
                    let r = transport_glue(
                        env,
                        globals,
                        global_offset,
                        i_name,
                        clos,
                        phi0,
                        &x,
                        session,
                    );
                    r.unwrap_or_else(|| {
                        Value::VTransport(
                            Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                            Arc::new(x),
                        )
                    })
                }

                // Data type transport: transport through a data type family.
                // First check if it's a constant family (same params at i0 and i1),
                // then handle indexed types (different params at i0 vs i1).
                (Value::VData(d0, _), Value::VData(d1, _)) if d0 == d1 => {
                    // Check if the family is constant (same params at i0 and i1).
                    let is_constant = {
                        let t0 = clos.apply_i(I::I0, session);
                        let t1 = clos.apply_i(I::I1, session);
                        quote(0, globals, global_offset, t0, session)
                            == quote(0, globals, global_offset, t1, session)
                    };
                    match x {
                        Value::VCon(ref d, ref con, ref args) if d == d0 => {
                            let result = transport_data_con(
                                env,
                                globals,
                                global_offset,
                                i_name,
                                clos,
                                con,
                                args,
                                !is_constant,
                                session,
                            );
                            record_step(
                                if is_constant {
                                    "transport-data"
                                } else {
                                    "transport-data-indexed"
                                }
                                .into(),
                                format!("transport (λi. {}) ({} ...)", d, con),
                                value_str(globals, global_offset, &result, session),
                            );
                            result
                        }
                        Value::VPCon(ref d, ref con, ref args, ref r) if d == d0 => {
                            let result = transport_data_pcon(
                                env,
                                globals,
                                global_offset,
                                i_name,
                                clos,
                                con,
                                args,
                                r,
                                !is_constant,
                                session,
                            );
                            record_step(
                                if is_constant {
                                    "transport-data-pcon"
                                } else {
                                    "transport-data-pcon-indexed"
                                }
                                .into(),
                                format!("transport (λi. {}) ({} ...)", d, con),
                                value_str(globals, global_offset, &result, session),
                            );
                            result
                        }
                        Value::VSqCon(ref d, ref con, ref args, ref r, ref s) if d == d0 => {
                            let result = transport_data_sqcon(
                                env,
                                globals,
                                global_offset,
                                i_name,
                                clos,
                                con,
                                args,
                                r,
                                s,
                                !is_constant,
                                session,
                            );
                            record_step(
                                if is_constant {
                                    "transport-data-sqcon"
                                } else {
                                    "transport-data-sqcon-indexed"
                                }
                                .into(),
                                format!("transport (λi. {}) ({} ...)", d, con),
                                value_str(globals, global_offset, &result, session),
                            );
                            result
                        }
                        Value::VCellCon(ref d, ref con, ref args, ref ivars) if d == d0 => {
                            let result = transport_data_cellcon(
                                env,
                                globals,
                                global_offset,
                                i_name,
                                clos,
                                con,
                                args,
                                ivars,
                                !is_constant,
                                session,
                            );
                            record_step(
                                if is_constant {
                                    "transport-data-cellcon"
                                } else {
                                    "transport-data-cellcon-indexed"
                                }
                                .into(),
                                format!("transport (λi. {}) ({} ...)", d, con),
                                value_str(globals, global_offset, &result, session),
                            );
                            result
                        }
                        _ => Value::VTransport(
                            Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                            Arc::new(x),
                        ),
                    }
                }

                _ => Value::VTransport(
                    Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                    Arc::new(x),
                ),
            }
        }
        other => Value::VNeutral(Neutral::ntransport(other, x)),
    }
}

/// Evaluate the body of a PLam at a formal interval variable (TVar(0) in the
/// returned term will be the interval binder).
fn eval_body_at_formal_interval(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    clos: &IClosure,
    session: &mut Session,
) -> (Scope, Value) {
    let body_with_var = beta(&shift(1, 0, &clos.body), &Term::TVar(0));
    let formal_env = env.extend(Value::VIntervalVar(env.len()));
    let evaluated = eval_nbe(&formal_env, globals, global_offset, &body_with_var, session);
    (formal_env, evaluated)
}

/// Apply a Closure with a dummy argument (for non-dependent extraction).
fn apply_non_dep(clos: &Closure, session: &mut Session) -> Value {
    clos.apply(Value::VInterval(I::I0), session)
}

/// Check whether a term references de Bruijn variable at the given level,
/// correctly tracking binder depth. Under each binder, the target variable's
/// de Bruijn index increases by 1.
pub fn uses_var_at_level(t: &Term, level: i32) -> bool {
    match t {
        Term::TVar(i) => *i == level,
        Term::TApp(f, a) => uses_var_at_level(f, level) || uses_var_at_level(a, level),
        Term::TAbs(_, b) => uses_var_at_level(b, level + 1),
        Term::TPi(_, a, b, _) => uses_var_at_level(a, level) || uses_var_at_level(b, level + 1),
        Term::TPath(a, u, v) => {
            uses_var_at_level(a, level)
                || uses_var_at_level(u, level)
                || uses_var_at_level(v, level)
        }
        Term::TId(a, u, v) => {
            uses_var_at_level(a, level)
                || uses_var_at_level(u, level)
                || uses_var_at_level(v, level)
        }
        Term::TRefl(a) => uses_var_at_level(a, level),
        Term::TJ(motive, base, p) => {
            uses_var_at_level(motive, level)
                || uses_var_at_level(base, level)
                || uses_var_at_level(p, level)
        }
        Term::PLam(_, b) => uses_var_at_level(b, level + 1),
        Term::PApp(p, r) => uses_var_at_level(p, level) || uses_var_at_level(r, level),
        Term::THComp(a, sys, base) => {
            uses_var_at_level(a, level)
                || sys.iter().any(|(phi, tube)| {
                    uses_var_at_level(phi, level) || uses_var_at_level(tube, level)
                })
                || uses_var_at_level(base, level)
        }
        Term::TComp(a, sys, base) => {
            uses_var_at_level(a, level)
                || sys.iter().any(|(phi, tube)| {
                    uses_var_at_level(phi, level) || uses_var_at_level(tube, level)
                })
                || uses_var_at_level(base, level)
        }
        Term::TFill(a, sys, base) => {
            uses_var_at_level(a, level)
                || sys.iter().any(|(phi, tube)| {
                    uses_var_at_level(phi, level) || uses_var_at_level(tube, level)
                })
                || uses_var_at_level(base, level)
        }
        Term::THFill(a, sys, base) => {
            uses_var_at_level(a, level)
                || sys.iter().any(|(phi, tube)| {
                    uses_var_at_level(phi, level) || uses_var_at_level(tube, level)
                })
                || uses_var_at_level(base, level)
        }
        Term::TEquiv(a, b) => uses_var_at_level(a, level) || uses_var_at_level(b, level),
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            uses_var_at_level(a, level)
                || uses_var_at_level(b, level)
                || uses_var_at_level(f, level)
                || uses_var_at_level(g, level)
                || uses_var_at_level(eta, level)
                || uses_var_at_level(eps, level)
        }
        Term::TEquivFwd(e, x) => uses_var_at_level(e, level) || uses_var_at_level(x, level),
        Term::TUa(e) => uses_var_at_level(e, level),
        Term::TTransport(p, x) => uses_var_at_level(p, level) || uses_var_at_level(x, level),
        Term::TTransp(a, r, x) => {
            uses_var_at_level(a, level)
                || uses_var_at_level(r, level)
                || uses_var_at_level(x, level)
        }
        Term::TGlue(a, phi, te) => {
            uses_var_at_level(a, level)
                || uses_var_at_level(phi, level)
                || uses_var_at_level(te, level)
        }
        Term::TGlueElem(phi, t, a) => {
            uses_var_at_level(phi, level)
                || uses_var_at_level(t, level)
                || uses_var_at_level(a, level)
        }
        Term::TUnglue(phi, te, g) => {
            uses_var_at_level(phi, level)
                || uses_var_at_level(te, level)
                || uses_var_at_level(g, level)
        }
        Term::TPartial(phi, a) => uses_var_at_level(phi, level) || uses_var_at_level(a, level),
        Term::TSystemType(sys) => sys
            .iter()
            .any(|(phi, a)| uses_var_at_level(phi, level) || uses_var_at_level(a, level)),
        Term::TSigma(_, a, b) => uses_var_at_level(a, level) || uses_var_at_level(b, level + 1),
        Term::TPair(a, b) => uses_var_at_level(a, level) || uses_var_at_level(b, level),
        Term::TFst(p) => uses_var_at_level(p, level),
        Term::TSnd(p) => uses_var_at_level(p, level),
        Term::TProj(_, r) => uses_var_at_level(r, level),
        Term::TRecordUpdate(r, updates) => {
            uses_var_at_level(r, level) || updates.iter().any(|(_, e)| uses_var_at_level(e, level))
        }
        Term::TUniv(_)
        | Term::TProp
        | Term::TSSet
        | Term::TIntervalTy
        | Term::TLevelTy
        | Term::TInterval(_)
        | Term::TCube(_) => false,
        Term::TLift(a, _) => uses_var_at_level(a, level),
        Term::TLower(a) => uses_var_at_level(a, level),
        Term::TData(_, params) => params.iter().any(|p| uses_var_at_level(p, level)),
        Term::TCon(_, _, args) => args.iter().any(|a| uses_var_at_level(a, level)),
        Term::TPCon(_, _, args, r) => {
            args.iter().any(|a| uses_var_at_level(a, level)) || uses_var_at_level(r, level)
        }
        Term::TSqCon(_, _, args, r, s) => {
            args.iter().any(|a| uses_var_at_level(a, level))
                || uses_var_at_level(r, level)
                || uses_var_at_level(s, level)
        }
        Term::TCellCon(_, _, args, ivars) => {
            args.iter().any(|a| uses_var_at_level(a, level))
                || ivars.iter().any(|v| uses_var_at_level(v, level))
        }
        Term::TElim(motive, cases, scrut) => {
            uses_var_at_level(motive, level)
                || uses_var_at_level(scrut, level)
                || cases.iter().any(|c| uses_var_at_level(&c.body, level + 1))
        }
        Term::Meta(_) => false,
        Term::TBy(_) => false,
        Term::TDelay(a) | Term::TNext(a) | Term::TForce(a) => uses_var_at_level(a, level),
        Term::TQuote(a) | Term::TUnquote(a) => uses_var_at_level(a, level),
        Term::TGetContext => false,
        Term::TGetType(a) => uses_var_at_level(a, level),
        Term::TUnify(a, bx) => uses_var_at_level(a, level) || uses_var_at_level(bx, level),
    }
}

/// Transport through Pi types.
fn transport_pi(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    arg_name: &str,
    x: Value,
    session: &mut Session,
) -> Value {
    let (formal_env, pi_at_var) =
        eval_body_at_formal_interval(env, globals, global_offset, clos, session);
    let cod_clos = match &pi_at_var {
        Value::VPi(_, _, cod_clos, _) => cod_clos,
        _ => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(x),
            );
        }
    };

    if !uses_var_at_level(&cod_clos.body, 0i32) {
        let b_val = apply_non_dep(cod_clos, session);
        let b_body = shift(
            1,
            1,
            &quote(formal_env.len(), globals, global_offset, b_val, session),
        );
        let b_fam = Term::PLam(i_name.to_string(), Arc::new(b_body));
        let x_term = quote(env.len(), globals, global_offset, x, session);
        let result = Term::TAbs(
            arg_name.to_string(),
            Arc::new(Term::TTransport(
                Arc::new(b_fam),
                Arc::new(Term::TApp(
                    Arc::new(shift(1, 0, &x_term)),
                    Arc::new(Term::TVar(0)),
                )),
            )),
        );
        eval_nbe(env, globals, global_offset, &result, session)
    } else {
        let p_term = quote(
            env.len(),
            globals,
            global_offset,
            Value::VPLam(i_name.to_string(), clos.clone()),
            session,
        );
        let x_term = quote(env.len(), globals, global_offset, x.clone(), session);
        let reduced = transport_term_fallback(p_term, x_term, session);
        match reduced {
            Term::TTransport(_, _) => Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(x),
            ),
            _ => eval_nbe(env, globals, global_offset, &reduced, session),
        }
    }
}

/// Transport through Path types.
fn transport_path(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    x: Value,
    session: &mut Session,
) -> Value {
    let (formal_env, path_at_var) =
        eval_body_at_formal_interval(env, globals, global_offset, clos, session);
    let a_val = match &path_at_var {
        Value::VPath(a, _, _) => a.as_ref().clone(),
        _ => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(x),
            );
        }
    };
    let a_body = shift(
        1,
        1,
        &quote(formal_env.len(), globals, global_offset, a_val, session),
    );
    let a_fam = Term::PLam(i_name.to_string(), Arc::new(a_body));
    let x_term = quote(env.len(), globals, global_offset, x, session);
    let a_fam_s = shift(1, 0, &a_fam);
    let result = Term::PLam(
        "j".to_string(),
        Arc::new(Term::TTransport(
            Arc::new(a_fam_s),
            Arc::new(Term::PApp(
                Arc::new(shift(1, 0, &x_term)),
                Arc::new(Term::TVar(0)),
            )),
        )),
    );
    eval_nbe(env, globals, global_offset, &result, session)
}

/// Transport through Sigma types (pair decomposition).
fn transport_sigma_pair(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    a: &Value,
    b: &Value,
    session: &mut Session,
) -> Value {
    let (formal_env, sigma_at_var) =
        eval_body_at_formal_interval(env, globals, global_offset, clos, session);
    let a_val = match &sigma_at_var {
        Value::VSigma(_, a_val, _) => a_val.as_ref().clone(),
        _ => Value::VUniv(LevelExpr::LConst(0)),
    };
    let a_body = shift(
        1,
        1,
        &quote(formal_env.len(), globals, global_offset, a_val, session),
    );
    let a_fam = Term::PLam(i_name.to_string(), Arc::new(a_body));

    let a_prime = eval_nbe(
        env,
        globals,
        global_offset,
        &Term::TTransport(
            Arc::new(a_fam.clone()),
            Arc::new(quote(env.len(), globals, global_offset, a.clone(), session)),
        ),
        session,
    );

    let b_val = match &sigma_at_var {
        Value::VSigma(_, _, cod_clos) => apply_non_dep(cod_clos, session),
        _ => Value::VUniv(LevelExpr::LConst(0)),
    };
    let b_body = shift(
        1,
        1,
        &quote(formal_env.len(), globals, global_offset, b_val, session),
    );
    let b_fam = Term::PLam(i_name.to_string(), Arc::new(b_body));

    let b_prime = eval_nbe(
        env,
        globals,
        global_offset,
        &Term::TTransport(
            Arc::new(b_fam),
            Arc::new(quote(env.len(), globals, global_offset, b.clone(), session)),
        ),
        session,
    );

    Value::VPair(Arc::new(a_prime), Arc::new(b_prime))
}

/// Transport a constructor `con c a₁ ... aₙ` through a data type family.
///
/// When `eval_at_i1` is false (constant family), builds type families from the
/// constructor signature at i0. When true (indexed family), builds type families
/// from the signature evaluated at i1, so that indices at the target endpoint
/// are correctly reflected.
///
/// Strategy: build the constructor's full Pi type from the Datatype definition,
/// transport the entire function through the family, then apply to the original
/// arguments. This works because:
///   transport (λi. D) (con c a₁ ... aₙ) = con c (trans₁ a₁) ... (transₙ aₙ)
/// where transₖ transports argument k through its type (instantiated with
/// the already-transported earlier arguments).
fn transport_data_con(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    con_name: &str,
    args: &[Value],
    eval_at_i1: bool,
    session: &mut Session,
) -> Value {
    let dts = session.current_dts();
    let d_name = match clos.apply_i(I::I0, session) {
        Value::VData(name, _) => name,
        _ => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VCon("".into(), con_name.into(), args.to_vec())),
            );
        }
    };
    let dt = match dts.iter().find(|dt| dt.name == d_name) {
        Some(dt) => dt.clone(),
        None => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VCon(d_name.clone(), con_name.into(), args.to_vec())),
            );
        }
    };
    let con_sig = match dt.find_con(con_name) {
        Some(sig) => sig.clone(),
        None => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VCon(d_name.clone(), con_name.into(), args.to_vec())),
            );
        }
    };

    let n = con_sig.arity();
    if n == 0 {
        return Value::VCon(d_name.clone(), con_name.into(), vec![]);
    }

    // Build type families for each argument.
    // For constant families (eval_at_i1=false), use the constructor signature directly.
    // For indexed families (eval_at_i1=true), evaluate the data type at the formal
    // interval variable and extract argument types from the resulting Pi type at i1.
    let mut result_args: Vec<Value> = Vec::new();

    if eval_at_i1 {
        // Indexed family: the data type's params change along the interval.
        // Evaluate the closure at the formal interval variable to get
        // VData(d, params_at_i) where each params_at_i[j] is the param's
        // interval-dependent value (may reference the interval variable).
        let (formal_env, dt_at_var) =
            eval_body_at_formal_interval(env, globals, global_offset, clos, session);
        let params_at_i = match &dt_at_var {
            Value::VData(_, params) => params.clone(),
            _ => vec![],
        };

        // Build type families for each constructor arg.
        // The constructor sig arg_tys are Terms in constructor scope:
        //   de Bruijn 0..n-1 = constructor args (innermost first)
        //   de Bruijn n..n+m-1 = data type params (innermost first)
        // After PLam shift (shift by 1), the interval variable sits at de Bruijn 0,
        // constructor args at 1..n, data type params at n+1..n+m.
        // Substitute each param variable TVar(n + m - j) with its interval-dependent value.
        for k in 0..n {
            let ty_k = con_sig.arg_tys[k].clone();
            let mut ty_shifted = ty_k;

            // Shift for the PLam binder
            for j in (0..=k).rev() {
                ty_shifted = shift(1, j as i32, &ty_shifted);
            }

            // Substitute data type params with their interval-dependent values.
            // After the PLam shift, param j (0-indexed in push order) is at
            // de Bruijn n + m - j (since params were pushed innermost-first).
            let num_params = dt.params.len();
            for j in 0..num_params {
                let pos = (n + num_params - j) as i32;
                if let Some(p_val) = params_at_i.get(j) {
                    let p_term = quote(
                        formal_env.len(),
                        globals,
                        global_offset,
                        p_val.clone(),
                        session,
                    );
                    ty_shifted = subst(pos, &p_term, &ty_shifted);
                }
            }

            // Substitute already-transported earlier args
            for j in 0..k {
                let arg_term = quote(
                    env.len(),
                    globals,
                    global_offset,
                    result_args[j].clone(),
                    session,
                );
                ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
            }

            let ty_fam = Term::PLam(i_name.to_string(), Arc::new(ty_shifted));
            let transported = eval_nbe(
                env,
                globals,
                global_offset,
                &Term::TTransport(
                    Arc::new(ty_fam),
                    Arc::new(quote(
                        env.len(),
                        globals,
                        global_offset,
                        args[k].clone(),
                        session,
                    )),
                ),
                session,
            );
            result_args.push(transported);
        }
    } else {
        // Constant family: use the constructor signature directly
        let substed_tys: Vec<Term> = con_sig.arg_tys.clone();
        for k in 0..n {
            let ty_k = substed_tys[k].clone();
            let mut ty_shifted = ty_k;
            for j in (0..=k).rev() {
                ty_shifted = shift(1, j as i32, &ty_shifted);
            }
            for j in 0..k {
                let arg_term = quote(
                    env.len(),
                    globals,
                    global_offset,
                    result_args[j].clone(),
                    session,
                );
                ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
            }
            let ty_fam = Term::PLam(i_name.to_string(), Arc::new(ty_shifted));
            let transported = eval_nbe(
                env,
                globals,
                global_offset,
                &Term::TTransport(
                    Arc::new(ty_fam),
                    Arc::new(quote(
                        env.len(),
                        globals,
                        global_offset,
                        args[k].clone(),
                        session,
                    )),
                ),
                session,
            );
            result_args.push(transported);
        }
    }

    Value::VCon(d_name.clone(), con_name.into(), result_args)
}

/// Transport a path constructor `pcon c a₁ ... aₙ r` through a data type family.
/// Same strategy as transport_data_con, but also keeps the interval argument r unchanged.
fn transport_data_pcon(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    con_name: &str,
    args: &[Value],
    r: &Value,
    eval_at_i1: bool,
    session: &mut Session,
) -> Value {
    let dts = session.current_dts();
    let d_name = match clos.apply_i(I::I0, session) {
        Value::VData(name, _) => name,
        _ => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VPCon(
                    "".into(),
                    con_name.into(),
                    args.to_vec(),
                    Arc::new(r.clone()),
                )),
            );
        }
    };
    let dt = match dts.iter().find(|dt| dt.name == d_name) {
        Some(dt) => dt.clone(),
        None => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VPCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    Arc::new(r.clone()),
                )),
            );
        }
    };
    let con_sig = match dt.find_pcon(con_name) {
        Some(sig) => sig.clone(),
        None => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VPCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    Arc::new(r.clone()),
                )),
            );
        }
    };

    let n = con_sig.arity();
    if n == 0 {
        return Value::VPCon(d_name.clone(), con_name.into(), vec![], Arc::new(r.clone()));
    }

    let mut result_args: Vec<Value> = Vec::new();

    if eval_at_i1 {
        // Indexed family: substitute param variables with interval-dependent values.
        let (formal_env, dt_at_var) =
            eval_body_at_formal_interval(env, globals, global_offset, clos, session);
        let params_at_i = match &dt_at_var {
            Value::VData(_, params) => params.clone(),
            _ => vec![],
        };
        let num_params = dt.params.len();
        for k in 0..n {
            let ty_k = con_sig.arg_tys[k].clone();
            let mut ty_shifted = ty_k;
            for j in (0..=k).rev() {
                ty_shifted = shift(1, j as i32, &ty_shifted);
            }
            for j in 0..num_params {
                let pos = (n + num_params - j) as i32;
                if let Some(p_val) = params_at_i.get(j) {
                    let p_term = quote(
                        formal_env.len(),
                        globals,
                        global_offset,
                        p_val.clone(),
                        session,
                    );
                    ty_shifted = subst(pos, &p_term, &ty_shifted);
                }
            }
            for j in 0..k {
                let arg_term = quote(
                    env.len(),
                    globals,
                    global_offset,
                    result_args[j].clone(),
                    session,
                );
                ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
            }
            let ty_fam = Term::PLam(i_name.to_string(), Arc::new(ty_shifted));
            let transported = eval_nbe(
                env,
                globals,
                global_offset,
                &Term::TTransport(
                    Arc::new(ty_fam),
                    Arc::new(quote(
                        env.len(),
                        globals,
                        global_offset,
                        args[k].clone(),
                        session,
                    )),
                ),
                session,
            );
            result_args.push(transported);
        }
    } else {
        let substed_tys: Vec<Term> = con_sig.arg_tys.clone();
        for k in 0..n {
            let ty_k = substed_tys[k].clone();
            let mut ty_shifted = ty_k;
            for j in (0..=k).rev() {
                ty_shifted = shift(1, j as i32, &ty_shifted);
            }
            for j in 0..k {
                let arg_term = quote(
                    env.len(),
                    globals,
                    global_offset,
                    result_args[j].clone(),
                    session,
                );
                ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
            }
            let ty_fam = Term::PLam(i_name.to_string(), Arc::new(ty_shifted));
            let transported = eval_nbe(
                env,
                globals,
                global_offset,
                &Term::TTransport(
                    Arc::new(ty_fam),
                    Arc::new(quote(
                        env.len(),
                        globals,
                        global_offset,
                        args[k].clone(),
                        session,
                    )),
                ),
                session,
            );
            result_args.push(transported);
        }
    }

    Value::VPCon(
        d_name.clone(),
        con_name.into(),
        result_args,
        Arc::new(r.clone()),
    )
}

/// Transport a square constructor `sqcon c a₁ ... aₙ r s` through a data type family.
fn transport_data_sqcon(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    con_name: &str,
    args: &[Value],
    r: &Value,
    s: &Value,
    eval_at_i1: bool,
    session: &mut Session,
) -> Value {
    let dts = session.current_dts();
    let d_name = match clos.apply_i(I::I0, session) {
        Value::VData(name, _) => name,
        _ => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VSqCon(
                    "".into(),
                    con_name.into(),
                    args.to_vec(),
                    Arc::new(r.clone()),
                    Arc::new(s.clone()),
                )),
            );
        }
    };
    let dt = match dts.iter().find(|dt| dt.name == d_name) {
        Some(dt) => dt.clone(),
        None => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VSqCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    Arc::new(r.clone()),
                    Arc::new(s.clone()),
                )),
            );
        }
    };
    let con_sig = match dt.find_sqcon(con_name) {
        Some(sig) => sig.clone(),
        None => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VSqCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    Arc::new(r.clone()),
                    Arc::new(s.clone()),
                )),
            );
        }
    };

    let n = con_sig.arity();
    if n == 0 {
        return Value::VSqCon(
            d_name.clone(),
            con_name.into(),
            vec![],
            Arc::new(r.clone()),
            Arc::new(s.clone()),
        );
    }

    let mut result_args: Vec<Value> = Vec::new();

    if eval_at_i1 {
        let (formal_env, dt_at_var) =
            eval_body_at_formal_interval(env, globals, global_offset, clos, session);
        let params_at_i = match &dt_at_var {
            Value::VData(_, params) => params.clone(),
            _ => vec![],
        };
        let num_params = dt.params.len();
        for k in 0..n {
            let ty_k = con_sig.arg_tys[k].clone();
            let mut ty_shifted = ty_k;
            for j in (0..=k).rev() {
                ty_shifted = shift(1, j as i32, &ty_shifted);
            }
            for j in 0..num_params {
                let pos = (n + num_params - j) as i32;
                if let Some(p_val) = params_at_i.get(j) {
                    let p_term = quote(
                        formal_env.len(),
                        globals,
                        global_offset,
                        p_val.clone(),
                        session,
                    );
                    ty_shifted = subst(pos, &p_term, &ty_shifted);
                }
            }
            for j in 0..k {
                let arg_term = quote(
                    env.len(),
                    globals,
                    global_offset,
                    result_args[j].clone(),
                    session,
                );
                ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
            }
            let ty_fam = Term::PLam(i_name.to_string(), Arc::new(ty_shifted));
            let transported = eval_nbe(
                env,
                globals,
                global_offset,
                &Term::TTransport(
                    Arc::new(ty_fam),
                    Arc::new(quote(
                        env.len(),
                        globals,
                        global_offset,
                        args[k].clone(),
                        session,
                    )),
                ),
                session,
            );
            result_args.push(transported);
        }
    } else {
        let substed_tys: Vec<Term> = con_sig.arg_tys.clone();
        for k in 0..n {
            let ty_k = substed_tys[k].clone();
            let mut ty_shifted = ty_k;
            for j in (0..=k).rev() {
                ty_shifted = shift(1, j as i32, &ty_shifted);
            }
            for j in 0..k {
                let arg_term = quote(
                    env.len(),
                    globals,
                    global_offset,
                    result_args[j].clone(),
                    session,
                );
                ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
            }
            let ty_fam = Term::PLam(i_name.to_string(), Arc::new(ty_shifted));
            let transported = eval_nbe(
                env,
                globals,
                global_offset,
                &Term::TTransport(
                    Arc::new(ty_fam),
                    Arc::new(quote(
                        env.len(),
                        globals,
                        global_offset,
                        args[k].clone(),
                        session,
                    )),
                ),
                session,
            );
            result_args.push(transported);
        }
    }

    Value::VSqCon(
        d_name.clone(),
        con_name.into(),
        result_args,
        Arc::new(r.clone()),
        Arc::new(s.clone()),
    )
}

/// Transport an n-dimensional cell constructor through a data type family.
/// Same strategy as transport_data_pcon/sqcon, but keeps all interval args unchanged.
fn transport_data_cellcon(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    con_name: &str,
    args: &[Value],
    ivars: &[Value],
    eval_at_i1: bool,
    session: &mut Session,
) -> Value {
    let dts = session.current_dts();
    let d_name = match clos.apply_i(I::I0, session) {
        Value::VData(name, _) => name,
        _ => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VCellCon(
                    "".into(),
                    con_name.into(),
                    args.to_vec(),
                    ivars.to_vec(),
                )),
            );
        }
    };
    let dt = match dts.iter().find(|dt| dt.name == d_name) {
        Some(dt) => dt.clone(),
        None => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VCellCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    ivars.to_vec(),
                )),
            );
        }
    };
    let con_sig = match dt.find_cellcon(con_name) {
        Some(sig) => sig.clone(),
        None => {
            return Value::VTransport(
                Arc::new(Value::VPLam("_".to_string(), clos.clone())),
                Arc::new(Value::VCellCon(
                    d_name.clone(),
                    con_name.into(),
                    args.to_vec(),
                    ivars.to_vec(),
                )),
            );
        }
    };

    let n = con_sig.arity();
    if n == 0 {
        return Value::VCellCon(d_name.clone(), con_name.into(), vec![], ivars.to_vec());
    }

    let mut result_args: Vec<Value> = Vec::new();

    if eval_at_i1 {
        let (formal_env, dt_at_var) =
            eval_body_at_formal_interval(env, globals, global_offset, clos, session);
        let params_at_i = match &dt_at_var {
            Value::VData(_, params) => params.clone(),
            _ => vec![],
        };
        let num_params = dt.params.len();
        for k in 0..n {
            let ty_k = con_sig.arg_tys[k].clone();
            let mut ty_shifted = ty_k;
            for j in (0..=k).rev() {
                ty_shifted = shift(1, j as i32, &ty_shifted);
            }
            for j in 0..num_params {
                let pos = (n + num_params - j) as i32;
                if let Some(p_val) = params_at_i.get(j) {
                    let p_term = quote(
                        formal_env.len(),
                        globals,
                        global_offset,
                        p_val.clone(),
                        session,
                    );
                    ty_shifted = subst(pos, &p_term, &ty_shifted);
                }
            }
            for j in 0..k {
                let arg_term = quote(
                    env.len(),
                    globals,
                    global_offset,
                    result_args[j].clone(),
                    session,
                );
                ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
            }
            let ty_fam = Term::PLam(i_name.to_string(), Arc::new(ty_shifted));
            let transported = eval_nbe(
                env,
                globals,
                global_offset,
                &Term::TTransport(
                    Arc::new(ty_fam),
                    Arc::new(quote(
                        env.len(),
                        globals,
                        global_offset,
                        args[k].clone(),
                        session,
                    )),
                ),
                session,
            );
            result_args.push(transported);
        }
    } else {
        let substed_tys: Vec<Term> = con_sig.arg_tys.clone();
        for k in 0..n {
            let ty_k = substed_tys[k].clone();
            let mut ty_shifted = ty_k;
            for j in (0..=k).rev() {
                ty_shifted = shift(1, j as i32, &ty_shifted);
            }
            for j in 0..k {
                let arg_term = quote(
                    env.len(),
                    globals,
                    global_offset,
                    result_args[j].clone(),
                    session,
                );
                ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
            }
            let ty_fam = Term::PLam(i_name.to_string(), Arc::new(ty_shifted));
            let transported = eval_nbe(
                env,
                globals,
                global_offset,
                &Term::TTransport(
                    Arc::new(ty_fam),
                    Arc::new(quote(
                        env.len(),
                        globals,
                        global_offset,
                        args[k].clone(),
                        session,
                    )),
                ),
                session,
            );
            result_args.push(transported);
        }
    }

    Value::VCellCon(d_name.clone(), con_name.into(), result_args, ivars.to_vec())
}

/// Transport through Glue types.
fn transport_glue(
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    i_name: &str,
    clos: &IClosure,
    phi0: &DNF,
    x: &Value,
    session: &mut Session,
) -> Option<Value> {
    if *phi0 == dnf_bot() {
        let (formal_env, glue_at_var) =
            eval_body_at_formal_interval(env, globals, global_offset, clos, session);
        let a_val = match &glue_at_var {
            Value::VGlue(a, _, _) => a.as_ref().clone(),
            _ => return None,
        };
        let a_body = shift(
            1,
            1,
            &quote(formal_env.len(), globals, global_offset, a_val, session),
        );
        let a_fam = Term::PLam(i_name.to_string(), Arc::new(a_body));
        Some(eval_nbe(
            env,
            globals,
            global_offset,
            &Term::TTransport(
                Arc::new(a_fam),
                Arc::new(quote(env.len(), globals, global_offset, x.clone(), session)),
            ),
            session,
        ))
    } else if *phi0 == dnf_top() {
        let (formal_env, glue_at_var) =
            eval_body_at_formal_interval(env, globals, global_offset, clos, session);
        let te_val = match &glue_at_var {
            Value::VGlue(_, _, te) => te.as_ref().clone(),
            _ => return None,
        };
        let dom = equiv_dom_value(te_val);
        let dom_body = shift(
            1,
            1,
            &quote(formal_env.len(), globals, global_offset, dom, session),
        );
        let dom_fam = Term::PLam(i_name.to_string(), Arc::new(dom_body));
        Some(eval_nbe(
            env,
            globals,
            global_offset,
            &Term::TTransport(
                Arc::new(dom_fam),
                Arc::new(quote(env.len(), globals, global_offset, x.clone(), session)),
            ),
            session,
        ))
    } else {
        // Non-trivial face: decompose glue elements using the cubical Glue transport rule.
        // transp (λi. Glue A [φ] te) (glue [φ] t a)
        //   = glue [φ] t (hcomp A [φ] (λi. t) a)
        // where t stays the same (constant equiv domain) and the base is composed
        // via hcomp to maintain the boundary condition on face φ.
        match x {
            Value::VGlueElem(phi_elem, t, a) if *phi_elem == *phi0 => {
                let (_, glue_at_var) =
                    eval_body_at_formal_interval(env, globals, global_offset, clos, session);
                let a_ty = match &glue_at_var {
                    Value::VGlue(a, _, _) => a.as_ref().clone(),
                    _ => return None,
                };

                // tube = λi. t  (constant tube in hcomp)
                let t_body = shift(
                    1,
                    0,
                    &quote(
                        env.len(),
                        globals,
                        global_offset,
                        t.as_ref().clone(),
                        session,
                    ),
                );
                let tube = Term::PLam(i_name.to_string(), Arc::new(t_body));
                let tube_val = eval_nbe(env, globals, global_offset, &tube, session);

                // Wrap as a single-entry system: [(phi, λi. tube)]
                let sys: DNFSystem = vec![(phi0.clone(), tube_val)];
                let hcomp_val = do_hcomp(
                    globals,
                    global_offset,
                    a_ty,
                    sys,
                    a.as_ref().clone(),
                    session,
                );

                Some(Value::VGlueElem(
                    phi0.clone(),
                    t.clone(),
                    Arc::new(hcomp_val),
                ))
            }
            _ => None,
        }
    }
}

/// Term-level transport reduction.
pub fn transport_term_fallback(p_: Term, x_: Term, session: &mut Session) -> Term {
    match p_ {
        Term::TUa(ref e) => nbe_eval(&Term::TEquivFwd(e.clone(), Arc::new(x_)), session),

        Term::PLam(ref i_name, ref body) => {
            let b0 = nbe_eval(&beta(body, &Term::TInterval(I::I0)), session);
            let b1 = nbe_eval(&beta(body, &Term::TInterval(I::I1)), session);

            if b0 == b1 {
                return x_;
            }

            match (&b0, &b1) {
                (Term::TPi(arg_name, a0, _, _), Term::TPi(_, a1, _, _)) => {
                    let arg_name = arg_name.clone();
                    let i_name = i_name.clone();

                    let a0_eval = nbe_eval(a0, session);
                    let a1_eval = nbe_eval(a1, session);
                    if a0_eval == a1_eval {
                        let b_fam = Term::PLam(
                            i_name.clone(),
                            Arc::new(
                                match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0)), session) {
                                    Term::TPi(_, _, b_i, _) => {
                                        let max_idx = max_var(&b_i);
                                        let temp = max_idx + 1;
                                        let tmp_var = Term::TVar(temp);
                                        let step1 = subst(0, &tmp_var, &b_i);
                                        let step2 = subst(1, &Term::TVar(0), &step1);
                                        subst(temp, &Term::TVar(1), &step2)
                                    }
                                    _ => {
                                        let b0_body = match &b0 {
                                            Term::TPi(_, _, b, _) => (**b).clone(),
                                            _ => b0.clone(),
                                        };
                                        shift(1, 0, &b0_body)
                                    }
                                },
                            ),
                        );
                        let x_shifted = shift(1, 0, &x_);
                        Term::TAbs(
                            arg_name,
                            Arc::new(nbe_eval(
                                &Term::TTransport(
                                    Arc::new(b_fam),
                                    Arc::new(nbe_eval(
                                        &Term::TApp(Arc::new(x_shifted), Arc::new(Term::TVar(0))),
                                        session,
                                    )),
                                ),
                                session,
                            )),
                        )
                    } else {
                        let b_non_dep = match &b0 {
                            Term::TPi(_, _, b0_body, _) => {
                                subst(0, &Term::TUniv(LevelExpr::LConst(0)), b0_body) == **b0_body
                            }
                            _ => false,
                        };
                        if b_non_dep {
                            let b0_body = match &b0 {
                                Term::TPi(_, _, b, _) => (**b).clone(),
                                _ => b0.clone(),
                            };
                            let b_fam = Term::PLam(
                                i_name.clone(),
                                Arc::new(
                                    match nbe_eval(
                                        &beta(&shift(1, 0, body), &Term::TVar(0)),
                                        session,
                                    ) {
                                        Term::TPi(_, _, b_i, _) => b_i.as_ref().clone(),
                                        _ => shift(1, 0, &b0_body),
                                    },
                                ),
                            );
                            let x_shifted = shift(1, 0, &x_);
                            Term::TAbs(
                                arg_name,
                                Arc::new(nbe_eval(
                                    &Term::TTransport(
                                        Arc::new(b_fam),
                                        Arc::new(nbe_eval(
                                            &Term::TApp(
                                                Arc::new(x_shifted),
                                                Arc::new(Term::TVar(0)),
                                            ),
                                            session,
                                        )),
                                    ),
                                    session,
                                )),
                            )
                        } else {
                            let arg_name = arg_name.clone();
                            let i_name = i_name.clone();

                            let pi_at_var =
                                nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0)), session);
                            let a_i = match &pi_at_var {
                                Term::TPi(_, a, _, _) => (**a).clone(),
                                _ => shift(1, 0, a0),
                            };
                            let b0_body = match &b0 {
                                Term::TPi(_, _, b, _) => (**b).clone(),
                                _ => b0.clone(),
                            };
                            let b_i = match &pi_at_var {
                                Term::TPi(_, _, b, _) => (**b).clone(),
                                _ => shift(1, 0, &b0_body),
                            };

                            let a_fam = Term::PLam(i_name.clone(), Arc::new(a_i));
                            let a_rev_fam = Term::PLam(
                                "j".to_string(),
                                Arc::new(Term::PApp(
                                    Arc::new(shift(1, 0, &a_fam)),
                                    Arc::new(Term::TInterval(I::Neg(Arc::new(I::Var(0))))),
                                )),
                            );

                            let y0_term = Term::TTransport(
                                Arc::new(shift(1, 0, &a_rev_fam)),
                                Arc::new(Term::TVar(0)),
                            );

                            let b_fam = Term::PLam(
                                i_name.clone(),
                                Arc::new({
                                    let max_idx = max_var(&b_i);
                                    let temp = max_idx + 1;
                                    let tmp_var = Term::TVar(temp);
                                    let step1 = subst(0, &tmp_var, &b_i);
                                    let step2 = subst(1, &Term::TVar(0), &step1);
                                    let b_i_swapped = subst(temp, &Term::TVar(1), &step2);

                                    let y0_shifted = shift(1, 0, &y0_term);
                                    let fill_at_i = nbe_eval(
                                        &Term::TTransport(
                                            Arc::new(Term::PLam(
                                                "j".to_string(),
                                                Arc::new(nbe_eval(
                                                    &Term::PApp(
                                                        Arc::new(shift(2, 0, &a_fam)),
                                                        Arc::new(Term::TInterval(I::Meet(
                                                            Arc::new(I::Var(1)),
                                                            Arc::new(I::Var(0)),
                                                        ))),
                                                    ),
                                                    session,
                                                )),
                                            )),
                                            Arc::new(y0_shifted),
                                        ),
                                        session,
                                    );
                                    nbe_eval(&subst(1, &fill_at_i, &b_i_swapped), session)
                                }),
                            );

                            let x_shifted = shift(1, 0, &x_);
                            Term::TAbs(
                                arg_name,
                                Arc::new(nbe_eval(
                                    &Term::TTransport(
                                        Arc::new(b_fam),
                                        Arc::new(nbe_eval(
                                            &Term::TApp(Arc::new(x_shifted), Arc::new(y0_term)),
                                            session,
                                        )),
                                    ),
                                    session,
                                )),
                            )
                        }
                    }
                }

                (Term::TPath(ty_a0, _, _), Term::TPath(_, _, _)) => {
                    let i_name = i_name.clone();
                    let ty_a0 = (**ty_a0).clone();

                    let a_fam = Term::PLam(
                        i_name.clone(),
                        Arc::new(
                            match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0)), session) {
                                Term::TPath(a, _, _) => a.as_ref().clone(),
                                _ => shift(1, 0, &ty_a0),
                            },
                        ),
                    );

                    let a_fam_s = shift(1, 0, &a_fam);
                    let x_shifted = shift(1, 0, &x_);
                    Term::PLam(
                        "j".to_string(),
                        Arc::new(nbe_eval(
                            &Term::TTransport(
                                Arc::new(a_fam_s),
                                Arc::new(Term::PApp(Arc::new(x_shifted), Arc::new(Term::TVar(0)))),
                            ),
                            session,
                        )),
                    )
                }

                (Term::TSigma(_, _, _), Term::TSigma(_, _, _)) => match x_ {
                    Term::TPair(ref a, ref b) => {
                        let i_name = i_name.clone();

                        let b0_a = match &b0 {
                            Term::TSigma(_, a, _) => (**a).clone(),
                            _ => b0.clone(),
                        };
                        let b0_b = match &b0 {
                            Term::TSigma(_, _, bz) => (**bz).clone(),
                            _ => b0.clone(),
                        };

                        let a_fam = Term::PLam(
                            i_name.clone(),
                            Arc::new(
                                match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0)), session) {
                                    Term::TSigma(_, a_i, _) => a_i.as_ref().clone(),
                                    _ => shift(1, 0, &b0_a),
                                },
                            ),
                        );

                        let a_prime = nbe_eval(
                            &Term::TTransport(Arc::new(a_fam.clone()), a.clone()),
                            session,
                        );

                        let a_clone = (**a).clone();
                        let b_fam = Term::PLam(
                            i_name.clone(),
                            Arc::new(
                                match nbe_eval(&beta(&shift(1, 0, body), &Term::TVar(0)), session) {
                                    Term::TSigma(_, _, b_i) => {
                                        let fill_at_i = nbe_eval(
                                            &Term::TTransport(
                                                Arc::new(Term::PLam(
                                                    "j".to_string(),
                                                    Arc::new(nbe_eval(
                                                        &Term::PApp(
                                                            Arc::new(shift(2, 0, &a_fam)),
                                                            Arc::new(Term::TInterval(I::Meet(
                                                                Arc::new(I::Var(1)),
                                                                Arc::new(I::Var(0)),
                                                            ))),
                                                        ),
                                                        session,
                                                    )),
                                                )),
                                                Arc::new(shift(1, 0, &a_clone)),
                                            ),
                                            session,
                                        );
                                        nbe_eval(&beta(&b_i, &fill_at_i), session)
                                    }
                                    _ => shift(1, 0, &b0_b),
                                },
                            ),
                        );

                        let b_prime =
                            nbe_eval(&Term::TTransport(Arc::new(b_fam), b.clone()), session);
                        Term::TPair(Arc::new(a_prime), Arc::new(b_prime))
                    }
                    _ => Term::TTransport(
                        Arc::new(Term::PLam(i_name.clone(), body.clone())),
                        Arc::new(x_),
                    ),
                },

                (Term::TGlue(_, phi0, _), Term::TGlue(_, _, _)) => {
                    let i_name = i_name.clone();
                    if is_bot_dnf(&nbe_eval(phi0, session)) {
                        nbe_eval(
                            &Term::TTransport(
                                Arc::new(Term::PLam(
                                    i_name.clone(),
                                    Arc::new(
                                        match nbe_eval(
                                            &beta(&shift(1, 0, body), &Term::TVar(0)),
                                            session,
                                        ) {
                                            Term::TGlue(a, _, _) => a.as_ref().clone(),
                                            other => other,
                                        },
                                    ),
                                )),
                                Arc::new(x_),
                            ),
                            session,
                        )
                    } else if is_top_dnf(&nbe_eval(phi0, session)) {
                        nbe_eval(
                            &Term::TTransport(
                                Arc::new(Term::PLam(
                                    i_name.clone(),
                                    Arc::new(
                                        match nbe_eval(
                                            &beta(&shift(1, 0, body), &Term::TVar(0)),
                                            session,
                                        ) {
                                            Term::TGlue(_, _, te) => {
                                                equiv_dom(&nbe_eval(&te, session))
                                            }
                                            other => other,
                                        },
                                    ),
                                )),
                                Arc::new(x_),
                            ),
                            session,
                        )
                    } else {
                        // Non-trivial face: if x_ is a GlueElem with matching face, decompose.
                        match &x_ {
                            Term::TGlueElem(phi_elem, t, a)
                                if nbe_eval(phi0, session) == nbe_eval(phi_elem, session) =>
                            {
                                let a_ty = match nbe_eval(
                                    &beta(&shift(1, 0, body), &Term::TVar(0)),
                                    session,
                                ) {
                                    Term::TGlue(a, _, _) => a.as_ref().clone(),
                                    other => other,
                                };
                                let tube = Term::PLam(i_name.clone(), Arc::new(shift(1, 0, &*t)));
                                let hcomp = Term::THComp(
                                    Arc::new(a_ty),
                                    vec![((**phi0).clone(), tube)],
                                    (*a).clone(),
                                );
                                Term::TGlueElem(
                                    Arc::new((**phi0).clone()),
                                    t.clone(),
                                    Arc::new(hcomp),
                                )
                            }
                            _ => Term::TTransport(
                                Arc::new(Term::PLam(i_name, body.clone())),
                                Arc::new(x_),
                            ),
                        }
                    }
                }

                // Lift transport: transport (λi. Lift (A i) lvl) (lift v) = lift (transport (λi. A i) v)
                (Term::TLift(_, _), Term::TLift(_, _)) => {
                    let i_name = i_name.clone();
                    match x_ {
                        Term::TLift(v, lvl) => {
                            let a_fam = Term::PLam(
                                i_name.clone(),
                                Arc::new(
                                    match nbe_eval(
                                        &beta(&shift(1, 0, body), &Term::TVar(0)),
                                        session,
                                    ) {
                                        Term::TLift(a, _) => a.as_ref().clone(),
                                        other => other,
                                    },
                                ),
                            );
                            let inner_transport = Term::TTransport(Arc::new(a_fam), v);
                            Term::TLift(Arc::new(inner_transport), lvl)
                        }
                        _ => Term::TTransport(
                            Arc::new(Term::PLam(i_name, body.clone())),
                            Arc::new(x_),
                        ),
                    }
                }

                // Lower transport: transport (λi. Lower (A i)) (lower v) = lower (transport (λi. A i) v)
                (Term::TLower(_), Term::TLower(_)) => {
                    let i_name = i_name.clone();
                    match x_ {
                        Term::TLower(v) => {
                            let a_fam = Term::PLam(
                                i_name.clone(),
                                Arc::new(
                                    match nbe_eval(
                                        &beta(&shift(1, 0, body), &Term::TVar(0)),
                                        session,
                                    ) {
                                        Term::TLower(a) => a.as_ref().clone(),
                                        other => other,
                                    },
                                ),
                            );
                            let inner_transport = Term::TTransport(Arc::new(a_fam), v);
                            Term::TLower(Arc::new(inner_transport))
                        }
                        _ => Term::TTransport(
                            Arc::new(Term::PLam(i_name, body.clone())),
                            Arc::new(x_),
                        ),
                    }
                }

                _ => Term::TTransport(
                    Arc::new(Term::PLam(i_name.clone(), body.clone())),
                    Arc::new(x_),
                ),
            }
        }

        p_ => Term::TTransport(Arc::new(p_), Arc::new(x_)),
    }
}
