//! Cubical composition operations: hcomp, comp, fill and hfill.

use super::elim::{do_apply, do_fst, do_papp, do_snd};
use super::eval::eval_nbe;
use super::quote::quote;
use super::trace::record_step;
use super::value::{Closure, DNFSystem, Globals, IClosure, Neutral, Scope, Value, value_str};
use crate::cubical::equality::definitionally_equal;
use crate::cubical::interval::{DNF, I, dnf_bot, dnf_top};
use crate::cubical::session::Session;
use crate::cubical::syntax::{Term, shift, subst};
use std::sync::Arc;

/// Try to match a constructor value and extract its ordinary + interval args.
/// Returns (con_name, ordinary_args, interval_args) or None.
fn match_ctor_args<'a>(
    v: &'a Value,
    expected_name: &str,
) -> Option<(&'a str, Vec<&'a Value>, Vec<&'a Value>)> {
    match v {
        Value::VCon(_, name, args) if name == expected_name => {
            Some((name.as_str(), args.iter().collect(), vec![]))
        }
        Value::VPCon(_, name, args, r) if name == expected_name => {
            Some((name.as_str(), args.iter().collect(), vec![r.as_ref()]))
        }
        Value::VSqCon(_, name, args, r, s) if name == expected_name => Some((
            name.as_str(),
            args.iter().collect(),
            vec![r.as_ref(), s.as_ref()],
        )),
        Value::VCellCon(_, name, args, ivars) if name == expected_name => {
            Some((name.as_str(), args.iter().collect(), ivars.iter().collect()))
        }
        _ => None,
    }
}

/// Check if all tubes in the system are constant (tube @ I0 ≡ tube @ I1)
/// AND coherent with base (tube @ I0 ≡ base). When this holds, the Kan
/// operations degenerate: hcomp/comp → base, fill/hfill → constant path.
fn all_tubes_constant_and_coherent(
    globals: &Globals,
    global_offset: usize,
    sys: &DNFSystem,
    base: &Value,
    session: &mut Session,
) -> bool {
    // Guard against re-entrancy. The tube check quotes the base/tubes and
    // compares them with `definitionally_equal`, which re-normalizes via
    // `nbe_eval_ctx` → `quote`. When the quoted body is itself a PLam/VLam
    // whose evaluation contains an hcomp, that re-normalization re-runs this
    // check on the same structure → infinite eval↔quote recursion (see the
    // ring_demo overflow). This check is only an optimization (the
    // constant-tube shortcut); bailing out is safe — the hcomp simply stays
    // stuck instead of reducing to base.
    let depth = session.all_tubes_depth_enter();
    if depth > 0 {
        session.all_tubes_depth_restore(depth);
        return false;
    }
    let result = all_tubes_constant_and_coherent_inner(globals, global_offset, sys, base, session);
    session.all_tubes_depth_restore(depth);
    result
}

fn all_tubes_constant_and_coherent_inner(
    globals: &Globals,
    global_offset: usize,
    sys: &DNFSystem,
    base: &Value,
    session: &mut Session,
) -> bool {
    let base_term = quote(0, globals, global_offset, base.clone(), session);
    for (_phi, tube) in sys {
        let t0 = do_papp(
            globals,
            global_offset,
            tube.clone(),
            Value::VInterval(I::I0),
            session,
        );
        let t1 = do_papp(
            globals,
            global_offset,
            tube.clone(),
            Value::VInterval(I::I1),
            session,
        );
        let t0_term = quote(0, globals, global_offset, t0, session);
        let t1_term = quote(0, globals, global_offset, t1, session);
        // Tube must be constant: t @ I0 ≡ t @ I1
        if !definitionally_equal(&t0_term, &t1_term, session) {
            return false;
        }
        // Tube must be coherent with base: t @ I0 ≡ base
        if !definitionally_equal(&t0_term, &base_term, session) {
            return false;
        }
    }
    true
}

pub fn do_hcomp(
    globals: &Globals,
    global_offset: usize,
    a_ty: Value,
    sys: DNFSystem,
    base: Value,
    session: &mut Session,
) -> Value {
    // Filter out ⊥ faces
    let sys: DNFSystem = sys
        .into_iter()
        .filter(|(phi, _)| *phi != dnf_bot())
        .collect();

    // Empty system → base
    if sys.is_empty() {
        record_step(
            "hcomp-empty".into(),
            "hcomp A [] base".into(),
            value_str(globals, global_offset, &base, session),
        );
        return base;
    }

    // Any face = ⊤ → corresponding tube applied at i1
    for (phi, tube) in &sys {
        if *phi == dnf_top() {
            let result = do_papp(
                globals,
                global_offset,
                tube.clone(),
                Value::VInterval(I::I1),
                session,
            );
            record_step(
                "hcomp-top-face".into(),
                "hcomp A [⊤ ↦ t, ...] base".into(),
                value_str(globals, global_offset, &result, session),
            );
            return result;
        }
    }

    // Constant-tube shortcut: when all tubes don't depend on the interval
    // variable (tube @ i0 ≡ tube @ i1) and agree with base, the system
    // imposes no varying constraint and hcomp reduces to base.
    if all_tubes_constant_and_coherent(globals, global_offset, &sys, &base, session) {
        record_step(
            "hcomp-const-tube".into(),
            "hcomp A [const tubes] base".into(),
            value_str(globals, global_offset, &base, session),
        );
        return base;
    }

    {
        // ── Deeper hcomp reductions ──
        //
        // 1. Pi decomposition: when the base is a function (VLam) and the
        //    type is a Pi, push hcomp pointwise:
        //    hcomp (Π x:A. B) φ (λi. f i) (λx. b x)
        //    ≡  λx. hcomp (B x) φ (λi. f i x) (b x)
        //
        // 2. Sigma decomposition: when the base is a pair, decompose:
        //    hcomp (Σ x:A. B) φ (p, q) (a, b)
        //    ≡  (hcomp A φ (λi. fst (p i)) a, hcomp (B (fst result)) φ (λi. snd (p i)) b)
        //
        // 3. Constant-tube shortcut: when the tube does not depend on the
        //    interval variable (tube @ 0 ≡ tube @ 1), the hcomp reduces to
        //    tube @ 1 regardless of phi.
        match (&a_ty, &base) {
            // ── Pi decomposition ──
            (Value::VPi(arg_name, _, cod_clos, _), Value::VLam(_, base_clos)) => {
                let arg_var = Value::VNeutral(Neutral::nvar(0));
                let inner_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let tube_at_arg = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_apply(
                                    globals,
                                    global_offset,
                                    tube_at_i,
                                    arg_var.clone(),
                                    session,
                                )
                            }
                            _ => do_apply(
                                globals,
                                global_offset,
                                tube.clone(),
                                arg_var.clone(),
                                session,
                            ),
                        };
                        (phi.clone(), tube_at_arg)
                    })
                    .collect();
                let base_at_arg = base_clos.apply(arg_var.clone(), session);
                let cod_at_arg = cod_clos.apply(arg_var, session);
                let inner = do_hcomp(
                    globals,
                    global_offset,
                    cod_at_arg,
                    inner_sys,
                    base_at_arg,
                    session,
                );
                let result = Value::VLam(
                    arg_name.clone(),
                    Closure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: {
                            let inner_term = quote(1, globals, global_offset, inner, session);
                            Term::TAbs(arg_name.clone(), Arc::new(inner_term))
                        },
                    },
                );
                record_step(
                    "hcomp-pi".into(),
                    "hcomp (Π _ _) sys f g".into(),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }

            // ── Sigma decomposition ──
            (Value::VSigma(_, fst_ty, snd_clos), Value::VPair(fst_base, snd_base)) => {
                let fst_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let fst_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_fst(globals, global_offset, tube_at_i, session)
                            }
                            _ => do_fst(globals, global_offset, tube.clone(), session),
                        };
                        let fst_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, fst_tube, session),
                            },
                        );
                        (phi.clone(), fst_tube_plam)
                    })
                    .collect();
                let fst_result = do_hcomp(
                    globals,
                    global_offset,
                    fst_ty.as_ref().clone(),
                    fst_sys,
                    (**fst_base).clone(),
                    session,
                );

                let snd_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let snd_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_snd(globals, global_offset, tube_at_i, session)
                            }
                            _ => do_snd(globals, global_offset, tube.clone(), session),
                        };
                        let snd_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, snd_tube, session),
                            },
                        );
                        (phi.clone(), snd_tube_plam)
                    })
                    .collect();
                let snd_result = do_hcomp(
                    globals,
                    global_offset,
                    snd_clos.apply((**fst_base).clone(), session),
                    snd_sys,
                    (**snd_base).clone(),
                    session,
                );

                let result = Value::VPair(Arc::new(fst_result), Arc::new(snd_result));
                record_step(
                    "hcomp-sigma".into(),
                    "hcomp (Σ _ _) sys p q".into(),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }

            // ── Data type decomposition: push hcomp through constructor arguments ──
            (Value::VData(d_name, _), _) => {
                let (base_con, base_args, base_ivars) = match &base {
                    Value::VCon(_, name, args) => (name.clone(), args.clone(), vec![]),
                    Value::VPCon(_, name, args, r) => {
                        (name.clone(), args.clone(), vec![(**r).clone()])
                    }
                    Value::VSqCon(_, name, args, r, s) => (
                        name.clone(),
                        args.clone(),
                        vec![(**r).clone(), (**s).clone()],
                    ),
                    Value::VCellCon(_, name, args, ivars) => {
                        (name.clone(), args.clone(), ivars.clone())
                    }
                    _ => return Value::VHComp(Arc::new(a_ty), sys, Arc::new(base)),
                };

                let dts = session.current_dts();
                let dt = match dts.iter().find(|dt| dt.name == *d_name) {
                    Some(dt) => dt.clone(),
                    None => return Value::VHComp(Arc::new(a_ty), sys, Arc::new(base)),
                };

                let arg_tys = match dt
                    .find_con(&base_con)
                    .map(|s| s.arg_tys.clone())
                    .or_else(|| dt.find_pcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_sqcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_cellcon(&base_con).map(|s| s.arg_tys.clone()))
                {
                    Some(tys) => tys,
                    None => return Value::VHComp(Arc::new(a_ty), sys, Arc::new(base)),
                };

                let n = arg_tys.len();
                if n == 0 {
                    return base;
                }

                let mut per_arg_tubes: Vec<Vec<(DNF, Value)>> = vec![vec![]; n];
                for (phi, tube) in &sys {
                    let tube_val = match tube {
                        Value::VPLam(_, iclos) => {
                            let formal_i = Value::VIntervalVar(0);
                            iclos.apply_interval_value(formal_i, session)
                        }
                        _ => tube.clone(),
                    };

                    if let Some((_, tube_args, _)) = match_ctor_args(&tube_val, &base_con) {
                        if tube_args.len() == n {
                            for (k, tube_arg) in tube_args.iter().enumerate() {
                                let tube_arg_plam = Value::VPLam(
                                    "_".to_string(),
                                    IClosure {
                                        env: Scope::empty(),
                                        globals: globals.clone(),
                                        global_offset,
                                        body: quote(
                                            1,
                                            globals,
                                            global_offset,
                                            (*tube_arg).clone(),
                                            session,
                                        ),
                                    },
                                );
                                per_arg_tubes[k].push((phi.clone(), tube_arg_plam));
                            }
                        } else {
                            return Value::VHComp(Arc::new(a_ty), sys, Arc::new(base));
                        }
                    } else {
                        return Value::VHComp(Arc::new(a_ty), sys, Arc::new(base));
                    }
                }

                let mut result_args: Vec<Value> = Vec::new();
                for k in 0..n {
                    let mut ty_shifted = arg_tys[k].clone();
                    for j in (0..=k).rev() {
                        ty_shifted = shift(1, j as i32, &ty_shifted);
                    }
                    for j in 0..k {
                        let arg_term =
                            quote(0, globals, global_offset, result_args[j].clone(), session);
                        ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
                    }
                    let arg_ty = eval_nbe(
                        &Scope::empty(),
                        globals,
                        global_offset,
                        &ty_shifted,
                        session,
                    );
                    let arg_result = do_hcomp(
                        globals,
                        global_offset,
                        arg_ty,
                        per_arg_tubes[k].clone(),
                        base_args[k].clone(),
                        session,
                    );
                    result_args.push(arg_result);
                }

                match &base {
                    Value::VCon(_, _, _) => {
                        Value::VCon(d_name.clone(), base_con.clone(), result_args)
                    }
                    Value::VPCon(_, _, _, _) => Value::VPCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_args,
                        Arc::new(base_ivars[0].clone()),
                    ),
                    Value::VSqCon(_, _, _, _, _) => Value::VSqCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_args,
                        Arc::new(base_ivars[0].clone()),
                        Arc::new(base_ivars[1].clone()),
                    ),
                    Value::VCellCon(_, _, _, _) => {
                        Value::VCellCon(d_name.clone(), base_con.clone(), result_args, base_ivars)
                    }
                    _ => unreachable!(),
                }
            }

            // ── Default: stuck hcomp ──
            _ => Value::VHComp(Arc::new(a_ty), sys, Arc::new(base)),
        }
    }
}

pub fn do_comp(
    globals: &Globals,
    global_offset: usize,
    a_fam: Value,
    sys: DNFSystem,
    base: Value,
    session: &mut Session,
) -> Value {
    // Filter out ⊥ faces
    let sys: DNFSystem = sys
        .into_iter()
        .filter(|(phi, _)| *phi != dnf_bot())
        .collect();

    // Empty system → base
    if sys.is_empty() {
        record_step(
            "comp-empty".into(),
            "comp _ [] base".into(),
            value_str(globals, global_offset, &base, session),
        );
        return base;
    }

    // Any face = ⊤ → corresponding tube applied at i1
    for (phi, tube) in &sys {
        if *phi == dnf_top() {
            let result = do_papp(
                globals,
                global_offset,
                tube.clone(),
                Value::VInterval(I::I1),
                session,
            );
            record_step(
                "comp-top-face".into(),
                "comp _ [⊤ ↦ t, ...] base".into(),
                value_str(globals, global_offset, &result, session),
            );
            return result;
        }
    }

    // Constant-tube shortcut
    if all_tubes_constant_and_coherent(globals, global_offset, &sys, &base, session) {
        record_step(
            "comp-const-tube".into(),
            "comp A [const tubes] base".into(),
            value_str(globals, global_offset, &base, session),
        );
        return base;
    }

    {
        match (&a_fam, &base) {
            // ── Pi decomposition ──
            (Value::VPi(arg_name, _, cod_clos, _), Value::VLam(_, base_clos)) => {
                let arg_var = Value::VNeutral(Neutral::nvar(0));
                let inner_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let tube_at_arg = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_apply(
                                    globals,
                                    global_offset,
                                    tube_at_i,
                                    arg_var.clone(),
                                    session,
                                )
                            }
                            _ => do_apply(
                                globals,
                                global_offset,
                                tube.clone(),
                                arg_var.clone(),
                                session,
                            ),
                        };
                        (phi.clone(), tube_at_arg)
                    })
                    .collect();
                let base_at_arg = base_clos.apply(arg_var.clone(), session);
                let cod_at_arg = cod_clos.apply(arg_var, session);
                let inner = do_comp(
                    globals,
                    global_offset,
                    cod_at_arg,
                    inner_sys,
                    base_at_arg,
                    session,
                );
                let result = Value::VLam(
                    arg_name.clone(),
                    Closure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: {
                            let inner_term = quote(1, globals, global_offset, inner, session);
                            Term::TAbs(arg_name.clone(), Arc::new(inner_term))
                        },
                    },
                );
                record_step(
                    "comp-pi".into(),
                    "comp (Π _ _) sys f g".into(),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }

            // ── Sigma decomposition ──
            (Value::VSigma(_, fst_ty, snd_clos), Value::VPair(fst_base, snd_base)) => {
                let fst_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let fst_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_fst(globals, global_offset, tube_at_i, session)
                            }
                            _ => do_fst(globals, global_offset, tube.clone(), session),
                        };
                        let fst_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, fst_tube, session),
                            },
                        );
                        (phi.clone(), fst_tube_plam)
                    })
                    .collect();
                let fst_result = do_comp(
                    globals,
                    global_offset,
                    fst_ty.as_ref().clone(),
                    fst_sys,
                    (**fst_base).clone(),
                    session,
                );

                let snd_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let snd_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_snd(globals, global_offset, tube_at_i, session)
                            }
                            _ => do_snd(globals, global_offset, tube.clone(), session),
                        };
                        let snd_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, snd_tube, session),
                            },
                        );
                        (phi.clone(), snd_tube_plam)
                    })
                    .collect();
                let snd_result = do_comp(
                    globals,
                    global_offset,
                    snd_clos.apply((**fst_base).clone(), session),
                    snd_sys,
                    (**snd_base).clone(),
                    session,
                );

                let result = Value::VPair(Arc::new(fst_result), Arc::new(snd_result));
                record_step(
                    "comp-sigma".into(),
                    "comp (Σ _ _) sys p q".into(),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }

            // ── Data type decomposition: push comp through constructor arguments ──
            (Value::VData(d_name, _), _) => {
                let (base_con, base_args, base_ivars) = match &base {
                    Value::VCon(_, name, args) => (name.clone(), args.clone(), vec![]),
                    Value::VPCon(_, name, args, r) => {
                        (name.clone(), args.clone(), vec![(**r).clone()])
                    }
                    Value::VSqCon(_, name, args, r, s) => (
                        name.clone(),
                        args.clone(),
                        vec![(**r).clone(), (**s).clone()],
                    ),
                    Value::VCellCon(_, name, args, ivars) => {
                        (name.clone(), args.clone(), ivars.clone())
                    }
                    _ => {
                        let result = Value::VComp(Arc::new(a_fam), sys, Arc::new(base));
                        record_step(
                            "comp-stuck".into(),
                            "comp _ _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                };

                let dts = session.current_dts();
                let dt = match dts.iter().find(|dt| dt.name == *d_name) {
                    Some(dt) => dt.clone(),
                    None => {
                        let result = Value::VComp(Arc::new(a_fam), sys, Arc::new(base));
                        record_step(
                            "comp-stuck".into(),
                            "comp _ _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                };

                let arg_tys = dt
                    .find_con(&base_con)
                    .map(|s| s.arg_tys.clone())
                    .or_else(|| dt.find_pcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_sqcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_cellcon(&base_con).map(|s| s.arg_tys.clone()));
                let arg_tys = match arg_tys {
                    Some(tys) => tys,
                    None => {
                        let result = Value::VComp(Arc::new(a_fam), sys, Arc::new(base));
                        record_step(
                            "comp-stuck".into(),
                            "comp _ _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                };

                let n = arg_tys.len();
                if n == 0 {
                    return base;
                }

                let mut per_arg_tubes: Vec<Vec<(DNF, Value)>> = vec![vec![]; n];
                for (phi, tube) in &sys {
                    let tube_val = match tube {
                        Value::VPLam(_, iclos) => {
                            let formal_i = Value::VIntervalVar(0);
                            iclos.apply_interval_value(formal_i, session)
                        }
                        _ => tube.clone(),
                    };

                    if let Some((_, tube_args, _)) = match_ctor_args(&tube_val, &base_con) {
                        if tube_args.len() == n {
                            for (k, tube_arg) in tube_args.iter().enumerate() {
                                let tube_arg_plam = Value::VPLam(
                                    "_".to_string(),
                                    IClosure {
                                        env: Scope::empty(),
                                        globals: globals.clone(),
                                        global_offset,
                                        body: quote(
                                            1,
                                            globals,
                                            global_offset,
                                            (*tube_arg).clone(),
                                            session,
                                        ),
                                    },
                                );
                                per_arg_tubes[k].push((phi.clone(), tube_arg_plam));
                            }
                        } else {
                            let result = Value::VComp(Arc::new(a_fam), sys, Arc::new(base));
                            record_step(
                                "comp-stuck".into(),
                                "comp _ _ _ _".into(),
                                value_str(globals, global_offset, &result, session),
                            );
                            return result;
                        }
                    } else {
                        let result = Value::VComp(Arc::new(a_fam), sys, Arc::new(base));
                        record_step(
                            "comp-stuck".into(),
                            "comp _ _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                }

                let mut result_args: Vec<Value> = Vec::new();
                for k in 0..n {
                    let mut ty_shifted = arg_tys[k].clone();
                    for j in (0..=k).rev() {
                        ty_shifted = shift(1, j as i32, &ty_shifted);
                    }
                    for j in 0..k {
                        let arg_term =
                            quote(0, globals, global_offset, result_args[j].clone(), session);
                        ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
                    }
                    let arg_ty = eval_nbe(
                        &Scope::empty(),
                        globals,
                        global_offset,
                        &ty_shifted,
                        session,
                    );
                    let arg_result = do_comp(
                        globals,
                        global_offset,
                        arg_ty,
                        per_arg_tubes[k].clone(),
                        base_args[k].clone(),
                        session,
                    );
                    result_args.push(arg_result);
                }

                let result = match &base {
                    Value::VCon(_, _, _) => {
                        Value::VCon(d_name.clone(), base_con.clone(), result_args)
                    }
                    Value::VPCon(_, _, _, _) => Value::VPCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_args,
                        Arc::new(base_ivars[0].clone()),
                    ),
                    Value::VSqCon(_, _, _, _, _) => Value::VSqCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_args,
                        Arc::new(base_ivars[0].clone()),
                        Arc::new(base_ivars[1].clone()),
                    ),
                    Value::VCellCon(_, _, _, _) => {
                        Value::VCellCon(d_name.clone(), base_con.clone(), result_args, base_ivars)
                    }
                    _ => unreachable!(),
                };
                record_step(
                    "comp-data".into(),
                    format!("comp (λi. {}) ({} ...)", d_name, base_con),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }

            _ => {
                let result = Value::VComp(Arc::new(a_fam), sys, Arc::new(base));
                record_step(
                    "comp-stuck".into(),
                    "comp _ _ _ _".into(),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }
        }
    }
}

pub fn do_fill(
    globals: &Globals,
    global_offset: usize,
    a_fam: Value,
    sys: DNFSystem,
    base: Value,
    session: &mut Session,
) -> Value {
    // Filter out ⊥ faces
    let sys: DNFSystem = sys
        .into_iter()
        .filter(|(phi, _)| *phi != dnf_bot())
        .collect();

    // Empty system → constant path
    if sys.is_empty() {
        let result = Value::VPLam(
            "j".to_string(),
            IClosure {
                env: Scope::empty(),
                globals: globals.clone(),
                global_offset,
                body: quote(1, globals, global_offset, base.clone(), session),
            },
        );
        record_step(
            "fill-empty".into(),
            "fill _ [] base".into(),
            value_str(globals, global_offset, &result, session),
        );
        return result;
    }

    // Any face = ⊤ → corresponding tube
    for (phi, tube) in &sys {
        if *phi == dnf_top() {
            let result = tube.clone();
            record_step(
                "fill-top-face".into(),
                "fill _ [⊤ ↦ t, ...] base".into(),
                value_str(globals, global_offset, &result, session),
            );
            return result;
        }
    }

    // Constant-tube shortcut: fill produces a constant path when tubes don't vary
    if all_tubes_constant_and_coherent(globals, global_offset, &sys, &base, session) {
        let result = Value::VPLam(
            "j".to_string(),
            IClosure {
                env: Scope::empty(),
                globals: globals.clone(),
                global_offset,
                body: quote(1, globals, global_offset, base.clone(), session),
            },
        );
        record_step(
            "fill-const-tube".into(),
            "fill A [const tubes] base".into(),
            value_str(globals, global_offset, &result, session),
        );
        return result;
    }

    // ── Decompose fill for Pi/Sigma/Data types ──
    // fill returns a PATH, so decomposition wraps inner fills with PApp at interval variable j.
    // The IClosure body binds j at level 0; inside TAbs, j is at TV(1).
    {
        match (&a_fam, &base) {
            // ── Pi decomposition ──
            // fill (Π x:A. B) sys (λx. f x) = λj. λx. fill B [sys x] (f x) @ j
            (Value::VPi(arg_name, _, cod_clos, _), Value::VLam(_, base_clos)) => {
                let arg_var = Value::VNeutral(Neutral::nvar(0));
                let inner_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let tube_at_arg = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_apply(
                                    globals,
                                    global_offset,
                                    tube_at_i,
                                    arg_var.clone(),
                                    session,
                                )
                            }
                            _ => do_apply(
                                globals,
                                global_offset,
                                tube.clone(),
                                arg_var.clone(),
                                session,
                            ),
                        };
                        (phi.clone(), tube_at_arg)
                    })
                    .collect();
                let base_at_arg = base_clos.apply(arg_var.clone(), session);
                let cod_at_arg = cod_clos.apply(arg_var, session);
                let inner = do_fill(
                    globals,
                    global_offset,
                    cod_at_arg,
                    inner_sys,
                    base_at_arg,
                    session,
                );
                let inner_term = quote(1, globals, global_offset, inner, session);
                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: Term::TAbs(
                            arg_name.clone(),
                            Arc::new(Term::PApp(Arc::new(inner_term), Arc::new(Term::TVar(1)))),
                        ),
                    },
                );
                record_step(
                    "fill-pi".into(),
                    "fill (Π _ _) sys f".into(),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }

            // ── Sigma decomposition ──
            // fill (Σ x:A. B) sys (a, b) = λj. (fill A [fst_sys] a @ j, fill B [snd_sys] b @ j)
            (Value::VSigma(_, fst_ty, snd_clos), Value::VPair(fst_base, snd_base)) => {
                let fst_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let fst_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_fst(globals, global_offset, tube_at_i, session)
                            }
                            _ => do_fst(globals, global_offset, tube.clone(), session),
                        };
                        let fst_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, fst_tube, session),
                            },
                        );
                        (phi.clone(), fst_tube_plam)
                    })
                    .collect();
                let fst_fill = do_fill(
                    globals,
                    global_offset,
                    fst_ty.as_ref().clone(),
                    fst_sys,
                    (**fst_base).clone(),
                    session,
                );

                let snd_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let snd_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_snd(globals, global_offset, tube_at_i, session)
                            }
                            _ => do_snd(globals, global_offset, tube.clone(), session),
                        };
                        let snd_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, snd_tube, session),
                            },
                        );
                        (phi.clone(), snd_tube_plam)
                    })
                    .collect();
                let snd_fill = do_fill(
                    globals,
                    global_offset,
                    snd_clos.apply((**fst_base).clone(), session),
                    snd_sys,
                    (**snd_base).clone(),
                    session,
                );

                let fst_fill_term = quote(1, globals, global_offset, fst_fill, session);
                let snd_fill_term = quote(1, globals, global_offset, snd_fill, session);
                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: Term::TPair(
                            Arc::new(Term::PApp(Arc::new(fst_fill_term), Arc::new(Term::TVar(1)))),
                            Arc::new(Term::PApp(Arc::new(snd_fill_term), Arc::new(Term::TVar(1)))),
                        ),
                    },
                );
                record_step(
                    "fill-sigma".into(),
                    "fill (Σ _ _) sys p".into(),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }

            // ── Data type decomposition: push fill through constructor arguments ──
            (Value::VData(d_name, _), _) => {
                let (base_con, base_args, base_ivars) = match &base {
                    Value::VCon(_, name, args) => (name.clone(), args.clone(), vec![]),
                    Value::VPCon(_, name, args, r) => {
                        (name.clone(), args.clone(), vec![(**r).clone()])
                    }
                    Value::VSqCon(_, name, args, r, s) => (
                        name.clone(),
                        args.clone(),
                        vec![(**r).clone(), (**s).clone()],
                    ),
                    Value::VCellCon(_, name, args, ivars) => {
                        (name.clone(), args.clone(), ivars.clone())
                    }
                    _ => {
                        let result = Value::VFill(Arc::new(a_fam), sys, Arc::new(base));
                        record_step(
                            "fill-stuck".into(),
                            "fill _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                };

                let dts = session.current_dts();
                let dt = match dts.iter().find(|dt| dt.name == *d_name) {
                    Some(dt) => dt.clone(),
                    None => {
                        let result = Value::VFill(Arc::new(a_fam), sys, Arc::new(base));
                        record_step(
                            "fill-stuck".into(),
                            "fill _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                };

                let arg_tys = match dt
                    .find_con(&base_con)
                    .map(|s| s.arg_tys.clone())
                    .or_else(|| dt.find_pcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_sqcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_cellcon(&base_con).map(|s| s.arg_tys.clone()))
                {
                    Some(tys) => tys,
                    None => {
                        let result = Value::VFill(Arc::new(a_fam), sys, Arc::new(base));
                        record_step(
                            "fill-stuck".into(),
                            "fill _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                };

                let n = arg_tys.len();
                if n == 0 {
                    // No arguments: fill is a constant path
                    let result = Value::VPLam(
                        "j".to_string(),
                        IClosure {
                            env: Scope::empty(),
                            globals: globals.clone(),
                            global_offset,
                            body: quote(1, globals, global_offset, base.clone(), session),
                        },
                    );
                    record_step(
                        "fill-data-empty".into(),
                        "fill D [] c".into(),
                        value_str(globals, global_offset, &result, session),
                    );
                    return result;
                }

                let mut per_arg_tubes: Vec<Vec<(DNF, Value)>> = vec![vec![]; n];
                for (phi, tube) in &sys {
                    let tube_val = match tube {
                        Value::VPLam(_, iclos) => {
                            let formal_i = Value::VIntervalVar(0);
                            iclos.apply_interval_value(formal_i, session)
                        }
                        _ => tube.clone(),
                    };

                    if let Some((_, tube_args, _)) = match_ctor_args(&tube_val, &base_con) {
                        if tube_args.len() == n {
                            for (k, tube_arg) in tube_args.iter().enumerate() {
                                let tube_arg_plam = Value::VPLam(
                                    "_".to_string(),
                                    IClosure {
                                        env: Scope::empty(),
                                        globals: globals.clone(),
                                        global_offset,
                                        body: quote(
                                            1,
                                            globals,
                                            global_offset,
                                            (*tube_arg).clone(),
                                            session,
                                        ),
                                    },
                                );
                                per_arg_tubes[k].push((phi.clone(), tube_arg_plam));
                            }
                        } else {
                            let result = Value::VFill(Arc::new(a_fam), sys, Arc::new(base));
                            record_step(
                                "fill-stuck".into(),
                                "fill _ _ _".into(),
                                value_str(globals, global_offset, &result, session),
                            );
                            return result;
                        }
                    } else {
                        let result = Value::VFill(Arc::new(a_fam), sys, Arc::new(base));
                        record_step(
                            "fill-stuck".into(),
                            "fill _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                }

                let mut result_arg_terms: Vec<Term> = Vec::new();
                for k in 0..n {
                    let mut ty_shifted = arg_tys[k].clone();
                    for j in (0..=k).rev() {
                        ty_shifted = shift(1, j as i32, &ty_shifted);
                    }
                    for j in 0..k {
                        let arg_term =
                            quote(0, globals, global_offset, base_args[j].clone(), session);
                        ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
                    }
                    let arg_ty = eval_nbe(
                        &Scope::empty(),
                        globals,
                        global_offset,
                        &ty_shifted,
                        session,
                    );
                    let arg_fill = do_fill(
                        globals,
                        global_offset,
                        arg_ty,
                        per_arg_tubes[k].clone(),
                        base_args[k].clone(),
                        session,
                    );
                    let arg_fill_term = quote(1, globals, global_offset, arg_fill, session);
                    result_arg_terms
                        .push(Term::PApp(Arc::new(arg_fill_term), Arc::new(Term::TVar(1))));
                }

                let con_term = match &base {
                    Value::VCon(_, _, _) => {
                        Term::TCon(d_name.clone(), base_con.clone(), result_arg_terms)
                    }
                    Value::VPCon(_, _, _, _) => Term::TPCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_arg_terms,
                        Arc::new(quote(
                            1,
                            globals,
                            global_offset,
                            base_ivars[0].clone(),
                            session,
                        )),
                    ),
                    Value::VSqCon(_, _, _, _, _) => Term::TSqCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_arg_terms,
                        Arc::new(quote(
                            1,
                            globals,
                            global_offset,
                            base_ivars[0].clone(),
                            session,
                        )),
                        Arc::new(quote(
                            1,
                            globals,
                            global_offset,
                            base_ivars[1].clone(),
                            session,
                        )),
                    ),
                    Value::VCellCon(_, _, _, _) => {
                        let ivar_terms: Vec<Term> = base_ivars
                            .iter()
                            .map(|v| quote(1, globals, global_offset, v.clone(), session))
                            .collect();
                        Term::TCellCon(
                            d_name.clone(),
                            base_con.clone(),
                            result_arg_terms,
                            ivar_terms,
                        )
                    }
                    _ => unreachable!(),
                };

                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: con_term,
                    },
                );
                record_step(
                    "fill-data".into(),
                    format!("fill (λi. {}) ({} ...)", d_name, base_con),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }

            // ── Default: stuck fill ──
            _ => {
                let result = Value::VFill(Arc::new(a_fam), sys, Arc::new(base));
                record_step(
                    "fill-stuck".into(),
                    "fill _ _ _".into(),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }
        }
    }
}

pub fn do_hfill(
    globals: &Globals,
    global_offset: usize,
    a_ty: Value,
    sys: DNFSystem,
    base: Value,
    session: &mut Session,
) -> Value {
    // Filter out ⊥ faces
    let sys: DNFSystem = sys
        .into_iter()
        .filter(|(phi, _)| *phi != dnf_bot())
        .collect();

    // Empty system → constant path
    if sys.is_empty() {
        let result = Value::VPLam(
            "j".to_string(),
            IClosure {
                env: Scope::empty(),
                globals: globals.clone(),
                global_offset,
                body: quote(1, globals, global_offset, base.clone(), session),
            },
        );
        record_step(
            "hfill-empty".into(),
            "hfill _ [] base".into(),
            value_str(globals, global_offset, &result, session),
        );
        return result;
    }

    // Any face = ⊤ → corresponding tube
    for (phi, tube) in &sys {
        if *phi == dnf_top() {
            let result = tube.clone();
            record_step(
                "hfill-top-face".into(),
                "hfill _ [⊤ ↦ t, ...] base".into(),
                value_str(globals, global_offset, &result, session),
            );
            return result;
        }
    }

    // Constant-tube shortcut: hfill produces a constant path when tubes don't vary
    if all_tubes_constant_and_coherent(globals, global_offset, &sys, &base, session) {
        let result = Value::VPLam(
            "j".to_string(),
            IClosure {
                env: Scope::empty(),
                globals: globals.clone(),
                global_offset,
                body: quote(1, globals, global_offset, base.clone(), session),
            },
        );
        record_step(
            "hfill-const-tube".into(),
            "hfill A [const tubes] base".into(),
            value_str(globals, global_offset, &result, session),
        );
        return result;
    }

    // ── Decompose hfill for Pi/Sigma/Data types ──
    // hfill returns a PATH, so decomposition wraps inner hfills with PApp at interval variable j.
    {
        match (&a_ty, &base) {
            // ── Pi decomposition ──
            // hfill (Π x:A. B) sys (λx. f x) = λj. λx. hfill B [sys x] (f x) @ j
            (Value::VPi(arg_name, _, cod_clos, _), Value::VLam(_, base_clos)) => {
                let arg_var = Value::VNeutral(Neutral::nvar(0));
                let inner_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let tube_at_arg = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_apply(
                                    globals,
                                    global_offset,
                                    tube_at_i,
                                    arg_var.clone(),
                                    session,
                                )
                            }
                            _ => do_apply(
                                globals,
                                global_offset,
                                tube.clone(),
                                arg_var.clone(),
                                session,
                            ),
                        };
                        (phi.clone(), tube_at_arg)
                    })
                    .collect();
                let base_at_arg = base_clos.apply(arg_var.clone(), session);
                let cod_at_arg = cod_clos.apply(arg_var, session);
                let inner = do_hfill(
                    globals,
                    global_offset,
                    cod_at_arg,
                    inner_sys,
                    base_at_arg,
                    session,
                );
                let inner_term = quote(1, globals, global_offset, inner, session);
                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: Term::TAbs(
                            arg_name.clone(),
                            Arc::new(Term::PApp(Arc::new(inner_term), Arc::new(Term::TVar(1)))),
                        ),
                    },
                );
                record_step(
                    "hfill-pi".into(),
                    "hfill (Π _ _) sys f".into(),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }

            // ── Sigma decomposition ──
            // hfill (Σ x:A. B) sys (a, b) = λj. (hfill A [fst_sys] a @ j, hfill B [snd_sys] b @ j)
            (Value::VSigma(_, fst_ty, snd_clos), Value::VPair(fst_base, snd_base)) => {
                let fst_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let fst_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_fst(globals, global_offset, tube_at_i, session)
                            }
                            _ => do_fst(globals, global_offset, tube.clone(), session),
                        };
                        let fst_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, fst_tube, session),
                            },
                        );
                        (phi.clone(), fst_tube_plam)
                    })
                    .collect();
                let fst_fill = do_hfill(
                    globals,
                    global_offset,
                    fst_ty.as_ref().clone(),
                    fst_sys,
                    (**fst_base).clone(),
                    session,
                );

                let snd_sys: DNFSystem = sys
                    .iter()
                    .map(|(phi, tube)| {
                        let snd_tube = match tube {
                            Value::VPLam(_, iclos) => {
                                let formal_i = Value::VIntervalVar(0);
                                let tube_at_i = iclos.apply_interval_value(formal_i, session);
                                do_snd(globals, global_offset, tube_at_i, session)
                            }
                            _ => do_snd(globals, global_offset, tube.clone(), session),
                        };
                        let snd_tube_plam = Value::VPLam(
                            "_".to_string(),
                            IClosure {
                                env: Scope::empty(),
                                globals: globals.clone(),
                                global_offset,
                                body: quote(1, globals, global_offset, snd_tube, session),
                            },
                        );
                        (phi.clone(), snd_tube_plam)
                    })
                    .collect();
                let snd_fill = do_hfill(
                    globals,
                    global_offset,
                    snd_clos.apply((**fst_base).clone(), session),
                    snd_sys,
                    (**snd_base).clone(),
                    session,
                );

                let fst_fill_term = quote(1, globals, global_offset, fst_fill, session);
                let snd_fill_term = quote(1, globals, global_offset, snd_fill, session);
                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: Term::TPair(
                            Arc::new(Term::PApp(Arc::new(fst_fill_term), Arc::new(Term::TVar(1)))),
                            Arc::new(Term::PApp(Arc::new(snd_fill_term), Arc::new(Term::TVar(1)))),
                        ),
                    },
                );
                record_step(
                    "hfill-sigma".into(),
                    "hfill (Σ _ _) sys p".into(),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }

            // ── Data type decomposition: push hfill through constructor arguments ──
            (Value::VData(d_name, _), _) => {
                let (base_con, base_args, base_ivars) = match &base {
                    Value::VCon(_, name, args) => (name.clone(), args.clone(), vec![]),
                    Value::VPCon(_, name, args, r) => {
                        (name.clone(), args.clone(), vec![(**r).clone()])
                    }
                    Value::VSqCon(_, name, args, r, s) => (
                        name.clone(),
                        args.clone(),
                        vec![(**r).clone(), (**s).clone()],
                    ),
                    Value::VCellCon(_, name, args, ivars) => {
                        (name.clone(), args.clone(), ivars.clone())
                    }
                    _ => {
                        let result = Value::VHFill(Arc::new(a_ty), sys, Arc::new(base));
                        record_step(
                            "hfill-stuck".into(),
                            "hfill _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                };

                let dts = session.current_dts();
                let dt = match dts.iter().find(|dt| dt.name == *d_name) {
                    Some(dt) => dt.clone(),
                    None => {
                        let result = Value::VHFill(Arc::new(a_ty), sys, Arc::new(base));
                        record_step(
                            "hfill-stuck".into(),
                            "hfill _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                };

                let arg_tys = match dt
                    .find_con(&base_con)
                    .map(|s| s.arg_tys.clone())
                    .or_else(|| dt.find_pcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_sqcon(&base_con).map(|s| s.arg_tys.clone()))
                    .or_else(|| dt.find_cellcon(&base_con).map(|s| s.arg_tys.clone()))
                {
                    Some(tys) => tys,
                    None => {
                        let result = Value::VHFill(Arc::new(a_ty), sys, Arc::new(base));
                        record_step(
                            "hfill-stuck".into(),
                            "hfill _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                };

                let n = arg_tys.len();
                if n == 0 {
                    let result = Value::VPLam(
                        "j".to_string(),
                        IClosure {
                            env: Scope::empty(),
                            globals: globals.clone(),
                            global_offset,
                            body: quote(1, globals, global_offset, base.clone(), session),
                        },
                    );
                    record_step(
                        "hfill-data-empty".into(),
                        "hfill D [] c".into(),
                        value_str(globals, global_offset, &result, session),
                    );
                    return result;
                }

                let mut per_arg_tubes: Vec<Vec<(DNF, Value)>> = vec![vec![]; n];
                for (phi, tube) in &sys {
                    let tube_val = match tube {
                        Value::VPLam(_, iclos) => {
                            let formal_i = Value::VIntervalVar(0);
                            iclos.apply_interval_value(formal_i, session)
                        }
                        _ => tube.clone(),
                    };

                    if let Some((_, tube_args, _)) = match_ctor_args(&tube_val, &base_con) {
                        if tube_args.len() == n {
                            for (k, tube_arg) in tube_args.iter().enumerate() {
                                let tube_arg_plam = Value::VPLam(
                                    "_".to_string(),
                                    IClosure {
                                        env: Scope::empty(),
                                        globals: globals.clone(),
                                        global_offset,
                                        body: quote(
                                            1,
                                            globals,
                                            global_offset,
                                            (*tube_arg).clone(),
                                            session,
                                        ),
                                    },
                                );
                                per_arg_tubes[k].push((phi.clone(), tube_arg_plam));
                            }
                        } else {
                            let result = Value::VHFill(Arc::new(a_ty), sys, Arc::new(base));
                            record_step(
                                "hfill-stuck".into(),
                                "hfill _ _ _".into(),
                                value_str(globals, global_offset, &result, session),
                            );
                            return result;
                        }
                    } else {
                        let result = Value::VHFill(Arc::new(a_ty), sys, Arc::new(base));
                        record_step(
                            "hfill-stuck".into(),
                            "hfill _ _ _".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        return result;
                    }
                }

                let mut result_arg_terms: Vec<Term> = Vec::new();
                for k in 0..n {
                    let mut ty_shifted = arg_tys[k].clone();
                    for j in (0..=k).rev() {
                        ty_shifted = shift(1, j as i32, &ty_shifted);
                    }
                    for j in 0..k {
                        let arg_term =
                            quote(0, globals, global_offset, base_args[j].clone(), session);
                        ty_shifted = subst(j as i32, &shift(0, j as i32, &arg_term), &ty_shifted);
                    }
                    let arg_ty = eval_nbe(
                        &Scope::empty(),
                        globals,
                        global_offset,
                        &ty_shifted,
                        session,
                    );
                    let arg_fill = do_hfill(
                        globals,
                        global_offset,
                        arg_ty,
                        per_arg_tubes[k].clone(),
                        base_args[k].clone(),
                        session,
                    );
                    let arg_fill_term = quote(1, globals, global_offset, arg_fill, session);
                    result_arg_terms
                        .push(Term::PApp(Arc::new(arg_fill_term), Arc::new(Term::TVar(1))));
                }

                let con_term = match &base {
                    Value::VCon(_, _, _) => {
                        Term::TCon(d_name.clone(), base_con.clone(), result_arg_terms)
                    }
                    Value::VPCon(_, _, _, _) => Term::TPCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_arg_terms,
                        Arc::new(quote(
                            1,
                            globals,
                            global_offset,
                            base_ivars[0].clone(),
                            session,
                        )),
                    ),
                    Value::VSqCon(_, _, _, _, _) => Term::TSqCon(
                        d_name.clone(),
                        base_con.clone(),
                        result_arg_terms,
                        Arc::new(quote(
                            1,
                            globals,
                            global_offset,
                            base_ivars[0].clone(),
                            session,
                        )),
                        Arc::new(quote(
                            1,
                            globals,
                            global_offset,
                            base_ivars[1].clone(),
                            session,
                        )),
                    ),
                    Value::VCellCon(_, _, _, _) => {
                        let ivar_terms: Vec<Term> = base_ivars
                            .iter()
                            .map(|v| quote(1, globals, global_offset, v.clone(), session))
                            .collect();
                        Term::TCellCon(
                            d_name.clone(),
                            base_con.clone(),
                            result_arg_terms,
                            ivar_terms,
                        )
                    }
                    _ => unreachable!(),
                };

                let result = Value::VPLam(
                    "j".to_string(),
                    IClosure {
                        env: Scope::empty(),
                        globals: globals.clone(),
                        global_offset,
                        body: con_term,
                    },
                );
                record_step(
                    "hfill-data".into(),
                    format!("hfill (λi. {}) ({} ...)", d_name, base_con),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }

            // ── Default: stuck hfill ──
            _ => {
                let result = Value::VHFill(Arc::new(a_ty), sys, Arc::new(base));
                record_step(
                    "hfill-stuck".into(),
                    "hfill _ _ _".into(),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }
        }
    }
}
