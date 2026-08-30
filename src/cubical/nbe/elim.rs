//! Eliminators on values: application, path application, projections,
//! datatype elimination and forcing.

use std::cell::RefCell;
use std::rc::Rc;

use super::eval::eval_nbe;
use super::hcomp::{do_comp, do_hcomp};
use super::quote::quote;
use super::trace::record_step;
use super::util::value_to_endpoint;
use super::value::{Globals, Neutral, NeutralInner, Scope, Value, value_str};
use crate::cubical::interval::I;
use crate::cubical::session::Session;
use crate::cubical::syntax::{ElimCase, Name, Term, max_var, subst};

pub fn do_force(v: Value, globals: &Globals, global_offset: usize, session: &mut Session) -> Value {
    match v {
        Value::VNext(inner) => {
            record_step(
                "force-next".into(),
                "Force (Next _)".into(),
                value_str(globals, global_offset, &inner, session),
            );
            *inner
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::nforce(n)),
        other => Value::VForce(Box::new(other)),
    }
}

pub fn do_apply(
    globals: &Globals,
    global_offset: usize,
    f: Value,
    a: Value,
    session: &mut Session,
) -> Value {
    match f {
        Value::VLam(ref x, ref clos) => {
            let result = clos.apply(a, session);
            record_step(
                "beta".into(),
                format!("(λ{}. _) _", x),
                value_str(globals, global_offset, &result, session),
            );
            result
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::napp(n, a)),
        other => Value::VApp(Box::new(other), Box::new(a)),
    }
}

/// Reduce a higher-constructor value `c args` applied at a concrete interval
/// endpoint to its face:
///   - path constructor:     `c args @ i0 = face0`,     `c args @ i1 = face1`
///   - square constructor:   the applied interval is the *outer* (r) one, so
///     `sq args @ i0 = face_j0` and `sq args @ i1 = face_j1` (paths in the
///     second interval), matching the do_elim/datatype typing
///     `PathP (<r> PathP (<s> A) face_i0 face_i1) face_j0 face_j1`
///   - n-dimensional cell:   the applied interval is the outermost one, so
///     `cell args @ i0 = faces[2n-2]` and `cell args @ i1 = faces[2n-1]`
///     ((n-1)-cells), the outermost face pair.
/// Returns `None` when the constructor is not a known higher constructor of
/// the datatype, `endpoint` is not a concrete endpoint, or the reduction
/// would be unsound here: the face is only re-evaluated in an empty scope,
/// which is faithful only when the ordinary args are closed (an open argument
/// keeps its absolute `NVar` level through the quote/eval round-trip, but
/// comparison contexts derive levels from their own surrounding term, so an
/// early reduction would misalign free-variable levels), and only when the
/// face does not reference the datatype's parameters (those are substituted
/// per-use by the typechecker, not at evaluation time).
fn reduce_con_at_endpoint(
    globals: &Globals,
    global_offset: usize,
    data: &Name,
    con: &Name,
    args: &[Value],
    endpoint: &I,
    session: &mut Session,
) -> Option<Value> {
    let dts = session.current_dts();
    let dt = dts.iter().find(|dt| &dt.name == data)?;
    let arity = args.len();
    let face: &Term = if let Some(sig) = dt.pcons.iter().find(|c| &c.name == con) {
        match endpoint {
            I::I0 => &sig.face0,
            I::I1 => &sig.face1,
            _ => return None,
        }
    } else if let Some(sig) = dt.sqcons.iter().find(|c| &c.name == con) {
        match endpoint {
            I::I0 => &sig.face_j0,
            I::I1 => &sig.face_j1,
            _ => return None,
        }
    } else if let Some(sig) = dt.cellcons.iter().find(|c| &c.name == con) {
        let dim = sig.dimension();
        match endpoint {
            I::I0 => &sig.faces[2 * dim - 2],
            I::I1 => &sig.faces[2 * dim - 1],
            _ => return None,
        }
    } else {
        return None;
    };
    if max_var(face) >= arity as i32 {
        return None;
    }
    let arg_terms: Vec<Term> = args
        .iter()
        .map(|a| quote(0, globals, global_offset, a.clone(), session))
        .collect();
    if arg_terms.iter().any(|t| max_var(t) >= 0) {
        return None;
    }
    let mut face_inst = face.clone();
    for k in (0..arity).rev() {
        face_inst = subst(k as i32, &arg_terms[arity - 1 - k], &face_inst);
    }
    Some(eval_nbe(
        &Scope::empty(),
        &Rc::new(RefCell::new(Vec::new())),
        0,
        &face_inst,
        session,
    ))
}

pub fn do_papp(
    globals: &Globals,
    global_offset: usize,
    p: Value,
    r: Value,
    session: &mut Session,
) -> Value {
    if let Some(i) = value_to_endpoint(&r)
        && let Value::VPLam(_, clos) = p
    {
        let end_lbl = if i == I::I0 { "0" } else { "1" };
        let result = clos.apply_i(i, session);
        record_step(
            "path-app".into(),
            format!("_ @ {}", end_lbl),
            value_str(globals, global_offset, &result, session),
        );
        return result;
    }

    match p {
        Value::VPLam(_, clos) => match r {
            Value::VInterval(ref i) => {
                let end_lbl = if *i == I::I0 {
                    "0".to_string()
                } else if *i == I::I1 {
                    "1".to_string()
                } else {
                    format!("{}", i)
                };
                let result = clos.apply_i(i.clone(), session);
                record_step(
                    "path-app".into(),
                    format!("_ @ {}", end_lbl),
                    value_str(globals, global_offset, &result, session),
                );
                result
            }
            Value::VIntervalVar(level) => clos.apply_i_var(level, session),
            other => Value::VPApp(
                Box::new(Value::VPLam("_".to_string(), clos)),
                Box::new(other),
            ),
        },
        Value::VNeutral(p) => {
            let r_frontier = Neutral::interval_frontier(&r);
            Value::VNeutral(Neutral::npapp(p, r.clone(), r_frontier))
        }
        // hcomp boundary reduction: (hcomp A sys base) @ 0 = base
        //                           (hcomp A sys base) @ 1 = first tube @ 1
        Value::VHComp(a, sys, base) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                match endpoint {
                    I::I0 => {
                        record_step(
                            "hcomp-papp-0".into(),
                            "hcomp _ _ _ @ 0".into(),
                            value_str(globals, global_offset, &base, session),
                        );
                        *base
                    }
                    I::I1 => {
                        // At i=1, any tube applied to I1 gives the result
                        // (all tubes agree at endpoints by well-formedness)
                        if let Some((_, first_tube)) = sys.first() {
                            let result = do_papp(
                                globals,
                                global_offset,
                                first_tube.clone(),
                                Value::VInterval(I::I1),
                                session,
                            );
                            record_step(
                                "hcomp-papp-1".into(),
                                "hcomp _ _ _ @ 1".into(),
                                value_str(globals, global_offset, &result, session),
                            );
                            result
                        } else {
                            // Empty system: shouldn't happen (filtered earlier), but fallback
                            Value::VPApp(Box::new(Value::VHComp(a, sys, base)), Box::new(r))
                        }
                    }
                    _ => Value::VPApp(Box::new(Value::VHComp(a, sys, base)), Box::new(r)),
                }
            } else {
                Value::VPApp(Box::new(Value::VHComp(a, sys, base)), Box::new(r))
            }
        }
        // fill boundary reduction: (fill A sys base) @ 0 = base
        //                          (fill A sys base) @ 1 = comp A sys base
        Value::VFill(a, sys, base) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                match endpoint {
                    I::I0 => {
                        record_step(
                            "fill-papp-0".into(),
                            "fill _ _ _ @ 0".into(),
                            value_str(globals, global_offset, &base, session),
                        );
                        *base
                    }
                    I::I1 => {
                        let result =
                            do_comp(globals, global_offset, *a, sys.clone(), *base, session);
                        record_step(
                            "fill-papp-1".into(),
                            "fill _ _ _ @ 1".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        result
                    }
                    _ => Value::VPApp(Box::new(Value::VFill(a, sys, base)), Box::new(r)),
                }
            } else {
                Value::VPApp(Box::new(Value::VFill(a, sys, base)), Box::new(r))
            }
        }
        // hfill boundary reduction: (hfill A sys base) @ 0 = base
        //                           (hfill A sys base) @ 1 = hcomp A sys base
        Value::VHFill(a, sys, base) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                match endpoint {
                    I::I0 => {
                        record_step(
                            "hfill-papp-0".into(),
                            "hfill _ _ _ @ 0".into(),
                            value_str(globals, global_offset, &base, session),
                        );
                        *base
                    }
                    I::I1 => {
                        let result =
                            do_hcomp(globals, global_offset, *a, sys.clone(), *base, session);
                        record_step(
                            "hfill-papp-1".into(),
                            "hfill _ _ _ @ 1".into(),
                            value_str(globals, global_offset, &result, session),
                        );
                        result
                    }
                    _ => Value::VPApp(Box::new(Value::VHFill(a, sys, base)), Box::new(r)),
                }
            } else {
                Value::VPApp(Box::new(Value::VHFill(a, sys, base)), Box::new(r))
            }
        }
        // Square constructor boundary reduction.
        //
        // A square constructor has type:
        //   PathP (<i> PathP (<j> A) face_i0 face_i1) face_j0 face_j1
        //
        // When the first interval is a concrete endpoint:
        //   sq @ 0 @ s  =  face_j0 @ s   (outer path at i=0 gives face_j0)
        //   sq @ 1 @ s  =  face_j1 @ s   (outer path at i=1 gives face_j1)
        Value::VSqCon(ref data, ref con, ref args, ref sq_r, ref sq_s) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                let dts = session.current_dts();
                if let Some(dt) = dts.iter().find(|dt| &dt.name == data)
                    && let Some(sig) = dt.sqcons.iter().find(|c| &c.name == con)
                {
                    let arity = sig.arity();
                    let face = match endpoint {
                        I::I0 => &sig.face_j0,
                        I::I1 => &sig.face_j1,
                        _ => unreachable!(),
                    };
                    let mut face_inst = face.clone();
                    let arg_terms: Vec<Term> = args
                        .iter()
                        .map(|a| quote(0, globals, global_offset, a.clone(), session))
                        .collect();
                    for k in (0..arity).rev() {
                        face_inst = subst(k as i32, &arg_terms[arity - 1 - k], &face_inst);
                    }
                    let empty_globals: Globals = Rc::new(RefCell::new(Vec::new()));
                    let face_val =
                        eval_nbe(&Scope::empty(), &empty_globals, 0, &face_inst, session);
                    record_step(
                        "sqcon-boundary".into(),
                        format!(
                            "{} @ {} @ _",
                            con,
                            if endpoint == I::I0 { "0" } else { "1" }
                        ),
                        value_str(globals, global_offset, &face_val, session),
                    );
                    return do_papp(globals, global_offset, face_val, (**sq_s).clone(), session);
                }
                Value::VPApp(
                    Box::new(Value::VSqCon(
                        data.clone(),
                        con.clone(),
                        args.clone(),
                        sq_r.clone(),
                        sq_s.clone(),
                    )),
                    Box::new(r),
                )
            } else {
                Value::VPApp(
                    Box::new(Value::VSqCon(
                        data.clone(),
                        con.clone(),
                        args.clone(),
                        sq_r.clone(),
                        sq_s.clone(),
                    )),
                    Box::new(r),
                )
            }
        }
        // N-dimensional cell constructor boundary reduction.
        //
        // A cell constructor with n interval args and faces
        //   faces = [f_0, f_1, ..., f_{2n-2}, f_{2n-1}]
        // has type:
        //   PathP (<i_1> ... PathP (<i_n> A) f_0 f_1) ... f_{2n-2} f_{2n-1})
        //
        // When the first interval arg is a concrete endpoint:
        //   cell @ 0 @ r2 @ ... @ rn  =  (eval f_{2n-2}[args]) @ r2 @ ... @ rn
        //   cell @ 1 @ r2 @ ... @ rn  =  (eval f_{2n-1}[args]) @ r2 @ ... @ rn
        Value::VCellCon(ref data, ref con, ref args, ref ivars) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                let dts = session.current_dts();
                if let Some(dt) = dts.iter().find(|dt| &dt.name == data)
                    && let Some(sig) = dt.cellcons.iter().find(|c| &c.name == con)
                {
                    let arity = sig.arity();
                    let dim = sig.dimension();
                    // The outermost face pair is the last pair in the faces list.
                    let face = match endpoint {
                        I::I0 => &sig.faces[2 * dim - 2],
                        I::I1 => &sig.faces[2 * dim - 1],
                        _ => unreachable!(),
                    };
                    // Guarded like reduce_con_at_endpoint: reduce only when the
                    // face does not reference the datatype's parameters and the
                    // args are closed (the face is re-evaluated in an empty
                    // scope, which is only faithful for closed args).
                    if max_var(face) >= arity as i32 {
                        return Value::VPApp(
                            Box::new(Value::VCellCon(
                                data.clone(),
                                con.clone(),
                                args.clone(),
                                ivars.clone(),
                            )),
                            Box::new(r),
                        );
                    }
                    let mut face_inst = face.clone();
                    let arg_terms: Vec<Term> = args
                        .iter()
                        .map(|a| quote(0, globals, global_offset, a.clone(), session))
                        .collect();
                    if arg_terms.iter().any(|t| max_var(t) >= 0) {
                        return Value::VPApp(
                            Box::new(Value::VCellCon(
                                data.clone(),
                                con.clone(),
                                args.clone(),
                                ivars.clone(),
                            )),
                            Box::new(r),
                        );
                    }
                    for k in (0..arity).rev() {
                        face_inst = subst(k as i32, &arg_terms[arity - 1 - k], &face_inst);
                    }
                    let empty_globals: Globals = Rc::new(RefCell::new(Vec::new()));
                    let mut face_val =
                        eval_nbe(&Scope::empty(), &empty_globals, 0, &face_inst, session);
                    record_step(
                        "cellcon-boundary".into(),
                        format!(
                            "{} @ {} @ ...",
                            con,
                            if endpoint == I::I0 { "0" } else { "1" }
                        ),
                        value_str(globals, global_offset, &face_val, session),
                    );
                    // Apply the face value to the remaining (n-1) interval args,
                    // outermost-first (matching the typechecker and do_elim).
                    for iv in ivars.iter().skip(1) {
                        face_val = do_papp(globals, global_offset, face_val, iv.clone(), session);
                    }
                    return face_val;
                }
                Value::VPApp(
                    Box::new(Value::VCellCon(
                        data.clone(),
                        con.clone(),
                        args.clone(),
                        ivars.clone(),
                    )),
                    Box::new(r),
                )
            } else {
                // Non-endpoint interval arg: build nested PApp for remaining ivars.
                let result = Value::VPApp(
                    Box::new(Value::VCellCon(
                        data.clone(),
                        con.clone(),
                        args.clone(),
                        ivars.clone(),
                    )),
                    Box::new(r),
                );
                result
            }
        }
        // Path constructor value applied at a concrete endpoint: `(c args @ r) @ s`.
        // The value's own interval `r` has already been consumed to produce a
        // point; an over-application reduces best-effort at the new endpoint's
        // face, mirroring the sqcon/cellcon boundary branches. Non-endpoint
        // applications stay neutral.
        Value::VPCon(ref data, ref con, ref args, ref _r) => {
            if let Some(endpoint) = value_to_endpoint(&r)
                && let Some(face_val) = reduce_con_at_endpoint(
                    globals,
                    global_offset,
                    data,
                    con,
                    args,
                    &endpoint,
                    session,
                )
            {
                record_step(
                    "pcon-boundary".into(),
                    format!(
                        "{} @ _ @ {}",
                        con,
                        if endpoint == I::I0 { "0" } else { "1" }
                    ),
                    value_str(globals, global_offset, &face_val, session),
                );
                face_val
            } else {
                Value::VPApp(
                    Box::new(Value::VPCon(
                        data.clone(),
                        con.clone(),
                        args.clone(),
                        _r.clone(),
                    )),
                    Box::new(r),
                )
            }
        }
        // Higher-constructor `VCon(d, c, args)` (the constructor applied to its
        // ordinary args but not yet to its interval(s)) applied at an interval
        // endpoint: reduce to the constructor's face at that endpoint. Covers
        // zero-arg path constructors like `line2 @ i0`, non-empty-arity ones
        // like `mer 0 @ i1`, and bare square/cell constructor references in
        // face terms (`square @ i0` is `face_j0`, a path; `cube3 @ i0` is
        // `faces[2n-2]`, an (n-1)-cell), all applied via a plain PApp.
        Value::VCon(ref data, ref con, ref args) => {
            if let Some(endpoint) = value_to_endpoint(&r)
                && let Some(face_val) = reduce_con_at_endpoint(
                    globals,
                    global_offset,
                    data,
                    con,
                    args,
                    &endpoint,
                    session,
                )
            {
                record_step(
                    "con-boundary".into(),
                    format!("{} @ {}", con, if endpoint == I::I0 { "0" } else { "1" }),
                    value_str(globals, global_offset, &face_val, session),
                );
                face_val
            } else {
                Value::VPApp(
                    Box::new(Value::VCon(data.clone(), con.clone(), args.clone())),
                    Box::new(r),
                )
            }
        }
        // VGlueElem endpoint reduction:
        //   VGlueElem(phi, t, a) @ 0 = a       (the base A-element)
        //   VGlueElem(phi, t, a) @ 1 = t       (the cap B-element)
        Value::VGlueElem(ref phi, ref t, ref a) => {
            if let Some(endpoint) = value_to_endpoint(&r) {
                match endpoint {
                    I::I0 => {
                        record_step(
                            "glue-elem-papp-0".into(),
                            "glue-elem _ _ _ @ 0".into(),
                            value_str(globals, global_offset, a, session),
                        );
                        (**a).clone()
                    }
                    I::I1 => {
                        record_step(
                            "glue-elem-papp-1".into(),
                            "glue-elem _ _ _ @ 1".into(),
                            value_str(globals, global_offset, t, session),
                        );
                        (**t).clone()
                    }
                    _ => Value::VPApp(
                        Box::new(Value::VGlueElem(phi.clone(), t.clone(), a.clone())),
                        Box::new(r),
                    ),
                }
            } else {
                Value::VPApp(
                    Box::new(Value::VGlueElem(phi.clone(), t.clone(), a.clone())),
                    Box::new(r),
                )
            }
        }
        other => Value::VPApp(Box::new(other), Box::new(r)),
    }
}

pub fn do_fst(globals: &Globals, global_offset: usize, p: Value, session: &mut Session) -> Value {
    match p {
        Value::VPair(a, _) => {
            record_step(
                "fst-pair".into(),
                "fst (_, _)".into(),
                value_str(globals, global_offset, &a, session),
            );
            *a
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::nfst(n)),
        other => Value::VFst(Box::new(other)),
    }
}

pub fn do_snd(globals: &Globals, global_offset: usize, p: Value, session: &mut Session) -> Value {
    match p {
        Value::VPair(_, b) => {
            record_step(
                "snd-pair".into(),
                "snd (_, _)".into(),
                value_str(globals, global_offset, &b, session),
            );
            *b
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::nsnd(n)),
        other => Value::VSnd(Box::new(other)),
    }
}

pub fn do_proj(field: &str, r: Value, session: &mut Session) -> Value {
    match r {
        // Desugar record update on projection: (r { x = v }).y → r.y when field != x
        Value::VRecordUpdate(r_inner, ref updates) => {
            if let Value::VCon(ref dt, _, ref args) = *r_inner.as_ref() {
                let dts = session.current_dts();
                if let Some(dt_sig) = dts.iter().find(|d| &d.name == dt) {
                    if let Some(field_names) = &dt_sig.field_names {
                        if let Some((_, val)) = updates.iter().find(|(f, _)| f == field) {
                            return val.clone();
                        }
                        if let Some(idx) = field_names.iter().position(|n| n == field) {
                            if idx < args.len() {
                                return args[idx].clone();
                            }
                        }
                    }
                }
            }
            Value::VProj(
                field.to_string(),
                Box::new(Value::VRecordUpdate(r_inner, updates.clone())),
            )
        }
        Value::VCon(_, _, ref args) => {
            let dts = session.current_dts();
            if let Some(dt) = dts.iter().find(|dt| {
                dt.cons.len() == 1
                    && dt.pcons.is_empty()
                    && dt.sqcons.is_empty()
                    && dt.cellcons.is_empty()
                    && dt.field_names.is_some()
            }) {
                if let Some(field_names) = &dt.field_names {
                    if let Some(idx) = field_names.iter().position(|n| n == field) {
                        if idx < args.len() {
                            return args[idx].clone();
                        }
                    }
                }
            }
            Value::VProj(field.to_string(), Box::new(r))
        }
        Value::VNeutral(n) => Value::VNeutral(Neutral::nproj(n, field.to_string())),
        other => Value::VProj(field.to_string(), Box::new(other)),
    }
}

pub fn do_elim(
    motive: Value,
    cases: &[ElimCase],
    scrut: Value,
    env: &Scope,
    globals: &Globals,
    global_offset: usize,
    session: &mut Session,
) -> Value {
    match scrut {
        Value::VCon(ref data, ref con, ref args) => {
            match cases.iter().find(|case| case.con == *con) {
                Some(case) => {
                    let mut env2_values: Vec<Value> = args.iter().rev().cloned().collect();
                    if case.as_name.is_some() {
                        env2_values.insert(0, Value::VCon(data.clone(), con.clone(), args.clone()));
                    }
                    let env2 = env.chain(env2_values);
                    let result = eval_nbe(&env2, globals, global_offset, &case.body, session);
                    record_step(
                        "elim-con".into(),
                        format!("elim _ [{}] ({} {})", con, data, con),
                        value_str(globals, global_offset, &result, session),
                    );
                    result
                }
                None => Value::VElim(
                    Box::new(motive),
                    cases.to_vec(),
                    Box::new(Value::VCon("".into(), con.clone(), args.clone())),
                    env.clone(),
                    global_offset,
                ),
            }
        }
        Value::VPCon(ref data, ref con, ref args, ref r) => {
            match cases.iter().find(|case| case.con == *con) {
                Some(case) => {
                    // The case body is laid out with the case's interval binder
                    // at the base of the environment (a phantom slot below the
                    // ordinary arguments), matching `quote_cases` and the
                    // typechecker's case context. Push the interval value
                    // there; the body's own path binders are applied on top by
                    // `do_papp` below.
                    let mut env2_values: Vec<Value> = Vec::with_capacity(args.len() + 1);
                    env2_values.push((**r).clone());
                    env2_values.extend(args.iter().rev().cloned());
                    let env2 = env.chain(env2_values);
                    let body = eval_nbe(&env2, globals, global_offset, &case.body, session);
                    let result = do_papp(globals, global_offset, body, (**r).clone(), session);
                    record_step(
                        "elim-pcon".into(),
                        format!("elim _ [{}] ({} {})", con, data, con),
                        value_str(globals, global_offset, &result, session),
                    );
                    result
                }
                None => Value::VElim(
                    Box::new(motive),
                    cases.to_vec(),
                    Box::new(Value::VPCon(
                        "".into(),
                        con.clone(),
                        args.clone(),
                        r.clone(),
                    )),
                    env.clone(),
                    global_offset,
                ),
            }
        }
        // Square constructor elimination: body has 2 interval binders.
        // Evaluate body with args in scope, then apply to both interval args.
        Value::VSqCon(ref data, ref con, ref args, ref r, ref s) => {
            match cases.iter().find(|case| case.con == *con) {
                Some(case) => {
                    // Interval binders sit below the ordinary args in the case
                    // body's environment layout (see the VPCon comment above);
                    // the sqcon's intervals fill the two phantom slots, innermost
                    // (the case's second interval binder) first.
                    let mut env2_values: Vec<Value> = Vec::with_capacity(args.len() + 2);
                    env2_values.push((**s).clone());
                    env2_values.push((**r).clone());
                    env2_values.extend(args.iter().rev().cloned());
                    let env2 = env.chain(env2_values);
                    let body = eval_nbe(&env2, globals, global_offset, &case.body, session);
                    // Body is PLam-shaped with 2 interval binders: apply to both r and s.
                    let body_at_r = do_papp(globals, global_offset, body, (**r).clone(), session);
                    let result = do_papp(globals, global_offset, body_at_r, (**s).clone(), session);
                    record_step(
                        "elim-sqcon".into(),
                        format!("elim _ [{}] ({} {})", con, data, con),
                        value_str(globals, global_offset, &result, session),
                    );
                    result
                }
                None => Value::VElim(
                    Box::new(motive),
                    cases.to_vec(),
                    Box::new(Value::VSqCon(
                        "".into(),
                        con.clone(),
                        args.clone(),
                        r.clone(),
                        s.clone(),
                    )),
                    env.clone(),
                    global_offset,
                ),
            }
        }
        // N-dimensional cell constructor elimination: body has n interval binders.
        // Evaluate body with args in scope, then apply to all interval args.
        Value::VCellCon(ref data, ref con, ref args, ref ivars) => {
            match cases.iter().find(|case| case.con == *con) {
                Some(case) => {
                    // Same convention as VPCon/VSqCon: the case body's
                    // environment has one phantom slot per interval binder at
                    // the base, below the ordinary args. The cell's interval
                    // values fill them innermost-first (the case context
                    // extends interval binders outermost-first).
                    let mut env2_values: Vec<Value> = Vec::with_capacity(args.len() + ivars.len());
                    env2_values.extend(ivars.iter().rev().cloned());
                    env2_values.extend(args.iter().rev().cloned());
                    let env2 = env.chain(env2_values);
                    let body = eval_nbe(&env2, globals, global_offset, &case.body, session);
                    // Apply body to all interval args (innermost first).
                    let mut result = body;
                    for iv in ivars.iter() {
                        result = do_papp(globals, global_offset, result, iv.clone(), session);
                    }
                    record_step(
                        "elim-cellcon".into(),
                        format!("elim _ [{}] ({} {})", con, data, con),
                        value_str(globals, global_offset, &result, session),
                    );
                    result
                }
                None => Value::VElim(
                    Box::new(motive),
                    cases.to_vec(),
                    Box::new(Value::VCellCon(
                        "".into(),
                        con.clone(),
                        args.clone(),
                        ivars.clone(),
                    )),
                    env.clone(),
                    global_offset,
                ),
            }
        }
        Value::VNeutral(n) => {
            // Phase 3: frontier-of-instability destabilization.
            // When the neutral's frontier is satisfied (interval variables
            // in the frontier are bound to concrete endpoints), try to
            // reduce the neutral. If it computes to a non-neutral value,
            // re-enter do_elim with the result.
            if let Some(destabilized) = try_destabilize(globals, global_offset, &n, session) {
                return do_elim(
                    motive,
                    cases,
                    destabilized,
                    env,
                    globals,
                    global_offset,
                    session,
                );
            }
            stuck_elim(motive, cases, n, env, global_offset)
        }
        other => Value::VElim(
            Box::new(motive),
            cases.to_vec(),
            Box::new(other),
            env.clone(),
            global_offset,
        ),
    }
}

/// Try to destabilize a neutral whose frontier of instability is satisfied.
///
/// When a neutral's frontier is satisfied (the interval variables it depends
/// on are bound to concrete endpoints), the neutral may be able to compute.
/// This function attempts to reduce the neutral by re-evaluating its spine
/// operations with concrete interval values.
///
/// Returns `Some(value)` if the neutral successfully reduced to a non-neutral
/// value, `None` if it's still stuck.
fn try_destabilize(
    globals: &Globals,
    global_offset: usize,
    n: &Neutral,
    session: &mut Session,
) -> Option<Value> {
    // Check if the frontier is satisfied.
    if !n.frontier().is_satisfied(&session.interval_bindings) {
        return None;
    }

    match n.inner() {
        // NVar never computes.
        NeutralInner::NVar(_) => None,

        // NPApp(p, r): path application. If r is an interval variable that's
        // now concrete, apply the path to the concrete endpoint.
        NeutralInner::NPApp(p, r) => {
            if let Value::VIntervalVar(level) = **r {
                if let Some(Some(concrete)) = session.interval_bindings.get(level) {
                    let p_val = Value::VNeutral((**p).clone());
                    let r_val = Value::VInterval(concrete.clone());
                    let result = do_papp(globals, global_offset, p_val, r_val, session);
                    if matches!(result, Value::VNeutral(_)) {
                        return None;
                    }
                    return Some(result);
                }
            }
            None
        }

        // NApp(f, a): function application. Try to destabilize f.
        NeutralInner::NApp(f, a) => {
            let f_val = try_destabilize(globals, global_offset, f, session)
                .unwrap_or(Value::VNeutral((**f).clone()));
            let result = do_apply(globals, global_offset, f_val, (**a).clone(), session);
            if matches!(result, Value::VNeutral(_)) {
                return None;
            }
            Some(result)
        }

        // NFst(p): first projection. Try to destabilize p.
        NeutralInner::NFst(p) => {
            let p_val = try_destabilize(globals, global_offset, p, session)
                .unwrap_or(Value::VNeutral((**p).clone()));
            let result = do_fst(globals, global_offset, p_val, session);
            if matches!(result, Value::VNeutral(_)) {
                return None;
            }
            Some(result)
        }

        // NSnd(p): second projection. Try to destabilize p.
        NeutralInner::NSnd(p) => {
            let p_val = try_destabilize(globals, global_offset, p, session)
                .unwrap_or(Value::VNeutral((**p).clone()));
            let result = do_snd(globals, global_offset, p_val, session);
            if matches!(result, Value::VNeutral(_)) {
                return None;
            }
            Some(result)
        }

        // NProj(n, field): record field projection. Try to destabilize n.
        NeutralInner::NProj(n, field) => {
            let n_val = try_destabilize(globals, global_offset, n, session)
                .unwrap_or(Value::VNeutral((**n).clone()));
            let result = do_proj(field, n_val, session);
            if matches!(result, Value::VNeutral(_)) {
                return None;
            }
            Some(result)
        }

        // NForce(n): force Next. Try to destabilize n.
        NeutralInner::NForce(n) => {
            let n_val = try_destabilize(globals, global_offset, n, session)
                .unwrap_or(Value::VNeutral((**n).clone()));
            let result = do_force(n_val, globals, global_offset, session);
            if matches!(result, Value::VNeutral(_)) {
                return None;
            }
            Some(result)
        }

        // NElim(motive, cases, scrut, env, go): datatype elimination.
        // Try to destabilize the scrutinee; if it computes to a constructor,
        // re-enter do_elim.
        NeutralInner::NElim(motive, cases, scrut, env, go) => {
            if let Some(scrut_val) = try_destabilize(globals, global_offset, scrut, session) {
                let result = do_elim(
                    *motive.clone(),
                    cases,
                    scrut_val,
                    env,
                    globals,
                    global_offset,
                    session,
                );
                if matches!(result, Value::VNeutral(_)) {
                    return None;
                }
                return Some(result);
            }
            None
        }

        // NSqApp, NCellApp, NTransport, NHComp, NComp, NFill, NHFill, NMeta:
        // don't try to destabilize (these are either always stuck or need
        // more complex handling).
        _ => None,
    }
}

fn stuck_elim(
    motive: Value,
    cases: &[ElimCase],
    n: Neutral,
    env: &Scope,
    global_offset: usize,
) -> Value {
    Value::VNeutral(Neutral::nelim(
        motive,
        cases.to_vec(),
        n,
        env.clone(),
        global_offset,
    ))
}
