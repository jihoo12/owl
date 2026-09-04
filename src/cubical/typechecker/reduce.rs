// HIT endpoint reduction (datatype-aware).
//
// Reduce `TPCon(d, pc, args, r)` at endpoints `r=I0`/`r=I1` to the
// corresponding declared face value, recursively.  This is needed because
// `nbe_eval` doesn't carry datatype definitions, so it cannot reduce path
// constructors at their boundaries without this extra pass.

use std::sync::Arc;

use crate::cubical::nbe::nbe_eval;
use crate::cubical::session::Session;
use crate::cubical::syntax::{Datatype, Term, subst};

pub fn reduce_pcon_endpoints_dt(dts: &[Datatype], t: &Term, session: &mut Session) -> Term {
    let t = nbe_eval(t, session);
    match &t {
        Term::TPCon(d, pc, args, r) => {
            let r_nf = nbe_eval(r, session);
            let (is_i0, is_i1) = match &r_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    (
                        dnf == crate::cubical::interval::dnf_bot(),
                        dnf == crate::cubical::interval::dnf_top(),
                    )
                }
                Term::TCube(d) => (
                    d == &crate::cubical::interval::dnf_bot(),
                    d == &crate::cubical::interval::dnf_top(),
                ),
                _ => (false, false),
            };
            if is_i0 || is_i1 {
                // Look up the face value from the PConSig.
                if let Some(dt) = dts.iter().find(|dt| &dt.name == d)
                    && let Some(sig) = dt.find_pcon(pc)
                {
                    // face0/face1 are in a scope of sig.arity() ordinary args.
                    // Substitute the checked args into the face term.
                    let reduced_args: Vec<Term> = args
                        .iter()
                        .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                        .collect();
                    let face = if is_i0 { &sig.face0 } else { &sig.face1 };
                    // Face parsing uses insert(0,...), so TVar(k) = arg_{num_args-1-k}.
                    // Substitute from highest face-var index to lowest.
                    let arity = reduced_args.len();
                    let mut face_inst = face.clone();
                    for k in (0..arity).rev() {
                        face_inst = subst(k as i32, &reduced_args[arity - 1 - k], &face_inst);
                    }
                    return reduce_pcon_endpoints_dt(dts, &nbe_eval(&face_inst, session), session);
                }
            }
            // Not at an endpoint (or datatype not found): reduce sub-terms.
            let reduced_args: Vec<Term> = args
                .iter()
                .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                .collect();
            nbe_eval(
                &Term::TPCon(d.clone(), pc.clone(), reduced_args, Arc::new(r_nf)),
                session,
            )
        }
        Term::TSqCon(d, sc, args, r, s) => {
            let r_nf = nbe_eval(r, session);
            let s_nf = nbe_eval(s, session);
            // Check if either interval is at an endpoint for boundary reduction.
            let (r_is_i0, r_is_i1) = match &r_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    (
                        dnf == crate::cubical::interval::dnf_bot(),
                        dnf == crate::cubical::interval::dnf_top(),
                    )
                }
                _ => (false, false),
            };
            let (s_is_i0, s_is_i1) = match &s_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    (
                        dnf == crate::cubical::interval::dnf_bot(),
                        dnf == crate::cubical::interval::dnf_top(),
                    )
                }
                _ => (false, false),
            };
            if let Some(dt) = dts.iter().find(|dt| &dt.name == d)
                && let Some(sig) = dt.find_sqcon(sc)
            {
                let arity = sig.arity();
                let reduced_args: Vec<Term> = args
                    .iter()
                    .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                    .collect();
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
                    return reduce_pcon_endpoints_dt(
                        dts,
                        &nbe_eval(&Term::PApp(Arc::new(face), s.clone()), session),
                        session,
                    );
                }
                if r_is_i1 {
                    // sq @ 1 @ s = face_j1 @ s (outer path at i=1 gives face_j1)
                    let face = subst_face(&sig.face_j1);
                    return reduce_pcon_endpoints_dt(
                        dts,
                        &nbe_eval(&Term::PApp(Arc::new(face), s.clone()), session),
                        session,
                    );
                }
                if s_is_i0 {
                    // sq @ r @ 0 = face_i0 (inner path at j=0 gives face_i0, a point)
                    let face = subst_face(&sig.face_i0);
                    return reduce_pcon_endpoints_dt(dts, &nbe_eval(&face, session), session);
                }
                if s_is_i1 {
                    // sq @ r @ 1 = face_i1 (inner path at j=1 gives face_i1, a point)
                    let face = subst_face(&sig.face_i1);
                    return reduce_pcon_endpoints_dt(dts, &nbe_eval(&face, session), session);
                }
            }
            // Not at an endpoint: reduce sub-terms.
            nbe_eval(
                &Term::TSqCon(
                    d.clone(),
                    sc.clone(),
                    args.iter()
                        .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                        .collect(),
                    Arc::new(r_nf),
                    Arc::new(s_nf),
                ),
                session,
            )
        }
        Term::TCellCon(d, cc, args, ivars) => {
            let dim = ivars.len();
            let ivar_nfs: Vec<Term> = ivars.iter().map(|v| nbe_eval(v, session)).collect();
            // Check which interval args are at endpoints.
            let ivar_is_endpoint: Vec<(bool, bool)> = ivar_nfs
                .iter()
                .map(|v| match v {
                    Term::TInterval(i) => {
                        let dnf = crate::cubical::interval::eval_interval(i);
                        (
                            dnf == crate::cubical::interval::dnf_bot(),
                            dnf == crate::cubical::interval::dnf_top(),
                        )
                    }
                    Term::TCube(d) => (
                        d == &crate::cubical::interval::dnf_bot(),
                        d == &crate::cubical::interval::dnf_top(),
                    ),
                    _ => (false, false),
                })
                .collect();
            if let Some(dt) = dts.iter().find(|dt| &dt.name == d)
                && let Some(sig) = dt.find_cellcon(cc)
            {
                let arity = sig.arity();
                let reduced_args: Vec<Term> = args
                    .iter()
                    .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                    .collect();
                let subst_face = |face: &Term| -> Term {
                    let mut t = face.clone();
                    for k in (0..arity).rev() {
                        t = subst(k as i32, &reduced_args[arity - 1 - k], &t);
                    }
                    t
                };
                // Try outermost interval arg first (highest dimension).
                // cell @ r1 @ r2 @ ... @ rn: if r1 is endpoint, reduce via outer face pair.
                if ivar_is_endpoint[0].0 || ivar_is_endpoint[0].1 {
                    let face = if ivar_is_endpoint[0].0 {
                        &sig.faces[2 * dim - 2] // face at outermost=0
                    } else {
                        &sig.faces[2 * dim - 1] // face at outermost=1
                    };
                    let face_inst = subst_face(face);
                    // The face is a (dim-1)-dimensional term; apply to remaining ivars.
                    // ivar_nfs[0] is the consumed outermost endpoint; skip it.
                    // Apply remaining in outermost-first order (matching PApp apply order).
                    let mut result = nbe_eval(&face_inst, session);
                    for iv in ivar_nfs[1..].iter() {
                        result = reduce_pcon_endpoints_dt(
                            dts,
                            &Term::PApp(Arc::new(result), Arc::new(iv.clone())),
                            session,
                        );
                    }
                    return reduce_pcon_endpoints_dt(dts, &result, session);
                }
            }
            // Not at an endpoint: reduce sub-terms.
            nbe_eval(
                &Term::TCellCon(
                    d.clone(),
                    cc.clone(),
                    args.iter()
                        .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                        .collect(),
                    ivar_nfs,
                ),
                session,
            )
        }
        // Recurse into PApp so that e.g. `pcon @ (~ i0)` reduces too.
        Term::PApp(p, r) => {
            // If p is TCon(d, pc, args) referencing a path constructor, and r
            // is a concrete endpoint, reduce via the PConSig faces.
            let r_nf = nbe_eval(r, session);
            let r_is_endpoint = match &r_nf {
                Term::TInterval(i) => {
                    let dnf = crate::cubical::interval::eval_interval(i);
                    dnf == crate::cubical::interval::dnf_bot()
                        || dnf == crate::cubical::interval::dnf_top()
                }
                _ => false,
            };
            if r_is_endpoint {
                if let Term::TCon(ref d, ref pc, ref args) = **p {
                    if let Some(dt) = dts.iter().find(|dt| &dt.name == d) {
                        // Try pcon first
                        if let Some(sig) = dt.find_pcon(pc) {
                            let is_i0 = match &r_nf {
                                Term::TInterval(i) => {
                                    crate::cubical::interval::eval_interval(i)
                                        == crate::cubical::interval::dnf_bot()
                                }
                                _ => false,
                            };
                            let face = if is_i0 { &sig.face0 } else { &sig.face1 };
                            let arity = args.len();
                            let reduced_args: Vec<Term> = args
                                .iter()
                                .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                                .collect();
                            let mut face_inst = face.clone();
                            for k in (0..arity).rev() {
                                face_inst =
                                    subst(k as i32, &reduced_args[arity - 1 - k], &face_inst);
                            }
                            return reduce_pcon_endpoints_dt(
                                dts,
                                &nbe_eval(&face_inst, session),
                                session,
                            );
                        }
                        // Try sqcon: first PApp on a bare sqcon TCon
                        // applies to the r (outer) interval.
                        // sq @ 0 = face_j0, sq @ 1 = face_j1
                        if let Some(sig) = dt.sqcons.iter().find(|c| &c.name == pc) {
                            let is_i0 = match &r_nf {
                                Term::TInterval(i) => {
                                    crate::cubical::interval::eval_interval(i)
                                        == crate::cubical::interval::dnf_bot()
                                }
                                _ => false,
                            };
                            let face = if is_i0 { &sig.face_j0 } else { &sig.face_j1 };
                            let arity = args.len();
                            let reduced_args: Vec<Term> = args
                                .iter()
                                .map(|a| reduce_pcon_endpoints_dt(dts, a, session))
                                .collect();
                            let mut face_inst = face.clone();
                            for k in (0..arity).rev() {
                                face_inst =
                                    subst(k as i32, &reduced_args[arity - 1 - k], &face_inst);
                            }
                            return reduce_pcon_endpoints_dt(
                                dts,
                                &nbe_eval(&face_inst, session),
                                session,
                            );
                        }
                    }
                }
            }
            let p2 = reduce_pcon_endpoints_dt(dts, p, session);
            nbe_eval(&Term::PApp(Arc::new(p2), Arc::new(r_nf.clone())), session)
        }
        // Recurse into PLam so that e.g. `PLam(k, cube3 @ i0 @ j @ k)` reduces too.
        Term::PLam(name, body) => Term::PLam(
            name.clone(),
            Arc::new(reduce_pcon_endpoints_dt(dts, body, session)),
        ),
        _ => t,
    }
}
