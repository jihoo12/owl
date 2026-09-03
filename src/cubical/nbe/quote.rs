//! Quoting: values back to normalised `Term`s.

use super::elim::try_destabilize;
use super::value::{Globals, Neutral, NeutralInner, Scope, Value};
use crate::cubical::session::Session;
use crate::cubical::syntax::{ElimCase, System, Term};
use std::sync::Arc;

/// Quoting can also diverge independently of `eval_nbe`: re-quoting a lambda
/// whose body re-references the same global value grows the quote recursion one
/// `TAbs` layer per cycle (`quote` -> `Closure::apply` -> `eval_nbe` -> `quote`),
/// while each `eval_nbe` call returns immediately. Cap the quote depth so such
/// values produce a finite (stuck) term instead of overflowing the stack. The
/// placeholder is an unbound `TVar(size)` (far beyond any real context), which
/// surfaces as an error downstream rather than silently passing. The cap must be
/// Maximum quote depth before returning a variable reference. Matches the
/// eval_nbe cap to prevent stack overflow on deep quote→eval→quote cycles.
const QUOTE_MAX_DEPTH: usize = 2000;

pub fn quote(
    size: usize,
    globals: &Globals,
    global_offset: usize,
    v: Value,
    session: &mut Session,
) -> Term {
    let n = session.quote_depth_enter();
    if n >= QUOTE_MAX_DEPTH {
        session.quote_depth_restore(n);
        return Term::TVar(size as i32);
    }
    let r = quote_inner(size, globals, global_offset, v, session);
    session.quote_depth_restore(n);
    r
}

fn quote_inner(
    size: usize,
    globals: &Globals,
    global_offset: usize,
    v: Value,
    session: &mut Session,
) -> Term {
    match v {
        Value::VNeutral(n) => quote_neutral(size, globals, global_offset, n, session),
        Value::VLam(x, clos) => Term::TAbs(
            x,
            Arc::new(quote(
                size + 1,
                globals,
                global_offset,
                clos.apply(Value::VNeutral(Neutral::nvar(size)), session),
                session,
            )),
        ),
        Value::VApp(f, a) => Term::TApp(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                f.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
        ),
        Value::VPi(x, a, b, implicit) => Term::TPi(
            x,
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size + 1,
                globals,
                global_offset,
                b.apply(Value::VNeutral(Neutral::nvar(size)), session),
                session,
            )),
            implicit,
        ),
        Value::VSigma(x, a, b) => Term::TSigma(
            x,
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size + 1,
                globals,
                global_offset,
                b.apply(Value::VNeutral(Neutral::nvar(size)), session),
                session,
            )),
        ),
        Value::VPair(a, b) => Term::TPair(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                b.as_ref().clone(),
                session,
            )),
        ),
        Value::VFst(p) => Term::TFst(Arc::new(quote(
            size,
            globals,
            global_offset,
            p.as_ref().clone(),
            session,
        ))),
        Value::VSnd(p) => Term::TSnd(Arc::new(quote(
            size,
            globals,
            global_offset,
            p.as_ref().clone(),
            session,
        ))),
        Value::VProj(field, r) => Term::TProj(
            field,
            Arc::new(quote(
                size,
                globals,
                global_offset,
                r.as_ref().clone(),
                session,
            )),
        ),
        Value::VRecordUpdate(r, updates) => Term::TRecordUpdate(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                r.as_ref().clone(),
                session,
            )),
            updates
                .iter()
                .map(|(f, e)| {
                    (
                        f.clone(),
                        quote(size, globals, global_offset, e.clone(), session),
                    )
                })
                .collect(),
        ),
        Value::VPath(a, u, v) => Term::TPath(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                u.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                v.as_ref().clone(),
                session,
            )),
        ),
        Value::VId(a, u, v) => Term::TId(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                u.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                v.as_ref().clone(),
                session,
            )),
        ),
        Value::VRefl(a) => Term::TRefl(Arc::new(quote(
            size,
            globals,
            global_offset,
            a.as_ref().clone(),
            session,
        ))),
        Value::VJelim(motive, base, p) => Term::TJ(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                motive.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                base.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                p.as_ref().clone(),
                session,
            )),
        ),
        Value::VPLam(x, clos) => Term::PLam(
            x,
            Arc::new(quote(
                size + 1,
                globals,
                global_offset,
                clos.apply_i_var(size, session),
                session,
            )),
        ),
        Value::VPApp(p, r) => Term::PApp(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                p.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                r.as_ref().clone(),
                session,
            )),
        ),
        Value::VUniv(n) => Term::TUniv(n),
        Value::VProp => Term::TProp,
        Value::VSSet => Term::TSSet,
        Value::VLevelTy => Term::TLevelTy,
        Value::VLift(a, lvl) => Term::TLift(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
            lvl,
        ),
        Value::VLower(a) => Term::TLower(Arc::new(quote(
            size,
            globals,
            global_offset,
            a.as_ref().clone(),
            session,
        ))),
        Value::VIntervalTy => Term::TIntervalTy,
        Value::VInterval(i) => Term::TInterval(i),
        Value::VIntervalVar(level) => level_to_var(size, level),
        Value::VCube(c) => Term::TCube(c),
        Value::VData(d, params) => Term::TData(
            d,
            params
                .into_iter()
                .map(|p| quote(size, globals, global_offset, p, session))
                .collect(),
        ),
        Value::VCon(d, c, args) => Term::TCon(
            d,
            c,
            args.into_iter()
                .map(|a| quote(size, globals, global_offset, a, session))
                .collect(),
        ),
        Value::VPCon(d, c, args, r) => Term::TPCon(
            d,
            c,
            args.into_iter()
                .map(|a| quote(size, globals, global_offset, a, session))
                .collect(),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                r.as_ref().clone(),
                session,
            )),
        ),
        Value::VSqCon(d, c, args, r, s) => Term::TSqCon(
            d,
            c,
            args.into_iter()
                .map(|a| quote(size, globals, global_offset, a, session))
                .collect(),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                r.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                s.as_ref().clone(),
                session,
            )),
        ),
        Value::VCellCon(d, c, args, ivars) => Term::TCellCon(
            d,
            c,
            args.into_iter()
                .map(|a| quote(size, globals, global_offset, a, session))
                .collect(),
            ivars
                .into_iter()
                .map(|v| quote(size, globals, global_offset, v, session))
                .collect(),
        ),
        Value::VElim(motive, cases, scrut, env, go) => Term::TElim(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                motive.as_ref().clone(),
                session,
            )),
            quote_cases(size, globals, global_offset, &env, go, cases, session),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                scrut.as_ref().clone(),
                session,
            )),
        ),
        Value::VGlue(a, phi, te) => Term::TGlue(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
            Arc::new(Term::TCube(phi)),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                te.as_ref().clone(),
                session,
            )),
        ),
        Value::VPartial(a, phi) => Term::TPartial(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                phi.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
        ),
        Value::VSystemType(sys) => Term::TSystemType(
            sys.into_iter()
                .map(|(phi, a)| {
                    (
                        Term::TCube(phi),
                        quote(size, globals, global_offset, a, session),
                    )
                })
                .collect(),
        ),
        Value::VGlueElem(phi, t, a) => Term::TGlueElem(
            Arc::new(Term::TCube(phi)),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                t.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
        ),
        Value::VUnglue(phi, te, g) => Term::TUnglue(
            Arc::new(Term::TCube(phi)),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                te.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                g.as_ref().clone(),
                session,
            )),
        ),
        Value::VEquiv(a, b) => Term::TEquiv(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                b.as_ref().clone(),
                session,
            )),
        ),
        Value::VMkEquiv(a, b, f, g, eta, eps) => Term::TMkEquiv(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                b.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                f.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                g.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                eta.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                eps.as_ref().clone(),
                session,
            )),
        ),
        Value::VEquivFwd(e, x) => Term::TEquivFwd(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                e.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                x.as_ref().clone(),
                session,
            )),
        ),
        Value::VUa(e) => Term::TUa(Arc::new(quote(
            size,
            globals,
            global_offset,
            e.as_ref().clone(),
            session,
        ))),
        Value::VTransport(p, x) => Term::TTransport(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                p.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                x.as_ref().clone(),
                session,
            )),
        ),
        Value::VTransp(a, r, x) => Term::TTransp(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                a.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                r.as_ref().clone(),
                session,
            )),
            Arc::new(quote(
                size,
                globals,
                global_offset,
                x.as_ref().clone(),
                session,
            )),
        ),
        Value::VHComp(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone(), session),
                    )
                })
                .collect();
            Term::THComp(
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    a.as_ref().clone(),
                    session,
                )),
                sys_term,
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    base.as_ref().clone(),
                    session,
                )),
            )
        }
        Value::VComp(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone(), session),
                    )
                })
                .collect();
            Term::TComp(
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    a.as_ref().clone(),
                    session,
                )),
                sys_term,
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    base.as_ref().clone(),
                    session,
                )),
            )
        }
        Value::VFill(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone(), session),
                    )
                })
                .collect();
            Term::TFill(
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    a.as_ref().clone(),
                    session,
                )),
                sys_term,
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    base.as_ref().clone(),
                    session,
                )),
            )
        }
        Value::VHFill(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone(), session),
                    )
                })
                .collect();
            Term::THFill(
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    a.as_ref().clone(),
                    session,
                )),
                sys_term,
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    base.as_ref().clone(),
                    session,
                )),
            )
        }
        Value::VDelay(a) => Term::TDelay(Arc::new(quote(
            size,
            globals,
            global_offset,
            a.as_ref().clone(),
            session,
        ))),
        Value::VNext(a) => Term::TNext(Arc::new(quote(
            size,
            globals,
            global_offset,
            a.as_ref().clone(),
            session,
        ))),
        Value::VForce(a) => Term::TForce(Arc::new(quote(
            size,
            globals,
            global_offset,
            a.as_ref().clone(),
            session,
        ))),
        Value::TermVal(t) => t.clone(),
    }
}

fn quote_neutral(
    size: usize,
    globals: &Globals,
    global_offset: usize,
    n: Neutral,
    session: &mut Session,
) -> Term {
    match n.inner() {
        NeutralInner::NVar(level) => level_to_var(size, *level),
        NeutralInner::NApp(f, a) => Term::TApp(
            Arc::new(quote_neutral(
                size,
                globals,
                global_offset,
                (**f).clone(),
                session,
            )),
            Arc::new(quote(size, globals, global_offset, (**a).clone(), session)),
        ),
        NeutralInner::NPApp(p, r) => Term::PApp(
            Arc::new(quote_neutral(
                size,
                globals,
                global_offset,
                (**p).clone(),
                session,
            )),
            Arc::new(quote(size, globals, global_offset, (**r).clone(), session)),
        ),
        NeutralInner::NSqApp(p, r, s) => {
            let pq = quote_neutral(size, globals, global_offset, (**p).clone(), session);
            let rq = quote(size, globals, global_offset, (**r).clone(), session);
            let sq = quote(size, globals, global_offset, (**s).clone(), session);
            Term::PApp(
                Arc::new(Term::PApp(Arc::new(pq), Arc::new(rq))),
                Arc::new(sq),
            )
        }
        NeutralInner::NCellApp(p, ivars) => {
            let mut result = quote_neutral(size, globals, global_offset, (**p).clone(), session);
            for iv in ivars.iter().rev() {
                result = Term::PApp(
                    Arc::new(result),
                    Arc::new(quote(size, globals, global_offset, iv.clone(), session)),
                );
            }
            result
        }
        NeutralInner::NFst(p) => Term::TFst(Arc::new(quote_neutral(
            size,
            globals,
            global_offset,
            (**p).clone(),
            session,
        ))),
        NeutralInner::NSnd(p) => Term::TSnd(Arc::new(quote_neutral(
            size,
            globals,
            global_offset,
            (**p).clone(),
            session,
        ))),
        NeutralInner::NElim(motive, cases, scrut, env, go) => Term::TElim(
            Arc::new(quote(
                size,
                globals,
                global_offset,
                (**motive).clone(),
                session,
            )),
            quote_cases(
                size,
                globals,
                global_offset,
                env,
                *go,
                cases.clone(),
                session,
            ),
            Arc::new(quote_neutral(
                size,
                globals,
                global_offset,
                (**scrut).clone(),
                session,
            )),
        ),
        NeutralInner::NTransport(p, x) => Term::TTransport(
            Arc::new(quote(size, globals, global_offset, (**p).clone(), session)),
            Arc::new(quote(size, globals, global_offset, (**x).clone(), session)),
        ),
        NeutralInner::NTransp(a, r, x) => Term::TTransp(
            Arc::new(quote(size, globals, global_offset, (**a).clone(), session)),
            Arc::new(quote(size, globals, global_offset, (**r).clone(), session)),
            Arc::new(quote(size, globals, global_offset, (**x).clone(), session)),
        ),
        NeutralInner::NHComp(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone(), session),
                    )
                })
                .collect();
            Term::THComp(
                Arc::new(quote(size, globals, global_offset, (**a).clone(), session)),
                sys_term,
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    (**base).clone(),
                    session,
                )),
            )
        }
        NeutralInner::NComp(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone(), session),
                    )
                })
                .collect();
            Term::TComp(
                Arc::new(quote(size, globals, global_offset, (**a).clone(), session)),
                sys_term,
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    (**base).clone(),
                    session,
                )),
            )
        }
        NeutralInner::NFill(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone(), session),
                    )
                })
                .collect();
            Term::TFill(
                Arc::new(quote(size, globals, global_offset, (**a).clone(), session)),
                sys_term,
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    (**base).clone(),
                    session,
                )),
            )
        }
        NeutralInner::NHFill(a, sys, base) => {
            let sys_term: System = sys
                .iter()
                .map(|(phi, tube)| {
                    (
                        Term::TCube(phi.clone()),
                        quote(size, globals, global_offset, tube.clone(), session),
                    )
                })
                .collect();
            Term::THFill(
                Arc::new(quote(size, globals, global_offset, (**a).clone(), session)),
                sys_term,
                Arc::new(quote(
                    size,
                    globals,
                    global_offset,
                    (**base).clone(),
                    session,
                )),
            )
        }
        NeutralInner::NMeta(i) => Term::Meta(*i),
        NeutralInner::NForce(n) => Term::TForce(Arc::new(quote_neutral(
            size,
            globals,
            global_offset,
            (**n).clone(),
            session,
        ))),
        NeutralInner::NProj(n, field) => Term::TProj(
            field.clone(),
            Arc::new(quote_neutral(
                size,
                globals,
                global_offset,
                (**n).clone(),
                session,
            )),
        ),
        NeutralInner::NUnquote(n) => Term::TUnquote(Arc::new(quote_neutral(
            size,
            globals,
            global_offset,
            (**n).clone(),
            session,
        ))),
    }
}

/// Re-anchor a stored elim case body for quotation.
///
/// A stuck elim stores the *raw source* case bodies. Those bodies reference
/// (in de Bruijn order): the case's own binders (TVar 0..nb), the enclosing
/// locals captured in the elim's creation `env`, and below-frame globals.
/// Re-evaluating the body under fresh binders would re-trigger recursive
/// definitions (e.g. `add`'s `suc` case body calls `add` on the pattern
/// variable), producing a fresh stuck elim every level — a non-terminating
/// growth. So we re-anchor *structurally*: local references are replaced by
/// the re-quoted captured values, binder references round-trip unchanged, and
/// global references are moved to below the quoting frame. Nothing is
/// re-evaluated, so recursion terminates.
fn quote_case_body(
    size: usize,
    globals: &Globals,
    global_offset: usize,
    env: &Scope,
    go: usize,
    t: &Term,
    session: &mut Session,
) -> Term {
    match t {
        Term::TVar(i) => {
            let i = *i as usize;
            if i < env.len() {
                let v = env.lookup(i).clone();
                match &v {
                    // Captured closures must be re-anchored structurally, not
                    // re-quoted via general `quote`: `quote` on a VLam applies
                    // the closure (`clos.apply`), which re-evaluates the body.
                    // Inside a stuck elim that body can reference recursive
                    // definitions (e.g. `add_comm m' n`), so re-evaluating it
                    // re-unfolds the definition one level per pass and never
                    // terminates. Re-anchoring the raw body under the
                    // closure's env keeps quoting evaluation-free (see the
                    // comment on `quote_case_body`).
                    Value::VLam(x, clos) => Term::TAbs(
                        x.clone(),
                        Arc::new(quote_case_body(
                            size + 1,
                            globals,
                            global_offset,
                            &clos.env.extend(Value::VNeutral(Neutral::nvar(size))),
                            clos.global_offset,
                            &clos.body,
                            session,
                        )),
                    ),
                    Value::VPLam(x, clos) => Term::PLam(
                        x.clone(),
                        Arc::new(quote_case_body(
                            size + 1,
                            globals,
                            global_offset,
                            &clos.env.extend(Value::VIntervalVar(size)),
                            clos.global_offset,
                            &clos.body,
                            session,
                        )),
                    ),
                    _ => {
                        // Phase 4: if this value is a neutral with a satisfied
                        // frontier, attempt destabilization before quoting.
                        // This is defensive — the kernel re-checks everything.
                        if let Value::VNeutral(ref n) = v {
                            if let Some(destabilized) =
                                try_destabilize(globals, global_offset, n, session)
                            {
                                return quote(size, globals, global_offset, destabilized, session);
                            }
                        }
                        quote(size, globals, global_offset, v.clone(), session)
                    }
                }
            } else {
                Term::TVar((size + go + i - env.len()) as i32)
            }
        }
        Term::TApp(f, a) => Term::TApp(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                f,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
        ),
        Term::TAbs(x, b) => Term::TAbs(
            x.clone(),
            Arc::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::nvar(size))),
                go,
                b,
                session,
            )),
        ),
        Term::TUniv(n) => Term::TUniv(n.clone()),
        Term::TProp => Term::TProp,
        Term::TSSet => Term::TSSet,
        Term::TLevelTy => Term::TLevelTy,
        Term::TLift(a, lvl) => Term::TLift(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            lvl.clone(),
        ),
        Term::TLower(a) => Term::TLower(Arc::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TIntervalTy => Term::TIntervalTy,
        Term::TPi(x, a, b, _) => Term::TPi(
            x.clone(),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Arc::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::nvar(size))),
                go,
                b,
                session,
            )),
            false,
        ),
        Term::TInterval(i) => Term::TInterval(i.clone()),
        Term::TCube(c) => Term::TCube(c.clone()),
        Term::TPath(a, u, v) => Term::TPath(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                u,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                v,
                session,
            )),
        ),
        Term::TId(a, u, v) => Term::TId(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                u,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                v,
                session,
            )),
        ),
        Term::TRefl(a) => Term::TRefl(Arc::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TJ(motive, base, p) => Term::TJ(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                motive,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                base,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                p,
                session,
            )),
        ),
        Term::PLam(x, b) => Term::PLam(
            x.clone(),
            Arc::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::nvar(size))),
                go,
                b,
                session,
            )),
        ),
        Term::PApp(p, r) => Term::PApp(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                p,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                r,
                session,
            )),
        ),
        Term::THComp(a, sys, u0) => Term::THComp(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        quote_case_body(size, globals, global_offset, env, go, phi, session),
                        quote_case_body(size, globals, global_offset, env, go, t, session),
                    )
                })
                .collect(),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                u0,
                session,
            )),
        ),
        Term::TComp(a, sys, u0) => Term::TComp(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        quote_case_body(size, globals, global_offset, env, go, phi, session),
                        quote_case_body(size, globals, global_offset, env, go, t, session),
                    )
                })
                .collect(),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                u0,
                session,
            )),
        ),
        Term::TFill(a, sys, u0) => Term::TFill(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        quote_case_body(size, globals, global_offset, env, go, phi, session),
                        quote_case_body(size, globals, global_offset, env, go, t, session),
                    )
                })
                .collect(),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                u0,
                session,
            )),
        ),
        Term::THFill(a, sys, u0) => Term::THFill(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            sys.iter()
                .map(|(phi, t)| {
                    (
                        quote_case_body(size, globals, global_offset, env, go, phi, session),
                        quote_case_body(size, globals, global_offset, env, go, t, session),
                    )
                })
                .collect(),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                u0,
                session,
            )),
        ),
        Term::TEquiv(a, b) => Term::TEquiv(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                b,
                session,
            )),
        ),
        Term::TMkEquiv(a, b, f, g, eta, eps) => Term::TMkEquiv(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                b,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                f,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                g,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                eta,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                eps,
                session,
            )),
        ),
        Term::TEquivFwd(e, x) => Term::TEquivFwd(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                e,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                x,
                session,
            )),
        ),
        Term::TUa(e) => Term::TUa(Arc::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            e,
            session,
        ))),
        Term::TTransport(p, x) => Term::TTransport(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                p,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                x,
                session,
            )),
        ),
        Term::TTransp(a, r, x) => Term::TTransp(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                r,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                x,
                session,
            )),
        ),
        Term::TGlue(a, phi, te) => Term::TGlue(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                phi,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                te,
                session,
            )),
        ),
        Term::TGlueElem(phi, t, a) => Term::TGlueElem(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                phi,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                t,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
        ),
        Term::TUnglue(phi, te, g) => Term::TUnglue(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                phi,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                te,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                g,
                session,
            )),
        ),
        Term::TPartial(phi, a) => Term::TPartial(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                phi,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
        ),
        Term::TSystemType(sys) => Term::TSystemType(
            sys.iter()
                .map(|(phi, a)| {
                    (
                        quote_case_body(size, globals, global_offset, env, go, phi, session),
                        quote_case_body(size, globals, global_offset, env, go, a, session),
                    )
                })
                .collect(),
        ),
        Term::TSigma(x, a, b) => Term::TSigma(
            x.clone(),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Arc::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::nvar(size))),
                go,
                b,
                session,
            )),
        ),
        Term::TPair(a, b) => Term::TPair(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                b,
                session,
            )),
        ),
        Term::TFst(p) => Term::TFst(Arc::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            p,
            session,
        ))),
        Term::TSnd(p) => Term::TSnd(Arc::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            p,
            session,
        ))),
        Term::TData(name, params) => Term::TData(
            name.clone(),
            params
                .iter()
                .map(|p| quote_case_body(size, globals, global_offset, env, go, p, session))
                .collect(),
        ),
        Term::TCon(data, con, args) => Term::TCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| quote_case_body(size, globals, global_offset, env, go, a, session))
                .collect(),
        ),
        Term::TPCon(data, con, args, r) => Term::TPCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| quote_case_body(size, globals, global_offset, env, go, a, session))
                .collect(),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                r,
                session,
            )),
        ),
        Term::TSqCon(data, con, args, r, s) => Term::TSqCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| quote_case_body(size, globals, global_offset, env, go, a, session))
                .collect(),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                r,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                s,
                session,
            )),
        ),
        Term::TCellCon(data, con, args, ivars) => Term::TCellCon(
            data.clone(),
            con.clone(),
            args.iter()
                .map(|a| quote_case_body(size, globals, global_offset, env, go, a, session))
                .collect(),
            ivars
                .iter()
                .map(|v| quote_case_body(size, globals, global_offset, env, go, v, session))
                .collect(),
        ),
        Term::TElim(motive, cases, scrut) => {
            let mut new_cases = Vec::with_capacity(cases.len());
            for case in cases {
                let extra = if case.as_name.is_some() { 1 } else { 0 };
                let nb = case.binders.len() + extra;
                let mut env2 = env.clone();
                for j in (0..nb).rev() {
                    env2 = env2.extend(Value::VNeutral(Neutral::nvar(size + j)));
                }
                new_cases.push(ElimCase {
                    con: case.con.clone(),
                    binders: case.binders.clone(),
                    body: Box::new(quote_case_body(
                        size + nb,
                        globals,
                        global_offset,
                        &env2,
                        go,
                        &case.body,
                        session,
                    )),
                    as_name: case.as_name.clone(),
                    record_bindings: case.record_bindings.clone(),
                    refinements: case.refinements.clone(),
                });
            }
            Term::TElim(
                Arc::new(quote_case_body(
                    size,
                    globals,
                    global_offset,
                    env,
                    go,
                    motive,
                    session,
                )),
                new_cases,
                Arc::new(quote_case_body(
                    size,
                    globals,
                    global_offset,
                    env,
                    go,
                    scrut,
                    session,
                )),
            )
        }
        Term::Meta(i) => Term::Meta(*i),
        Term::TBy(_) => panic!("TBy should be resolved before NbE"),
        Term::TDelay(a) => Term::TDelay(Arc::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TNext(a) => Term::TNext(Arc::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TForce(a) => Term::TForce(Arc::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TQuote(a) => Term::TQuote(Arc::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TUnquote(a) => Term::TUnquote(Arc::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TGetContext => Term::TGetContext,
        Term::TGetType(a) => Term::TGetType(Arc::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TUnify(a, bx) => Term::TUnify(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                bx,
                session,
            )),
        ),
        Term::TProj(field, r) => Term::TProj(
            field.clone(),
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                r,
                session,
            )),
        ),
        Term::TRecordUpdate(r, updates) => Term::TRecordUpdate(
            Arc::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                r,
                session,
            )),
            updates
                .iter()
                .map(|(f, e)| {
                    (
                        f.clone(),
                        quote_case_body(size, globals, global_offset, env, go, e, session),
                    )
                })
                .collect(),
        ),
    }
}

pub(super) fn quote_cases(
    size: usize,
    globals: &Globals,
    global_offset: usize,
    env: &Scope,
    go: usize,
    cases: Vec<ElimCase>,
    session: &mut Session,
) -> Vec<ElimCase> {
    cases
        .into_iter()
        .map(|case| {
            let extra = if case.as_name.is_some() { 1 } else { 0 };
            let nb = case.binders.len() + extra;
            let mut env2 = env.clone();
            for j in (0..nb).rev() {
                env2 = env2.extend(Value::VNeutral(Neutral::nvar(size + j)));
            }
            ElimCase {
                con: case.con,
                binders: case.binders.clone(),
                body: Box::new(quote_case_body(
                    size + nb,
                    globals,
                    global_offset,
                    &env2,
                    go,
                    &case.body,
                    session,
                )),
                as_name: case.as_name,
                record_bindings: case.record_bindings,
                refinements: case.refinements.clone(),
            }
        })
        .collect()
}

fn level_to_var(size: usize, level: usize) -> Term {
    if level < size {
        Term::TVar((size - level - 1) as i32)
    } else {
        Term::TVar(level.saturating_sub(size) as i32)
    }
}

// ---------------------------------------------------------------------------
// Metavariable store and helpers — delegated to session module
// ---------------------------------------------------------------------------
