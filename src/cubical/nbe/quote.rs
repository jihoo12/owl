//! Quoting: values back to normalised `Term`s.

use super::value::{Globals, Neutral, Scope, Value};
use crate::cubical::session::Session;
use crate::cubical::syntax::{ElimCase, System, Term};

/// Quoting can also diverge independently of `eval_nbe`: re-quoting a lambda
/// whose body re-references the same global value grows the quote recursion one
/// `TAbs` layer per cycle (`quote` -> `Closure::apply` -> `eval_nbe` -> `quote`),
/// while each `eval_nbe` call returns immediately. Cap the quote depth so such
/// values produce a finite (stuck) term instead of overflowing the stack. The
/// placeholder is an unbound `TVar(size)` (far beyond any real context), which
/// surfaces as an error downstream rather than silently passing. The cap must be
/// low enough to fit the debug-build stack frames on the smallest thread stack
/// the normalizer may run on (test threads default to 2 MiB).

const QUOTE_MAX_DEPTH: usize = 200;

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
            Box::new(quote(
                size + 1,
                globals,
                global_offset,
                clos.apply(Value::VNeutral(Neutral::NVar(size)), session),
                session,
            )),
        ),
        Value::VApp(f, a) => Term::TApp(
            Box::new(quote(size, globals, global_offset, *f, session)),
            Box::new(quote(size, globals, global_offset, *a, session)),
        ),
        Value::VPi(x, a, b) => Term::TPi(
            x,
            Box::new(quote(size, globals, global_offset, *a, session)),
            Box::new(quote(
                size + 1,
                globals,
                global_offset,
                b.apply(Value::VNeutral(Neutral::NVar(size)), session),
                session,
            )),
        ),
        Value::VSigma(x, a, b) => Term::TSigma(
            x,
            Box::new(quote(size, globals, global_offset, *a, session)),
            Box::new(quote(
                size + 1,
                globals,
                global_offset,
                b.apply(Value::VNeutral(Neutral::NVar(size)), session),
                session,
            )),
        ),
        Value::VPair(a, b) => Term::TPair(
            Box::new(quote(size, globals, global_offset, *a, session)),
            Box::new(quote(size, globals, global_offset, *b, session)),
        ),
        Value::VFst(p) => Term::TFst(Box::new(quote(size, globals, global_offset, *p, session))),
        Value::VSnd(p) => Term::TSnd(Box::new(quote(size, globals, global_offset, *p, session))),
        Value::VProj(field, r) => Term::TProj(
            field,
            Box::new(quote(size, globals, global_offset, *r, session)),
        ),
        Value::VRecordUpdate(r, updates) => Term::TRecordUpdate(
            Box::new(quote(size, globals, global_offset, *r, session)),
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
            Box::new(quote(size, globals, global_offset, *a, session)),
            Box::new(quote(size, globals, global_offset, *u, session)),
            Box::new(quote(size, globals, global_offset, *v, session)),
        ),
        Value::VPLam(x, clos) => Term::PLam(
            x,
            Box::new(quote(
                size + 1,
                globals,
                global_offset,
                clos.apply_i_var(size, session),
                session,
            )),
        ),
        Value::VPApp(p, r) => Term::PApp(
            Box::new(quote(size, globals, global_offset, *p, session)),
            Box::new(quote(size, globals, global_offset, *r, session)),
        ),
        Value::VUniv(n) => Term::TUniv(n),
        Value::VProp => Term::TProp,
        Value::VSSet => Term::TSSet,
        Value::VLift(a, lvl) => Term::TLift(
            Box::new(quote(size, globals, global_offset, *a, session)),
            lvl,
        ),
        Value::VLower(a) => {
            Term::TLower(Box::new(quote(size, globals, global_offset, *a, session)))
        }
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
            Box::new(quote(size, globals, global_offset, *r, session)),
        ),
        Value::VSqCon(d, c, args, r, s) => Term::TSqCon(
            d,
            c,
            args.into_iter()
                .map(|a| quote(size, globals, global_offset, a, session))
                .collect(),
            Box::new(quote(size, globals, global_offset, *r, session)),
            Box::new(quote(size, globals, global_offset, *s, session)),
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
            Box::new(quote(size, globals, global_offset, *motive, session)),
            quote_cases(size, globals, global_offset, &env, go, cases, session),
            Box::new(quote(size, globals, global_offset, *scrut, session)),
        ),
        Value::VGlue(a, phi, te) => Term::TGlue(
            Box::new(quote(size, globals, global_offset, *a, session)),
            Box::new(Term::TCube(phi)),
            Box::new(quote(size, globals, global_offset, *te, session)),
        ),
        Value::VPartial(a, phi) => Term::TPartial(
            Box::new(quote(size, globals, global_offset, *phi, session)),
            Box::new(quote(size, globals, global_offset, *a, session)),
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
            Box::new(Term::TCube(phi)),
            Box::new(quote(size, globals, global_offset, *t, session)),
            Box::new(quote(size, globals, global_offset, *a, session)),
        ),
        Value::VUnglue(phi, te, g) => Term::TUnglue(
            Box::new(Term::TCube(phi)),
            Box::new(quote(size, globals, global_offset, *te, session)),
            Box::new(quote(size, globals, global_offset, *g, session)),
        ),
        Value::VEquiv(a, b) => Term::TEquiv(
            Box::new(quote(size, globals, global_offset, *a, session)),
            Box::new(quote(size, globals, global_offset, *b, session)),
        ),
        Value::VMkEquiv(a, b, f, g, eta, eps) => Term::TMkEquiv(
            Box::new(quote(size, globals, global_offset, *a, session)),
            Box::new(quote(size, globals, global_offset, *b, session)),
            Box::new(quote(size, globals, global_offset, *f, session)),
            Box::new(quote(size, globals, global_offset, *g, session)),
            Box::new(quote(size, globals, global_offset, *eta, session)),
            Box::new(quote(size, globals, global_offset, *eps, session)),
        ),
        Value::VEquivFwd(e, x) => Term::TEquivFwd(
            Box::new(quote(size, globals, global_offset, *e, session)),
            Box::new(quote(size, globals, global_offset, *x, session)),
        ),
        Value::VUa(e) => Term::TUa(Box::new(quote(size, globals, global_offset, *e, session))),
        Value::VTransport(p, x) => Term::TTransport(
            Box::new(quote(size, globals, global_offset, *p, session)),
            Box::new(quote(size, globals, global_offset, *x, session)),
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
                Box::new(quote(size, globals, global_offset, *a, session)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base, session)),
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
                Box::new(quote(size, globals, global_offset, *a, session)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base, session)),
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
                Box::new(quote(size, globals, global_offset, *a, session)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base, session)),
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
                Box::new(quote(size, globals, global_offset, *a, session)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base, session)),
            )
        }
        Value::VDelay(a) => {
            Term::TDelay(Box::new(quote(size, globals, global_offset, *a, session)))
        }
        Value::VNext(a) => Term::TNext(Box::new(quote(size, globals, global_offset, *a, session))),
        Value::VForce(a) => {
            Term::TForce(Box::new(quote(size, globals, global_offset, *a, session)))
        }
    }
}

fn quote_neutral(
    size: usize,
    globals: &Globals,
    global_offset: usize,
    n: Neutral,
    session: &mut Session,
) -> Term {
    match n {
        Neutral::NVar(level) => level_to_var(size, level),
        Neutral::NApp(f, a) => Term::TApp(
            Box::new(quote_neutral(size, globals, global_offset, *f, session)),
            Box::new(quote(size, globals, global_offset, *a, session)),
        ),
        Neutral::NPApp(p, r) => Term::PApp(
            Box::new(quote_neutral(size, globals, global_offset, *p, session)),
            Box::new(quote(size, globals, global_offset, *r, session)),
        ),
        Neutral::NSqApp(p, r, s) => {
            let pq = quote_neutral(size, globals, global_offset, *p, session);
            let rq = quote(size, globals, global_offset, *r, session);
            let sq = quote(size, globals, global_offset, *s, session);
            Term::PApp(
                Box::new(Term::PApp(Box::new(pq), Box::new(rq))),
                Box::new(sq),
            )
        }
        Neutral::NCellApp(p, ivars) => {
            let mut result = quote_neutral(size, globals, global_offset, *p, session);
            for iv in ivars.into_iter().rev() {
                result = Term::PApp(
                    Box::new(result),
                    Box::new(quote(size, globals, global_offset, iv, session)),
                );
            }
            result
        }
        Neutral::NFst(p) => Term::TFst(Box::new(quote_neutral(
            size,
            globals,
            global_offset,
            *p,
            session,
        ))),
        Neutral::NSnd(p) => Term::TSnd(Box::new(quote_neutral(
            size,
            globals,
            global_offset,
            *p,
            session,
        ))),
        Neutral::NElim(motive, cases, scrut, env, go) => Term::TElim(
            Box::new(quote(size, globals, global_offset, *motive, session)),
            quote_cases(size, globals, global_offset, &env, go, cases, session),
            Box::new(quote_neutral(size, globals, global_offset, *scrut, session)),
        ),
        Neutral::NTransport(p, x) => Term::TTransport(
            Box::new(quote(size, globals, global_offset, *p, session)),
            Box::new(quote(size, globals, global_offset, *x, session)),
        ),
        Neutral::NHComp(a, sys, base) => {
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
                Box::new(quote(size, globals, global_offset, *a, session)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base, session)),
            )
        }
        Neutral::NComp(a, sys, base) => {
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
                Box::new(quote(size, globals, global_offset, *a, session)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base, session)),
            )
        }
        Neutral::NFill(a, sys, base) => {
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
                Box::new(quote(size, globals, global_offset, *a, session)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base, session)),
            )
        }
        Neutral::NHFill(a, sys, base) => {
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
                Box::new(quote(size, globals, global_offset, *a, session)),
                sys_term,
                Box::new(quote(size, globals, global_offset, *base, session)),
            )
        }
        Neutral::NMeta(i) => Term::Meta(i),
        Neutral::NForce(n) => Term::TForce(Box::new(quote_neutral(
            size,
            globals,
            global_offset,
            *n,
            session,
        ))),
        Neutral::NProj(n, field) => Term::TProj(
            field,
            Box::new(quote_neutral(size, globals, global_offset, *n, session)),
        ),
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
                        Box::new(quote_case_body(
                            size + 1,
                            globals,
                            global_offset,
                            &clos.env.extend(Value::VNeutral(Neutral::NVar(size))),
                            clos.global_offset,
                            &clos.body,
                            session,
                        )),
                    ),
                    Value::VPLam(x, clos) => Term::PLam(
                        x.clone(),
                        Box::new(quote_case_body(
                            size + 1,
                            globals,
                            global_offset,
                            &clos.env.extend(Value::VIntervalVar(size)),
                            clos.global_offset,
                            &clos.body,
                            session,
                        )),
                    ),
                    _ => quote(size, globals, global_offset, v.clone(), session),
                }
            } else {
                Term::TVar((size + go + i - env.len()) as i32)
            }
        }
        Term::TApp(f, a) => Term::TApp(
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                f,
                session,
            )),
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::NVar(size))),
                go,
                b,
                session,
            )),
        ),
        Term::TUniv(n) => Term::TUniv(*n),
        Term::TProp => Term::TProp,
        Term::TSSet => Term::TSSet,
        Term::TLift(a, lvl) => Term::TLift(
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            *lvl,
        ),
        Term::TLower(a) => Term::TLower(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TIntervalTy => Term::TIntervalTy,
        Term::TPi(x, a, b) => Term::TPi(
            x.clone(),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Box::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::NVar(size))),
                go,
                b,
                session,
            )),
        ),
        Term::TInterval(i) => Term::TInterval(i.clone()),
        Term::TCube(c) => Term::TCube(c.clone()),
        Term::TPath(a, u, v) => Term::TPath(
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                u,
                session,
            )),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                v,
                session,
            )),
        ),
        Term::PLam(x, b) => Term::PLam(
            x.clone(),
            Box::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::NVar(size))),
                go,
                b,
                session,
            )),
        ),
        Term::PApp(p, r) => Term::PApp(
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                p,
                session,
            )),
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                b,
                session,
            )),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                f,
                session,
            )),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                g,
                session,
            )),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                eta,
                session,
            )),
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                e,
                session,
            )),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                x,
                session,
            )),
        ),
        Term::TUa(e) => Term::TUa(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            e,
            session,
        ))),
        Term::TTransport(p, x) => Term::TTransport(
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                p,
                session,
            )),
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                phi,
                session,
            )),
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                phi,
                session,
            )),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                t,
                session,
            )),
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                phi,
                session,
            )),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                te,
                session,
            )),
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                phi,
                session,
            )),
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Box::new(quote_case_body(
                size + 1,
                globals,
                global_offset,
                &env.extend(Value::VNeutral(Neutral::NVar(size))),
                go,
                b,
                session,
            )),
        ),
        Term::TPair(a, b) => Term::TPair(
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                a,
                session,
            )),
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                b,
                session,
            )),
        ),
        Term::TFst(p) => Term::TFst(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            p,
            session,
        ))),
        Term::TSnd(p) => Term::TSnd(Box::new(quote_case_body(
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
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
                size,
                globals,
                global_offset,
                env,
                go,
                r,
                session,
            )),
            Box::new(quote_case_body(
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
                    env2 = env2.extend(Value::VNeutral(Neutral::NVar(size + j)));
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
                Box::new(quote_case_body(
                    size,
                    globals,
                    global_offset,
                    env,
                    go,
                    motive,
                    session,
                )),
                new_cases,
                Box::new(quote_case_body(
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
        Term::TDelay(a) => Term::TDelay(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TNext(a) => Term::TNext(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TForce(a) => Term::TForce(Box::new(quote_case_body(
            size,
            globals,
            global_offset,
            env,
            go,
            a,
            session,
        ))),
        Term::TProj(field, r) => Term::TProj(
            field.clone(),
            Box::new(quote_case_body(
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
            Box::new(quote_case_body(
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
                env2 = env2.extend(Value::VNeutral(Neutral::NVar(size + j)));
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
