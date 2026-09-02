//! Metavariable helpers over terms: occurrence check, solving, zonking and
//! unsolved-meta collection. The metavariable store itself lives in
//! `crate::cubical::session`.

use crate::cubical::session::{Session, get_meta_solution};
use crate::cubical::syntax::Term;
use std::sync::Arc;

pub fn meta_mentions(id: i32, t: &Term) -> bool {
    match t {
        Term::Meta(j) => *j == id,
        Term::TVar(_)
        | Term::TUniv(_)
        | Term::TProp
        | Term::TSSet
        | Term::TIntervalTy
        | Term::TLevelTy
        | Term::TInterval(_)
        | Term::TCube(_) => false,
        Term::TApp(f, a) => meta_mentions(id, f) || meta_mentions(id, a),
        Term::TAbs(_, b) | Term::PLam(_, b) => meta_mentions(id, b),
        Term::TPi(_, a, b, _) | Term::TSigma(_, a, b) => {
            meta_mentions(id, a) || meta_mentions(id, b)
        }
        Term::TPath(a, u, v) => {
            meta_mentions(id, a) || meta_mentions(id, u) || meta_mentions(id, v)
        }
        Term::TId(a, u, v) => meta_mentions(id, a) || meta_mentions(id, u) || meta_mentions(id, v),
        Term::TRefl(a) => meta_mentions(id, a),
        Term::TJ(motive, base, p) => {
            meta_mentions(id, motive) || meta_mentions(id, base) || meta_mentions(id, p)
        }
        Term::PApp(p, r) => meta_mentions(id, p) || meta_mentions(id, r),
        Term::THComp(a, sys, base)
        | Term::TComp(a, sys, base)
        | Term::TFill(a, sys, base)
        | Term::THFill(a, sys, base) => {
            meta_mentions(id, a)
                || meta_mentions(id, base)
                || sys
                    .iter()
                    .any(|(phi, tube)| meta_mentions(id, phi) || meta_mentions(id, tube))
        }
        Term::TEquiv(a, b) => meta_mentions(id, a) || meta_mentions(id, b),
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            meta_mentions(id, a)
                || meta_mentions(id, b)
                || meta_mentions(id, f)
                || meta_mentions(id, g)
                || meta_mentions(id, eta)
                || meta_mentions(id, eps)
        }
        Term::TEquivFwd(e, x) | Term::TTransport(e, x) => {
            meta_mentions(id, e) || meta_mentions(id, x)
        }
        Term::TTransp(a, r, x) => {
            meta_mentions(id, a) || meta_mentions(id, r) || meta_mentions(id, x)
        }
        Term::TUa(e) => meta_mentions(id, e),
        Term::TGlue(a, phi, te) => {
            meta_mentions(id, a) || meta_mentions(id, phi) || meta_mentions(id, te)
        }
        Term::TGlueElem(phi, t, a) => {
            meta_mentions(id, phi) || meta_mentions(id, t) || meta_mentions(id, a)
        }
        Term::TUnglue(phi, te, g) => {
            meta_mentions(id, phi) || meta_mentions(id, te) || meta_mentions(id, g)
        }
        Term::TPartial(phi, a) => meta_mentions(id, phi) || meta_mentions(id, a),
        Term::TSystemType(sys) => sys
            .iter()
            .any(|(phi, a)| meta_mentions(id, phi) || meta_mentions(id, a)),
        Term::TPair(a, b) => meta_mentions(id, a) || meta_mentions(id, b),
        Term::TFst(p)
        | Term::TSnd(p)
        | Term::TProj(_, p)
        | Term::TLift(p, _)
        | Term::TLower(p)
        | Term::TDelay(p)
        | Term::TNext(p)
        | Term::TForce(p) => meta_mentions(id, p),
        Term::TRecordUpdate(r, updates) => {
            meta_mentions(id, r) || updates.iter().any(|(_, e)| meta_mentions(id, e))
        }
        Term::TData(_, params) => params.iter().any(|p| meta_mentions(id, p)),
        Term::TCon(_, _, args) => args.iter().any(|a| meta_mentions(id, a)),
        Term::TPCon(_, _, args, r) => {
            args.iter().any(|a| meta_mentions(id, a)) || meta_mentions(id, r)
        }
        Term::TSqCon(_, _, args, r, s) => {
            args.iter().any(|a| meta_mentions(id, a))
                || meta_mentions(id, r)
                || meta_mentions(id, s)
        }
        Term::TCellCon(_, _, args, ivars) => {
            args.iter().any(|a| meta_mentions(id, a)) || ivars.iter().any(|v| meta_mentions(id, v))
        }
        Term::TElim(motive, cases, scrut) => {
            meta_mentions(id, motive)
                || meta_mentions(id, scrut)
                || cases.iter().any(|c| meta_mentions(id, &c.body))
        }
        Term::TBy(_) => false,
    }
}

pub fn try_solve_meta(id: i32, rhs: &Term, session: &mut Session) -> bool {
    if id < 0 {
        return false;
    }
    if session.get_meta_solution(id).is_some() {
        return true;
    }
    if meta_mentions(id, rhs) {
        return false;
    }
    session.solve_meta(id, rhs.clone());
    true
}

pub fn zonk(t: &Term, session: &Session) -> Term {
    fn zonk_inner(term: &Term, session: &Session) -> Term {
        match term {
            Term::Meta(i) => {
                if let Some(solution) = session.get_meta_solution(*i) {
                    solution.clone()
                } else {
                    term.clone()
                }
            }
            Term::TVar(_)
            | Term::TUniv(_)
            | Term::TProp
            | Term::TSSet
            | Term::TIntervalTy
            | Term::TLevelTy
            | Term::TInterval(_)
            | Term::TCube(_)
            | Term::TBy(_) => term.clone(),
            Term::TApp(f, a) => Term::TApp(
                Arc::new(zonk_inner(f, session)),
                Arc::new(zonk_inner(a, session)),
            ),
            Term::TAbs(n, b) | Term::PLam(n, b) => {
                let ctor = match term {
                    Term::TAbs(_, _) => Term::TAbs,
                    _ => Term::PLam,
                };
                ctor(n.clone(), Arc::new(zonk_inner(b, session)))
            }
            Term::TPi(n, a, b, bc) => Term::TPi(
                n.clone(),
                Arc::new(zonk_inner(a, session)),
                Arc::new(zonk_inner(b, session)),
                *bc,
            ),
            Term::TSigma(n, a, b) => Term::TSigma(
                n.clone(),
                Arc::new(zonk_inner(a, session)),
                Arc::new(zonk_inner(b, session)),
            ),
            Term::TPath(a, u, v) => Term::TPath(
                Arc::new(zonk_inner(a, session)),
                Arc::new(zonk_inner(u, session)),
                Arc::new(zonk_inner(v, session)),
            ),
            Term::TId(a, u, v) => Term::TId(
                Arc::new(zonk_inner(a, session)),
                Arc::new(zonk_inner(u, session)),
                Arc::new(zonk_inner(v, session)),
            ),
            Term::TRefl(a) => Term::TRefl(Arc::new(zonk_inner(a, session))),
            Term::TJ(motive, base, p) => Term::TJ(
                Arc::new(zonk_inner(motive, session)),
                Arc::new(zonk_inner(base, session)),
                Arc::new(zonk_inner(p, session)),
            ),
            Term::PApp(p, r) => Term::PApp(
                Arc::new(zonk_inner(p, session)),
                Arc::new(zonk_inner(r, session)),
            ),
            Term::THComp(a, sys, base) => Term::THComp(
                Arc::new(zonk_inner(a, session)),
                zonk_sys(sys, session),
                Arc::new(zonk_inner(base, session)),
            ),
            Term::TComp(a, sys, base) => Term::TComp(
                Arc::new(zonk_inner(a, session)),
                zonk_sys(sys, session),
                Arc::new(zonk_inner(base, session)),
            ),
            Term::TFill(a, sys, base) => Term::TFill(
                Arc::new(zonk_inner(a, session)),
                zonk_sys(sys, session),
                Arc::new(zonk_inner(base, session)),
            ),
            Term::THFill(a, sys, base) => Term::THFill(
                Arc::new(zonk_inner(a, session)),
                zonk_sys(sys, session),
                Arc::new(zonk_inner(base, session)),
            ),
            Term::TEquiv(a, b) => Term::TEquiv(
                Arc::new(zonk_inner(a, session)),
                Arc::new(zonk_inner(b, session)),
            ),
            Term::TMkEquiv(a, b, f, g, eta, eps) => Term::TMkEquiv(
                Arc::new(zonk_inner(a, session)),
                Arc::new(zonk_inner(b, session)),
                Arc::new(zonk_inner(f, session)),
                Arc::new(zonk_inner(g, session)),
                Arc::new(zonk_inner(eta, session)),
                Arc::new(zonk_inner(eps, session)),
            ),
            Term::TEquivFwd(e, x) => Term::TEquivFwd(
                Arc::new(zonk_inner(e, session)),
                Arc::new(zonk_inner(x, session)),
            ),
            Term::TTransport(e, x) => Term::TTransport(
                Arc::new(zonk_inner(e, session)),
                Arc::new(zonk_inner(x, session)),
            ),
            Term::TTransp(a, r, x) => Term::TTransp(
                Arc::new(zonk_inner(a, session)),
                Arc::new(zonk_inner(r, session)),
                Arc::new(zonk_inner(x, session)),
            ),
            Term::TUa(e) => Term::TUa(Arc::new(zonk_inner(e, session))),
            Term::TGlue(a, phi, te) => Term::TGlue(
                Arc::new(zonk_inner(a, session)),
                Arc::new(zonk_inner(phi, session)),
                Arc::new(zonk_inner(te, session)),
            ),
            Term::TGlueElem(phi, t, a) => Term::TGlueElem(
                Arc::new(zonk_inner(phi, session)),
                Arc::new(zonk_inner(t, session)),
                Arc::new(zonk_inner(a, session)),
            ),
            Term::TUnglue(phi, te, g) => Term::TUnglue(
                Arc::new(zonk_inner(phi, session)),
                Arc::new(zonk_inner(te, session)),
                Arc::new(zonk_inner(g, session)),
            ),
            Term::TPartial(phi, a) => Term::TPartial(
                Arc::new(zonk_inner(phi, session)),
                Arc::new(zonk_inner(a, session)),
            ),
            Term::TSystemType(sys) => Term::TSystemType(zonk_sys(sys, session)),
            Term::TPair(a, b) => Term::TPair(
                Arc::new(zonk_inner(a, session)),
                Arc::new(zonk_inner(b, session)),
            ),
            Term::TFst(p) => Term::TFst(Arc::new(zonk_inner(p, session))),
            Term::TSnd(p) => Term::TSnd(Arc::new(zonk_inner(p, session))),
            Term::TProj(n, p) => Term::TProj(n.clone(), Arc::new(zonk_inner(p, session))),
            Term::TLift(p, n) => Term::TLift(Arc::new(zonk_inner(p, session)), n.clone()),
            Term::TLower(p) => Term::TLower(Arc::new(zonk_inner(p, session))),
            Term::TDelay(p) => Term::TDelay(Arc::new(zonk_inner(p, session))),
            Term::TNext(p) => Term::TNext(Arc::new(zonk_inner(p, session))),
            Term::TForce(p) => Term::TForce(Arc::new(zonk_inner(p, session))),
            Term::TRecordUpdate(r, updates) => Term::TRecordUpdate(
                Arc::new(zonk_inner(r, session)),
                updates
                    .iter()
                    .map(|(n, e)| (n.clone(), zonk_inner(e, session)))
                    .collect(),
            ),
            Term::TData(n, params) => Term::TData(
                n.clone(),
                params.iter().map(|p| zonk_inner(p, session)).collect(),
            ),
            Term::TCon(n, idx, args) => Term::TCon(
                n.clone(),
                idx.clone(),
                args.iter().map(|a| zonk_inner(a, session)).collect(),
            ),
            Term::TPCon(n, idx, args, r) => Term::TPCon(
                n.clone(),
                idx.clone(),
                args.iter().map(|a| zonk_inner(a, session)).collect(),
                Arc::new(zonk_inner(r, session)),
            ),
            Term::TSqCon(n, idx, args, r, s) => Term::TSqCon(
                n.clone(),
                idx.clone(),
                args.iter().map(|a| zonk_inner(a, session)).collect(),
                Arc::new(zonk_inner(r, session)),
                Arc::new(zonk_inner(s, session)),
            ),
            Term::TCellCon(n, idx, args, ivars) => Term::TCellCon(
                n.clone(),
                idx.clone(),
                args.iter().map(|a| zonk_inner(a, session)).collect(),
                ivars.iter().map(|v| zonk_inner(v, session)).collect(),
            ),
            Term::TElim(motive, cases, scrut) => Term::TElim(
                Arc::new(zonk_inner(motive, session)),
                cases
                    .iter()
                    .map(|c| {
                        let mut zonked = c.clone();
                        zonked.body = Box::new(zonk_inner(&c.body, session));
                        zonked
                    })
                    .collect(),
                Arc::new(zonk_inner(scrut, session)),
            ),
        }
    }
    fn zonk_sys(
        sys: &crate::cubical::syntax::System,
        session: &Session,
    ) -> crate::cubical::syntax::System {
        sys.iter()
            .map(|(phi, tube)| (zonk_inner(phi, session), zonk_inner(tube, session)))
            .collect()
    }
    zonk_inner(t, session)
}

pub(super) fn has_meta_in_term(t: &Term) -> bool {
    match t {
        Term::Meta(_) => true,
        _ => {
            let children = term_children_ref(t);
            children.into_iter().any(has_meta_in_term)
        }
    }
}

fn term_children_ref(t: &Term) -> Vec<&Term> {
    match t {
        Term::TVar(_)
        | Term::TUniv(_)
        | Term::TProp
        | Term::TSSet
        | Term::TIntervalTy
        | Term::TLevelTy
        | Term::TInterval(_)
        | Term::TCube(_)
        | Term::Meta(_) => vec![],
        Term::TApp(f, a) => vec![f.as_ref(), a.as_ref()],
        Term::TAbs(_, b) | Term::PLam(_, b) => vec![b.as_ref()],
        Term::TPi(_, a, b, _) | Term::TSigma(_, a, b) => vec![a.as_ref(), b.as_ref()],
        Term::TPath(a, u, v) => vec![a.as_ref(), u.as_ref(), v.as_ref()],
        Term::TId(a, u, v) => vec![a.as_ref(), u.as_ref(), v.as_ref()],
        Term::TRefl(a) => vec![a.as_ref()],
        Term::TJ(motive, base, p) => vec![motive.as_ref(), base.as_ref(), p.as_ref()],
        Term::PApp(p, r) => vec![p.as_ref(), r.as_ref()],
        Term::THComp(a, sys, base)
        | Term::TComp(a, sys, base)
        | Term::TFill(a, sys, base)
        | Term::THFill(a, sys, base) => {
            let mut children = vec![a.as_ref(), base.as_ref()];
            for (phi, tube) in sys {
                children.push(phi);
                children.push(tube);
            }
            children
        }
        Term::TEquiv(a, b) => vec![a.as_ref(), b.as_ref()],
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            vec![
                a.as_ref(),
                b.as_ref(),
                f.as_ref(),
                g.as_ref(),
                eta.as_ref(),
                eps.as_ref(),
            ]
        }
        Term::TEquivFwd(e, x) | Term::TTransport(e, x) => vec![e.as_ref(), x.as_ref()],
        Term::TTransp(a, r, x) => vec![a.as_ref(), r.as_ref(), x.as_ref()],
        Term::TUa(e) => vec![e.as_ref()],
        Term::TGlue(a, phi, te) => vec![a.as_ref(), phi.as_ref(), te.as_ref()],
        Term::TGlueElem(phi, t, a) => vec![phi.as_ref(), t.as_ref(), a.as_ref()],
        Term::TUnglue(phi, te, g) => vec![phi.as_ref(), te.as_ref(), g.as_ref()],
        Term::TPartial(phi, a) => vec![phi.as_ref(), a.as_ref()],
        Term::TSystemType(sys) => sys
            .iter()
            .flat_map(|(phi, a)| vec![phi as &Term, a as &Term])
            .collect(),
        Term::TPair(a, b) => vec![a.as_ref(), b.as_ref()],
        Term::TFst(p)
        | Term::TSnd(p)
        | Term::TProj(_, p)
        | Term::TLift(p, _)
        | Term::TLower(p)
        | Term::TDelay(p)
        | Term::TNext(p)
        | Term::TForce(p) => vec![p.as_ref()],
        Term::TRecordUpdate(r, updates) => {
            let mut children: Vec<&Term> = vec![r.as_ref()];
            for (_, e) in updates.iter() {
                children.push(e);
            }
            children
        }
        Term::TData(_, params) => params.iter().collect(),
        Term::TCon(_, _, args) => args.iter().collect(),
        Term::TPCon(_, _, args, r) => {
            let mut children: Vec<&Term> = args.iter().collect();
            children.push(r.as_ref());
            children
        }
        Term::TSqCon(_, _, args, r, s) => {
            let mut children: Vec<&Term> = args.iter().collect();
            children.push(r.as_ref());
            children.push(s.as_ref());
            children
        }
        Term::TCellCon(_, _, args, ivars) => {
            let mut children: Vec<&Term> = args.iter().collect();
            children.extend(ivars.iter());
            children
        }
        Term::TElim(motive, cases, scrut) => {
            let mut children = vec![motive.as_ref(), scrut.as_ref()];
            for case in cases {
                children.push(case.body.as_ref());
            }
            children
        }
        Term::TBy(_) => vec![],
    }
}

/// Collect the ids of every unsolved hole (`Term::Meta` with no solution)
/// appearing in `t`.
pub fn collect_unsolved_metas(t: &Term) -> Vec<i32> {
    fn walk(t: &Term, out: &mut Vec<i32>) {
        match t {
            Term::Meta(i) => {
                if get_meta_solution(*i).is_none() && !out.contains(i) {
                    out.push(*i);
                }
            }
            _ => {
                for child in term_children_ref(t) {
                    walk(child, out);
                }
            }
        }
    }
    let mut out = Vec::new();
    walk(t, &mut out);
    out
}
