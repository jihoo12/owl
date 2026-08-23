//! Metavariable helpers over terms: occurrence check, solving, zonking and
//! unsolved-meta collection. The metavariable store itself lives in
//! `crate::cubical::session`.

use crate::cubical::session::{Session, get_meta_solution};
use crate::cubical::syntax::Term;

pub fn meta_mentions(id: i32, t: &Term) -> bool {
    match t {
        Term::Meta(j) => *j == id,
        Term::TVar(_)
        | Term::TUniv(_)
        | Term::TProp
        | Term::TSSet
        | Term::TIntervalTy
        | Term::TInterval(_)
        | Term::TCube(_) => false,
        Term::TApp(f, a) => meta_mentions(id, f) || meta_mentions(id, a),
        Term::TAbs(_, b) | Term::PLam(_, b) => meta_mentions(id, b),
        Term::TPi(_, a, b) | Term::TSigma(_, a, b) => meta_mentions(id, a) || meta_mentions(id, b),
        Term::TPath(a, u, v) => {
            meta_mentions(id, a) || meta_mentions(id, u) || meta_mentions(id, v)
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
    match t {
        Term::Meta(i) => {
            if let Some(solution) = session.get_meta_solution(*i) {
                solution
            } else {
                t.clone()
            }
        }
        _ => {
            let mut cloned = t.clone();
            fn zonk_sub(term: &mut Term, session: &Session) {
                match term {
                    Term::Meta(i) => {
                        if let Some(solution) = session.get_meta_solution(*i) {
                            *term = solution;
                        }
                    }
                    _ => {
                        let children = term_children_mut(term);
                        for child in children {
                            zonk_sub(child, session);
                        }
                    }
                }
            }
            zonk_sub(&mut cloned, session);
            cloned
        }
    }
}

fn term_children_mut(t: &mut Term) -> Vec<&mut Term> {
    match t {
        Term::TVar(_)
        | Term::TUniv(_)
        | Term::TProp
        | Term::TSSet
        | Term::TIntervalTy
        | Term::TInterval(_)
        | Term::TCube(_)
        | Term::Meta(_) => vec![],
        Term::TApp(f, a) => vec![f.as_mut(), a.as_mut()],
        Term::TAbs(_, b) | Term::PLam(_, b) => vec![b.as_mut()],
        Term::TPi(_, a, b) | Term::TSigma(_, a, b) => vec![a.as_mut(), b.as_mut()],
        Term::TPath(a, u, v) => vec![a.as_mut(), u.as_mut(), v.as_mut()],
        Term::PApp(p, r) => vec![p.as_mut(), r.as_mut()],
        Term::THComp(a, sys, base)
        | Term::TComp(a, sys, base)
        | Term::TFill(a, sys, base)
        | Term::THFill(a, sys, base) => {
            let mut children = vec![a.as_mut(), base.as_mut()];
            for (phi, tube) in sys.iter_mut() {
                children.push(phi);
                children.push(tube);
            }
            children
        }
        Term::TEquiv(a, b) => vec![a.as_mut(), b.as_mut()],
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            vec![
                a.as_mut(),
                b.as_mut(),
                f.as_mut(),
                g.as_mut(),
                eta.as_mut(),
                eps.as_mut(),
            ]
        }
        Term::TEquivFwd(e, x) | Term::TTransport(e, x) => vec![e.as_mut(), x.as_mut()],
        Term::TUa(e) => vec![e.as_mut()],
        Term::TGlue(a, phi, te) => vec![a.as_mut(), phi.as_mut(), te.as_mut()],
        Term::TGlueElem(phi, t, a) => vec![phi.as_mut(), t.as_mut(), a.as_mut()],
        Term::TUnglue(phi, te, g) => vec![phi.as_mut(), te.as_mut(), g.as_mut()],
        Term::TPartial(phi, a) => vec![phi.as_mut(), a.as_mut()],
        Term::TSystemType(sys) => sys
            .iter_mut()
            .flat_map(|(phi, a)| vec![phi as &mut Term, a as &mut Term])
            .collect(),
        Term::TPair(a, b) => vec![a.as_mut(), b.as_mut()],
        Term::TFst(p)
        | Term::TSnd(p)
        | Term::TLift(p, _)
        | Term::TLower(p)
        | Term::TDelay(p)
        | Term::TNext(p)
        | Term::TForce(p) => vec![p.as_mut()],
        Term::TProj(_, p) => vec![p.as_mut()],
        Term::TRecordUpdate(r, updates) => {
            let mut children: Vec<&mut Term> = vec![r.as_mut()];
            for (_, e) in updates.iter_mut() {
                children.push(e);
            }
            children
        }
        Term::TData(_, params) => params.iter_mut().collect(),
        Term::TCon(_, _, args) => args.iter_mut().collect(),
        Term::TPCon(_, _, args, r) => {
            let mut children: Vec<&mut Term> = args.iter_mut().collect();
            children.push(r.as_mut());
            children
        }
        Term::TSqCon(_, _, args, r, s) => {
            let mut children: Vec<&mut Term> = args.iter_mut().collect();
            children.push(r.as_mut());
            children.push(s.as_mut());
            children
        }
        Term::TCellCon(_, _, args, ivars) => {
            let mut children: Vec<&mut Term> = args.iter_mut().collect();
            children.extend(ivars.iter_mut());
            children
        }
        Term::TElim(motive, cases, scrut) => {
            let mut children = vec![motive.as_mut(), scrut.as_mut()];
            for case in cases.iter_mut() {
                children.push(case.body.as_mut());
            }
            children
        }
        Term::TBy(_) => vec![],
    }
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
        | Term::TInterval(_)
        | Term::TCube(_)
        | Term::Meta(_) => vec![],
        Term::TApp(f, a) => vec![f.as_ref(), a.as_ref()],
        Term::TAbs(_, b) | Term::PLam(_, b) => vec![b.as_ref()],
        Term::TPi(_, a, b) | Term::TSigma(_, a, b) => vec![a.as_ref(), b.as_ref()],
        Term::TPath(a, u, v) => vec![a.as_ref(), u.as_ref(), v.as_ref()],
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
