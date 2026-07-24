//! Pretty-printing for terms, tactics, and related syntax.

use std::fmt;

use super::{Datatype, Name, Tactic, Term};

pub fn nat_to_int(t: &Term) -> Option<i64> {
    match t {
        Term::TCon(d, c, args) if d == "Nat" => match (c.as_str(), args.as_slice()) {
            ("zero", []) => Some(0),
            ("suc", [arg]) => nat_to_int(arg).map(|n| n + 1),
            _ => None,
        },
        _ => None,
    }
}

pub fn show_term(env: &[Name], t: &Term) -> String {
    match t {
        Term::TVar(i) => {
            let i = *i as usize;
            if i < env.len() {
                env[i].clone()
            } else {
                format!("#{}", i)
            }
        }
        Term::TApp(f, a) => format!("({} {})", show_term(env, f), show_term(env, a)),
        Term::TAbs(x, b) => {
            let mut env2 = vec![x.clone()];
            env2.extend_from_slice(env);
            format!("fun {} => {}", x, show_term(&env2, b))
        }
        Term::TUniv(n) => format!("U{}", n),
        Term::TIntervalTy => "I".to_string(),
        Term::TPi(x, a, b) => {
            let mut env2 = vec![x.clone()];
            env2.extend_from_slice(env);
            format!(
                "forall ({} : {}), {}",
                x,
                show_term(env, a),
                show_term(&env2, b)
            )
        }
        Term::TInterval(i) => format!("{}", i),
        Term::TCube(c) => format!("{}", c),
        Term::TPath(a, u, v) => format!(
            "Path {} {} {}",
            show_term(env, a),
            show_term(env, u),
            show_term(env, v)
        ),
        Term::PLam(i, b) => {
            let mut env2 = vec![i.clone()];
            env2.extend_from_slice(env);
            format!("<{}> {}", i, show_term(&env2, b))
        }
        Term::PApp(p, r) => format!("{} @ {}", show_term(env, p), show_term(env, r)),
        Term::THComp(a, sys, u0) => {
            let sys_str: Vec<String> = sys
                .iter()
                .map(|(phi, t)| format!("{} -> {}", show_term(env, phi), show_term(env, t)))
                .collect();
            format!(
                "hcomp {} [{}] {}",
                show_term(env, a),
                sys_str.join(", "),
                show_term(env, u0)
            )
        }
        Term::TComp(a, sys, u0) => {
            let sys_str: Vec<String> = sys
                .iter()
                .map(|(phi, t)| format!("{} -> {}", show_term(env, phi), show_term(env, t)))
                .collect();
            format!(
                "comp {} [{}] {}",
                show_term(env, a),
                sys_str.join(", "),
                show_term(env, u0)
            )
        }
        Term::TFill(a, sys, u0) => {
            let sys_str: Vec<String> = sys
                .iter()
                .map(|(phi, t)| format!("{} -> {}", show_term(env, phi), show_term(env, t)))
                .collect();
            format!(
                "fill {} [{}] {}",
                show_term(env, a),
                sys_str.join(", "),
                show_term(env, u0)
            )
        }
        Term::THFill(a, sys, u0) => {
            let sys_str: Vec<String> = sys
                .iter()
                .map(|(phi, t)| format!("{} -> {}", show_term(env, phi), show_term(env, t)))
                .collect();
            format!(
                "hfill {} [{}] {}",
                show_term(env, a),
                sys_str.join(", "),
                show_term(env, u0)
            )
        }
        Term::TEquiv(a, b) => format!("Equiv {} {}", show_term(env, a), show_term(env, b)),
        Term::TMkEquiv(a, b, f, g, eta, eps) => format!(
            "mkEquiv {} {} {} {} {} {}",
            show_term(env, a),
            show_term(env, b),
            show_term(env, f),
            show_term(env, g),
            show_term(env, eta),
            show_term(env, eps)
        ),
        Term::TEquivFwd(e, x) => {
            format!("equivFwd ({}) {}", show_term(env, e), show_term(env, x))
        }
        Term::TUa(e) => format!("ua ({})", show_term(env, e)),
        Term::TTransport(p, x) => {
            format!("transport ({}) {}", show_term(env, p), show_term(env, x))
        }
        Term::TGlue(a, phi, te) => format!(
            "Glue {} [{}] ({})",
            show_term(env, a),
            show_term(env, phi),
            show_term(env, te)
        ),
        Term::TGlueElem(phi, t, a) => format!(
            "glue [{}] ({}) {}",
            show_term(env, phi),
            show_term(env, t),
            show_term(env, a)
        ),
        Term::TUnglue(phi, te, g) => format!(
            "unglue [{}] ({}) {}",
            show_term(env, phi),
            show_term(env, te),
            show_term(env, g)
        ),
        Term::TSigma(x, a, b) => {
            let mut env2 = vec![x.clone()];
            env2.extend_from_slice(env);
            format!(
                "Sigma ({} : {}), {}",
                x,
                show_term(env, a),
                show_term(&env2, b)
            )
        }
        Term::TPair(a, b) => format!("({} , {})", show_term(env, a), show_term(env, b)),
        Term::TFst(p) => format!("fst {}", show_term(env, p)),
        Term::TSnd(p) => format!("snd {}", show_term(env, p)),
        Term::TData(d, params) => {
            if params.is_empty() {
                d.clone()
            } else {
                let parts: Vec<String> = params.iter().map(|p| show_term(env, p)).collect();
                format!("({} {})", d, parts.join(" "))
            }
        }
        t @ Term::TCon(_, c, args) => {
            if let Some(n) = nat_to_int(t) {
                return format!("{}", n);
            }
            if args.is_empty() {
                c.clone()
            } else {
                let parts: Vec<String> = args.iter().map(|a| show_term(env, a)).collect();
                format!("({} {})", c, parts.join(" "))
            }
        }
        Term::TPCon(_, c, args, r) => {
            let mut parts: Vec<String> = args.iter().map(|a| show_term(env, a)).collect();
            parts.push(format!("@ {}", show_term(env, r)));
            format!("({} {})", c, parts.join(" "))
        }
        Term::TSqCon(_, c, args, r, s) => {
            let mut parts: Vec<String> = args.iter().map(|a| show_term(env, a)).collect();
            parts.push(format!("@ {} @ {}", show_term(env, r), show_term(env, s)));
            format!("({} {})", c, parts.join(" "))
        }
        Term::TElim(motive, cases, scrut) => {
            let case_strs: Vec<String> = cases
                .iter()
                .map(|case| {
                    let mut env2 = case.binders.clone();
                    env2.reverse();
                    env2.extend_from_slice(env);
                    format!(
                        "{} {} -> {}",
                        case.con,
                        case.binders.join(" "),
                        show_term(&env2, &case.body)
                    )
                })
                .collect();
            format!(
                "elim[{}] {{ {} }} {}",
                show_term(env, motive),
                case_strs.join(" | "),
                show_term(env, scrut)
            )
        }
        Term::Meta(i) => format!("?{}", i),
        Term::TBy(tactics) => {
            let tactic_strs: Vec<String> = tactics.iter().map(|t| show_tactic(env, t)).collect();
            format!("by {}", tactic_strs.join("; "))
        }
    }
}

pub fn show_tactic(env: &[Name], t: &Tactic) -> String {
    match t {
        Tactic::Exact(term) => format!("exact {}", show_term(env, term)),
        Tactic::Intro(names) => format!("intro {}", names.join(" ")),
        Tactic::Apply(term) => format!("apply {}", show_term(env, term)),
        Tactic::Assumption => "assumption".to_string(),
        Tactic::Reflexivity => "reflexivity".to_string(),
        Tactic::Symmetry => "symmetry".to_string(),
        Tactic::Split => "split".to_string(),
        Tactic::Constructor(name) => match name {
            Some(n) => format!("constructor {}", n),
            None => "constructor".to_string(),
        },
        Tactic::Destruct(name) => format!("destruct {}", name),
        Tactic::Transitivity => "transitivity".to_string(),
        Tactic::Compute => "compute".to_string(),
        Tactic::Trivial => "trivial".to_string(),
    }
}

#[allow(dead_code)]
pub fn show_datatype(dt: &Datatype) -> String {
    let mut parts = Vec::new();
    for con in &dt.cons {
        if con.arg_tys.is_empty() {
            parts.push(con.name.clone());
        } else {
            let tys: Vec<String> = con.arg_tys.iter().map(|t| show_term(&[], t)).collect();
            parts.push(format!("{} : {}", con.name, tys.join(" -> ")));
        }
    }
    for pcon in &dt.pcons {
        let tys: Vec<String> = pcon.arg_tys.iter().map(|t| show_term(&[], t)).collect();
        parts.push(format!(
            "{} : {} -> Path {} {} {}",
            pcon.name,
            tys.join(" -> "),
            dt.name,
            show_term(&[], &pcon.face0),
            show_term(&[], &pcon.face1),
        ));
    }
    format!("data {} = {}", dt.name, parts.join(" | "))
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", show_term(&[], self))
    }
}
