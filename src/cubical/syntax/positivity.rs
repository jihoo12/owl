//! Strict positivity checking for datatype declarations.

use std::fmt;

use super::{Datatype, Name, Term};

/// An error returned when a datatype occurs negatively in its own definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PositivityError {
    pub datatype: Name,
    pub constructor: Name,
    pub message: String,
}

impl fmt::Display for PositivityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "positivity violation in constructor '{}' of '{}': {}",
            self.constructor, self.datatype, self.message
        )
    }
}

/// Check that `target` occurs strictly positively in `ty`.
///
/// `negative` tracks whether we are currently under an odd number of arrow
/// domains (i.e. a negative position). When `negative` is true and `target`
/// appears, that is a violation.
fn check_positivity_in(target: &str, ty: &Term, negative: bool) -> Result<(), PositivityError> {
    match ty {
        Term::TVar(_) => Ok(()),
        Term::TUniv(_) | Term::TIntervalTy | Term::TInterval(_) | Term::TCube(_) => Ok(()),
        Term::TData(name, params) => {
            if name == target && negative {
                Err(PositivityError {
                    datatype: target.to_string(),
                    constructor: String::new(),
                    message: format!(
                        "datatype '{}' appears on the left side of an arrow",
                        target
                    ),
                })
            } else {
                for p in params {
                    check_positivity_in(target, p, negative)?;
                }
                Ok(())
            }
        }
        Term::TApp(f, a) | Term::PApp(f, a) | Term::TEquiv(f, a) | Term::TEquivFwd(f, a)
        | Term::TTransport(f, a) | Term::TPair(f, a) => {
            check_positivity_in(target, f, negative)?;
            check_positivity_in(target, a, negative)
        }
        Term::TFst(p) | Term::TSnd(p) => check_positivity_in(target, p, negative),
        Term::TAbs(_, body) | Term::PLam(_, body) | Term::TUa(body) => {
            check_positivity_in(target, body, negative)
        }
        Term::TPi(_, a, b) => {
            // Domain A is in a negative position (argument position).
            check_positivity_in(target, a, true)?;
            // Codomain B is in a positive position (result position).
            check_positivity_in(target, b, false)
        }
        Term::TSigma(_, a, b) => {
            check_positivity_in(target, a, negative)?;
            check_positivity_in(target, b, negative)
        }
        Term::TPath(a, u, v) | Term::TGlue(a, u, v) | Term::TGlueElem(a, u, v)
        | Term::TUnglue(a, u, v) => {
            check_positivity_in(target, a, negative)?;
            check_positivity_in(target, u, negative)?;
            check_positivity_in(target, v, negative)
        }
        Term::TPartial(phi, a) => {
            check_positivity_in(target, phi, negative)?;
            check_positivity_in(target, a, negative)
        }
        Term::THComp(a, sys, u0)
        | Term::TComp(a, sys, u0)
        | Term::TFill(a, sys, u0)
        | Term::THFill(a, sys, u0) => {
            check_positivity_in(target, a, negative)?;
            for (phi, t) in sys {
                check_positivity_in(target, phi, negative)?;
                check_positivity_in(target, t, negative)?;
            }
            check_positivity_in(target, u0, negative)
        }
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            check_positivity_in(target, a, negative)?;
            check_positivity_in(target, b, negative)?;
            check_positivity_in(target, f, negative)?;
            check_positivity_in(target, g, negative)?;
            check_positivity_in(target, eta, negative)?;
            check_positivity_in(target, eps, negative)
        }
        Term::TCon(_, _, args) => {
            for arg in args {
                check_positivity_in(target, arg, negative)?;
            }
            Ok(())
        }
        Term::TPCon(_, _, args, r) => {
            for arg in args {
                check_positivity_in(target, arg, negative)?;
            }
            check_positivity_in(target, r, negative)
        }
        Term::TElim(motive, cases, scrut) => {
            check_positivity_in(target, motive, negative)?;
            for case in cases {
                check_positivity_in(target, &case.body, negative)?;
            }
            check_positivity_in(target, scrut, negative)
        }
        Term::Meta(_) => Ok(()),
        Term::TBy(_) => Ok(()),
        Term::TSqCon(_, _, args, r, s) => {
            for a in args {
                check_positivity_in(target, a, negative)?;
            }
            check_positivity_in(target, r, negative)?;
            check_positivity_in(target, s, negative)
        }
    }
}

/// Check that a constructor's argument types are strictly positive with respect
/// to the given datatype.
fn check_con_positivity(
    dt_name: &str,
    con_name: &str,
    arg_tys: &[Term],
) -> Result<(), PositivityError> {
    for (i, ty) in arg_tys.iter().enumerate() {
        check_positivity_in(dt_name, ty, false).map_err(|mut e| {
            e.constructor = con_name.to_string();
            e.message = format!(
                "argument {} of constructor '{}': {}",
                i, con_name, e.message
            );
            e
        })?;
    }
    Ok(())
}

/// Check that a datatype declaration is strictly positive.
///
/// Returns `Ok(())` if all constructors are positive, or the first
/// `PositivityError` found.
pub fn check_datatype_positivity(dt: &Datatype) -> Result<(), PositivityError> {
    for con in &dt.cons {
        check_con_positivity(&dt.name, &con.name, &con.arg_tys)?;
    }
    for pcon in &dt.pcons {
        check_con_positivity(&dt.name, &pcon.name, &pcon.arg_tys)?;
        check_positivity_in(&dt.name, &pcon.face0, false).map_err(|mut e| {
            e.constructor = pcon.name.clone();
            e.message = format!(
                "face0 of path constructor '{}': {}",
                pcon.name, e.message
            );
            e
        })?;
        check_positivity_in(&dt.name, &pcon.face1, false).map_err(|mut e| {
            e.constructor = pcon.name.clone();
            e.message = format!(
                "face1 of path constructor '{}': {}",
                pcon.name, e.message
            );
            e
        })?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cubical::syntax::{ConSig, PConSig};

    fn b(t: Term) -> Box<Term> {
        Box::new(t)
    }

    #[test]
    fn positive_nat_is_ok() {
        let dt = Datatype {
            name: "Nat".into(),
            params: vec![],
            cons: vec![
                ConSig { name: "zero".into(), arg_tys: vec![] },
                ConSig { name: "suc".into(), arg_tys: vec![Term::TData("Nat".into(), vec![])] },
            ],
            pcons: vec![],
            sqcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn positive_list_is_ok() {
        let dt = Datatype {
            name: "List".into(),
            params: vec![],
            cons: vec![
                ConSig { name: "nil".into(), arg_tys: vec![] },
                ConSig {
                    name: "cons".into(),
                    arg_tys: vec![
                        Term::TUniv(0),
                        Term::TData("List".into(), vec![]),
                    ],
                },
            ],
            pcons: vec![],
            sqcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn positive_nested_pi_is_ok() {
        let dt = Datatype {
            name: "Bad".into(),
            params: vec![],
            cons: vec![ConSig {
                name: "mk".into(),
                arg_tys: vec![Term::TPi(
                    "_".into(),
                    b(Term::TPi("_".into(), b(Term::TData("Nat".into(), vec![])), b(Term::TData("Nat".into(), vec![])))),
                    b(Term::TData("Nat".into(), vec![])),
                )],
            }],
            pcons: vec![],
            sqcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn negative_recursive_type_is_rejected() {
        let dt = Datatype {
            name: "Bad".into(),
            params: vec![],
            cons: vec![ConSig {
                name: "cons".into(),
                arg_tys: vec![Term::TPi(
                    "_".into(),
                    b(Term::TData("Bad".into(), vec![])),
                    b(Term::TData("Bad".into(), vec![])),
                )],
            }],
            pcons: vec![],
            sqcons: vec![],
            universe_level: None,
        };
        let err = check_datatype_positivity(&dt).unwrap_err();
        assert_eq!(err.datatype, "Bad");
        assert_eq!(err.constructor, "cons");
    }

    #[test]
    fn positive_deeply_nested_pi_is_ok() {
        let dt = Datatype {
            name: "Bad".into(),
            params: vec![],
            cons: vec![ConSig {
                name: "cons".into(),
                arg_tys: vec![Term::TPi(
                    "_".into(),
                    b(Term::TPi(
                        "_".into(),
                        b(Term::TData("Nat".into(), vec![])),
                        b(Term::TData("Bad".into(), vec![])),
                    )),
                    b(Term::TData("Bad".into(), vec![])),
                )],
            }],
            pcons: vec![],
            sqcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn negative_domain_in_pi_is_rejected() {
        let dt = Datatype {
            name: "Bad".into(),
            params: vec![],
            cons: vec![ConSig {
                name: "cons".into(),
                arg_tys: vec![Term::TPi(
                    "_".into(),
                    b(Term::TPi(
                        "_".into(),
                        b(Term::TData("Bad".into(), vec![])),
                        b(Term::TData("Nat".into(), vec![])),
                    )),
                    b(Term::TData("Bad".into(), vec![])),
                )],
            }],
            pcons: vec![],
            sqcons: vec![],
            universe_level: None,
        };
        let err = check_datatype_positivity(&dt).unwrap_err();
        assert_eq!(err.datatype, "Bad");
    }

    #[test]
    fn positive_sigma_is_ok() {
        let dt = Datatype {
            name: "Pair".into(),
            params: vec![],
            cons: vec![ConSig {
                name: "mk".into(),
                arg_tys: vec![Term::TSigma(
                    "_".into(),
                    b(Term::TData("Nat".into(), vec![])),
                    b(Term::TData("Nat".into(), vec![])),
                )],
            }],
            pcons: vec![],
            sqcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn positive_path_type_is_ok() {
        let dt = Datatype {
            name: "S1".into(),
            params: vec![],
            cons: vec![ConSig { name: "base".into(), arg_tys: vec![] }],
            pcons: vec![PConSig {
                name: "loop".into(),
                arg_tys: vec![],
                face0: Term::TCon("S1".into(), "base".into(), vec![]),
                face1: Term::TCon("S1".into(), "base".into(), vec![]),
            }],
            sqcons: vec![],
            universe_level: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }
}
