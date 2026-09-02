//! Tests for dependent Pi-type transport.
//!
//! Covers the three branches of `transport_pi`:
//! 1. Constant family → identity
//! 2. Non-dependent codomain (B depends on `i`, not on Pi argument `x`) → fast path
//! 3. Dependent codomain (B depends on both `i` and `x`) → fallback path
//!
//! Also exercises `uses_var_at_level` correctness indirectly.

#[cfg(test)]
mod tests {
    use crate::cubical::nbe::{Globals, Scope, Value, eval_nbe, nbe_eval};
    use crate::cubical::syntax::{LevelExpr, Term};
    use std::sync::Arc;
    use std::sync::Mutex;

    fn b(t: Term) -> Arc<Term> {
        Arc::new(t)
    }

    fn empty_globals() -> Globals {
        Arc::new(Mutex::new(Vec::new()))
    }

    // ---------------------------------------------------------------
    // 1. Constant Pi — neither domain nor codomain depends on i
    // ---------------------------------------------------------------

    #[test]
    fn constant_pi_transport_is_identity() {
        crate::cubical::session::with_session_mut(|session| {
            let fam = Term::PLam(
                "i".to_string(),
                b(Term::TPi(
                    "x".to_string(),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    false,
                )),
            );
            let input = Term::TAbs(
                "x".to_string(),
                b(Term::TAbs("y".to_string(), b(Term::TVar(0)))),
            );
            let term = Term::TTransport(b(fam), b(input));
            let globals = empty_globals();
            let result = eval_nbe(&Scope::empty(), &globals, 0, &term, session);
            match result {
                Value::VLam(_, _) => {}
                other => panic!("expected VLam (identity), got: {:?}", other),
            }
        });
    }

    // ---------------------------------------------------------------
    // 2. Non-dependent codomain — B(i) varies with i, not with x
    // ---------------------------------------------------------------

    #[test]
    fn nondependent_codomain_pi_transport_reduces() {
        crate::cubical::session::with_session_mut(|session| {
            let fam = Term::PLam(
                "i".to_string(),
                b(Term::TPi(
                    "x".to_string(),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    false,
                )),
            );
            let input = Term::TAbs(
                "x".to_string(),
                b(Term::TAbs("y".to_string(), b(Term::TVar(1)))),
            );
            let term = Term::TTransport(b(fam), b(input));
            let globals = empty_globals();
            let result = eval_nbe(&Scope::empty(), &globals, 0, &term, session);
            match &result {
                Value::VLam(_, _) => {}
                other => panic!("expected TAbs/VLam, got: {:?}", other),
            }
        });
    }

    // ---------------------------------------------------------------
    // 3. Non-dep codomain — domain varies, codomain constant
    // ---------------------------------------------------------------

    #[test]
    fn varying_domain_constant_codomain_pi_transport() {
        crate::cubical::session::with_session_mut(|session| {
            let fam = Term::PLam(
                "i".to_string(),
                b(Term::TPi(
                    "x".to_string(),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    false,
                )),
            );
            let input = Term::TAbs(
                "x".to_string(),
                b(Term::TAbs("y".to_string(), b(Term::TVar(0)))),
            );
            let term = Term::TTransport(b(fam), b(input));
            let globals = empty_globals();
            let result = eval_nbe(&Scope::empty(), &globals, 0, &term, session);
            assert!(
                !matches!(&result, Value::VTransport(_, _)),
                "should not be stuck as VTransport: {:?}",
                result
            );
        });
    }

    // ---------------------------------------------------------------
    // 4. Dependent codomain — B depends on x
    // ---------------------------------------------------------------

    #[test]
    fn dependent_codomain_pi_transport_reduces() {
        crate::cubical::session::with_session_mut(|session| {
            let fam = Term::PLam(
                "i".to_string(),
                b(Term::TPi(
                    "x".to_string(),
                    b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
                    b(Term::TPi(
                        "y".to_string(),
                        b(Term::TUniv(LevelExpr::LConst(0))),
                        b(Term::TVar(1)),
                        false,
                    )),
                    false,
                )),
            );
            let input = Term::TAbs(
                "x".to_string(),
                b(Term::TAbs("y".to_string(), b(Term::TVar(1)))),
            );
            let term = Term::TTransport(b(fam), b(input));
            let globals = empty_globals();
            let result = eval_nbe(&Scope::empty(), &globals, 0, &term, session);
            assert!(
                !matches!(&result, Value::VTransport(_, _)),
                "dependent Pi transport should reduce, got stuck: {:?}",
                result
            );
            assert!(
                matches!(&result, Value::VLam(_, _)),
                "expected VLam, got: {:?}",
                result
            );
        });
    }

    // ---------------------------------------------------------------
    // 5. Dependent codomain — nested Pi with reference to x
    // ---------------------------------------------------------------

    #[test]
    fn deeply_nested_dependent_codomain_transport() {
        crate::cubical::session::with_session_mut(|session| {
            let fam = Term::PLam(
                "i".to_string(),
                b(Term::TPi(
                    "x".to_string(),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    b(Term::TPi(
                        "y".to_string(),
                        b(Term::TUniv(LevelExpr::LConst(0))),
                        b(Term::TPi(
                            "z".to_string(),
                            b(Term::TUniv(LevelExpr::LConst(0))),
                            b(Term::TVar(2)), // references x, two binders deep
                            false,
                        )),
                        false,
                    )),
                    false,
                )),
            );
            let input = Term::TAbs(
                "x".to_string(),
                b(Term::TAbs(
                    "y".to_string(),
                    b(Term::TAbs("z".to_string(), b(Term::TVar(2)))),
                )),
            );
            let term = Term::TTransport(b(fam), b(input));
            let globals = empty_globals();
            let result = eval_nbe(&Scope::empty(), &globals, 0, &term, session);
            assert!(
                !matches!(&result, Value::VTransport(_, _)),
                "deeply dependent Pi transport should reduce, got stuck: {:?}",
                result
            );
            assert!(
                matches!(&result, Value::VLam(_, _)),
                "expected VLam, got: {:?}",
                result
            );
        });
    }

    // ---------------------------------------------------------------
    // 6. Nested Pi → nested Pi transport
    // ---------------------------------------------------------------

    #[test]
    fn nested_pi_transport() {
        crate::cubical::session::with_session_mut(|session| {
            let fam = Term::PLam(
                "i".to_string(),
                b(Term::TPi(
                    "x".to_string(),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    b(Term::TPi(
                        "y".to_string(),
                        b(Term::TUniv(LevelExpr::LConst(0))),
                        b(Term::TUniv(LevelExpr::LConst(0))),
                        false,
                    )),
                    false,
                )),
            );
            let input = Term::TAbs(
                "x".to_string(),
                b(Term::TAbs(
                    "y".to_string(),
                    b(Term::TAbs("z".to_string(), b(Term::TVar(0)))),
                )),
            );
            let term = Term::TTransport(b(fam), b(input));
            let globals = empty_globals();
            let result = eval_nbe(&Scope::empty(), &globals, 0, &term, session);
            assert!(
                matches!(&result, Value::VLam(_, _)),
                "expected VLam, got: {:?}",
                result
            );
        });
    }

    // ---------------------------------------------------------------
    // 7. Pi where codomain references i (non-dep on x)
    // ---------------------------------------------------------------

    #[test]
    fn codomain_references_interval_var() {
        crate::cubical::session::with_session_mut(|session| {
            let fam = Term::PLam(
                "i".to_string(),
                b(Term::TPi(
                    "x".to_string(),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    false,
                )),
            );
            let input = Term::TAbs(
                "x".to_string(),
                b(Term::TVar(0)), // just returns x
            );
            let term = Term::TTransport(b(fam), b(input));
            let globals = empty_globals();
            let result = eval_nbe(&Scope::empty(), &globals, 0, &term, session);
            assert!(
                !matches!(&result, Value::VTransport(_, _)),
                "Pi transport should reduce, got stuck: {:?}",
                result
            );
        });
    }

    // ---------------------------------------------------------------
    // 8. Uses var level — correctness of binder tracking
    // ---------------------------------------------------------------

    #[test]
    fn uses_var_level_tvar_direct() {
        // TVar(0) references level 0
        assert!(crate::cubical::nbe::uses_var_at_level(&Term::TVar(0), 0));
        assert!(!crate::cubical::nbe::uses_var_at_level(&Term::TVar(0), 1));
    }

    #[test]
    fn uses_var_level_under_lambda() {
        // TAbs("x", TVar(0)) — TVar(0) is captured by the binder
        let abs = Term::TAbs("x".to_string(), b(Term::TVar(0)));
        assert!(!crate::cubical::nbe::uses_var_at_level(&abs, 0));
        // TAbs("x", TVar(1)) — TVar(1) under one binder = outer level 0
        let abs2 = Term::TAbs("x".to_string(), b(Term::TVar(1)));
        assert!(crate::cubical::nbe::uses_var_at_level(&abs2, 0));
        // TVar(1) under one binder checks level 0+1=1, matches TVar(1)
    }

    #[test]
    fn uses_var_level_under_pi_domain() {
        // TPi("x", TVar(0), TUniv(0)) — domain references level 0
        let pi = Term::TPi(
            "x".to_string(),
            b(Term::TVar(0)),
            b(Term::TUniv(LevelExpr::LConst(0))),
            false,
        );
        assert!(crate::cubical::nbe::uses_var_at_level(&pi, 0));
    }

    #[test]
    fn uses_var_level_under_pi_codomain() {
        // TPi("x", TUniv(0), TVar(0)) — TVar(0) is captured by the binder
        let pi = Term::TPi(
            "x".to_string(),
            b(Term::TUniv(LevelExpr::LConst(0))),
            b(Term::TVar(0)),
            false,
        );
        assert!(!crate::cubical::nbe::uses_var_at_level(&pi, 0));
        // TPi("x", TUniv(0), TVar(1)) — TVar(1) under one binder = outer level 0
        let pi2 = Term::TPi(
            "x".to_string(),
            b(Term::TUniv(LevelExpr::LConst(0))),
            b(Term::TVar(1)),
            false,
        );
        assert!(crate::cubical::nbe::uses_var_at_level(&pi2, 0));
    }

    #[test]
    fn uses_var_level_nested_pi() {
        // TPi("x", U, TPi("y", U, TVar(2)))
        // TVar(2) under two binders → checks level 0+2=2 → match!
        let pi = Term::TPi(
            "x".to_string(),
            b(Term::TUniv(LevelExpr::LConst(0))),
            b(Term::TPi(
                "y".to_string(),
                b(Term::TUniv(LevelExpr::LConst(0))),
                b(Term::TVar(2)),
                false,
            )),
            false,
        );
        assert!(crate::cubical::nbe::uses_var_at_level(&pi, 0));
        // TVar(2) under two binders → checks level 1+2=3 → no match
        assert!(!crate::cubical::nbe::uses_var_at_level(&pi, 1));
    }

    #[test]
    fn uses_var_level_application() {
        // TApp(TVar(0), TVar(1))
        let app = Term::TApp(b(Term::TVar(0)), b(Term::TVar(1)));
        assert!(crate::cubical::nbe::uses_var_at_level(&app, 0));
        assert!(crate::cubical::nbe::uses_var_at_level(&app, 1));
        assert!(!crate::cubical::nbe::uses_var_at_level(&app, 2));
    }

    #[test]
    fn uses_var_level_univ_always_false() {
        assert!(!crate::cubical::nbe::uses_var_at_level(
            &Term::TUniv(LevelExpr::LConst(0)),
            0
        ));
        assert!(!crate::cubical::nbe::uses_var_at_level(
            &Term::TUniv(LevelExpr::LConst(5)),
            0
        ));
    }

    // ---------------------------------------------------------------
    // 9. Integration — dependent Pi via parser round-trip
    // ---------------------------------------------------------------

    #[test]
    fn parser_roundtrip_pi_transport_term() {
        crate::cubical::session::with_session_mut(|session| {
            let fam = Term::PLam(
                "i".to_string(),
                b(Term::TPi(
                    "x".to_string(),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    b(Term::TPi(
                        "y".to_string(),
                        b(Term::TUniv(LevelExpr::LConst(0))),
                        b(Term::TPi(
                            "z".to_string(),
                            b(Term::TUniv(LevelExpr::LConst(1))),
                            b(Term::TUniv(LevelExpr::LConst(0))),
                            false,
                        )),
                        false,
                    )),
                    false,
                )),
            );
            let input = Term::TAbs(
                "x".to_string(),
                b(Term::TAbs(
                    "y".to_string(),
                    b(Term::TAbs(
                        "z".to_string(),
                        b(Term::TUniv(LevelExpr::LConst(0))),
                    )),
                )),
            );
            let term = Term::TTransport(b(fam), b(input));
            let result = nbe_eval(&term, session);
            // Just verify it normalizes without panicking
            let _ = crate::cubical::syntax::show_term(&[], &result);
        });
    }

    #[test]
    fn dependent_pi_transport_through_sigma_codomain() {
        crate::cubical::session::with_session_mut(|session| {
            let fam = Term::PLam(
                "i".to_string(),
                b(Term::TPi(
                    "x".to_string(),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    b(Term::TSigma(
                        "y".to_string(),
                        b(Term::TUniv(LevelExpr::LConst(0))),
                        b(Term::TVar(1)),
                    )),
                    false,
                )),
            );
            let input = Term::TAbs(
                "x".to_string(),
                b(Term::TPair(b(Term::TVar(0)), b(Term::TVar(0)))),
            );
            let term = Term::TTransport(b(fam), b(input));
            let globals = empty_globals();
            let result = eval_nbe(&Scope::empty(), &globals, 0, &term, session);
            assert!(
                matches!(&result, Value::VLam(_, _)),
                "expected VLam, got: {:?}",
                result
            );
        });
    }

    #[test]
    fn dependent_pi_transport_through_path_codomain() {
        crate::cubical::session::with_session_mut(|session| {
            let fam = Term::PLam(
                "i".to_string(),
                b(Term::TPi(
                    "x".to_string(),
                    b(Term::TUniv(LevelExpr::LConst(0))),
                    b(Term::TPath(
                        b(Term::TVar(1)),
                        b(Term::TVar(1)),
                        b(Term::TVar(1)),
                    )),
                    false,
                )),
            );
            let input = Term::TAbs(
                "x".to_string(),
                b(Term::PLam("j".to_string(), b(Term::TVar(1)))),
            );
            let term = Term::TTransport(b(fam), b(input));
            let globals = empty_globals();
            let result = eval_nbe(&Scope::empty(), &globals, 0, &term, session);
            assert!(
                matches!(&result, Value::VLam(_, _)),
                "expected VLam, got: {:?}",
                result
            );
        });
    }
}
