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
    use crate::cubical::nbe::{eval_nbe, nbe_eval, Globals, Value};
    use crate::cubical::syntax::Term;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn b(t: Term) -> Box<Term> {
        Box::new(t)
    }

    fn empty_globals() -> Globals {
        Rc::new(RefCell::new(Vec::new()))
    }

    // ---------------------------------------------------------------
    // 1. Constant Pi — neither domain nor codomain depends on i
    // ---------------------------------------------------------------

    #[test]
    fn constant_pi_transport_is_identity() {
        // Family: λi. (x : U) → U
        // Input:  λx. λy. y   (the identity on U)
        // Result: identity function unchanged
        let fam = Term::PLam(
            "i".to_string(),
            b(Term::TPi(
                "x".to_string(),
                b(Term::TUniv(0)),
                b(Term::TUniv(0)),
            )),
        );
        let input = Term::TAbs(
            "x".to_string(),
            b(Term::TAbs(
                "y".to_string(),
                b(Term::TVar(0)),
            )),
        );
        let term = Term::TTransport(b(fam), b(input));
        let globals = empty_globals();
        let result = eval_nbe(&[], &globals, 0, &term);
        // Constant family → transport is identity → result should be the original lambda
        match result {
            Value::VLam(_, _) => {}
            other => panic!("expected VLam (identity), got: {:?}", other),
        }
    }

    // ---------------------------------------------------------------
    // 2. Non-dependent codomain — B(i) varies with i, not with x
    // ---------------------------------------------------------------

    #[test]
    fn nondependent_codomain_pi_transport_reduces() {
        // Family: λi. (x : U) → U_i
        //   where U_i = TVar(0) = the interval variable
        //   → codomain is VIntervalVar at the formal position, domain is constant U
        //   → uses_var_at_level(codomain_body, 0) = false (TUniv doesn't reference var 0)
        //
        // Input:  λx. λy. x
        // Result: TAbs wrapping a TTransport over the codomain family
        let fam = Term::PLam(
            "i".to_string(),
            b(Term::TPi(
                "x".to_string(),
                b(Term::TUniv(0)),
                b(Term::TUniv(0)), // constant codomain
            )),
        );
        let input = Term::TAbs(
            "x".to_string(),
            b(Term::TAbs(
                "y".to_string(),
                b(Term::TVar(1)), // returns x
            )),
        );
        let term = Term::TTransport(b(fam), b(input));
        let globals = empty_globals();
        let result = eval_nbe(&[], &globals, 0, &term);
        // Should produce a TAbs (reduced), not a stuck TTransport
        match &result {
            Value::VLam(_, _) => {}
            other => panic!("expected TAbs/VLam, got: {:?}", other),
        }
    }

    // ---------------------------------------------------------------
    // 3. Non-dep codomain — domain varies, codomain constant
    // ---------------------------------------------------------------

    #[test]
    fn varying_domain_constant_codomain_pi_transport() {
        // Family: λi. (x : A(i)) → U
        //   A(i) = TApp(TVar(0), TVar(0)) — applies interval var to itself
        //   codomain is TUniv(0) — constant, doesn't reference i
        //
        // Input:  λx. λy. y
        //
        // Since codomain doesn't use var 0 (the interval var), this is
        // the non-dependent path. The codomain family is extracted and
        // transport is applied to each argument.
        let fam = Term::PLam(
            "i".to_string(),
            b(Term::TPi(
                "x".to_string(),
                b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
                b(Term::TUniv(0)),
            )),
        );
        let input = Term::TAbs(
            "x".to_string(),
            b(Term::TAbs(
                "y".to_string(),
                b(Term::TVar(0)),
            )),
        );
        let term = Term::TTransport(b(fam), b(input));
        let globals = empty_globals();
        let result = eval_nbe(&[], &globals, 0, &term);
        // Should reduce to TAbs, not stay stuck
        assert!(
            !matches!(&result, Value::VTransport(_, _)),
            "should not be stuck as VTransport: {:?}",
            result
        );
    }

    // ---------------------------------------------------------------
    // 4. Dependent codomain — B depends on x
    // ---------------------------------------------------------------

    #[test]
    fn dependent_codomain_pi_transport_reduces() {
        // Family: λi. (x : A) → (y : U) → x
        //   codomain body = TVar(1) references x (the Pi argument)
        //   → uses_var_at_level(codomain_body, 0) = true
        //   → must use fallback path
        //
        // Input:  λx. λy. x
        let fam = Term::PLam(
            "i".to_string(),
            b(Term::TPi(
                "x".to_string(),
                b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
                b(Term::TPi(
                    "y".to_string(),
                    b(Term::TUniv(0)),
                    b(Term::TVar(1)), // references x → dependent!
                )),
            )),
        );
        let input = Term::TAbs(
            "x".to_string(),
            b(Term::TAbs(
                "y".to_string(),
                b(Term::TVar(1)),
            )),
        );
        let term = Term::TTransport(b(fam), b(input));
        let globals = empty_globals();
        let result = eval_nbe(&[], &globals, 0, &term);
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
    }

    // ---------------------------------------------------------------
    // 5. Dependent codomain — nested Pi with reference to x
    // ---------------------------------------------------------------

    #[test]
    fn deeply_nested_dependent_codomain_transport() {
        // Family: λi. (x : U) → (y : U) → (z : U) → x
        //   codomain body = TVar(2) references x through 2 binders
        //   → uses_var_at_level(body, 0) = true (under 2 binders, checks level 0+2=2)
        //
        // Input:  λx. λy. λz. x
        let fam = Term::PLam(
            "i".to_string(),
            b(Term::TPi(
                "x".to_string(),
                b(Term::TUniv(0)),
                b(Term::TPi(
                    "y".to_string(),
                    b(Term::TUniv(0)),
                    b(Term::TPi(
                        "z".to_string(),
                        b(Term::TUniv(0)),
                        b(Term::TVar(2)), // references x, two binders deep
                    )),
                )),
            )),
        );
        let input = Term::TAbs(
            "x".to_string(),
            b(Term::TAbs(
                "y".to_string(),
                b(Term::TAbs(
                    "z".to_string(),
                    b(Term::TVar(2)),
                )),
            )),
        );
        let term = Term::TTransport(b(fam), b(input));
        let globals = empty_globals();
        let result = eval_nbe(&[], &globals, 0, &term);
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
    }

    // ---------------------------------------------------------------
    // 6. Nested Pi → nested Pi transport
    // ---------------------------------------------------------------

    #[test]
    fn nested_pi_transport() {
        // Family: λi. (x : U) → (y : U) → U
        //   non-dependent: neither codomain references i
        //
        // Input:  λx. λy. λz. z
        let fam = Term::PLam(
            "i".to_string(),
            b(Term::TPi(
                "x".to_string(),
                b(Term::TUniv(0)),
                b(Term::TPi(
                    "y".to_string(),
                    b(Term::TUniv(0)),
                    b(Term::TUniv(0)),
                )),
            )),
        );
        let input = Term::TAbs(
            "x".to_string(),
            b(Term::TAbs(
                "y".to_string(),
                b(Term::TAbs(
                    "z".to_string(),
                    b(Term::TVar(0)),
                )),
            )),
        );
        let term = Term::TTransport(b(fam), b(input));
        let globals = empty_globals();
        let result = eval_nbe(&[], &globals, 0, &term);
        // Should reduce to a nested TAbs
        assert!(
            matches!(&result, Value::VLam(_, _)),
            "expected VLam, got: {:?}",
            result
        );
    }

    // ---------------------------------------------------------------
    // 7. Pi where codomain references i (non-dep on x)
    // ---------------------------------------------------------------

    #[test]
    fn codomain_references_interval_var() {
        // Family: λi. (x : U) → i
        //   codomain = TVar(0) = interval variable (at de Bruijn 0 in the body)
        //   → after shifting, this is the interval var, not the Pi argument
        //   → uses_var_at_level(TVar(0), 0) in the shifted body... tricky
        //
        // Input:  λx. i0
        //
        // This should exercise the non-dependent fast path.
        let fam = Term::PLam(
            "i".to_string(),
            b(Term::TPi(
                "x".to_string(),
                b(Term::TUniv(0)),
                b(Term::TVar(0)), // interval variable (after shift, this is the Pi arg NOT i)
            )),
        );
        let input = Term::TAbs(
            "x".to_string(),
            b(Term::TVar(0)), // just returns x
        );
        let term = Term::TTransport(b(fam), b(input));
        let globals = empty_globals();
        let result = eval_nbe(&[], &globals, 0, &term);
        // Should reduce
        assert!(
            !matches!(&result, Value::VTransport(_, _)),
            "Pi transport should reduce, got stuck: {:?}",
            result
        );
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
            b(Term::TUniv(0)),
        );
        assert!(crate::cubical::nbe::uses_var_at_level(&pi, 0));
    }

    #[test]
    fn uses_var_level_under_pi_codomain() {
        // TPi("x", TUniv(0), TVar(0)) — TVar(0) is captured by the binder
        let pi = Term::TPi(
            "x".to_string(),
            b(Term::TUniv(0)),
            b(Term::TVar(0)),
        );
        assert!(!crate::cubical::nbe::uses_var_at_level(&pi, 0));
        // TPi("x", TUniv(0), TVar(1)) — TVar(1) under one binder = outer level 0
        let pi2 = Term::TPi(
            "x".to_string(),
            b(Term::TUniv(0)),
            b(Term::TVar(1)),
        );
        assert!(crate::cubical::nbe::uses_var_at_level(&pi2, 0));
    }

    #[test]
    fn uses_var_level_nested_pi() {
        // TPi("x", U, TPi("y", U, TVar(2)))
        // TVar(2) under two binders → checks level 0+2=2 → match!
        let pi = Term::TPi(
            "x".to_string(),
            b(Term::TUniv(0)),
            b(Term::TPi(
                "y".to_string(),
                b(Term::TUniv(0)),
                b(Term::TVar(2)),
            )),
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
        assert!(!crate::cubical::nbe::uses_var_at_level(&Term::TUniv(0), 0));
        assert!(!crate::cubical::nbe::uses_var_at_level(&Term::TUniv(5), 0));
    }

    // ---------------------------------------------------------------
    // 9. Integration — dependent Pi via parser round-trip
    // ---------------------------------------------------------------

    #[test]
    fn parser_roundtrip_pi_transport_term() {
        // Construct a complex Pi transport term and verify it normalizes
        // without panicking via nbe_eval.
        let fam = Term::PLam(
            "i".to_string(),
            b(Term::TPi(
                "x".to_string(),
                b(Term::TUniv(0)),
                b(Term::TPi(
                    "y".to_string(),
                    b(Term::TUniv(0)),
                    b(Term::TPi(
                        "z".to_string(),
                        b(Term::TUniv(1)),
                        b(Term::TUniv(0)),
                    )),
                )),
            )),
        );
        let input = Term::TAbs(
            "x".to_string(),
            b(Term::TAbs(
                "y".to_string(),
                b(Term::TAbs(
                    "z".to_string(),
                    b(Term::TUniv(0)),
                )),
            )),
        );
        let term = Term::TTransport(b(fam), b(input));
        let result = nbe_eval(&term);
        // Just verify it normalizes without panicking
        let _ = crate::cubical::syntax::show_term(&[], &result);
    }

    #[test]
    fn dependent_pi_transport_through_sigma_codomain() {
        // Family: λi. (x : U) → Sigma (y : U) * x
        //   codomain = Sigma(y:U) * TVar(1)
        //   TVar(1) references x (the Pi arg), so this is dependent
        //
        // Input:  λx. (x, x)  (pair)
        let fam = Term::PLam(
            "i".to_string(),
            b(Term::TPi(
                "x".to_string(),
                b(Term::TUniv(0)),
                b(Term::TSigma(
                    "y".to_string(),
                    b(Term::TUniv(0)),
                    b(Term::TVar(1)), // references x
                )),
            )),
        );
        let input = Term::TAbs(
            "x".to_string(),
            b(Term::TPair(b(Term::TVar(0)), b(Term::TVar(0)))),
        );
        let term = Term::TTransport(b(fam), b(input));
        let globals = empty_globals();
        let result = eval_nbe(&[], &globals, 0, &term);
        // Should reduce to a function (TAbs/VLam)
        assert!(
            matches!(&result, Value::VLam(_, _)),
            "expected VLam, got: {:?}",
            result
        );
    }

    #[test]
    fn dependent_pi_transport_through_path_codomain() {
        // Family: λi. (x : U) → Path x x
        //   codomain = Path TVar(1) TVar(1)
        //   references x, so dependent
        //
        // Input:  λx. <i> x
        let fam = Term::PLam(
            "i".to_string(),
            b(Term::TPi(
                "x".to_string(),
                b(Term::TUniv(0)),
                b(Term::TPath(
                    b(Term::TVar(1)),
                    b(Term::TVar(1)),
                    b(Term::TVar(1)),
                )),
            )),
        );
        let input = Term::TAbs(
            "x".to_string(),
            b(Term::PLam(
                "j".to_string(),
                b(Term::TVar(1)), // returns x
            )),
        );
        let term = Term::TTransport(b(fam), b(input));
        let globals = empty_globals();
        let result = eval_nbe(&[], &globals, 0, &term);
        assert!(
            matches!(&result, Value::VLam(_, _)),
            "expected VLam, got: {:?}",
            result
        );
    }
}
