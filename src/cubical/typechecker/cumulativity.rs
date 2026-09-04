// Universe cumulativity and subtyping checks for the typechecker.

use std::sync::Arc;

use crate::cubical::interval::{DNF, dnf_leq};
use crate::cubical::nbe::nbe_eval;
use crate::cubical::session::Session;
use crate::cubical::syntax::{Datatype, LevelExpr, Term, Variance, compute_param_variances};

/// Extract a DNF from a term that is known to represent a face (TCube or TInterval).
pub fn term_to_dnf(t: &Term, session: &mut Session) -> DNF {
    match nbe_eval(t, session) {
        Term::TCube(d) => d,
        Term::TInterval(i) => crate::cubical::interval::eval_interval(&i),
        _ => crate::cubical::interval::dnf_bot(),
    }
}

/// Check whether `inferred` is a subtype of `expected` under cumulativity.
///
/// Rules:
/// - `TUniv(n) ≤ TUniv(m)` when `n ≤ m` (cumulativity of universes)
/// - `TPi(x, A, B) ≤ TPi(x, A', B')` when `A' ≤ A` (contravariant domain)
///   and `B ≤ B'` (covariant codomain), checked recursively
/// - `TSigma(x, A, B) ≤ TSigma(x, A', B')` when `A ≤ A'` and `B ≤ B'`
///   (covariant in both), checked recursively
/// - `TData(d, ps) ≤ TData(d, ps')` with covariant parameters
///   (this covers desugared record types)
/// - `TPartial(phi, A) ≤ TPartial(psi, A)` when `phi ⇒ psi` (cofibration subtyping)
/// - Reflexive: identical (syntactically equal) terms are always subtypes,
///   so recursion through Π/Σ/record codomains and parameters that mention
///   bound variables succeeds.
pub fn cumulativity_check(
    expected: &Term,
    inferred: &Term,
    dts: &[Datatype],
    session: &mut Session,
) -> bool {
    match (expected, inferred) {
        // Prop ≤ U0 (cumulativity: Prop is a subuniverse of U0)
        (Term::TUniv(m), Term::TProp) if m.as_const().map_or(false, |c| c >= 0) => true,
        // SSet ≤ U1
        (Term::TUniv(m), Term::TSSet) if m.as_const().map_or(false, |c| c >= 1) => true,
        // Prop ≤ Prop
        (Term::TProp, Term::TProp) => true,
        // SSet ≤ SSet
        (Term::TSSet, Term::TSSet) => true,
        // Lift cumulativity: lift A m ≤ lift B m when A ≤ B
        (Term::TLift(a_exp, m1), Term::TLift(a_inf, m2)) if m1 == m2 => {
            cumulativity_check(a_exp, a_inf, dts, session)
        }
        // Lower cumulativity: lower A ≤ lower B when A ≤ B
        (Term::TLower(a_exp), Term::TLower(a_inf)) => {
            cumulativity_check(a_exp, a_inf, dts, session)
        }

        // Universe cumulativity: U_n is subtype of U_m when n ≤ m
        // When level expressions can't be evaluated (contain variables),
        // fall through to structural equality.
        (Term::TUniv(m), Term::TUniv(n)) => n.leq(m, &[]).unwrap_or_else(|| n == m),

        // Pi cumulativity: contravariant in domain, covariant in codomain
        (Term::TPi(_, a_exp, b_exp, _), Term::TPi(_, a_inf, b_inf, _)) => {
            cumulativity_check(a_inf, a_exp, dts, session)
                && cumulativity_check(b_exp, b_inf, dts, session)
        }

        // Sigma cumulativity: covariant in both components
        (Term::TSigma(_, a_exp, b_exp), Term::TSigma(_, a_inf, b_inf)) => {
            cumulativity_check(a_exp, a_inf, dts, session)
                && cumulativity_check(b_exp, b_inf, dts, session)
        }

        // Cofibration subtyping: [_ | phi] A ≤ [_ | psi] A when phi ⇒ psi
        (Term::TPartial(phi_exp, a_exp), Term::TPartial(phi_inf, a_inf)) => {
            let phi_exp_dnf = term_to_dnf(phi_exp, session);
            let phi_inf_dnf = term_to_dnf(phi_inf, session);
            // The inferred partial element has face phi_inf; the expected has phi_exp.
            // phi_inf ⇒ phi_exp means the inferred is defined on a "larger" face,
            // so it's a valid subtype.
            dnf_leq(&phi_inf_dnf, &phi_exp_dnf) && cumulativity_check(a_exp, a_inf, dts, session)
        }

        // Inductive type cumulativity: same datatype, parameters checked
        // according to their variance.
        //
        // Covariant-only checking of all parameters is UNSOUND: a datatype
        // whose parameters occur negatively (e.g. inside an arrow domain in a
        // constructor argument type) is contravariant, and one that occurs
        // both positively and negatively is invariant.  For such parameters
        // the comparison must be reversed or restricted to definitional
        // equality — otherwise `Bad U0 ≤ Bad U1` typechecks for a `Bad A`
        // that is not covariant in `A`.
        //
        // TData(d, ps) ≤ TData(d, ps') when, per parameter i with variance v:
        //   Covariant:     ps[i] ≤ ps'[i]
        //   Contravariant: ps'[i] ≤ ps[i]
        //   Invariant:     ps[i] == ps'[i]
        //   Unused:        any direction (treated as covariant)
        // Different datatypes are never subtypes of each other.
        (Term::TData(d_exp, ps_exp), Term::TData(d_inf, ps_inf)) => {
            if d_exp != d_inf || ps_exp.len() != ps_inf.len() {
                return false;
            }
            let variances: Vec<Variance> = if ps_exp.is_empty() {
                Vec::new()
            } else {
                dts.iter()
                    .position(|d| &d.name == d_exp)
                    .map(|i| {
                        compute_param_variances(dts)
                            .get(i)
                            .cloned()
                            .unwrap_or_default()
                    })
                    .unwrap_or_default()
            };
            ps_exp
                .iter()
                .zip(ps_inf.iter())
                .enumerate()
                .all(|(i, (a, b))| match variances.get(i) {
                    // Covariant or unused (and unregistered datatypes fall
                    // back to the historical covariant behavior): check b ≤ a.
                    Some(Variance::Covariant) | Some(Variance::Unused) | None => {
                        cumulativity_check(a, b, dts, session)
                    }
                    // Contravariant: check a ≤ b.
                    Some(Variance::Contravariant) => cumulativity_check(b, a, dts, session),
                    // Invariant: require definitional equality.
                    Some(Variance::Invariant) => a == b,
                })
        }

        // Path type cumulativity: Path A u v ≤ Path A' u' v' when A ≤ A' (covariant),
        // u ≤ u' and v ≤ v' (endpoints covariant).
        (Term::TPath(a_exp, u_exp, v_exp), Term::TPath(a_inf, u_inf, v_inf)) => {
            cumulativity_check(a_exp, a_inf, dts, session)
                && cumulativity_check(u_exp, u_inf, dts, session)
                && cumulativity_check(v_exp, v_inf, dts, session)
        }

        // Reflexivity: any term is a subtype of itself.  This is the
        // fallthrough for structurally-identical terms that the arms above
        // don't recurse into — most importantly de Bruijn variables
        // (TVar(i) ≤ TVar(i)) and neutral terms (TApp, TFst, ...) appearing
        // inside the covariant/contravariant positions of a Π, Σ, record, or
        // datatype comparison.  Without it, legal subtyping that only differs
        // in universe levels *inside* a dependent codomain or record parameter
        // is rejected, because the recursion bottoms out on an identical
        // bound-variable reference and falls through to `false`.
        //
        // Callers normalize both sides with `nbe_eval` first, so this
        // compares normal forms (syntactic equality there ≈ definitional
        // equality for closed terms).  Subtyping is reflexive, so this is
        // always sound.
        (a, b) => a == b,
    }
}

// ---------------------------------------------------------------------------
// EtaResult convenience
// ---------------------------------------------------------------------------

impl crate::cubical::equality::EtaResult {
    pub(crate) fn is_equal(&self) -> bool {
        *self == crate::cubical::equality::EtaResult::Equal
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cubical::parser::parse_term;
    use crate::cubical::syntax::LevelExpr;

    /// `cumulativity_check(expected, inferred)` returns whether `inferred ≤ expected`.
    fn sub(expected: &str, inferred: &str, session: &mut Session) -> bool {
        let e = nbe_eval(
            &parse_term(expected, session).expect("parse expected"),
            session,
        );
        let i = nbe_eval(
            &parse_term(inferred, session).expect("parse inferred"),
            session,
        );
        cumulativity_check(&e, &i, &[], session)
    }

    fn sub_t(expected: &Term, inferred: &Term, session: &mut Session) -> bool {
        cumulativity_check(
            &nbe_eval(expected, session),
            &nbe_eval(inferred, session),
            &[],
            session,
        )
    }

    /// Assert `inferred ≤ expected`.
    fn assert_sub(expected: &str, inferred: &str, session: &mut Session) {
        assert!(
            sub(expected, inferred, session),
            "expected `{} <= {}` to hold under cumulativity",
            inferred,
            expected
        );
    }

    /// Assert `inferred ≰ expected`.
    fn assert_not_sub(expected: &str, inferred: &str, session: &mut Session) {
        assert!(
            !sub(expected, inferred, session),
            "expected `{} <= {}` to FAIL under cumulativity",
            inferred,
            expected
        );
    }

    fn tdata(name: &str, params: Vec<Term>) -> Term {
        Term::TData(name.to_string(), params)
    }

    fn t_univ(n: i32) -> Term {
        Term::TUniv(LevelExpr::LConst(n))
    }

    /// `cumulativity_check` against a concrete datatype environment, so the
    /// `TData` arm can resolve parameter variance.
    fn cumul_dts(
        dts: &[Datatype],
        expected: &Term,
        inferred: &Term,
        session: &mut Session,
    ) -> bool {
        cumulativity_check(
            &nbe_eval(expected, session),
            &nbe_eval(inferred, session),
            dts,
            session,
        )
    }

    /// A single-parameter datatype `D (A : U0)` whose constructor arguments
    /// are `arg_tys` (referencing `A` as `TVar(0)`).
    fn dt_one_param(name: &str, arg_tys: Vec<Term>) -> Datatype {
        Datatype {
            name: name.to_string(),
            params: vec![("A".into(), Term::TUniv(LevelExpr::LConst(0)))],
            cons: vec![crate::cubical::syntax::ConSig {
                name: "mk".into(),
                arg_tys,
                return_args: None,
            }],
            pcons: vec![],
            sqcons: vec![],
            cellcons: vec![],
            universe_level: None,
            field_names: None,
        }
    }

    #[test]
    fn datatype_cumulativity_respects_contravariant_parameters() {
        crate::cubical::session::with_session_mut(|session| {
            // D (A) with `mk : (A -> U0) -> D A`: A occurs in an arrow domain,
            // so D is contravariant in A.  Under covariant-only checking this
            // would unsoundly accept `D U0 ≤ D U1`.
            let dts = vec![dt_one_param(
                "D",
                vec![Term::TPi(
                    "_".into(),
                    Arc::new(Term::TVar(0)),
                    Arc::new(Term::TUniv(LevelExpr::LConst(0))),
                    false,
                )],
            )];
            let d_u0 = tdata("D", vec![t_univ(0)]);
            let d_u1 = tdata("D", vec![t_univ(1)]);
            // Contravariance: D U0 ≤ D U1 requires U1 ≤ U0 (false) ...
            assert!(!cumul_dts(&dts, &d_u1, &d_u0, session));
            // ... and D U1 ≤ D U0 requires U0 ≤ U1 (true).
            assert!(cumul_dts(&dts, &d_u0, &d_u1, session));
        });
    }

    #[test]
    fn datatype_cumulativity_rejects_invariant_parameters() {
        crate::cubical::session::with_session_mut(|session| {
            // D (A) with `mk : A -> (A -> U0) -> D A`: A occurs both positively
            // and negatively, so D is invariant in A and neither subtyping
            // direction is allowed.
            let dts = vec![dt_one_param(
                "D",
                vec![
                    Term::TVar(0),
                    Term::TPi(
                        "_".into(),
                        Arc::new(Term::TVar(0)),
                        Arc::new(Term::TUniv(LevelExpr::LConst(0))),
                        false,
                    ),
                ],
            )];
            let d_u0 = tdata("D", vec![t_univ(0)]);
            let d_u1 = tdata("D", vec![t_univ(1)]);
            assert!(!cumul_dts(&dts, &d_u1, &d_u0, session));
            assert!(!cumul_dts(&dts, &d_u0, &d_u1, session));
            // Identical instantiations still compare fine.
            assert!(cumul_dts(&dts, &d_u0, &d_u0, session));
        });
    }

    #[test]
    fn datatype_cumulativity_keeps_covariant_records() {
        crate::cubical::session::with_session_mut(|session| {
            // R (A) with field `content : A`: A occurs positively (a record's
            // field is covariant), so the historical covariant behavior is kept.
            let dts = vec![dt_one_param("R", vec![Term::TVar(0)])];
            let r_u0 = tdata("R", vec![t_univ(0)]);
            let r_u1 = tdata("R", vec![t_univ(1)]);
            assert!(cumul_dts(&dts, &r_u1, &r_u0, session));
            assert!(!cumul_dts(&dts, &r_u0, &r_u1, session));
        });
    }

    #[test]
    fn datatype_cumulativity_propagates_variance_through_nested_types() {
        crate::cubical::session::with_session_mut(|session| {
            // Bar (A) with `b : (A -> U0) -> Bar A` (contravariant) and
            // Foo (A) with `mk : Bar A -> Foo A` — Foo's parameter inherits
            // Bar's contravariance through the nested application.
            let dts = vec![
                dt_one_param(
                    "Bar",
                    vec![Term::TPi(
                        "_".into(),
                        Arc::new(Term::TVar(0)),
                        Arc::new(Term::TUniv(LevelExpr::LConst(0))),
                        false,
                    )],
                ),
                dt_one_param("Foo", vec![tdata("Bar", vec![Term::TVar(0)])]),
            ];
            let foo_u0 = tdata("Foo", vec![t_univ(0)]);
            let foo_u1 = tdata("Foo", vec![t_univ(1)]);
            assert!(!cumul_dts(&dts, &foo_u1, &foo_u0, session));
            assert!(cumul_dts(&dts, &foo_u0, &foo_u1, session));
        });
    }

    #[test]
    fn universe_levels() {
        crate::cubical::session::with_session_mut(|session| {
            assert_sub("U1", "U0", session);
            assert_sub("U2", "U1", session);
            assert_sub("U0", "U0", session);
            assert_not_sub("U0", "U1", session);
            assert_not_sub("U1", "U2", session);
        });
    }

    #[test]
    fn pi_cumulativity() {
        crate::cubical::session::with_session_mut(|session| {
            // Contravariant domain: a function accepting a *larger* domain (U1) is
            // usable wherever a smaller domain (U0) is expected.
            assert_sub("∀ (A : U0), A -> A", "∀ (A : U1), A -> A", session);
            assert_not_sub("∀ (A : U1), A -> A", "∀ (A : U0), A -> A", session);
            // Covariant codomain: A -> U0 <= A -> U1.
            assert_sub("∀ (A : U0), A -> U1", "∀ (A : U0), A -> U0", session);
            assert_not_sub("∀ (A : U0), A -> U0", "∀ (A : U0), A -> U1", session);
            // Dependent codomain referencing the bound variable: reflexivity of
            // the variable is required for this comparison to close.
            assert_sub("∀ (A : U0), A -> U1", "∀ (A : U1), A -> U1", session);
            assert_not_sub("U1", "∀ (A : U0), A -> A", session);
        });
    }

    #[test]
    fn sigma_cumulativity() {
        crate::cubical::session::with_session_mut(|session| {
            // Covariant in both components.
            assert_sub("Σ (B : U1), B", "Σ (B : U0), B", session);
            assert_not_sub("Σ (B : U0), B", "Σ (B : U1), B", session);
            // Codomain mentioning the bound variable, differing only by universe.
            assert_sub("Σ (B : U0), B -> U1", "Σ (B : U0), B -> U0", session);
            assert_not_sub("Σ (B : U0), B -> U0", "Σ (B : U0), B -> U1", session);
        });
    }

    #[test]
    fn datatype_and_record_cumulativity() {
        crate::cubical::session::with_session_mut(|session| {
            // Identical datatypes are reflexive (empty parameters).
            assert!(sub_t(&tdata("Nat", vec![]), &tdata("Nat", vec![]), session));
            // Covariant datatype parameters (records desugar to TData).
            assert!(sub_t(
                &tdata("Pair", vec![t_univ(1), t_univ(1)]),
                &tdata("Pair", vec![t_univ(0), t_univ(0)]),
                session,
            ));
            assert!(sub_t(
                &tdata("Pair", vec![t_univ(1), tdata("Nat", vec![])]),
                &tdata("Pair", vec![t_univ(0), tdata("Nat", vec![])]),
                session,
            ));
            // Negative: parameters are covariant, not contravariant.
            assert!(!sub_t(
                &tdata("Pair", vec![t_univ(0), t_univ(0)]),
                &tdata("Pair", vec![t_univ(1), t_univ(1)]),
                session,
            ));
            // Negative: different datatypes are incomparable.
            assert!(!sub_t(
                &tdata("Bool", vec![]),
                &tdata("Nat", vec![]),
                session
            ));
            // Record params that are bound variables are reflexive.
            assert!(sub_t(
                &tdata("Pair", vec![Term::TVar(0), Term::TVar(1)]),
                &tdata("Pair", vec![Term::TVar(0), Term::TVar(1)]),
                session,
            ));
        });
    }

    #[test]
    fn bound_variables_are_reflexive() {
        crate::cubical::session::with_session_mut(|session| {
            // TVar(i) <= TVar(i) — required for recursion through dependent
            // codomains to succeed.
            assert_sub("∀ (x : U0), x -> x", "∀ (x : U0), x -> x", session);
            // A variable is not a subtype of a different term (here: U1).
            assert_not_sub("∀ (x : U0), x -> U1", "∀ (x : U0), x -> x", session);
            // Nor is a datatype a subtype of a universe (built directly, since
            // `Nat` is not registered in the standalone `parse_term` parser).
            // `∀ (x : U0), x -> Nat` vs `∀ (x : U0), x -> U1`.
            let pi_x_to = |cod: Term| {
                Term::TPi(
                    "x".into(),
                    Arc::new(Term::TUniv(LevelExpr::LConst(0))),
                    Arc::new(Term::TPi(
                        String::new(),
                        Arc::new(Term::TVar(1)),
                        Arc::new(cod),
                        false,
                    )),
                    false,
                )
            };
            assert!(!sub_t(
                &pi_x_to(t_univ(1)),
                &pi_x_to(tdata("Nat", vec![])),
                session
            ));
        });
    }

    #[test]
    fn path_and_partial_cumulativity() {
        crate::cubical::session::with_session_mut(|session| {
            // Path type component covariant (constant family).
            assert_sub("Path U1 i0 i0", "Path U0 i0 i0", session);
            // Partial: same (bottom) cofibration, body covariant.
            // The top face `i1` is avoided here: nbe_eval collapses `[_ | i1] A`
            // to `A` before the check runs, so the test would compare a `TPartial`
            // against a bare type instead of exercising the TPartial rule.
            assert_sub("[_ | i0] U1", "[_ | i0] U0", session);
            // Negative: body is covariant, not contravariant.
            assert_not_sub("[_ | i0] U0", "[_ | i0] U1", session);
        });
    }

    #[test]
    fn lift_and_lower_cumulativity() {
        crate::cubical::session::with_session_mut(|session| {
            assert!(sub_t(
                &Term::TLift(Arc::new(t_univ(1)), LevelExpr::LConst(1)),
                &Term::TLift(Arc::new(t_univ(0)), LevelExpr::LConst(1)),
                session,
            ));
            assert!(sub_t(
                &Term::TLower(Arc::new(t_univ(1))),
                &Term::TLower(Arc::new(t_univ(0))),
                session,
            ));
            assert!(!sub_t(
                &Term::TLift(Arc::new(t_univ(0)), LevelExpr::LConst(1)),
                &Term::TLift(Arc::new(t_univ(1)), LevelExpr::LConst(1)),
                session,
            ));
        });
    }
}
