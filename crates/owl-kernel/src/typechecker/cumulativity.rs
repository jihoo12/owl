// Universe cumulativity and subtyping checks for the typechecker.

use std::sync::Arc;

use crate::interval::{DNF, dnf_leq};
use crate::nbe::nbe_eval;
use crate::session::Session;
use crate::syntax::{Datatype, LevelExpr, Term, Variance, compute_param_variances};

/// Extract a DNF from a term that is known to represent a face (TCube or TInterval).
pub fn term_to_dnf(t: &Term, session: &mut Session) -> DNF {
    match nbe_eval(t, session) {
        Term::TCube(d) => d,
        Term::TInterval(i) => crate::interval::eval_interval(&i),
        _ => crate::interval::dnf_bot(),
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

        // Pi cumulativity: contravariant in domain, covariant in codomain.
        // Implicit flags must match — implicit and explicit Pi types
        // are not interconvertible under subtyping.
        (Term::TPi(_, a_exp, b_exp, imp_exp), Term::TPi(_, a_inf, b_inf, imp_inf)) => {
            imp_exp == imp_inf
                && cumulativity_check(a_inf, a_exp, dts, session)
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

impl crate::equality::EtaResult {
    pub(crate) fn is_equal(&self) -> bool {
        *self == crate::equality::EtaResult::Equal
    }
}
