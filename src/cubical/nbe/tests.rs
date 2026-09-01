use super::*;
use crate::cubical::interval::{DNF, I, Literal};
use std::collections::BTreeSet;
use std::sync::Mutex;

fn b(t: Term) -> Arc<Term> {
    Arc::new(t)
}

#[test]
fn identity_function_normalizes_to_itself() {
    crate::cubical::session::with_session_mut(|session| {
        let id = Term::TAbs("x".to_string(), b(Term::TVar(0)));
        assert_eq!(nbe_eval(&id, session), id);
    });
}

#[test]
fn beta_reduces_identity_application() {
    crate::cubical::session::with_session_mut(|session| {
        let term = Term::TApp(
            b(Term::TAbs("x".to_string(), b(Term::TVar(0)))),
            b(Term::TUniv(0)),
        );
        assert_eq!(nbe_eval(&term, session), Term::TUniv(0));
    });
}

#[test]
fn fst_of_pair_reduces() {
    crate::cubical::session::with_session_mut(|session| {
        let term = Term::TFst(b(Term::TPair(b(Term::TUniv(0)), b(Term::TUniv(1)))));
        assert_eq!(nbe_eval(&term, session), Term::TUniv(0));
    });
}

#[test]
fn transport_over_constant_family_is_identity() {
    crate::cubical::session::with_session_mut(|session| {
        let family = Term::PLam("i".to_string(), b(Term::TUniv(0)));
        let term = Term::TTransport(b(family), b(Term::TUniv(1)));
        assert_eq!(nbe_eval(&term, session), Term::TUniv(1));
    });
}

#[test]
fn transport_over_nonconstant_pi_produces_lambda() {
    crate::cubical::session::with_session_mut(|session| {
        let body = Term::TPi(
            "x".to_string(),
            b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
            b(Term::TUniv(0)),
            false,
        );
        let fam = Term::PLam("i".to_string(), b(body));
        let arg = Term::TAbs("x".to_string(), b(Term::TUniv(0)));
        let term = Term::TTransport(b(fam), b(arg));
        let result = nbe_eval(&term, session);
        assert!(
            matches!(&result, Term::TAbs(_, _)),
            "expected TAbs, got: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    });
}

#[test]
fn deep_transport_fallback_unsticks_pi() {
    crate::cubical::session::with_session_mut(|session| {
        let body = Term::TPi(
            "x".to_string(),
            b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
            b(Term::TUniv(0)),
            false,
        );
        let fam = Term::PLam("i".to_string(), b(body));
        let arg = Term::TAbs("x".to_string(), b(Term::TUniv(0)));
        let term = Term::TTransport(b(fam), b(arg));
        let result = nbe_eval(&term, session);
        assert!(
            !matches!(result, Term::TTransport(_, _)),
            "transport should not be stuck: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    });
}

#[test]
fn sigma_transport_on_pair_reduces() {
    crate::cubical::session::with_session_mut(|session| {
        let sigma = Term::TSigma("x".to_string(), b(Term::TUniv(0)), b(Term::TUniv(1)));
        let fam = Term::PLam("i".to_string(), b(sigma));
        let pair = Term::TPair(b(Term::TUniv(0)), b(Term::TUniv(1)));
        let term = Term::TTransport(b(fam), b(pair.clone()));
        let result = nbe_eval(&term, session);
        assert_eq!(result, pair);
    });
}

#[test]
fn path_transport_produces_plam() {
    crate::cubical::session::with_session_mut(|session| {
        let path = Term::TPath(
            b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
            b(Term::TUniv(0)),
            b(Term::TUniv(0)),
        );
        let fam = Term::PLam("i".to_string(), b(path));
        let arg = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let term = Term::TTransport(b(fam), b(arg));
        let result = nbe_eval(&term, session);
        assert!(
            matches!(&result, Term::PLam(_, _)),
            "expected PLam, got: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    });
}

#[test]
fn native_pi_transport_no_deep_fallback() {
    crate::cubical::session::with_session_mut(|session| {
        let body = Term::TPi(
            "x".to_string(),
            b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
            b(Term::TUniv(0)),
            false,
        );
        let fam = Term::PLam("i".to_string(), b(body));
        let arg = Term::TAbs("x".to_string(), b(Term::TUniv(0)));
        let term = Term::TTransport(b(fam), b(arg));
        let result = nbe_eval(&term, session);
        assert!(
            matches!(&result, Term::TAbs(_, _)),
            "expected TAbs (native Pi transport), got: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    });
}

#[test]
fn dependent_codomain_pi_transport_reduces() {
    crate::cubical::session::with_session_mut(|session| {
        // Family: λi. (x : i x) → (y : U) → x
        // The codomain (y:U) → x depends on x (the Pi argument), so this
        // exercises the dependent Pi transport code path.
        let body = Term::TPi(
            "x".to_string(),
            b(Term::TApp(b(Term::TVar(1)), b(Term::TVar(0)))),
            b(Term::TPi(
                "y".to_string(),
                b(Term::TUniv(0)),
                b(Term::TVar(1)),
                false,
            )),
            false,
        );
        let fam = Term::PLam("i".to_string(), b(body));
        let arg = Term::TAbs(
            "x".to_string(),
            b(Term::TAbs("y".to_string(), b(Term::TVar(1)))),
        );
        let term = Term::TTransport(b(fam), b(arg));
        let result = nbe_eval(&term, session);
        assert!(
            !matches!(&result, Term::TTransport(_, _)),
            "dependent Pi transport should reduce, got stuck: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
        assert!(
            matches!(&result, Term::TAbs(_, _)),
            "expected TAbs, got: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    });
}

#[test]
fn hcomp_papp_at_zero_reduces_to_base() {
    crate::cubical::session::with_session_mut(|session| {
        // hcomp A [(i0, tube)] base @ 0 should reduce to base
        // (non-trivial face keeps hcomp stuck until papp)
        let tube = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let hcomp = Term::THComp(
            b(Term::TUniv(0)),
            vec![(Term::TInterval(I::Var(0)), tube)],
            b(Term::TUniv(1)),
        );
        let term = Term::PApp(b(hcomp), b(Term::TInterval(I::I0)));
        let result = nbe_eval(&term, session);
        assert_eq!(result, Term::TUniv(1));
    });
}

#[test]
fn hcomp_papp_at_one_reduces_to_tube_at_one() {
    crate::cubical::session::with_session_mut(|session| {
        // hcomp A [(i0, tube)] base @ 1 should reduce to tube @ 1
        let tube = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let hcomp = Term::THComp(
            b(Term::TUniv(0)),
            vec![(Term::TInterval(I::Var(0)), tube)],
            b(Term::TUniv(1)),
        );
        let term = Term::PApp(b(hcomp), b(Term::TInterval(I::I1)));
        let result = nbe_eval(&term, session);
        assert_eq!(result, Term::TUniv(0));
    });
}

#[test]
fn hcomp_const_tube_coherent_reduces_to_base() {
    crate::cubical::session::with_session_mut(|session| {
        // hcomp U [i1 => λj. U0] U0 should reduce to U0 (constant-tube shortcut)
        // Tube PLam("j", U0) is constant (U0 at both I0 and I1) and equals base U0.
        let tube = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let hcomp = Term::THComp(
            b(Term::TUniv(0)),
            vec![(Term::TInterval(I::I1), tube)],
            b(Term::TUniv(0)),
        );
        let result = nbe_eval(&hcomp, session);
        assert_eq!(
            result,
            Term::TUniv(0),
            "constant-tube hcomp should reduce to base"
        );
    });
}

#[test]
fn fill_const_tube_coherent_reduces_to_const_path() {
    crate::cubical::session::with_session_mut(|session| {
        // fill U [i1 => λj. U0] U0 should reduce to λj. U0 (constant-tube shortcut)
        let tube = Term::PLam("j".to_string(), b(Term::TUniv(0)));
        let fill = Term::TFill(
            b(Term::TUniv(0)),
            vec![(Term::TInterval(I::I1), tube)],
            b(Term::TUniv(0)),
        );
        let result = nbe_eval(&fill, session);
        assert!(
            matches!(&result, Term::PLam(_, _)),
            "constant-tube fill should reduce to VPLam (constant path), got: {}",
            crate::cubical::syntax::show_term(&[], &result)
        );
    });
}

#[test]
fn glue_transport_on_glue_elem_decomposes() {
    crate::cubical::session::with_session_mut(|session| {
        // transport (λi. Glue (TVar(i)) [phi] te) (glue [phi] cap base)
        // where phi is non-trivial constant (Pos(1) — different from transport var)
        // A = TVar(0) varies with i (VInterval(I::I0) at i=0, VInterval(I::I1) at i=1)
        // so the family is non-constant and transport_glue is reached.
        //
        // Result: glue [phi] cap (hcomp A_type [phi] (λi. cap) base)
        let non_trivial_phi = Term::TCube(DNF {
            cubes: BTreeSet::from([BTreeSet::from([Literal::Pos(1)])]),
        });
        let glue_ty = Term::TGlue(
            b(Term::TVar(0)), // A varies with i → makes family non-constant
            b(non_trivial_phi.clone()),
            b(Term::TUniv(0)), // te
        );
        let fam = Term::PLam("i".to_string(), b(glue_ty));
        let cap = Term::TUniv(1);
        let base = Term::TUniv(2);
        let glue_elem = Term::TGlueElem(b(non_trivial_phi.clone()), b(cap), b(base));
        let transport = Term::TTransport(b(fam), b(glue_elem));
        let globals: Globals = Arc::new(Mutex::new(Vec::new()));
        let result = eval_nbe(&Scope::empty(), &globals, 0, &transport, session);
        let phi_dnf = DNF {
            cubes: BTreeSet::from([BTreeSet::from([Literal::Pos(1)])]),
        };
        match result {
            Value::VGlueElem(phi, t, a) => {
                assert_eq!(phi, phi_dnf, "face should be the non-trivial phi");
                match &*t {
                    Value::VUniv(n) => assert_eq!(*n, 1, "cap should be U1"),
                    other => panic!("expected VUniv(1) for cap, got: {:?}", other),
                }
                match &*a {
                    Value::VHComp(_, h_sys, h_base) => {
                        // Single-entry system with the expected face
                        assert_eq!(h_sys.len(), 1, "hcomp system should have 1 entry");
                        assert_eq!(h_sys[0].0, phi_dnf, "hcomp face should match");
                        match &**h_base {
                            Value::VUniv(n) => assert_eq!(*n, 2, "hcomp base should be U2"),
                            other => {
                                panic!("expected VUniv(2) for hcomp base, got: {:?}", other)
                            }
                        }
                    }
                    other => panic!("expected VHComp, got: {:?}", other),
                }
            }
            other => panic!("expected VGlueElem, got: {:?}", other),
        }
    });
}

#[test]
fn glue_transport_on_non_glue_elem_stays_stuck() {
    crate::cubical::session::with_session_mut(|session| {
        // transport (λi. Glue (TVar(i)) [phi] te) U0
        // A varies → family non-constant, but input is not GlueElem → stuck
        let non_trivial_phi = Term::TCube(DNF {
            cubes: BTreeSet::from([BTreeSet::from([Literal::Pos(1)])]),
        });
        let glue_ty = Term::TGlue(b(Term::TVar(0)), b(non_trivial_phi), b(Term::TUniv(0)));
        let fam = Term::PLam("i".to_string(), b(glue_ty));
        let transport = Term::TTransport(b(fam), b(Term::TUniv(0)));
        let globals: Globals = Arc::new(Mutex::new(Vec::new()));
        let result = eval_nbe(&Scope::empty(), &globals, 0, &transport, session);
        match result {
            Value::VTransport(_, _) => {}
            other => panic!("expected stuck VTransport, got: {:?}", other),
        }
    });
}

#[test]
fn glue_transport_face_mismatch_stays_stuck() {
    crate::cubical::session::with_session_mut(|session| {
        // transport (λi. Glue (TVar(i)) [phi1] te) (glue [phi2] cap base)
        // phi1 != phi2 → decomposition fails → stuck
        let phi1 = Term::TCube(DNF {
            cubes: BTreeSet::from([BTreeSet::from([Literal::Pos(1)])]),
        });
        let phi2 = Term::TCube(DNF {
            cubes: BTreeSet::from([BTreeSet::from([Literal::NegVar(1)])]),
        });
        let glue_ty = Term::TGlue(b(Term::TVar(0)), b(phi1), b(Term::TUniv(0)));
        let fam = Term::PLam("i".to_string(), b(glue_ty));
        let glue_elem = Term::TGlueElem(b(phi2), b(Term::TUniv(1)), b(Term::TUniv(2)));
        let transport = Term::TTransport(b(fam), b(glue_elem));
        let globals: Globals = Arc::new(Mutex::new(Vec::new()));
        let result = eval_nbe(&Scope::empty(), &globals, 0, &transport, session);
        match result {
            Value::VTransport(_, _) => {}
            other => panic!(
                "expected stuck VTransport on face mismatch, got: {:?}",
                other
            ),
        }
    });
}

#[test]
fn deep_tapp_chain_does_not_overflow() {
    // Build: ((id id) id) ... id  with 10000 applications.
    // The depth guard (EVAL_NBE_MAX_DEPTH=2000) caps the recursion so it
    // doesn't overflow the stack.  The result is a stuck neutral (VNeutral)
    // because the depth limit is hit before full normalization.
    // We use a 64 MiB stack thread (like all example guards) for headroom.
    let n = 10_000;
    let id = Term::TAbs("x".to_string(), b(Term::TVar(0)));
    let mut term = Term::TApp(b(id.clone()), b(id.clone()));
    for _ in 2..n {
        term = Term::TApp(b(term), b(id.clone()));
    }
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            crate::cubical::session::with_session_mut(|session| {
                let empty_globals: super::Globals =
                    std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
                let env = super::Scope::empty();
                let _val = super::eval_nbe(&env, &empty_globals, 0, &term, session);
            });
        })
        .expect("spawn deep tapp test thread");
    handle.join().expect("deep tapp test thread panicked");
}

#[test]
fn deep_tapp_chain_does_not_overflow_small_stack() {
    // Same test as above but on a 2 MiB stack — the default libtest size.
    // With Arc-based Term::clone being O(1), the depth guard at 2000 prevents
    // stack overflow even on a minimal stack.
    let n = 2_500;
    let id = Term::TAbs("x".to_string(), b(Term::TVar(0)));
    let mut term = Term::TApp(b(id.clone()), b(id.clone()));
    for _ in 2..n {
        term = Term::TApp(b(term), b(id.clone()));
    }
    let handle = std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(move || {
            crate::cubical::session::with_session_mut(|session| {
                let empty_globals: super::Globals =
                    std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
                let env = super::Scope::empty();
                let _val = super::eval_nbe(&env, &empty_globals, 0, &term, session);
            });
        })
        .expect("spawn deep tapp test thread");
    handle.join().expect("deep tapp test thread panicked");
}
