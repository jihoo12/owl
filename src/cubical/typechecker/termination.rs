//! Structural recursion / guard checking for the eliminator.
//!
//! The checker verifies that every recursive call in a `TElim` case body
//! is made on a structurally smaller argument — one of the case binders
//! introduced by the pattern match. This ensures termination.

use crate::cubical::session::Session;
use crate::cubical::syntax::{ElimCase, Term};

/// Check if the guard check should be skipped (well-founded recursion mode).
pub fn should_skip_guard(session: &Session) -> bool {
    session.should_skip_guard()
}

/// Set or clear the skip-guard flag.
pub fn set_skip_guard(skip: bool, session: &mut Session) {
    session.set_skip_guard(skip)
}

/// The name of the definition whose body is currently being guard-checked,
/// if any.
pub fn current_def(session: &Session) -> Option<String> {
    session.current_def()
}

/// Set the name of the definition being guard-checked; returns the previous
/// value so callers can restore it.
pub fn set_current_def(name: Option<String>, session: &mut Session) -> Option<String> {
    session.set_current_def(name)
}

/// Result of checking a single case body for structural recursion.
#[derive(Debug, Clone)]
pub enum GuardStatus {
    /// The case body is guarded: all recursive calls use a binder as the
    /// recursive argument (structurally smaller than the scrutinee).
    Ok,
    /// The case body makes a recursive call where the recursive argument
    /// is not one of the case binders — possible non-termination.
    Violation { case: String, msg: String },
}

/// Check that a `TElim` satisfies the structural recursion guard.
///
/// `d` is the name of the datatype being eliminated.
/// `cases` are the eliminator cases.
/// ` scrut_args_count` is the number of binders in each case.
///
/// `def_idx` is the de Bruijn index of the definition being checked in the
/// context of the eliminator (i.e. `ctx` at the `TElim` node, *without* the
/// eliminator's own case binders). Recursive calls that go through the
/// definition's own name are represented as `TApp(TVar(def_idx), ...)` once
/// the case binders are in scope, and are checked just like nested `TElim`
/// recursive calls. Pass `None` when no definition is being checked.
///
/// The check walks each case body looking for nested `TElim` calls and
/// self-references to the definition being checked, both on the same
/// datatype. Each such call must pass a case binder
/// (de Bruijn index in `0..binder_count`) as the recursive argument.
pub fn check_guard(d: &str, cases: &[ElimCase], def_idx: Option<i32>) -> GuardStatus {
    for case in cases {
        let binder_count = case.binders.len() + if case.as_name.is_some() { 1 } else { 0 };
        // The current definition sits just below the eliminator's case
        // binders, so its index is `def_idx + binder_count`.
        let case_def_idx = def_idx.map(|i| i + binder_count as i32);
        if let Err(msg) = check_body_guard(d, &case.body, binder_count, case_def_idx) {
            return GuardStatus::Violation {
                case: case.con.clone(),
                msg,
            };
        }
    }
    GuardStatus::Ok
}

/// Recursively check a term for guarded recursive calls.
///
/// `d` — the datatype being eliminated (recursive calls target this).
/// `body` — the term to check.
/// `binder_count` — number of case binders in scope (de Bruijn 0..binder_count-1).
/// `def_idx` — current de Bruijn index of the definition being checked,
///             `None` when no definition is in scope.
fn check_body_guard(
    d: &str,
    body: &Term,
    binder_count: usize,
    def_idx: Option<i32>,
) -> Result<(), String> {
    match body {
        // Recursive call: TElim on the same datatype.
        Term::TElim(motive, inner_cases, scrut) => {
            // Check if the motive targets our datatype.
            if motive_targets_datatype(d, motive) {
                // The scrutinee of the recursive call must be a case binder
                // (de Bruijn index < binder_count).
                match scrut.as_ref() {
                    Term::TVar(i) => {
                        let idx = *i as usize;
                        if idx < binder_count {
                            Ok(())
                        } else {
                            Err(format!(
                                "recursive call uses variable at index {} \
                                 but only {} case binders are available \
                                 (index {} would be the scrutinee itself)",
                                idx, binder_count, binder_count
                            ))
                        }
                    }
                    other => {
                        // Non-variable scrutinee in recursive call:
                        // we conservatively reject it unless it's a constructor
                        // application (which is structurally decreasing).
                        if is_constructor_of(d, other) {
                            Ok(())
                        } else {
                            Err(format!(
                                "recursive call uses non-variable scrutinee: {:?}",
                                other
                            ))
                        }
                    }
                }
            } else {
                // Different datatype — no guard requirement, but check
                // subterms for nested guard violations against d.
                check_body_guard(d, motive, binder_count, def_idx)?;
                for case in inner_cases {
                    let n = case.binders.len() as i32;
                    check_body_guard(
                        d,
                        &case.body,
                        binder_count + case.binders.len(),
                        def_idx.map(|i| i + n),
                    )?;
                }
                check_body_guard(d, scrut, binder_count, def_idx)
            }
        }

        // Lambda: extend binder count.
        Term::TAbs(_, body) => check_body_guard(d, body, binder_count + 1, def_idx.map(|i| i + 1)),
        Term::PLam(_, body) => check_body_guard(d, body, binder_count, def_idx),

        // Recursive call via TApp/PApp spine: the head is a reference to the
        // definition being checked (`TVar(def_idx)`), applied to arguments.
        Term::TApp(..) | Term::PApp(..) => {
            let (head, args) = peel_app_spine(body);
            if let Some(di) = def_idx {
                if !args.is_empty() {
                    if let Term::TVar(gi) = head {
                        if *gi == di {
                            // A self-call to the definition being checked.
                            // It is guarded iff at least one argument is a
                            // case binder (de Bruijn index < binder_count) —
                            // a strict subterm of the scrutinee.
                            let guarded = args.iter().any(|a| {
                                matches!(a, Term::TVar(i) if *i >= 0 && (*i as usize) < binder_count)
                            });
                            if !guarded {
                                return Err(format!(
                                    "recursive call to the definition being checked \
                                     passes no structurally smaller argument \
                                     ({} case binders are available, so indices 0..{} \
                                     are strictly smaller)",
                                    binder_count, binder_count
                                ));
                            }
                        }
                    }
                }
            }
            check_body_guard(d, head, binder_count, def_idx)?;
            for a in args {
                check_body_guard(d, a, binder_count, def_idx)?;
            }
            Ok(())
        }

        // Sigma, pair, fst, snd — check subterms.
        Term::TSigma(_, a, b) => {
            check_body_guard(d, a, binder_count, def_idx)?;
            check_body_guard(d, b, binder_count + 1, def_idx.map(|i| i + 1))
        }
        Term::TPair(a, b) => {
            check_body_guard(d, a, binder_count, def_idx)?;
            check_body_guard(d, b, binder_count, def_idx)
        }
        Term::TFst(p) | Term::TSnd(p) => check_body_guard(d, p, binder_count, def_idx),

        // Pi — domain is negative, codomain is positive.
        Term::TPi(_, a, b, _) => {
            check_body_guard(d, a, binder_count, def_idx)?;
            check_body_guard(d, b, binder_count + 1, def_idx.map(|i| i + 1))
        }

        // Path type.
        Term::TPath(a, u, v) => {
            check_body_guard(d, a, binder_count, def_idx)?;
            check_body_guard(d, u, binder_count, def_idx)?;
            check_body_guard(d, v, binder_count, def_idx)
        }

        // Identity type.
        Term::TId(a, u, v) => {
            check_body_guard(d, a, binder_count, def_idx)?;
            check_body_guard(d, u, binder_count, def_idx)?;
            check_body_guard(d, v, binder_count, def_idx)
        }
        Term::TRefl(a) => check_body_guard(d, a, binder_count, def_idx),
        Term::TJ(motive, base, p) => {
            check_body_guard(d, motive, binder_count, def_idx)?;
            check_body_guard(d, base, binder_count, def_idx)?;
            check_body_guard(d, p, binder_count, def_idx)
        }

        // Kan operations.
        Term::THComp(a, sys, base)
        | Term::TComp(a, sys, base)
        | Term::TFill(a, sys, base)
        | Term::THFill(a, sys, base) => {
            check_body_guard(d, a, binder_count, def_idx)?;
            for (phi, t) in sys {
                check_body_guard(d, phi, binder_count, def_idx)?;
                check_body_guard(d, t, binder_count, def_idx)?;
            }
            check_body_guard(d, base, binder_count, def_idx)
        }

        // Equiv, transport, glue, etc.
        Term::TEquiv(a, b) | Term::TEquivFwd(a, b) | Term::TTransport(a, b) => {
            check_body_guard(d, a, binder_count, def_idx)?;
            check_body_guard(d, b, binder_count, def_idx)
        }
        Term::TTransp(a, r, x) => {
            check_body_guard(d, a, binder_count, def_idx)?;
            check_body_guard(d, r, binder_count, def_idx)?;
            check_body_guard(d, x, binder_count, def_idx)
        }
        Term::TUa(e) => check_body_guard(d, e, binder_count, def_idx),

        Term::TGlue(a, phi, te) | Term::TGlueElem(a, phi, te) | Term::TUnglue(a, phi, te) => {
            check_body_guard(d, a, binder_count, def_idx)?;
            check_body_guard(d, phi, binder_count, def_idx)?;
            check_body_guard(d, te, binder_count, def_idx)
        }

        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            check_body_guard(d, a, binder_count, def_idx)?;
            check_body_guard(d, b, binder_count, def_idx)?;
            check_body_guard(d, f, binder_count, def_idx)?;
            check_body_guard(d, g, binder_count, def_idx)?;
            check_body_guard(d, eta, binder_count, def_idx)?;
            check_body_guard(d, eps, binder_count, def_idx)
        }

        Term::TPartial(phi, a) => {
            check_body_guard(d, phi, binder_count, def_idx)?;
            check_body_guard(d, a, binder_count, def_idx)
        }

        Term::TSystemType(sys) => {
            for (phi, a) in sys {
                check_body_guard(d, phi, binder_count, def_idx)?;
                check_body_guard(d, a, binder_count, def_idx)?;
            }
            Ok(())
        }

        Term::TCon(_, _, args) | Term::TPCon(_, _, args, _) => {
            for arg in args {
                check_body_guard(d, arg, binder_count, def_idx)?;
            }
            Ok(())
        }
        Term::TSqCon(_, _, args, r, s) => {
            for arg in args {
                check_body_guard(d, arg, binder_count, def_idx)?;
            }
            check_body_guard(d, r, binder_count, def_idx)?;
            check_body_guard(d, s, binder_count, def_idx)
        }
        Term::TCellCon(_, _, args, ivars) => {
            for arg in args {
                check_body_guard(d, arg, binder_count, def_idx)?;
            }
            for iv in ivars {
                check_body_guard(d, iv, binder_count, def_idx)?;
            }
            Ok(())
        }

        // Atoms — no recursion possible.
        Term::TVar(_)
        | Term::TUniv(_)
        | Term::TProp
        | Term::TSSet
        | Term::TIntervalTy
        | Term::TInterval(_)
        | Term::TCube(_)
        | Term::TData(_, _)
        | Term::Meta(_) => Ok(()),

        Term::TBy(_) | Term::TLift(_, _) | Term::TLower(_) => Ok(()),

        // Record projection — recurse into the record term.
        Term::TProj(_, r) => check_body_guard(d, r, binder_count, def_idx),

        // Record update — recurse into record and update values.
        Term::TRecordUpdate(r, updates) => {
            check_body_guard(d, r, binder_count, def_idx)?;
            for (_, e) in updates {
                check_body_guard(d, e, binder_count, def_idx)?;
            }
            Ok(())
        }

        // Coinduction — recurse into subterms.
        Term::TDelay(a) | Term::TNext(a) | Term::TForce(a) => {
            check_body_guard(d, a, binder_count, def_idx)
        }
    }
}

/// Peel the application spine off `t`, returning the head and every argument
/// (term arguments via `TApp`, interval arguments via `PApp`).
fn peel_app_spine(t: &Term) -> (&Term, Vec<&Term>) {
    match t {
        Term::TApp(f, a) | Term::PApp(f, a) => {
            let (head, mut args) = peel_app_spine(f);
            args.push(a.as_ref());
            (head, args)
        }
        other => (other, Vec::new()),
    }
}

/// Check if a motive (TAbs-shaped) targets the given datatype.
fn motive_targets_datatype(d: &str, motive: &Term) -> bool {
    match motive {
        Term::TAbs(_, body) => motive_targets_datatype(d, body),
        Term::TApp(f, a) => {
            matches!(a.as_ref(), Term::TData(name, _) if name == d) || motive_targets_datatype(d, f)
        }
        Term::TData(name, _) => name == d,
        _ => false,
    }
}

/// Check if a term is a constructor application of the given datatype.
fn is_constructor_of(d: &str, t: &Term) -> bool {
    match t {
        Term::TCon(name, _, _) => name == d,
        Term::TPCon(name, _, _, _) => name == d,
        Term::TSqCon(name, _, _, _, _) => name == d,
        Term::TCellCon(name, _, _, _) => name == d,
        _ => false,
    }
}
