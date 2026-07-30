//! Structural recursion / guard checking for the eliminator.
//!
//! The checker verifies that every recursive call in a `TElim` case body
//! is made on a structurally smaller argument — one of the case binders
//! introduced by the pattern match. This ensures termination.

use std::cell::Cell;

use crate::cubical::syntax::{ElimCase, Term};

// Thread-local flag to skip the structural guard check.
// Set by `process_def` when a definition is annotated with `by_wf`.
thread_local! {
    static SKIP_GUARD: Cell<bool> = Cell::new(false);
}

/// Check if the guard check should be skipped (well-founded recursion mode).
pub fn should_skip_guard() -> bool {
    SKIP_GUARD.with(|f| f.get())
}

/// Set or clear the skip-guard flag.
pub fn set_skip_guard(skip: bool) {
    SKIP_GUARD.with(|f| f.set(skip));
}

/// Result of checking a single case body for structural recursion.
#[derive(Debug, Clone)]
pub enum GuardStatus {
    /// The case body is guarded: all recursive calls use a binder as the
    /// recursive argument (structurally smaller than the scrutinee).
    Ok,
    /// The case body makes a recursive call where the recursive argument
    /// is not one of the case binders — possible non-termination.
    Violation {
        case: String,
        msg: String,
    },
}

/// Check that a `TElim` satisfies the structural recursion guard.
///
/// `d` is the name of the datatype being eliminated.
/// `cases` are the eliminator cases.
/// ` scrut_args_count` is the number of binders in each case.
///
/// The check walks each case body looking for nested `TElim` calls
/// on the same datatype. Each such call must pass a case binder
/// (de Bruijn index in `0..binder_count`) as the recursive argument.
pub fn check_guard(
    d: &str,
    cases: &[ElimCase],
) -> GuardStatus {
    for case in cases {
        let binder_count = case.binders.len()
            + if case.as_name.is_some() { 1 } else { 0 };
        if let Err(msg) = check_body_guard(d, &case.body, binder_count) {
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
fn check_body_guard(
    d: &str,
    body: &Term,
    binder_count: usize,
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
                check_body_guard(d, motive, binder_count)?;
                for case in inner_cases {
                    check_body_guard(d, &case.body, binder_count + case.binders.len())?;
                }
                check_body_guard(d, scrut, binder_count)
            }
        }

        // Lambda: extend binder count.
        Term::TAbs(_, body) => check_body_guard(d, body, binder_count + 1),
        Term::PLam(_, body) => check_body_guard(d, body, binder_count),

        // Recursive call via TApp(TElim(...), arg): check the TElim part.
        Term::TApp(f, a) => {
            check_body_guard(d, f, binder_count)?;
            check_body_guard(d, a, binder_count)
        }
        Term::PApp(f, a) => {
            check_body_guard(d, f, binder_count)?;
            check_body_guard(d, a, binder_count)
        }

        // Sigma, pair, fst, snd — check subterms.
        Term::TSigma(_, a, b) => {
            check_body_guard(d, a, binder_count)?;
            check_body_guard(d, b, binder_count + 1)
        }
        Term::TPair(a, b) => {
            check_body_guard(d, a, binder_count)?;
            check_body_guard(d, b, binder_count)
        }
        Term::TFst(p) | Term::TSnd(p) => check_body_guard(d, p, binder_count),

        // Pi — domain is negative, codomain is positive.
        Term::TPi(_, a, b) => {
            check_body_guard(d, a, binder_count)?;
            check_body_guard(d, b, binder_count + 1)
        }

        // Path type.
        Term::TPath(a, u, v) => {
            check_body_guard(d, a, binder_count)?;
            check_body_guard(d, u, binder_count)?;
            check_body_guard(d, v, binder_count)
        }

        // Kan operations.
        Term::THComp(a, sys, base)
        | Term::TComp(a, sys, base)
        | Term::TFill(a, sys, base)
        | Term::THFill(a, sys, base) => {
            check_body_guard(d, a, binder_count)?;
            for (phi, t) in sys {
                check_body_guard(d, phi, binder_count)?;
                check_body_guard(d, t, binder_count)?;
            }
            check_body_guard(d, base, binder_count)
        }

        // Equiv, transport, glue, etc.
        Term::TEquiv(a, b) | Term::TEquivFwd(a, b) | Term::TTransport(a, b) => {
            check_body_guard(d, a, binder_count)?;
            check_body_guard(d, b, binder_count)
        }
        Term::TUa(e) => check_body_guard(d, e, binder_count),

        Term::TGlue(a, phi, te) | Term::TGlueElem(a, phi, te) | Term::TUnglue(a, phi, te) => {
            check_body_guard(d, a, binder_count)?;
            check_body_guard(d, phi, binder_count)?;
            check_body_guard(d, te, binder_count)
        }

        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            check_body_guard(d, a, binder_count)?;
            check_body_guard(d, b, binder_count)?;
            check_body_guard(d, f, binder_count)?;
            check_body_guard(d, g, binder_count)?;
            check_body_guard(d, eta, binder_count)?;
            check_body_guard(d, eps, binder_count)
        }

        Term::TPartial(phi, a) => {
            check_body_guard(d, phi, binder_count)?;
            check_body_guard(d, a, binder_count)
        }

        Term::TSystemType(sys) => {
            for (phi, a) in sys {
                check_body_guard(d, phi, binder_count)?;
                check_body_guard(d, a, binder_count)?;
            }
            Ok(())
        }

        Term::TCon(_, _, args) | Term::TPCon(_, _, args, _) => {
            for arg in args {
                check_body_guard(d, arg, binder_count)?;
            }
            Ok(())
        }
        Term::TSqCon(_, _, args, r, s) => {
            for arg in args {
                check_body_guard(d, arg, binder_count)?;
            }
            check_body_guard(d, r, binder_count)?;
            check_body_guard(d, s, binder_count)
        }
        Term::TCellCon(_, _, args, ivars) => {
            for arg in args {
                check_body_guard(d, arg, binder_count)?;
            }
            for iv in ivars {
                check_body_guard(d, iv, binder_count)?;
            }
            Ok(())
        }

        // Atoms — no recursion possible.
        Term::TVar(_) | Term::TUniv(_) | Term::TProp | Term::TSSet
        | Term::TIntervalTy | Term::TInterval(_) | Term::TCube(_)
        | Term::TData(_, _) | Term::Meta(_) => Ok(()),

        Term::TBy(_) | Term::TLift(_, _) | Term::TLower(_) => Ok(()),

        // Record projection — recurse into the record term.
        Term::TProj(_, r) => check_body_guard(d, r, binder_count),

        // Record update — recurse into record and update values.
        Term::TRecordUpdate(r, updates) => {
            check_body_guard(d, r, binder_count)?;
            for (_, e) in updates {
                check_body_guard(d, e, binder_count)?;
            }
            Ok(())
        }

        // Coinduction — recurse into subterms.
        Term::TDelay(a) | Term::TNext(a) | Term::TForce(a) => {
            check_body_guard(d, a, binder_count)
        }
    }
}

/// Check if a motive (TAbs-shaped) targets the given datatype.
fn motive_targets_datatype(d: &str, motive: &Term) -> bool {
    match motive {
        Term::TAbs(_, body) => motive_targets_datatype(d, body),
        Term::TApp(f, a) => {
            matches!(a.as_ref(), Term::TData(name, _) if name == d)
                || motive_targets_datatype(d, f)
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
