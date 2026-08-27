//! Strict positivity checking for datatype declarations, plus a per-parameter
//! variance analysis used to keep `TData` cumulativity sound.

use std::fmt;

use super::{Datatype, Name, Term};

/// Variance of a datatype parameter, derived from its occurrences in the
/// datatype's constructor argument types.
///
/// The subtyping rule for `TData(d, ps) ≤ TData(d, ps')` must respect the
/// variance of each parameter `i`:
/// - `Covariant`:  `ps[i] ≤ ps'[i]`
/// - `Contravariant`: `ps'[i] ≤ ps[i]`
/// - `Invariant`: `ps[i] == ps'[i]` (definitional equality)
/// - `Unused`: the parameter never occurs; both directions are harmless, so
///   it is treated as covariant (a covariant check is always sound for an
///   unused parameter — it may be incomplete, never unsound).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Variance {
    Covariant,
    Contravariant,
    Invariant,
    Unused,
}

/// Polarity bits: a parameter occurrence is tracked as appearing in positive
/// and/or negative positions. `0` means no occurrence yet.
const POL_POS: u8 = 0b01;
const POL_NEG: u8 = 0b10;

/// Swap positive and negative bits (used when crossing an arrow domain).
fn flip_pol(p: u8) -> u8 {
    ((p & POL_POS) << 1) | ((p & POL_NEG) >> 1)
}

/// Polarity-set product: `p ⊗ v`. Used when the parameter occurs inside the
/// argument of a nested `TData` application whose own parameter has variance
/// `v`: positive ⊗ positive = positive, positive ⊗ negative = negative, etc.
fn mul_pol(p: u8, v: u8) -> u8 {
    let mut r = 0;
    if p & POL_POS != 0 {
        r |= v;
    }
    if p & POL_NEG != 0 {
        r |= flip_pol(v);
    }
    r
}

/// Walk `ty`, recording into `out` (indexed by the parameter index of
/// `dts[di]`) the polarity with which each parameter occurs.
///
/// - `depth`: number of binders entered below the starting scope. The
///   datatype's parameters live at de Bruijn indices `nparams - 1 - i` inside
///   constructor argument types (index 0 in a fresh scope), so a `TVar(k)`
///   refers to parameter `nparams - 1 - (k - depth)` when `k >= depth`.
///   Indices below `depth` are constructor-argument or interval binders and
///   are ignored (they are value positions, not type positions).
/// - `pset`: the polarity set accumulated so far. Starts as `POL_POS` at the
///   root of a constructor argument type.
///
/// Occurrences whose polarity cannot be established are walked at *both*
/// polarities, which forces the parameter to be invariant — a sound
/// under-approximation (over-restrictive, never unsound).
fn walk_param_polarities(
    dts: &[Datatype],
    var: &[Vec<u8>],
    di: usize,
    ty: &Term,
    depth: usize,
    pset: u8,
    out: &mut [u8],
) {
    let nparams = dts[di].params.len();
    match ty {
        Term::TVar(k) => {
            let idx = *k as usize;
            if idx >= depth {
                let j = nparams as i64 - 1 - (idx as i64 - depth as i64);
                if j >= 0 && (j as usize) < nparams {
                    out[j as usize] |= pset;
                }
            }
        }
        // Arrow: the domain is a negative position, the codomain positive.
        Term::TPi(_, a, b, _) => {
            walk_param_polarities(dts, var, di, a, depth, flip_pol(pset), out);
            walk_param_polarities(dts, var, di, b, depth + 1, pset, out);
        }
        // Sigma: both components are positive positions.
        Term::TSigma(_, a, b) => {
            walk_param_polarities(dts, var, di, a, depth, pset, out);
            walk_param_polarities(dts, var, di, b, depth + 1, pset, out);
        }
        Term::TAbs(_, body) => {
            walk_param_polarities(dts, var, di, body, depth + 1, pset, out);
        }
        Term::PLam(_, body) => {
            walk_param_polarities(dts, var, di, body, depth + 1, pset, out);
        }
        // Nested datatype application: the `k`-th argument passes through the
        // variance of the referenced datatype's `k`-th parameter.
        Term::TData(name, args) => {
            if let Some(dj) = dts.iter().position(|d| &d.name == name) {
                for (k, arg) in args.iter().enumerate() {
                    if let Some(v) = var[dj].get(k) {
                        walk_param_polarities(dts, var, di, arg, depth, mul_pol(pset, *v), out);
                    } else {
                        // Too many arguments for the referenced datatype
                        // (should not occur in well-typed code): treat the
                        // extra argument conservatively as invariant.
                        walk_param_polarities(dts, var, di, arg, depth, pset, out);
                        walk_param_polarities(dts, var, di, arg, depth, flip_pol(pset), out);
                    }
                }
            } else {
                // Datatype not in scope: conservative — treat occurrences
                // inside its arguments as invariant.
                for arg in args {
                    walk_param_polarities(dts, var, di, arg, depth, pset, out);
                    walk_param_polarities(dts, var, di, arg, depth, flip_pol(pset), out);
                }
            }
        }
        // Clear type positions: covariant in every component.
        Term::TPath(a, u, v) => {
            walk_param_polarities(dts, var, di, a, depth, pset, out);
            walk_param_polarities(dts, var, di, u, depth, pset, out);
            walk_param_polarities(dts, var, di, v, depth, pset, out);
        }
        Term::TPartial(phi, a) => {
            walk_param_polarities(dts, var, di, phi, depth, pset, out);
            walk_param_polarities(dts, var, di, a, depth, pset, out);
        }
        Term::TSystemType(sys) => {
            for (phi, a) in sys {
                walk_param_polarities(dts, var, di, phi, depth, pset, out);
                walk_param_polarities(dts, var, di, a, depth, pset, out);
            }
        }
        Term::TLift(a, _) | Term::TLower(a) => {
            walk_param_polarities(dts, var, di, a, depth, pset, out);
        }
        // Delay is covariant (single constructor `Next : A -> Delay A`).
        Term::TDelay(a) | Term::TNext(a) | Term::TForce(a) => {
            walk_param_polarities(dts, var, di, a, depth, pset, out);
        }
        // Leaves.
        Term::TUniv(_)
        | Term::TProp
        | Term::TSSet
        | Term::TIntervalTy
        | Term::TInterval(_)
        | Term::TCube(_)
        | Term::Meta(_)
        | Term::TBy(_) => {}
        // Remaining forms put subterms in positions whose polarity we cannot
        // establish — walk every subterm at both polarities (invariant).
        other => walk_param_polarities_both(dts, var, di, other, depth, pset, out),
    }
}

/// Conservative fallback: walk `ty`'s subterms at both polarities so that any
/// parameter occurrence inside forces invariance.
fn walk_param_polarities_both(
    dts: &[Datatype],
    var: &[Vec<u8>],
    di: usize,
    ty: &Term,
    depth: usize,
    pset: u8,
    out: &mut [u8],
) {
    fn both(
        dts: &[Datatype],
        var: &[Vec<u8>],
        di: usize,
        children: &[&Term],
        depth: usize,
        pset: u8,
        out: &mut [u8],
    ) {
        for c in children {
            walk_param_polarities(dts, var, di, c, depth, pset, out);
            walk_param_polarities(dts, var, di, c, depth, flip_pol(pset), out);
        }
    }
    match ty {
        Term::TApp(f, a) | Term::PApp(f, a) => {
            both(dts, var, di, &[f.as_ref(), a.as_ref()], depth, pset, out);
        }
        Term::TEquiv(f, a) | Term::TEquivFwd(f, a) | Term::TTransport(f, a) | Term::TPair(f, a) => {
            both(dts, var, di, &[f.as_ref(), a.as_ref()], depth, pset, out);
        }
        Term::TFst(p) | Term::TSnd(p) | Term::TUa(p) | Term::TProj(_, p) => {
            both(dts, var, di, &[p.as_ref()], depth, pset, out);
        }
        Term::THComp(a, sys, u0)
        | Term::TComp(a, sys, u0)
        | Term::TFill(a, sys, u0)
        | Term::THFill(a, sys, u0) => {
            both(dts, var, di, &[a.as_ref(), u0.as_ref()], depth, pset, out);
            for (phi, t) in sys {
                both(dts, var, di, &[phi, t], depth, pset, out);
            }
        }
        Term::TGlue(a, u, v) | Term::TGlueElem(a, u, v) | Term::TUnglue(a, u, v) => {
            both(
                dts,
                var,
                di,
                &[a.as_ref(), u.as_ref(), v.as_ref()],
                depth,
                pset,
                out,
            );
        }
        Term::TMkEquiv(a, b, f, g, eta, eps) => {
            both(
                dts,
                var,
                di,
                &[
                    a.as_ref(),
                    b.as_ref(),
                    f.as_ref(),
                    g.as_ref(),
                    eta.as_ref(),
                    eps.as_ref(),
                ],
                depth,
                pset,
                out,
            );
        }
        Term::TCon(_, _, args) => {
            for a in args {
                both(dts, var, di, &[a], depth, pset, out);
            }
        }
        Term::TPCon(_, _, args, r) => {
            for a in args {
                both(dts, var, di, &[a], depth, pset, out);
            }
            both(dts, var, di, &[r.as_ref()], depth, pset, out);
        }
        Term::TSqCon(_, _, args, r, s) => {
            for a in args {
                both(dts, var, di, &[a], depth, pset, out);
            }
            both(dts, var, di, &[r.as_ref(), s.as_ref()], depth, pset, out);
        }
        Term::TCellCon(_, _, args, ivars) => {
            for a in args {
                both(dts, var, di, &[a], depth, pset, out);
            }
            for v in ivars {
                both(dts, var, di, &[v], depth, pset, out);
            }
        }
        Term::TElim(motive, cases, scrut) => {
            both(
                dts,
                var,
                di,
                &[motive.as_ref(), scrut.as_ref()],
                depth,
                pset,
                out,
            );
            for case in cases {
                both(dts, var, di, &[&case.body], depth, pset, out);
            }
        }
        Term::TRecordUpdate(r, updates) => {
            both(dts, var, di, &[r.as_ref()], depth, pset, out);
            for (_, e) in updates {
                both(dts, var, di, &[e], depth, pset, out);
            }
        }
        _ => {}
    }
}

/// Compute the variance of every parameter of every datatype in `dts`.
///
/// Returns a vector parallel to `dts`; entry `i` holds the variance of each
/// parameter of `dts[i]` in declaration (outermost-first) order.
///
/// The analysis is a least fixed point over all datatypes in `dts`: mutually
/// recursive datatypes and nested datatype applications resolve through the
/// variance of the referenced datatype's parameters. Any occurrence whose
/// polarity cannot be established is treated as invariant, so the result is
/// always a sound under-approximation.
pub fn compute_param_variances(dts: &[Datatype]) -> Vec<Vec<Variance>> {
    let n = dts.len();
    let mut var: Vec<Vec<u8>> = dts.iter().map(|dt| vec![0u8; dt.params.len()]).collect();
    loop {
        let mut next = var.clone();
        let mut changed = false;
        for di in 0..n {
            let mut contrib = vec![0u8; dts[di].params.len()];
            // Constructor argument types reference only the datatype
            // parameters (via de Bruijn `nparams - 1 - i`), so the walk
            // starts at depth 0. Dependent fields (references to earlier
            // arguments) are not supported.
            for con in &dts[di].cons {
                for at in &con.arg_tys {
                    walk_param_polarities(dts, &var, di, at, 0, POL_POS, &mut contrib);
                }
            }
            for pcon in &dts[di].pcons {
                for at in &pcon.arg_tys {
                    walk_param_polarities(dts, &var, di, at, 0, POL_POS, &mut contrib);
                }
                // Faces live in the scope of the constructor's ordinary
                // arguments (`arg_tys.len()` binders).
                let d = pcon.arg_tys.len();
                walk_param_polarities(dts, &var, di, &pcon.face0, d, POL_POS, &mut contrib);
                walk_param_polarities(dts, &var, di, &pcon.face1, d, POL_POS, &mut contrib);
            }
            for sqcon in &dts[di].sqcons {
                for at in &sqcon.arg_tys {
                    walk_param_polarities(dts, &var, di, at, 0, POL_POS, &mut contrib);
                }
                let d = sqcon.arg_tys.len();
                for face in [
                    &sqcon.face_i0,
                    &sqcon.face_i1,
                    &sqcon.face_j0,
                    &sqcon.face_j1,
                ] {
                    walk_param_polarities(dts, &var, di, face, d, POL_POS, &mut contrib);
                }
            }
            for cellcon in &dts[di].cellcons {
                for at in &cellcon.arg_tys {
                    walk_param_polarities(dts, &var, di, at, 0, POL_POS, &mut contrib);
                }
                let d = cellcon.arg_tys.len();
                for face in &cellcon.faces {
                    walk_param_polarities(dts, &var, di, face, d, POL_POS, &mut contrib);
                }
            }
            for (i, c) in contrib.iter().enumerate() {
                let merged = var[di][i] | c;
                if merged != var[di][i] {
                    next[di][i] = merged;
                    changed = true;
                }
            }
        }
        var = next;
        if !changed {
            break;
        }
    }
    var.into_iter()
        .map(|row| {
            row.into_iter()
                .map(|bits| match bits {
                    0 => Variance::Unused,
                    POL_POS => Variance::Covariant,
                    POL_NEG => Variance::Contravariant,
                    _ => Variance::Invariant,
                })
                .collect()
        })
        .collect()
}

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
        Term::TProp | Term::TSSet => Ok(()),
        Term::TLift(a, _) | Term::TLower(a) => check_positivity_in(target, a, negative),
        Term::TData(name, params) => {
            if name == target && negative {
                Err(PositivityError {
                    datatype: target.to_string(),
                    constructor: String::new(),
                    message: format!("datatype '{}' appears on the left side of an arrow", target),
                })
            } else {
                for p in params {
                    check_positivity_in(target, p, negative)?;
                }
                Ok(())
            }
        }
        Term::TApp(f, a)
        | Term::PApp(f, a)
        | Term::TEquiv(f, a)
        | Term::TEquivFwd(f, a)
        | Term::TTransport(f, a)
        | Term::TPair(f, a) => {
            check_positivity_in(target, f, negative)?;
            check_positivity_in(target, a, negative)
        }
        Term::TFst(p) | Term::TSnd(p) => check_positivity_in(target, p, negative),
        Term::TAbs(_, body) | Term::PLam(_, body) | Term::TUa(body) => {
            check_positivity_in(target, body, negative)
        }
        Term::TPi(_, a, b, _) => {
            // Domain A is in a negative position (argument position).
            check_positivity_in(target, a, true)?;
            // Codomain B is in a positive position (result position).
            check_positivity_in(target, b, false)
        }
        Term::TSigma(_, a, b) => {
            check_positivity_in(target, a, negative)?;
            check_positivity_in(target, b, negative)
        }
        Term::TPath(a, u, v)
        | Term::TGlue(a, u, v)
        | Term::TGlueElem(a, u, v)
        | Term::TUnglue(a, u, v) => {
            check_positivity_in(target, a, negative)?;
            check_positivity_in(target, u, negative)?;
            check_positivity_in(target, v, negative)
        }
        Term::TPartial(phi, a) => {
            check_positivity_in(target, phi, negative)?;
            check_positivity_in(target, a, negative)
        }
        Term::TSystemType(sys) => {
            for (phi, a) in sys {
                check_positivity_in(target, phi, negative)?;
                check_positivity_in(target, a, negative)?;
            }
            Ok(())
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
        Term::TCellCon(_, _, args, ivars) => {
            for a in args {
                check_positivity_in(target, a, negative)?;
            }
            for v in ivars {
                check_positivity_in(target, v, negative)?;
            }
            Ok(())
        }
        Term::TProj(_, r) => check_positivity_in(target, r, negative),
        Term::TRecordUpdate(r, updates) => {
            check_positivity_in(target, r, negative)?;
            for (_, e) in updates {
                check_positivity_in(target, e, negative)?;
            }
            Ok(())
        }
        Term::TDelay(a) | Term::TNext(a) | Term::TForce(a) => {
            check_positivity_in(target, a, negative)
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
            e.message = format!("face0 of path constructor '{}': {}", pcon.name, e.message);
            e
        })?;
        check_positivity_in(&dt.name, &pcon.face1, false).map_err(|mut e| {
            e.constructor = pcon.name.clone();
            e.message = format!("face1 of path constructor '{}': {}", pcon.name, e.message);
            e
        })?;
    }
    for cellcon in &dt.cellcons {
        check_con_positivity(&dt.name, &cellcon.name, &cellcon.arg_tys)?;
        for (fi, face) in cellcon.faces.iter().enumerate() {
            check_positivity_in(&dt.name, face, false).map_err(|mut e| {
                e.constructor = cellcon.name.clone();
                e.message = format!(
                    "face{} of cell constructor '{}': {}",
                    fi, cellcon.name, e.message
                );
                e
            })?;
        }
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
                ConSig {
                    name: "zero".into(),
                    arg_tys: vec![],
                },
                ConSig {
                    name: "suc".into(),
                    arg_tys: vec![Term::TData("Nat".into(), vec![])],
                },
            ],
            pcons: vec![],
            sqcons: vec![],
            cellcons: vec![],
            universe_level: None,
            field_names: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn positive_list_is_ok() {
        let dt = Datatype {
            name: "List".into(),
            params: vec![],
            cons: vec![
                ConSig {
                    name: "nil".into(),
                    arg_tys: vec![],
                },
                ConSig {
                    name: "cons".into(),
                    arg_tys: vec![Term::TUniv(0), Term::TData("List".into(), vec![])],
                },
            ],
            pcons: vec![],
            sqcons: vec![],
            cellcons: vec![],
            universe_level: None,
            field_names: None,
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
                    b(Term::TPi(
                        "_".into(),
                        b(Term::TData("Nat".into(), vec![])),
                        b(Term::TData("Nat".into(), vec![])),
                        false,
                    )),
                    b(Term::TData("Nat".into(), vec![])),
                    false,
                )],
            }],
            pcons: vec![],
            sqcons: vec![],
            cellcons: vec![],
            universe_level: None,
            field_names: None,
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
                    false,
                )],
            }],
            pcons: vec![],
            sqcons: vec![],
            cellcons: vec![],
            universe_level: None,
            field_names: None,
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
                        false,
                    )),
                    b(Term::TData("Bad".into(), vec![])),
                    false,
                )],
            }],
            pcons: vec![],
            sqcons: vec![],
            cellcons: vec![],
            universe_level: None,
            field_names: None,
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
                        false,
                    )),
                    b(Term::TData("Bad".into(), vec![])),
                    false,
                )],
            }],
            pcons: vec![],
            sqcons: vec![],
            cellcons: vec![],
            universe_level: None,
            field_names: None,
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
            cellcons: vec![],
            universe_level: None,
            field_names: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    #[test]
    fn positive_path_type_is_ok() {
        let dt = Datatype {
            name: "S1".into(),
            params: vec![],
            cons: vec![ConSig {
                name: "base".into(),
                arg_tys: vec![],
            }],
            pcons: vec![PConSig {
                name: "loop".into(),
                arg_tys: vec![],
                face0: Term::TCon("S1".into(), "base".into(), vec![]),
                face1: Term::TCon("S1".into(), "base".into(), vec![]),
            }],
            sqcons: vec![],
            cellcons: vec![],
            universe_level: None,
            field_names: None,
        };
        assert!(check_datatype_positivity(&dt).is_ok());
    }

    // -----------------------------------------------------------------------
    // Parameter variance
    // -----------------------------------------------------------------------

    fn var_dt(name: &str, arg_tys: Vec<Term>) -> Datatype {
        Datatype {
            name: name.into(),
            params: vec![("A".into(), Term::TUniv(0))],
            cons: vec![ConSig {
                name: "mk".into(),
                arg_tys,
            }],
            pcons: vec![],
            sqcons: vec![],
            cellcons: vec![],
            universe_level: None,
            field_names: None,
        }
    }

    fn var_of(dt: &Datatype) -> Variance {
        compute_param_variances(&[dt.clone()])[0][0]
    }

    #[test]
    fn record_param_is_covariant() {
        assert_eq!(
            var_of(&var_dt("R", vec![Term::TVar(0)])),
            Variance::Covariant
        );
    }

    #[test]
    fn param_in_arrow_domain_is_contravariant() {
        let dt = var_dt(
            "Bad",
            vec![Term::TPi(
                "_".into(),
                b(Term::TVar(0)),
                b(Term::TUniv(0)),
                false,
            )],
        );
        assert_eq!(var_of(&dt), Variance::Contravariant);
    }

    #[test]
    fn param_both_positions_is_invariant() {
        let dt = var_dt(
            "Bad",
            vec![
                Term::TVar(0),
                Term::TPi("_".into(), b(Term::TVar(0)), b(Term::TUniv(0)), false),
            ],
        );
        assert_eq!(var_of(&dt), Variance::Invariant);
    }

    #[test]
    fn param_unused_in_any_constructor() {
        assert_eq!(var_of(&var_dt("C", vec![Term::TUniv(0)])), Variance::Unused);
    }

    #[test]
    fn recursive_covariant_param_stays_covariant() {
        // List (A) with `cons : A -> List A -> List A` is covariant in A.
        let dt = var_dt(
            "List",
            vec![
                Term::TVar(0),
                Term::TData("List".into(), vec![Term::TVar(0)]),
            ],
        );
        assert_eq!(var_of(&dt), Variance::Covariant);
    }

    #[test]
    fn variance_propagates_through_nested_datatypes() {
        // Bar (A) is contravariant; Foo (A) with `mk : Bar A -> Foo A` must
        // inherit that contravariance from the nested application.
        let bar = var_dt(
            "Bar",
            vec![Term::TPi(
                "_".into(),
                b(Term::TVar(0)),
                b(Term::TUniv(0)),
                false,
            )],
        );
        let foo = var_dt("Foo", vec![Term::TData("Bar".into(), vec![Term::TVar(0)])]);
        let variances = compute_param_variances(&[bar, foo]);
        assert_eq!(variances[0], vec![Variance::Contravariant]);
        assert_eq!(variances[1], vec![Variance::Contravariant]);
    }

    #[test]
    fn mutual_recursion_resolves_variance_fixed_point() {
        // Even/E (A): `ev : E A -> Even A` and `od : Even A -> E A`.
        // A never occurs in a constructor argument, so both are Unused, and
        // the fixed point must terminate with that answer.
        let even = var_dt("Even", vec![Term::TData("E".into(), vec![Term::TVar(0)])]);
        let e = var_dt("E", vec![Term::TData("Even".into(), vec![Term::TVar(0)])]);
        let variances = compute_param_variances(&[even, e]);
        assert_eq!(variances[0], vec![Variance::Unused]);
        assert_eq!(variances[1], vec![Variance::Unused]);
    }
}
