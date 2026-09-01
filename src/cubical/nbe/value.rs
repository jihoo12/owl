//! Core NbE runtime types: scopes, values, neutrals and closures.
//!
//! Split out of the former monolithic `nbe/mod.rs`; the module tree is
//! documented in `mod.rs`.
#![allow(clippy::enum_variant_names)]

use std::fmt;
use std::sync::{Arc, Mutex};

use super::eval::{eval_nbe, subst_interval_var};
use super::quote::quote;
use crate::cubical::debug;
use crate::cubical::interval::{DNF, I};
use crate::cubical::session::Session;
use crate::cubical::syntax::{ElimCase, Level, Name, Term, show_term};

pub type Env = Vec<Value>;

/// A persistent, Rc-linked environment for NbE.
/// Extending is O(1) — existing bindings are shared via Rc rather than deep-copied.
#[derive(Debug, Clone)]
pub struct Scope {
    /// Most recently bound values (innermost at index 0).
    local: Vec<Value>,
    /// Older bindings shared via Rc.
    parent: Option<Arc<Scope>>,
    /// Total number of bindings.
    len: usize,
}

impl Scope {
    pub fn empty() -> Scope {
        Scope {
            local: vec![],
            parent: None,
            len: 0,
        }
    }

    /// Extend with a single innermost binding. O(1).
    pub fn extend(&self, v: Value) -> Scope {
        Scope {
            local: vec![v],
            parent: Some(Arc::new(self.clone())),
            len: self.len + 1,
        }
    }

    /// Chain values as innermost bindings, with self as parent. O(|values|).
    pub fn chain(&self, values: Vec<Value>) -> Scope {
        if values.is_empty() {
            return self.clone();
        }
        let vlen = values.len();
        Scope {
            local: values,
            parent: Some(Arc::new(self.clone())),
            len: self.len + vlen,
        }
    }

    /// Look up the value at de Bruijn index `i` (0 = innermost). O(depth).
    pub fn lookup(&self, i: usize) -> &Value {
        if i < self.local.len() {
            &self.local[i]
        } else {
            self.parent.as_ref().unwrap().lookup(i - self.local.len())
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn to_vec(&self) -> Vec<Value> {
        let mut result = Vec::with_capacity(self.len);
        self.collect_into(&mut result);
        result
    }

    fn collect_into(&self, result: &mut Vec<Value>) {
        if let Some(ref p) = self.parent {
            p.collect_into(result);
        }
        result.extend(self.local.iter().rev().cloned());
    }
}

/// A system at value level: list of (DNF face, value) pairs.
pub type DNFSystem = Vec<(DNF, Value)>;

/// A shared reference to the global definition values.
/// All closures created during evaluation share the same `Globals` so that
/// recursive self-references resolve correctly after placeholder replacement.
pub type Globals = Arc<Mutex<Vec<Value>>>;

pub(super) fn value_str(
    globals: &Globals,
    global_offset: usize,
    v: &Value,
    session: &mut Session,
) -> String {
    if !debug::is_active() {
        return String::new();
    }
    let term = quote(0, globals, global_offset, v.clone(), session);
    show_term(&[], &term)
}

#[derive(Debug, Clone)]
pub enum Value {
    VNeutral(Neutral),
    VLam(Name, Closure),
    VApp(Arc<Value>, Arc<Value>),
    VPi(Name, Arc<Value>, Closure, bool),
    VSigma(Name, Arc<Value>, Closure),
    VPair(Arc<Value>, Arc<Value>),
    VPath(Arc<Value>, Arc<Value>, Arc<Value>),
    VPLam(Name, IClosure),
    VPApp(Arc<Value>, Arc<Value>),
    VUniv(Level),
    VProp,
    VSSet,
    VLift(Arc<Value>, Level),
    VLower(Arc<Value>),
    VIntervalTy,
    VInterval(I),
    VIntervalVar(usize),
    VCube(DNF),
    VData(Name, Vec<Value>),
    VCon(Name, Name, Vec<Value>),
    VPCon(Name, Name, Vec<Value>, Arc<Value>),
    VSqCon(Name, Name, Vec<Value>, Arc<Value>, Arc<Value>),
    /// N-dimensional cell constructor value: `VCellCon(dt, con, args, ivars)`.
    VCellCon(Name, Name, Vec<Value>, Vec<Value>),
    /// Stuck eliminator. The trailing `Scope` is the evaluation environment
    /// at the eliminator's creation site; it is used when re-quoting the
    /// stored raw case bodies (see `quote_case_body`).
    VElim(Arc<Value>, Vec<ElimCase>, Arc<Value>, Scope, usize),
    VGlue(Arc<Value>, DNF, Arc<Value>),
    VPartial(Arc<Value>, Arc<Value>),
    VSystemType(DNFSystem),
    VGlueElem(DNF, Arc<Value>, Arc<Value>),
    VUnglue(DNF, Arc<Value>, Arc<Value>),
    VEquiv(Arc<Value>, Arc<Value>),
    VMkEquiv(
        Arc<Value>,
        Arc<Value>,
        Arc<Value>,
        Arc<Value>,
        Arc<Value>,
        Arc<Value>,
    ),
    VEquivFwd(Arc<Value>, Arc<Value>),
    VUa(Arc<Value>),
    VTransport(Arc<Value>, Arc<Value>),
    /// Generalized transport: `VTransp(family, direction, base)`.
    /// Stuck when `direction` is a non-concrete interval variable.
    VTransp(Arc<Value>, Arc<Value>, Arc<Value>),
    VHComp(Arc<Value>, DNFSystem, Arc<Value>),
    VComp(Arc<Value>, DNFSystem, Arc<Value>),
    VFill(Arc<Value>, DNFSystem, Arc<Value>),
    VHFill(Arc<Value>, DNFSystem, Arc<Value>),
    VFst(Arc<Value>),
    VSnd(Arc<Value>),
    VProj(Name, Arc<Value>),
    VRecordUpdate(Arc<Value>, Vec<(Name, Value)>),
    VDelay(Arc<Value>),
    VNext(Arc<Value>),
    VForce(Arc<Value>),
}

#[derive(Debug, Clone)]
pub struct Closure {
    pub env: Scope,
    pub globals: Globals,
    pub global_offset: usize,
    pub body: Term,
}

#[derive(Debug, Clone)]
pub struct IClosure {
    pub env: Scope,
    pub globals: Globals,
    pub global_offset: usize,
    pub body: Term,
}

/// Frontier of instability for a neutral term (Sterling-Angiuli 2021).
///
/// Each neutral form `e : ne_φ(A)` carries a frontier `φ` — a predicate on
/// free interval variables indicating when the neutral "ceases to be neutral"
/// and must compute. When `φ` is satisfied (e.g., an interval variable is
/// instantiated to `i0` or `i1`), the neutral **destabilizes** and reduces.
///
/// The frontier is conservative: it may say "doesn't compute" when the neutral
/// actually could, but never the reverse. This preserves soundness.
#[derive(Debug, Clone, PartialEq)]
pub enum Frontier {
    /// Ordinary variable — never computes. The default for most neutrals.
    False,
    /// Computes when the interval variable at the given level equals the
    /// given endpoint (`I0` or `I1`).
    IntervalEq(usize, I),
    /// Computes when either sub-frontier fires.
    Or(Arc<Frontier>, Arc<Frontier>),
    /// Computes when both sub-frontiers fire.
    And(Arc<Frontier>, Arc<Frontier>),
}

impl fmt::Display for Frontier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Frontier::False => write!(f, "⊥"),
            Frontier::IntervalEq(lvl, I::I0) => write!(f, "i{}=0", lvl),
            Frontier::IntervalEq(lvl, I::I1) => write!(f, "i{}=1", lvl),
            Frontier::IntervalEq(lvl, I::Var(v)) => write!(f, "i{}=i{}", lvl, v),
            Frontier::IntervalEq(lvl, _) => write!(f, "i{}=?", lvl),
            Frontier::Or(a, b) => write!(f, "({} ∨ {})", a, b),
            Frontier::And(a, b) => write!(f, "({} ∧ {})", a, b),
        }
    }
}

impl Frontier {
    /// Check if this frontier is satisfied given concrete interval bindings.
    /// `interval_env[i]` is `Some(value)` if interval variable at level `i`
    /// has been instantiated to a concrete value.
    pub fn is_satisfied(&self, interval_env: &[Option<I>]) -> bool {
        match self {
            Frontier::False => false,
            Frontier::IntervalEq(level, endpoint) => {
                matches!(interval_env.get(*level), Some(Some(v)) if v == endpoint)
            }
            Frontier::Or(a, b) => a.is_satisfied(interval_env) || b.is_satisfied(interval_env),
            Frontier::And(a, b) => a.is_satisfied(interval_env) && b.is_satisfied(interval_env),
        }
    }

    /// Combine two frontiers with disjunction (used when building compound
    /// neutrals: the compound computes when either sub-neutral computes).
    pub fn or(self, other: Frontier) -> Frontier {
        match (&self, &other) {
            (Frontier::False, _) => other,
            (_, Frontier::False) => self,
            _ => Frontier::Or(Arc::new(self), Arc::new(other)),
        }
    }

    /// Combine two frontiers with conjunction.
    pub fn and(self, other: Frontier) -> Frontier {
        match (&self, &other) {
            (Frontier::False, _) | (_, Frontier::False) => Frontier::False,
            _ => Frontier::And(Arc::new(self), Arc::new(other)),
        }
    }

    /// The default frontier for ordinary variables.
    pub fn false_frontier() -> Frontier {
        Frontier::False
    }
}

/// A neutral term paired with its frontier of instability.
///
/// This is the Sterling-Angiuli "stabilized neutral": the `NeutralInner`
/// carries the spine structure, and the `Frontier` records when it computes.
#[derive(Debug, Clone)]
pub struct Neutral {
    inner: NeutralInner,
    frontier: Frontier,
}

#[derive(Debug, Clone)]
pub enum NeutralInner {
    NVar(usize),
    NApp(Arc<Neutral>, Arc<Value>),
    NPApp(Arc<Neutral>, Arc<Value>),
    NSqApp(Arc<Neutral>, Arc<Value>, Arc<Value>),
    /// N-dimensional cell application: `NCellApp(neutral, [r1, r2, ..., rn])`.
    NCellApp(Arc<Neutral>, Vec<Value>),
    NFst(Arc<Neutral>),
    NSnd(Arc<Neutral>),
    NElim(Arc<Value>, Vec<ElimCase>, Arc<Neutral>, Scope, usize),
    NTransport(Arc<Value>, Arc<Value>),
    NTransp(Arc<Value>, Arc<Value>, Arc<Value>),
    NHComp(Arc<Value>, DNFSystem, Arc<Value>),
    NComp(Arc<Value>, DNFSystem, Arc<Value>),
    NFill(Arc<Value>, DNFSystem, Arc<Value>),
    NHFill(Arc<Value>, DNFSystem, Arc<Value>),
    NMeta(i32),
    NForce(Arc<Neutral>),
    /// Record field projection stuck on a neutral record value.
    NProj(Arc<Neutral>, Name),
}

impl Neutral {
    /// Create a new neutral with the given inner form and frontier.
    pub fn new(inner: NeutralInner, frontier: Frontier) -> Self {
        Neutral { inner, frontier }
    }

    /// Access the frontier of instability.
    pub fn frontier(&self) -> &Frontier {
        &self.frontier
    }

    /// Consume the neutral, returning (inner, frontier).
    pub fn into_parts(self) -> (NeutralInner, Frontier) {
        (self.inner, self.frontier)
    }

    /// Access the inner form.
    pub fn inner(&self) -> &NeutralInner {
        &self.inner
    }

    /// Map over the inner form, preserving the frontier.
    pub fn map_inner<F: FnOnce(NeutralInner) -> NeutralInner>(self, f: F) -> Self {
        let frontier = self.frontier.clone();
        Neutral::new(f(self.inner), frontier)
    }

    /// Set the frontier (used when rebuilding neutrals during quoting).
    pub fn with_frontier(self, frontier: Frontier) -> Self {
        Neutral {
            inner: self.inner,
            frontier,
        }
    }

    // ── Convenience constructors ────────────────────────────────────────
    // These build common neutral forms with correct frontier computation.

    /// Variable neutral — never computes (frontier = False).
    pub fn nvar(level: usize) -> Self {
        Neutral::new(NeutralInner::NVar(level), Frontier::False)
    }

    /// Metavariable neutral — never computes until solved.
    pub fn nmeta(id: i32) -> Self {
        Neutral::new(NeutralInner::NMeta(id), Frontier::False)
    }

    /// Function application stuck on neutral `f`.
    /// Frontier = f's frontier (the application computes when f computes).
    pub fn napp(f: Neutral, a: Value) -> Self {
        let frontier = f.frontier.clone();
        Neutral::new(NeutralInner::NApp(Arc::new(f), Arc::new(a)), frontier)
    }

    /// Path application stuck on neutral `p` applied to interval `r`.
    /// Frontier = p's frontier ∨ (r=0 ∨ r=1) — computes when p computes
    /// OR when r is a concrete endpoint.
    pub fn npapp(p: Neutral, r: Value, r_frontier: Frontier) -> Self {
        let frontier = p.frontier().clone().or(r_frontier);
        Neutral::new(NeutralInner::NPApp(Arc::new(p), Arc::new(r)), frontier)
    }

    /// Square application stuck on neutral `p` applied to intervals `r`, `s`.
    pub fn nsqapp(
        p: Neutral,
        r: Value,
        s: Value,
        r_frontier: Frontier,
        s_frontier: Frontier,
    ) -> Self {
        let frontier = p.frontier().clone().or(r_frontier).or(s_frontier);
        Neutral::new(
            NeutralInner::NSqApp(Arc::new(p), Arc::new(r), Arc::new(s)),
            frontier,
        )
    }

    /// N-dimensional cell application stuck on neutral `p`.
    pub fn ncellapp(p: Neutral, ivars: Vec<Value>, ivars_frontiers: Vec<Frontier>) -> Self {
        let mut frontier = p.frontier().clone();
        for f in ivars_frontiers {
            frontier = frontier.or(f);
        }
        Neutral::new(NeutralInner::NCellApp(Arc::new(p), ivars), frontier)
    }

    /// Fst projection stuck on neutral `p`.
    pub fn nfst(p: Neutral) -> Self {
        let frontier = p.frontier().clone();
        Neutral::new(NeutralInner::NFst(Arc::new(p)), frontier)
    }

    /// Snd projection stuck on neutral `p`.
    pub fn nsnd(p: Neutral) -> Self {
        let frontier = p.frontier().clone();
        Neutral::new(NeutralInner::NSnd(Arc::new(p)), frontier)
    }

    /// Elimination stuck on neutral scrutinee.
    /// Frontier = scrutinee's frontier (computes when scrutinee computes).
    pub fn nelim(
        motive: Value,
        cases: Vec<ElimCase>,
        scrut: Neutral,
        env: Scope,
        go: usize,
    ) -> Self {
        let frontier = scrut.frontier().clone();
        Neutral::new(
            NeutralInner::NElim(Arc::new(motive), cases, Arc::new(scrut), env, go),
            frontier,
        )
    }

    /// Transport stuck on a neutral family.
    pub fn ntransport(fam: Value, x: Value) -> Self {
        Neutral::new(
            NeutralInner::NTransport(Arc::new(fam), Arc::new(x)),
            Frontier::False,
        )
    }

    /// Generalized transport stuck on a neutral family or direction.
    pub fn ntransp(fam: Value, dir: Value, x: Value) -> Self {
        Neutral::new(
            NeutralInner::NTransp(Arc::new(fam), Arc::new(dir), Arc::new(x)),
            Frontier::False,
        )
    }

    /// hcomp stuck.
    pub fn nhcomp(a: Value, sys: DNFSystem, base: Value) -> Self {
        Neutral::new(
            NeutralInner::NHComp(Arc::new(a), sys, Arc::new(base)),
            Frontier::False,
        )
    }

    /// comp stuck.
    pub fn ncomp(a: Value, sys: DNFSystem, base: Value) -> Self {
        Neutral::new(
            NeutralInner::NComp(Arc::new(a), sys, Arc::new(base)),
            Frontier::False,
        )
    }

    /// fill stuck.
    pub fn nfill(a: Value, sys: DNFSystem, base: Value) -> Self {
        Neutral::new(
            NeutralInner::NFill(Arc::new(a), sys, Arc::new(base)),
            Frontier::False,
        )
    }

    /// hfill stuck.
    pub fn nhfill(a: Value, sys: DNFSystem, base: Value) -> Self {
        Neutral::new(
            NeutralInner::NHFill(Arc::new(a), sys, Arc::new(base)),
            Frontier::False,
        )
    }

    /// Force stuck on neutral `n`.
    pub fn nforce(n: Neutral) -> Self {
        let frontier = n.frontier().clone();
        Neutral::new(NeutralInner::NForce(Arc::new(n)), frontier)
    }

    /// Record field projection stuck on neutral `n`.
    pub fn nproj(n: Neutral, field: Name) -> Self {
        let frontier = n.frontier().clone();
        Neutral::new(NeutralInner::NProj(Arc::new(n), field), frontier)
    }

    /// Helper to compute the frontier for interval variable `r`.
    /// Returns `Or(r=0, r=1)` if `r` is an interval variable, `False` otherwise.
    pub fn interval_frontier(r: &Value) -> Frontier {
        match r {
            Value::VIntervalVar(level) => Frontier::Or(
                Arc::new(Frontier::IntervalEq(*level, I::I0)),
                Arc::new(Frontier::IntervalEq(*level, I::I1)),
            ),
            _ => Frontier::False,
        }
    }
}

impl Closure {
    pub fn apply(&self, v: Value, session: &mut Session) -> Value {
        let env = self.env.extend(v);
        eval_nbe(&env, &self.globals, self.global_offset, &self.body, session)
    }
}

impl IClosure {
    pub fn apply_i(&self, i: I, session: &mut Session) -> Value {
        self.apply_interval_value(Value::VInterval(i), session)
    }

    pub(super) fn apply_i_var(&self, level: usize, session: &mut Session) -> Value {
        self.apply_interval_value(Value::VIntervalVar(level), session)
    }

    pub fn apply_interval_value(&self, v: Value, session: &mut Session) -> Value {
        match &v {
            Value::VInterval(i) => {
                // Record that the closure's interval variable (at de Bruijn
                // level = current env length) is bound to concrete `i`.
                // This feeds into Frontier::is_satisfied for destabilization.
                let level = self.env.len();
                session.record_interval_binding(level, i);

                // The closure body references its bound interval variable as
                // `I::Var(0)` (incrementing under nested PLams). Substitute it
                // with the applied interval value *before* evaluating; extending
                // the env is insufficient because eval_nbe's TInterval arm never
                // resolves interval vars against the env.
                //
                // The interval binder occupies a term slot in the parsed body
                // (the parser pushes a dummy binder for `<i>`), so we must push a
                // slot onto the env here as well — matching the `VIntervalVar`
                // and `other` arms below — or term variables inside the body
                // resolve one binder too high.
                let body = subst_interval_var(&self.body, 0, i);
                let env = self.env.extend(Value::VInterval(i.clone()));
                eval_nbe(&env, &self.globals, self.global_offset, &body, session)
            }
            Value::VIntervalVar(_level) => {
                let env = self.env.extend(v);
                eval_nbe(&env, &self.globals, self.global_offset, &self.body, session)
            }
            other => {
                let env = self.env.extend(other.clone());
                eval_nbe(&env, &self.globals, self.global_offset, &self.body, session)
            }
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frontier_false_never_satisfied() {
        let f = Frontier::False;
        assert!(!f.is_satisfied(&[]));
        assert!(!f.is_satisfied(&[Some(I::I0)]));
        assert!(!f.is_satisfied(&[Some(I::I1)]));
    }

    #[test]
    fn frontier_interval_eq_i0() {
        let f = Frontier::IntervalEq(0, I::I0);
        // Level 0 bound to I0 → satisfied
        assert!(f.is_satisfied(&[Some(I::I0)]));
        // Level 0 bound to I1 → not satisfied
        assert!(!f.is_satisfied(&[Some(I::I1)]));
        // Level 0 unbound → not satisfied
        assert!(!f.is_satisfied(&[None]));
        // Level 0 not in env → not satisfied
        assert!(!f.is_satisfied(&[]));
    }

    #[test]
    fn frontier_interval_eq_i1() {
        let f = Frontier::IntervalEq(1, I::I1);
        // Level 1 bound to I1 → satisfied
        assert!(f.is_satisfied(&[Some(I::I0), Some(I::I1)]));
        // Level 1 bound to I0 → not satisfied
        assert!(!f.is_satisfied(&[Some(I::I0), Some(I::I0)]));
    }

    #[test]
    fn frontier_or() {
        let f = Frontier::Or(
            Arc::new(Frontier::IntervalEq(0, I::I0)),
            Arc::new(Frontier::IntervalEq(0, I::I1)),
        );
        // Either i0=0 or i0=1 → satisfied when either holds
        assert!(f.is_satisfied(&[Some(I::I0)]));
        assert!(f.is_satisfied(&[Some(I::I1)]));
        // Unbound → not satisfied
        assert!(!f.is_satisfied(&[None]));
        assert!(!f.is_satisfied(&[]));
    }

    #[test]
    fn frontier_and() {
        let f = Frontier::And(
            Arc::new(Frontier::IntervalEq(0, I::I0)),
            Arc::new(Frontier::IntervalEq(1, I::I1)),
        );
        // Both must hold
        assert!(f.is_satisfied(&[Some(I::I0), Some(I::I1)]));
        assert!(!f.is_satisfied(&[Some(I::I0), Some(I::I0)]));
        assert!(!f.is_satisfied(&[Some(I::I1), Some(I::I1)]));
        assert!(!f.is_satisfied(&[None, Some(I::I1)]));
    }

    #[test]
    fn frontier_or_short_circuits() {
        let f = Frontier::Or(
            Arc::new(Frontier::IntervalEq(0, I::I0)),
            Arc::new(Frontier::False),
        );
        // First branch fires
        assert!(f.is_satisfied(&[Some(I::I0)]));
        // Second branch is False, first doesn't fire
        assert!(!f.is_satisfied(&[Some(I::I1)]));
    }

    #[test]
    fn frontier_and_short_circuits() {
        let f = Frontier::And(
            Arc::new(Frontier::False),
            Arc::new(Frontier::IntervalEq(0, I::I0)),
        );
        // First branch is False → entire And is False
        assert!(!f.is_satisfied(&[Some(I::I0)]));
    }

    #[test]
    fn frontier_or_flattens_false() {
        let f = Frontier::False.or(Frontier::IntervalEq(0, I::I0));
        assert!(matches!(f, Frontier::IntervalEq(0, I::I0)));
    }

    #[test]
    fn frontier_and_flattens_false() {
        let f = Frontier::False.and(Frontier::IntervalEq(0, I::I0));
        assert!(matches!(f, Frontier::False));
    }

    #[test]
    fn neutral_nvar_has_false_frontier() {
        let n = Neutral::nvar(42);
        assert_eq!(n.frontier(), &Frontier::False);
        assert!(matches!(n.inner(), NeutralInner::NVar(42)));
    }

    #[test]
    fn neutral_nmeta_has_false_frontier() {
        let n = Neutral::nmeta(7);
        assert_eq!(n.frontier(), &Frontier::False);
    }

    #[test]
    fn neutral_napp_inherits_frontier() {
        let n = Neutral::nvar(0);
        let app = Neutral::napp(n, Value::VUniv(0));
        assert_eq!(app.frontier(), &Frontier::False);
    }

    #[test]
    fn neutral_npapp_computes_frontier() {
        let p = Neutral::nvar(0);
        let r = Value::VIntervalVar(1);
        let r_frontier = Neutral::interval_frontier(&r);
        let pp = Neutral::npapp(p, r, r_frontier);
        // Frontier should be False ∨ (i1=0 ∨ i1=1) = (i1=0 ∨ i1=1)
        let expected = Frontier::Or(
            Arc::new(Frontier::IntervalEq(1, I::I0)),
            Arc::new(Frontier::IntervalEq(1, I::I1)),
        );
        assert_eq!(pp.frontier(), &expected);
    }

    #[test]
    fn neutral_npapp_concrete_r_has_false_frontier() {
        let p = Neutral::nvar(0);
        let r = Value::VInterval(I::I0);
        let r_frontier = Neutral::interval_frontier(&r);
        let pp = Neutral::npapp(p, r, r_frontier);
        // Concrete interval → r_frontier = False → combined = False ∨ False = False
        assert_eq!(pp.frontier(), &Frontier::False);
    }

    #[test]
    fn interval_frontier_var() {
        let v = Value::VIntervalVar(3);
        let f = Neutral::interval_frontier(&v);
        let expected = Frontier::Or(
            Arc::new(Frontier::IntervalEq(3, I::I0)),
            Arc::new(Frontier::IntervalEq(3, I::I1)),
        );
        assert_eq!(f, expected);
    }

    #[test]
    fn interval_frontier_concrete() {
        let v = Value::VInterval(I::I0);
        let f = Neutral::interval_frontier(&v);
        assert_eq!(f, Frontier::False);
    }

    #[test]
    fn neutral_nelim_inherits_frontier() {
        let scrut = Neutral::nvar(0);
        let elim = Neutral::nelim(Value::VUniv(0), vec![], scrut, Scope::empty(), 0);
        assert_eq!(elim.frontier(), &Frontier::False);
    }

    #[test]
    fn neutral_nelim_with_path_scrut() {
        // Scrutinee is NPApp with interval var → frontier = (i1=0 ∨ i1=1)
        let p = Neutral::nvar(0);
        let r = Value::VIntervalVar(1);
        let r_frontier = Neutral::interval_frontier(&r);
        let scrut = Neutral::npapp(p, r, r_frontier);
        let elim = Neutral::nelim(Value::VUniv(0), vec![], scrut, Scope::empty(), 0);
        // Elim inherits scrutinee's frontier
        let expected = Frontier::Or(
            Arc::new(Frontier::IntervalEq(1, I::I0)),
            Arc::new(Frontier::IntervalEq(1, I::I1)),
        );
        assert_eq!(elim.frontier(), &expected);
    }

    #[test]
    fn neutral_nforce_inherits_frontier() {
        let n = Neutral::nvar(0);
        let f = Neutral::nforce(n);
        assert_eq!(f.frontier(), &Frontier::False);
    }

    #[test]
    fn neutral_nproj_inherits_frontier() {
        let n = Neutral::nvar(0);
        let p = Neutral::nproj(n, "field".to_string());
        assert_eq!(p.frontier(), &Frontier::False);
    }
}
