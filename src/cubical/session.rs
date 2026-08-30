//! Consolidated session state — replaces all scattered thread-locals with one `Session`.
//!
//! All mutable state that was previously stored in separate `thread_local!` blocks
//! is now inside a single `Session` struct behind one `thread_local!`.  The public
//! accessor functions preserve the existing API so the rest of the crate continues
//! to compile without changes.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::ptr;
use std::rc::Rc;

use crate::cubical::interval::I;
use crate::cubical::syntax::{Datatype, Name, Term};
use crate::cubical::typechecker::errors::Pos;

// Re-export core NbE types.
pub use crate::cubical::nbe::Value;

/// A shared reference to the global definition values.
pub type Globals = Rc<RefCell<Vec<Value>>>;

/// All implicit state consolidated into one struct.
pub struct Session {
    // ── NbE state ───────────────────────────────────────────────────
    pub dts: Vec<Datatype>,
    pub globals: Option<Globals>,
    pub eval_cache: HashMap<Term, Term>,
    pub eval_depth: usize,
    pub quote_depth: usize,
    pub all_tubes_depth: usize,

    // ── Metavariable state ──────────────────────────────────────────
    pub meta_solutions: Vec<Option<Term>>,
    pub meta_names: Vec<Option<Name>>,
    pub meta_expected: Vec<Option<Term>>,

    // ── Equality state ──────────────────────────────────────────────
    pub elim_case_recurse_depth: usize,

    // ── Frontier-of-instability interval tracking ──────────────────
    // Maps de Bruijn level → concrete interval value (if known).
    // Populated by IClosure::apply_interval_value when a closure is
    // applied with a concrete interval. Used by Frontier::is_satisfied
    // to determine when neutrals can destabilize.
    pub interval_bindings: Vec<Option<I>>,

    // ── Typechecker flags ───────────────────────────────────────────
    pub skip_plam_endpt: bool,
    pub skip_guard: bool,
    pub current_def: Option<String>,

    // ── Error positions ─────────────────────────────────────────────
    pub decl_name_positions: Vec<(Name, Pos, bool)>,
    // ── Debug trace ─────────────────────────────────────────────────
}

impl Session {
    pub fn new() -> Self {
        Session {
            dts: Vec::new(),
            globals: None,
            eval_cache: HashMap::new(),
            eval_depth: 0,
            quote_depth: 0,
            all_tubes_depth: 0,
            meta_solutions: Vec::new(),
            meta_names: Vec::new(),
            meta_expected: Vec::new(),
            elim_case_recurse_depth: 0,
            interval_bindings: Vec::new(),
            skip_plam_endpt: false,
            skip_guard: false,
            current_def: None,
            decl_name_positions: Vec::new(),
        }
    }
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

impl Session {
    // ── NbE: datatypes ──────────────────────────────────────────────
    pub fn set_current_dts(&mut self, dts: &[Datatype]) {
        self.dts = dts.to_vec();
    }
    pub fn current_dts(&self) -> Vec<Datatype> {
        self.dts.clone()
    }

    // ── NbE: globals ────────────────────────────────────────────────
    pub fn set_current_globals(&mut self, globals: Option<Globals>) -> Option<Globals> {
        std::mem::replace(&mut self.globals, globals)
    }
    pub fn get_current_globals(&self) -> Option<Globals> {
        self.globals.clone()
    }

    // ── NbE: eval cache ────────────────────────────────────────────
    pub fn eval_cache_get(&self, t: &Term) -> Option<Term> {
        self.eval_cache.get(t).cloned()
    }
    pub fn eval_cache_insert(&mut self, t: Term, result: Term) {
        self.eval_cache.insert(t, result);
    }
    pub fn clear_nbe_cache(&mut self) {
        self.eval_cache.clear();
    }

    // ── NbE: eval depth ────────────────────────────────────────────
    pub fn eval_depth_enter(&mut self) -> usize {
        let d = self.eval_depth;
        self.eval_depth += 1;
        d
    }
    pub fn eval_depth_restore(&mut self, d: usize) {
        self.eval_depth = d;
    }

    // ── NbE: quote depth ───────────────────────────────────────────
    pub fn quote_depth_enter(&mut self) -> usize {
        let d = self.quote_depth;
        self.quote_depth += 1;
        d
    }
    pub fn quote_depth_restore(&mut self, d: usize) {
        self.quote_depth = d;
    }

    // ── NbE: all-tubes depth ───────────────────────────────────────
    pub fn all_tubes_depth_enter(&mut self) -> usize {
        let d = self.all_tubes_depth;
        self.all_tubes_depth += 1;
        d
    }
    pub fn all_tubes_depth_restore(&mut self, d: usize) {
        self.all_tubes_depth = d;
    }

    // ── Metavariable store ─────────────────────────────────────────
    pub fn fresh_meta_id(&mut self) -> i32 {
        let id = self.meta_solutions.len() as i32;
        self.meta_solutions.push(None);
        self.meta_names.push(None);
        self.meta_expected.push(None);
        id
    }
    pub fn set_meta_name(&mut self, id: i32, name: Name) {
        if id >= 0 && (id as usize) < self.meta_names.len() {
            self.meta_names[id as usize] = Some(name);
        }
    }
    pub fn get_meta_name(&self, id: i32) -> Option<Name> {
        if id < 0 {
            return None;
        }
        self.meta_names.get(id as usize).and_then(|o| o.clone())
    }
    pub fn set_meta_expected(&mut self, id: i32, ty: Term) {
        if id >= 0
            && (id as usize) < self.meta_expected.len()
            && self.meta_expected[id as usize].is_none()
        {
            self.meta_expected[id as usize] = Some(ty);
        }
    }
    pub fn get_meta_expected(&self, id: i32) -> Option<Term> {
        if id < 0 {
            return None;
        }
        self.meta_expected.get(id as usize).and_then(|o| o.clone())
    }
    pub fn solve_meta(&mut self, id: i32, solution: Term) {
        if id >= 0 && (id as usize) < self.meta_solutions.len() {
            self.meta_solutions[id as usize] = Some(solution);
        }
    }
    pub fn get_meta_solution(&self, id: i32) -> Option<Term> {
        if id < 0 {
            return None;
        }
        self.meta_solutions.get(id as usize).and_then(|o| o.clone())
    }
    #[allow(dead_code)]
    pub fn clear_metavars(&mut self) {
        self.meta_solutions.clear();
        self.meta_names.clear();
        self.meta_expected.clear();
    }
    #[allow(dead_code)]
    pub fn clear_all_caches(&mut self) {
        self.eval_cache.clear();
        self.meta_solutions.clear();
        self.meta_names.clear();
        self.meta_expected.clear();
    }

    // ── Equality ───────────────────────────────────────────────────
    pub fn elim_depth_enter(&mut self) -> usize {
        let d = self.elim_case_recurse_depth;
        self.elim_case_recurse_depth += 1;
        d
    }
    pub fn elim_depth_restore(&mut self, d: usize) {
        self.elim_case_recurse_depth = d;
    }

    // ── Frontier-of-instability interval bindings ──────────────────
    /// Record that interval variable at de Bruijn level `level` is
    /// bound to concrete interval `i`. Called by IClosure when a
    /// closure is applied with a concrete interval value.
    pub fn record_interval_binding(&mut self, level: usize, i: &I) {
        // Extend the vec if needed (fill gaps with None = unknown).
        while self.interval_bindings.len() <= level {
            self.interval_bindings.push(None);
        }
        self.interval_bindings[level] = Some(i.clone());
    }

    /// Check if interval variable at `level` is bound to `endpoint`.
    pub fn interval_is_concrete(&self, level: usize, endpoint: &I) -> bool {
        matches!(self.interval_bindings.get(level), Some(Some(v)) if v == endpoint)
    }

    // ── Typechecker flags ──────────────────────────────────────────
    pub fn should_skip_guard(&self) -> bool {
        self.skip_guard
    }
    pub fn set_skip_guard(&mut self, skip: bool) {
        self.skip_guard = skip;
    }
    pub fn current_def(&self) -> Option<String> {
        self.current_def.clone()
    }
    pub fn set_current_def(&mut self, name: Option<String>) -> Option<String> {
        std::mem::replace(&mut self.current_def, name)
    }
    pub fn should_skip_plam_endpt(&self) -> bool {
        self.skip_plam_endpt
    }
    pub fn set_skip_plam_endpt(&mut self, skip: bool) {
        self.skip_plam_endpt = skip;
    }

    // ── Error positions ────────────────────────────────────────────
    pub fn set_decl_name_positions(&mut self, v: Vec<(Name, Pos, bool)>) {
        self.decl_name_positions = v;
    }
    pub fn clear_decl_name_positions(&mut self) {
        self.decl_name_positions.clear();
    }
    pub fn with_decl_name_positions<R>(&self, f: impl FnOnce(&[(Name, Pos, bool)]) -> R) -> R {
        f(&self.decl_name_positions)
    }
}

// ---------------------------------------------------------------------------
// Single thread-local holding all session state.
// ---------------------------------------------------------------------------

thread_local! {
    static SESSION: RefCell<Session> = RefCell::new(Session::new());
    /// Raw pointer to the active `Session`, set by `with_session_mut`.
    /// Allows read-only access from code that doesn't receive `&Session`
    /// (e.g. `show_term`) without triggering a RefCell re-borrow.
    static CURRENT_SESSION: Cell<*const Session> = const { Cell::new(ptr::null()) };
}

/// Run a closure with mutable access to the session.
pub fn with_session_mut<R>(f: impl FnOnce(&mut Session) -> R) -> R {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        let raw = &*s as *const Session;
        CURRENT_SESSION.with(|c| c.set(raw));
        let r = f(&mut s);
        CURRENT_SESSION.with(|c| c.set(ptr::null()));
        r
    })
}

/// Borrow the current session as a shared reference, if one is active
/// (i.e. we are inside `with_session_mut`). Returns `None` otherwise.
/// Useful in code paths (like pretty-printing) that don't receive `&Session`.
pub fn current_session() -> Option<&'static Session> {
    CURRENT_SESSION.with(|c| {
        let p = c.get();
        if p.is_null() {
            None
        } else {
            Some(unsafe { &*p })
        }
    })
}

/// Run a closure with shared access to the session.
#[allow(dead_code)]
pub fn with_session<R>(f: impl FnOnce(&Session) -> R) -> R {
    SESSION.with(|cell| f(&cell.borrow()))
}

/// Replace the entire session. Returns the previous one.
#[allow(dead_code)]
pub fn replace_session(s: Session) -> Session {
    SESSION.with(|cell| std::mem::replace(&mut *cell.borrow_mut(), s))
}

/// Take the current session, leaving a default in its place.
#[allow(dead_code)]
pub fn take_session() -> Session {
    SESSION.with(|cell| std::mem::take(&mut *cell.borrow_mut()))
}

// ===========================================================================
// Minimal backward-compat free functions kept for external call sites.
// All internal callers should use Session methods directly.
// ===========================================================================

pub fn get_meta_name(id: i32) -> Option<Name> {
    SESSION.with(|cell| {
        cell.borrow()
            .meta_names
            .get(id as usize)
            .and_then(|o| o.clone())
    })
}

pub fn get_meta_solution(id: i32) -> Option<Term> {
    if id < 0 {
        return None;
    }
    SESSION.with(|cell| {
        cell.borrow()
            .meta_solutions
            .get(id as usize)
            .and_then(|o| o.clone())
    })
}
