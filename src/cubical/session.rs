//! Consolidated session state — replaces all scattered thread-locals with one `Session`.
//!
//! All mutable state that was previously stored in separate `thread_local!` blocks
//! is now inside a single `Session` struct behind one `thread_local!`.  The public
//! accessor functions preserve the existing API so the rest of the crate continues
//! to compile without changes.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::cubical::nbe::trace::ReductionStep;
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

    // ── Typechecker flags ───────────────────────────────────────────
    pub skip_plam_endpt: bool,
    pub skip_guard: bool,
    pub current_def: Option<String>,

    // ── Error positions ─────────────────────────────────────────────
    pub decl_name_positions: Vec<(Name, Pos, bool)>,

    // ── Debug trace ─────────────────────────────────────────────────
    pub reduction_trace: Vec<ReductionStep>,
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
            skip_plam_endpt: false,
            skip_guard: false,
            current_def: None,
            decl_name_positions: Vec::new(),
            reduction_trace: Vec::new(),
        }
    }
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Single thread-local holding all session state.
// ---------------------------------------------------------------------------

thread_local! {
    static SESSION: RefCell<Session> = RefCell::new(Session::new());
}

/// Run a closure with mutable access to the session.
pub fn with_session_mut<R>(f: impl FnOnce(&mut Session) -> R) -> R {
    SESSION.with(|cell| f(&mut cell.borrow_mut()))
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
// Drop-in accessor functions (same API as the old thread-locals)
// ===========================================================================

// ── NbE: datatypes ────────────────────────────────────────────────────

pub fn set_current_dts(dts: &[Datatype]) {
    SESSION.with(|cell| cell.borrow_mut().dts = dts.to_vec());
}

pub fn current_dts() -> Vec<Datatype> {
    SESSION.with(|cell| cell.borrow().dts.clone())
}

// ── NbE: globals ──────────────────────────────────────────────────────

pub fn set_current_globals(globals: Option<Globals>) -> Option<Globals> {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        std::mem::replace(&mut s.globals, globals)
    })
}

pub fn get_current_globals() -> Option<Globals> {
    SESSION.with(|cell| cell.borrow().globals.clone())
}

// ── NbE: eval cache ──────────────────────────────────────────────────

pub fn eval_cache_get(t: &Term) -> Option<Term> {
    SESSION.with(|cell| cell.borrow().eval_cache.get(t).cloned())
}

pub fn eval_cache_insert(t: Term, result: Term) {
    SESSION.with(|cell| cell.borrow_mut().eval_cache.insert(t, result));
}

pub fn clear_nbe_cache() {
    SESSION.with(|cell| cell.borrow_mut().eval_cache.clear());
}

// ── NbE: eval depth guard ────────────────────────────────────────────

pub fn eval_depth_enter() -> usize {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        let d = s.eval_depth;
        s.eval_depth += 1;
        d
    })
}

pub fn eval_depth_restore(d: usize) {
    SESSION.with(|cell| cell.borrow_mut().eval_depth = d);
}

// ── NbE: quote depth guard ───────────────────────────────────────────

pub fn quote_depth_enter() -> usize {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        let d = s.quote_depth;
        s.quote_depth += 1;
        d
    })
}

pub fn quote_depth_restore(d: usize) {
    SESSION.with(|cell| cell.borrow_mut().quote_depth = d);
}

// ── NbE: all-tubes depth guard ───────────────────────────────────────

pub fn all_tubes_depth_enter() -> usize {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        let d = s.all_tubes_depth;
        s.all_tubes_depth += 1;
        d
    })
}

pub fn all_tubes_depth_restore(d: usize) {
    SESSION.with(|cell| cell.borrow_mut().all_tubes_depth = d);
}

// ── Metavariable store ───────────────────────────────────────────────

pub fn fresh_meta_id() -> i32 {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        let id = s.meta_solutions.len() as i32;
        s.meta_solutions.push(None);
        s.meta_names.push(None);
        s.meta_expected.push(None);
        id
    })
}

pub fn set_meta_name(id: i32, name: Name) {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        if id >= 0 && (id as usize) < s.meta_names.len() {
            s.meta_names[id as usize] = Some(name);
        }
    });
}

pub fn get_meta_name(id: i32) -> Option<Name> {
    if id < 0 {
        return None;
    }
    SESSION.with(|cell| {
        cell.borrow()
            .meta_names
            .get(id as usize)
            .and_then(|o| o.clone())
    })
}

pub fn set_meta_expected(id: i32, ty: Term) {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        if id >= 0
            && (id as usize) < s.meta_expected.len()
            && s.meta_expected[id as usize].is_none()
        {
            s.meta_expected[id as usize] = Some(ty);
        }
    });
}

pub fn get_meta_expected(id: i32) -> Option<Term> {
    if id < 0 {
        return None;
    }
    SESSION.with(|cell| {
        cell.borrow()
            .meta_expected
            .get(id as usize)
            .and_then(|o| o.clone())
    })
}

pub fn solve_meta(id: i32, solution: Term) {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        if id >= 0 && (id as usize) < s.meta_solutions.len() {
            s.meta_solutions[id as usize] = Some(solution);
        }
    });
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

pub fn clear_metavars() {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        s.meta_solutions.clear();
        s.meta_names.clear();
        s.meta_expected.clear();
    });
}

pub fn clear_all_caches() {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        s.eval_cache.clear();
        s.meta_solutions.clear();
        s.meta_names.clear();
        s.meta_expected.clear();
    });
}

// ── Equality: elim-case recurse depth ────────────────────────────────

pub fn elim_depth_enter() -> usize {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        let d = s.elim_case_recurse_depth;
        s.elim_case_recurse_depth += 1;
        d
    })
}

pub fn elim_depth_restore(d: usize) {
    SESSION.with(|cell| cell.borrow_mut().elim_case_recurse_depth = d);
}

// ── Typechecker flags ────────────────────────────────────────────────

pub fn should_skip_guard() -> bool {
    SESSION.with(|cell| cell.borrow().skip_guard)
}

pub fn set_skip_guard(skip: bool) {
    SESSION.with(|cell| cell.borrow_mut().skip_guard = skip);
}

pub fn current_def() -> Option<String> {
    SESSION.with(|cell| cell.borrow().current_def.clone())
}

pub fn set_current_def(name: Option<String>) -> Option<String> {
    SESSION.with(|cell| {
        let mut s = cell.borrow_mut();
        std::mem::replace(&mut s.current_def, name)
    })
}

pub fn should_skip_plam_endpt() -> bool {
    SESSION.with(|cell| cell.borrow().skip_plam_endpt)
}

pub fn set_skip_plam_endpt(skip: bool) {
    SESSION.with(|cell| cell.borrow_mut().skip_plam_endpt = skip);
}

// ── Error positions ──────────────────────────────────────────────────

pub fn set_decl_name_positions(v: Vec<(Name, Pos, bool)>) {
    SESSION.with(|cell| cell.borrow_mut().decl_name_positions = v);
}

pub fn clear_decl_name_positions() {
    SESSION.with(|cell| cell.borrow_mut().decl_name_positions.clear());
}

pub fn with_decl_name_positions<R>(f: impl FnOnce(&[(Name, Pos, bool)]) -> R) -> R {
    SESSION.with(|cell| {
        let s = cell.borrow();
        f(&s.decl_name_positions)
    })
}
