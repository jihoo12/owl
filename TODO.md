# TODO.md — Remaining improvements for owl

> The checklist below is the live status tracker (`[x]` = done, `[ ]` = open).

## Completed (implementation log)

- [x] PathP (dependent path types) — Added as syntactic sugar over TPath. `PathP (<i> A i) u v` parses to `TPath(PLam("i", A i), u, v)`. Type families work correctly with endpoint checking.

- [x] General systems for hcomp/comp/fill/hfill — Multi-face system syntax `[phi => tube, ...]` using `=>` (FatArrow) separator. Old single-face syntax `comp A phi tube base` still works (desugars to single-entry system). The `System` type is `Vec<(Term, Term)>`. Top-face reduction applies tube at i1 (not raw VPLam). Constant type families handled correctly for comp/fill. Compatibility checking delegated to face-by-face `check_faces` calls.

- [x] Parameterized inductive types — `TData(Name, Vec<Term>)` across all files. Parser handles `(A : Type)` parameter binders. Two-phase parameter inference in typechecker. Constructor arg types reference params via de Bruijn indices.

- [x] Higher inductive types (HITs) with path constructors — Parser supports `[ face0 , face1 ]` syntax for path constructors. Typechecker checks path constructor case bodies as PLam against TPath with correct endpoints. `reduce_pcon_endpoints_dt` reduces path constructors at endpoints. Fixed de Bruijn scope bugs: parser binder ordering, face term scope in expected_body_ty, and subst-based arg substitution in reduce_pcon_endpoints_dt.

- [x] Better error cascade in check_dt — Added specific `check_dt` arms for `THComp`, `TComp`, `TFill`, `THFill`. Expected type is checked first (via cumulativity) before delegating sub-term checking to `infer_dt`. On `infer_dt` failure, retries with `nbe_eval` to handle cases where the Kan operation reduces. This gives clearer error messages for type mismatches while preserving correct handling of face compatibility.

- [x] Truncation types (isProp, isSet, isGroupoid) — Parser-level desugaring of `isProp A`, `isSet A`, `isGroupoid A` into nested Pi/Path types. `isProp A` desugars to `(x : A) -> (y : A) -> Path A x y`. `isSet A` desugars to `(x : A) -> (y : A) -> (p : Path A x y) -> (q : Path A x y) -> Path (Path A x y) p q`. `isGroupoid A` desugars similarly with 6 binders.

- [x] Set-quotients / quotient types — Demonstrated via HITs with path constructors. Pattern: define `MyInt` with point constructors and a path constructor `squash` that identifies two points. Path application (`squash @ i0`, `squash @ i1`) accesses endpoints. Eliminators must respect path boundaries.

- [x] Square constructors (2D HIT cells) — `[[ face_i0, face_i1, face_j0, face_j1 ]]` syntax for square constructors in HITs. Parser creates `TSqCon(d, con, args, r, s)` terms. `infer_dt` builds nested PathP type `PathP (<r> PathP (<s> TData(d)) fi0 fi1) fj0 fj1`. `check_dt` handles TSqCon against TData by verifying data type match and interval arg validity. `SKIP_PLAM_ENDPT` flag skips boundary checks for HIT case bodies. Applied `apply_literal` for IVar-based endpoint checks. Identity function on Torus typechecks correctly.

- [x] Partial elements / Cubical Subtypes — `[_ | phi] A` syntax for partial elements. Added `TPartial(phi, A)` term constructor and `VPartial` value constructor. Supports both bracket syntax `[_ | phi] A` and keyword syntax `Partial phi A`. Type inference: `TPartial(phi, A) : U_n` when `A : U_n`. NbE reduction: `TPartial(i1, A)` reduces to `A`. Parser, pretty-printer, equality, positivity checker, and apply_literal all handle the new constructor.

- [x] Fix 3 pre-existing example errors — `hits_parameterized.owl`, `stress_glue_hcomp.owl`, `stress_transport.owl` now pass (112 tests, 18 examples all green):
  - PLam boundary check shift: Added `shift(-1, 0, ...)` to `body_at0`/`body_at1` in PLam check (matching the existing shift in path constructor endpoint check).
  - Parser: Path constructor space-application now extends TCon args instead of wrapping in TApp chains, so `@ interval` correctly creates TPCon.
  - `reduce_pcon_endpoints_dt` TApp chain: Now walks TApp chains to find underlying TCon for path constructor endpoint reduction.

- [x] Debug improvements (`-d` flag) — `process_def` logs definition name on entry. `ContextualError` wraps TypeError with definition name. Trace printing distinguishes success/error cases. Debug scope output shows term, expected type, and context depth.

- [x] Prop and SSet universes — `TProp` (impredicative, at U0) and `TSSet` (predicative, at U1) added to Term/Value enums. Prop is closed under Pi/Sigma/Path when both sides are Prop (impredicativity). SSet is predicative. Parser, pretty-printer, NbE, positivity, and cumulativity all handle the new constructors. `TUniv(0)` cumulates into `TProp` via cumulativity check.

- [x] Universe lifting/lowering — `TLower(t)` and `Tlift(t)` (lower/lift) for moving terms between universe levels. Parser, pretty-printer, NbE, equality, and positivity all handle the new constructors. `lower` at U0 reduces to identity.

- [x] Cumulativity for inductive types — `TData(d, ps) <= TData(d, ps')` when names match and parameters are checked covariantly. `TPath` cumulativity in all three components. Implemented in `cumulativity_check`.

- [x] Termination / Guard checking — Structural recursion guard in `termination.rs`. Recursive calls in TElim arms must pass a case binder (de Bruijn index < binder_count) as the scrutinee. Rejects non-structural recursion with `TerminationViolation` error. Wired into `infer_dt` before return type checking.

- [x] Induction-induction (mutual inductive types) — `inductive A where ... | with inductive B where ...` syntax. `Decl::DataMutual(Vec<Datatype>)` variant. Forward references: all mutual datatypes registered before constructor parsing. Driver `process_data_mutual` does two-phase processing (register all, then check constructors). Parser `sync_from_env` handles `DataMutual`.

- [x] Induction-recursion — `inductive D where ... | with f : T := e` syntax. `Decl::DataWithFunc { dt, func_name, func_ty, func_val }` variant. Function name added to parser `global_env` for self-reference. Driver `process_data_with_func` calls `process_data` then `process_def`. Parser `sync_from_env` adds func_name to global_env for subsequent declarations.

- [x] Well-founded recursion — `by_wf` annotation on `def` disables structural guard check via thread-local flag. Parser uses `stop_at_by_wf` to correctly parse the annotation. Wired in `process_def` and `termination.rs`.

- [x] Coinduction — `Delay A` type, `Next` constructor, `Force` destructor with `Force (Next x) = x` beta rule. Added `TDelay`/`TNext`/`TForce` to Term, `VDelay`/`VNext`/`VForce` to Value, `NForce` to Neutral. Full pipeline: shift/subst/max_var, pretty-printer, parser (prefix operators), NbE eval/quote, typechecker (Delay A : U_n when A : U_n, Force : Delay A -> A), equality, positivity. Parser `Delay` in `parse_atom`, `Next`/`Force` in `parse_prefix_or_atom`.

- [x] Stress test and documentation — `examples/stress_mutual_and_ir.owl` exercises all 5 new features. `examples/stress_hit_elimination.owl` exercises nested pattern matching (4-level deep), dependent elimination, parameterized HITs, and hcomp/fill. `docs/reference.md` updated with Prop/SSet, lift/lower, mutual inductives, induction-recursion, termination guard, and worked examples.

- [x] Parser nested pattern matching — Column-based `|` nesting: records column of first `|` in match, breaks when `self.peek().col < my_col`. Fixed infinite recursion in termination checker via `motive_targets_datatype` + `check_body_guard` else branch. Nested patterns work across all HIT types.

- [x] Safe `CURRENT_DTS` — Replaced `Cell<Option<*const [Datatype]>>` raw pointer with `RefCell<Vec<Datatype>>` in thread-local. Eliminates all `unsafe` from `nbe/mod.rs`.

- [x] Type errors point at the offending variable — The parser records the source position of every variable use (and each definition name) while parsing, exposing them via `ProgramParser::take_decl_positions`. The driver accumulates these across the whole program and installs them into the typechecker's thread-local `DECL_NAME_POS` table before checking each declaration. `err_pos` (the `pos` fields on `TypeError` variants) now resolves the most-local de Bruijn variable of the offending term to a real `line:col`, so messages print e.g. `Expected a Π-type, but found: Nat  at 5:43`.

---

## Remaining — Open Items by Category & Priority

> Legend: 🔴 High priority · 🟡 Medium priority · 🟢 Low priority
> (Priority reflects impact on soundness/core usability vs. polish/ecosystem breadth.)

### A. Core Type Theory Soundness Gaps 🔴

These extend already-partially-implemented features (cumulativity); until closed, some legal
subtyping relations are simply not recognized by the checker.

- [x] **Cumulativity for Sigma/Pi types** — extend the existing universe-level cumulativity check to Σ/Π. Π is contravariant in the domain / covariant in the codomain; Σ is covariant in both. Implemented in `cumulativity_check` (see `src/cubical/typechecker/mod.rs`), with tests in `src/cubical/typechecker/mod.rs` and `src/cubical/parser/tests.rs` and a worked example in `examples/cumulativity_sigma_pi.owl`.
- [x] **Cumulativity for record types** — extend cumulativity to desugared record (single-constructor) types. Covered by the `TData` (covariant parameters) rule, since records desugar to single-constructor inductives; see `cumulativity_check` and `examples/cumulativity_sigma_pi.owl`.
- [x] **Variance-aware datatype parameter cumulativity** — the `TData` cumulativity rule now respects per-parameter variance (see `compute_param_variances` in `src/cubical/syntax/positivity.rs`): covariant parameters are checked covariantly, contravariant parameters (occurring only in arrow domains) are checked contravariantly, and invariant parameters (occurring both positively and negatively) require definitional equality. Without this, `Bad U0 ≤ Bad U1` typechecked for a `Bad A` whose parameter occurs negatively. Variance is a least fixed point over the datatype environment, so it propagates through nested datatype applications and mutual definitions. Unit tests in `src/cubical/syntax/positivity.rs` and `src/cubical/typechecker/mod.rs`; integration tests in `src/cubical/parser/tests.rs`.

### B. Decision Procedures / Proof Automation 🔴

The single highest-leverage category for day-to-day proof productivity — these let users
discharge routine algebraic/arithmetic goals in one line instead of writing them by hand.

- [ ] **Omega / Linear arithmetic** — decision procedure for linear arithmetic over Nat/Int. *(🔴 — most general-purpose payoff; underlies many other proofs.)*
- [ ] **Ring solver** — decision procedure for ring identities (normalize + compare polynomial forms). *(🔴 — classic high-value tactic, e.g. Coq/Agda's `ring`.)*
- [ ] **Group solver** — decision procedure for group identities (associativity, identity, inverses). *(🟡 — narrower scope than ring, useful once ring solver exists.)*
- [ ] **Field solver** — decision procedure for field identities (ring + division/inverse reasoning). *(🟡 — natural follow-on to ring solver; depends on it.)*
- [ ] **Decision procedure for propositional equality** — automate reflexivity/symmetry/transitivity chains. *(🟡)*

### C. Pattern Matching 🟡

- [ ] **Nested constructor patterns** — e.g. `suc (suc zero)` matching a literal 2 (requires a full pattern AST rather than the current flat-binder matching). *(🟡 — meaningful ergonomics win, moderate implementation cost.)*

### D. Module & Import System 🟡

Needed for organizing larger codebases/libraries; not blocking for single-file examples.

- [ ] `module M where ...` — basic namespace declaration. *(🟡)*
- [ ] Module parameters. *(🟢 — depends on basic modules first.)*
- [ ] Module instantiation. *(🟢 — depends on module parameters.)*
- [ ] Qualified imports (`import M as mod`). *(🟡)*
- [ ] Selective imports (`import M only [x, y]`). *(🟢)*
- [ ] Unification of same-name imports. *(🟢)*

### E. Proof Assistant UX 🟡

- [ ] **Interactive REPL proof sessions** — per-tactic goal display (`:proof` / `:goals` / `:admit` / `:done`). *(🟡 — big quality-of-life improvement once hole/tactic infrastructure already exists.)*

### F. Performance & Metaprogramming 🟢

- [ ] **Incremental normalization**. *(🟢 — optimization, not correctness-blocking; current NbE already has sharing + memoization.)*
- [ ] **Bidirectional type checking**. *(🟡 — could simplify/streamline the existing infer/check split; worth revisiting if elaboration perf becomes an issue.)*
- [ ] **Reflection API**. *(🟢 — powerful but speculative; no immediate consumer.)*
- [ ] **Custom tactics**. *(🟢 — depends on the built-in tactic language and likely the reflection API.)*
- [ ] **Proof automation** (general). *(🟢 — umbrella goal; mostly subsumed by items in section B.)*

### G. Library & Ecosystem 🟢

Breadth-of-content work — valuable but doesn't gate the type theory or tooling itself.

- [ ] **Standard library**:
  - Data types (Nat, Int, List, Vector, etc.)
  - Algebra (groups, rings, fields, modules)
  - Order theory (posets, lattices)
  - Topology (continuous maps, homotopy)
  - Category theory (functors, natural transformations)
- [ ] **Documentation**:
  - Tutorial / Getting started guide
  - API reference
  - Example gallery
  - Comparison with other cubical systems (Agda cubical, cubicaltt)

---

## Suggested Order of Attack

1. 🔴 **Cumulativity for Σ/Π and records** — closes soundness gaps in an already-partial feature; cheap relative to payoff.
2. 🔴 **Omega (linear arithmetic)** and **Ring solver** — highest-value automation; unlocks Group/Field solvers afterward.
3. 🟡 **Module system basics** (`module M where`) + **qualified imports** — needed before the standard library work in §G can scale.
4. 🟡 **Nested constructor patterns** — moderate-cost ergonomics fix, independent of everything else.
5. 🟡 **Interactive REPL proof sessions** — biggest remaining UX win, builds on existing hole/tactic machinery.
6. 🟢 Remaining items (Group/Field solver, reflection API, custom tactics, incremental normalization, stdlib, docs) — valuable but can proceed in parallel/opportunistically once the above land.
