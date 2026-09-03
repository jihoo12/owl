# TODO.md — Owl: Closing the Gap with Cubical Agda

> **Goal**: Make Owl a competitive cubical type theory proof assistant.
> Checklist format: `[x]` = done, `[ ]` = open.
> Priority: 🔴 blocks core features · 🟡 important for parity · 🟢 polish / nice-to-have.

---

## Completed

- [x] **E1 — Reflection API (Phase 1+2+3: quote/unquote, getContext, getType, TC monad, unify).** ✅ Phase 1: `TQuote`/`TUnquote`, `quote_ast`/`unquote_ast` keywords. Phase 2: `TGetContext`/`TGetType`, `getContext_ast`/`getType_ast` keywords, session-stored context and pre-computed type results. Phase 3: `TUnify` keyword `unify_ast` — checks definitional equality of two terms' types via `definitionally_equal_ctx_r`, returns Unit or type error. `lib/reflection.owl` postulates `OwlTerm`, `quote`, `unquote`, `getType`, `getContext`, `TC`, `tc_return`, `tc_bind`, `unify`, `tc_guard`. `TC` is an identity monad (computationally `TC A = A`). `examples/reflection_demo.owl` exercises the API. All 263 tests pass.

- [x] **G4 — Topology / Homotopy.** ✅ `lib/topology.owl` expanded: added `coproduct_topology` (proof that coproduct of open sets is open), `continuous_comp` (composition of continuous maps), `discrete_continuous` (universal property: any function from discrete space is continuous). Product topology type definition (`product_opens`) and `indiscrete_opens` type added. `examples/topology_demo.owl` exercises the constructions. Previously added: `lib/homotopy.owl` (path operations, homotopy, equivalences, loop spaces, truncated types, contractibility), `lib/suspension.owl` (Susp HIT), `lib/circle.owl` (S1 HIT), `lib/logic.owl`. Fixed parallel substitution bug. 263/263 tests pass.

- [x] **B2 — Absurd patterns (`()`).** ✅ Added `()` as syntactic sugar for zero-case match on empty types. `absurd: bool` field on `MatchArm` in `patterns.rs`, detected in `parse_match_arm`, desugared to empty cases in `parse_match_cases`. `lib/logic.owl` updated. File: `examples/absurd_pattern.owl`. 261/261 tests pass.

- [x] **E2 — Postulates.** ✅ Added `postulate x : T` declarations. `Decl::Postulate` variant in parser/driver, `Env::postulate()` method, `process_postulate()` typechecks `T : U_n`, postulates stored as opaque `VNeutral(NVar(i))` neutrals. `build_definition_values` fixes NVar level after eval so quoting works correctly in any context. `examples/postulate.owl` exercises postulated types, constants, type formers, and use in definitions. 259/259 tests pass.

- [x] **A5 — Higher-dimensional hcomp (Path type decomposition).** ✅ Added Path type decomposition to `hcomp`, `comp`, `fill`, and `hfill` in `nbe/hcomp.rs`. When the carrier type is `VPath(A, x, y)`, the operations decompose by composing at each point of the interval, reducing square composition (2D hcomp) to 1D composition in the carrier type. Example: `examples/higher_dim_hcomp.owl`. 258/258 tests pass.

- [x] **D1 — Universe polymorphism.** ✅ Added `LevelExpr` enum (`LVar(i32)`, `LConst(i32)`, `LSuc(Box<LevelExpr>)`, `LMax(Box<LevelExpr>, Box<LevelExpr>)`) to `syntax/mod.rs`. Changed `TUniv(Level)` and `TLift(Arc<Term>, Level)` to hold `LevelExpr` instead of bare `i32`. Level expressions support `shift`/`subst`/`max_var` — level variables share the term variable de Bruijn namespace. Added `TLevelTy`/`VLevelTy` for the `Level` type. Parser: `U (lsuc l)`, `U (max l1 l2)`, `U l`, `U0`/`U1` backward compat. `Level` keyword recognized. `lift`/`lower` are prefix keywords. NbE: `VUniv`/`VLift` hold `LevelExpr`. Typechecker: `type_level_dt` returns `LevelExpr`, `U_n : U_{n+1}` via `LevelExpr::suc`, Pi/Sigma/Glue/Equiv/Partial/SystemType use `LevelExpr::max`. Cumulativity: `leq` with structural equality fallback for stuck level variables. Files: `syntax/mod.rs`, `syntax/pretty.rs`, `parser/grammar.rs`, `nbe/value.rs`, `nbe/eval.rs`, `nbe/quote.rs`, `nbe/transport.rs`, `nbe/meta.rs`, `typechecker/mod.rs`, `typechecker/errors.rs`, `typechecker/termination.rs`, `driver.rs`, `equality.rs`, `syntax/positivity.rs`. Example: `examples/universe_poly.owl`. 257/257 tests pass.

- [x] **A4 — Cubical identity types (`Id`).** ✅ Added `TId(A, a, b)`, `TRefl(x)`, `TJ(motive, base, p)` to `Term` enum. Parser: `Id A x y`, `Refl x`, `J motive base p`. NbE: `VId`, `VRefl`, `VJelim` values; `do_j` computes `J B d (Refl x) = d` (key definitional reduction). Quote: bidirectional reconstruction. Typechecker: `Id A a b : U_n`, `Refl x : Id A x x`, `J motive base p : B y p`. Example `examples/id_types.owl` tests type formation, reflexivity, and J computing on refl. 257/257 tests pass, `cargo fmt` clean.

- [x] **A3 — Frontier-of-instability Phase 4 (quoting).** ✅ Made `try_destabilize` `pub(super)` in `elim.rs`. In `quote_case_body`, the `_ => quote(...)` fallback now checks if the value is a `VNeutral` with a satisfied frontier and attempts destabilization before quoting. This hardens quoting for stuck elim case bodies that capture interval-bound neutrals. Defensive — kernel re-checks everything. 256/256 tests pass, `cargo fmt` clean.

- [x] **NbE eval depth guard + Arc-based O(1) clone + TApp spine trampoline.** `EVAL_NBE_MAX_DEPTH=2000` in `eval.rs` prevents stack overflow. All `Term`/`Value`/`Neutral`/`I`/`Frontier` subterms migrated from `Box` to `Arc` — `Term::clone()` is now O(1) (atomic refcount). `meta.rs` zonk rewritten as recursive rebuild (no in-place mutation). TApp evaluation collects the left spine iteratively: `TApp(TApp(TApp(f, a1), a2), a3)` → head=f, spine=[a1,a2,a3], then iteratively apply. This eliminates O(n) stack depth for deep application chains. Deep TApp chains (2,500+ applications) work on a 2 MiB stack thread. 256/256 tests pass, `cargo fmt` clean.

- [x] **A2 — Indexed inductive type transport.** Fixed `transport_data_con`/`pcon`/`sqcon`/`cellcon` in `transport.rs`. The old indexed path tried to extract Pi types from `VData(d, params_at_i)`, which immediately fell through (VData is not VPi). The new approach: evaluate the closure at the formal interval variable to get `VData(d, params_at_i)`, then for each constructor arg type `T_k`, substitute each data type param variable `TVar(n + m - j)` with `quote(params_at_i[j])`. This correctly builds type families where data type parameters change along the interval. Creating a test for the non-constant path requires a `Path Type A B` with `A ≠ B`, which needs Glue/univalence — deferred. 253/253 tests pass, `cargo fmt` clean.

- [x] **A1 — Generalized transport (`transp`) primitive.** ✅ Full implementation: `TTransp(A, r, x)` AST, `VTransp`/`NTransp` values, parser syntax, eval with endpoint reduction (`i0`→base, `i1`→`do_transport`, non-concrete→stuck), eta-expansion for non-VPLam families, quote/quote_neutral/quote_case_body, typechecker infer rule, per-typeformer decomposition via `do_transport` VPLam branch (Pi, Sigma, Path, data, Glue). `examples/transp_basic.owl` exercises constant-family, function-lambda, Sigma, Pi, nested transport. 253/253 tests pass.

- [x] **Frontier-of-instability — Phases 1–3.** `Frontier` enum in `value.rs` (`False`, `IntervalEq`, `Or`, `And`), `Neutral` struct with `{ inner, frontier }`, 15 convenience constructors with correct frontier propagation. `try_destabilize` in `elim.rs` checks `frontier.is_satisfied(interval_bindings)` and recursively destabilizes neutrals (NPApp, NApp, NFst, NSnd, NProj, NForce, NElim). `IClosure::apply_interval_value` populates `Session::interval_bindings`. 253/253 tests pass. Phase 4 (quoting update) remains.

- [x] **H4 — Implicit arguments + instance search.** `{x : A}` implicit binder syntax. Typechecker auto-fills via context/global `Env.instances` DB. `ring`/`field`/`group` tactics resolve instances.

- [x] **Performance pass.** opt-level-2 dev/test, verify-once policy, 256 MiB CLI stack, `OWL_TIMINGS=1`. `cargo test` ~31–54 s.

- [x] **H5 — `lib/algebra.owl`.** `CommRing`/`Group`/`Field`/`Module` records. `NatCommRing` bundled instance. `examples/module_demo.owl`, `examples/natcommring_demo.owl`.

- [x] **H3 — Int `by omega` + Int algebra.** Omega over Nat/Int. First batch of Int ring laws (comm, unit/zero mul, neg-neg, congruence glue). Deferred: assoc, distributivity, `IntCommRing` bundling.

- [x] **Section B closed — `by group` + `by eq`.** Group solver over abstract `Group A mul inv one`. Equality chaining via BFS over context paths + transitivity lemma.

- [x] **Module system.** `module M where`, parameters `module M (A : Type) where`, instantiation `module N = M (e)`, qualified/aliased imports, selective imports `only [...]`, provenance-based conflict detection.

- [x] **NbE split + Session consolidation.** 7,192-line `nbe/mod.rs` → focused submodules. 14 `thread_local!` blocks → single `Session` struct. `&mut Session` threaded through 62 NbE functions + 150 external call sites.

- [x] **Nested constructor patterns.** Phase 1 (parser compilation) + Phase 2 (HIT-case refinement). Column-based nesting, completeness check, `as`/or-patterns combined with nesting.

- [x] **Square/cell-constructor endpoint reduction.** `VSqCon`/`VCellCon` at concrete endpoints → face values. `reduce_con_at_endpoint` generalized for pcon/sqcon/cellcon. `mer 0 @ i1 → sso 0`.

- [x] **HITs — path/square/n-cell constructors.** `[ face0, face1 ]`, `[[ fi0, fi1, fj0, fj1 ]]`, `[[[...]]]` syntax. Full eliminator support with interval phantom slots.

- [x] **Glue / univalence.** `Glue`, `glue`, `unglue`, `Equiv`, `mkEquiv`, `equivFwd`, `ua`. `transport (ua e) x` reduces to `equivFwd e x`.

- [x] **Cubical primitives.** `hcomp`, `comp`, `fill`, `hfill` with multi-face systems `[phi => tube, ...]`.

- [x] **Transport.** `transport`/`coe` along `Path U A B`. Decomposes through Pi, Sigma, Path, data, Glue.

- [x] **Path types.** `Path A u v`, `PathP (<i> A i) u v`, path lambda `<i> body`, path application `p @ r`, endpoint reductions.

- [x] **Universes.** `U0 : U1 : U2 : ...`, `Prop` (impredicative), `SSet` (predicative strict), `Lift`/`Lower`. Cumulativity (Pi, Sigma, data, Path, records).

- [x] **Inductive types.** Parameterized, recursive, mutual (induction-induction), induction-recursion. Positivity checking.

- [x] **Records.** Field projection, dot notation, record update, record patterns.

- [x] **Coinduction.** `Delay A`, `Next`, `Force` with `Force (Next x) = x`.

- [x] **Termination.** Structural recursion guard. `by_wf` for well-founded recursion.

- [x] **Decision procedures.** `by omega`, `by ring`, `by ring with C`, `by field with F`, `by group with G`, `by eq`.

- [x] **F2 — `forall` after `->`.** Parser now accepts `A -> forall (x : B), C -> D` as `A -> (forall (x : B), (C -> D))`. `forall` binds looser than `->`. Documented in `docs/reference.md` §Pi Types and §Grammar. `examples/forall_after_arrow.owl` exercises the new syntax.

- [x] **H5 — `lib/algebra.owl`.** `CommRing`/`Group`/`Field`/`Module` records. `NatCommRing` bundled instance. `examples/module_demo.owl`, `examples/natcommring_demo.owl`.

- [x] **Pattern matching.** Nested patterns, or-patterns, `as`-patterns, record patterns, completeness check.

- [x] **Partial elements / cubical subtypes.** `[_ | phi] A`, `Partial phi A`.

---

## Open Items

### A. Core Type Theory — Closing Cubical Agda Gaps 🔴

These are the fundamental features Cubical Agda has that Owl lacks. They affect soundness, expressiveness, and normalization.

#### A1. Generalized transport (`transp`) ✅

Cubical Agda's `transp` handles **non-constant type families**: `transp : (A : I → Set ℓ) → I → A i0 → A i1`. It computes through the type former (Pi, Sigma, data, etc.) case-by-case.

**Completed**:
- [x] `TTransp(A, r, x)` AST with shift/subst/max_var/pretty
- [x] `VTransp` value, `NTransp` neutral, `Neutral::ntransp` constructor
- [x] Parser syntax: `transp A r x` (3 prefix args)
- [x] Eval: endpoint reduction (`i0`→base, `i1`→do_transport, non-concrete→stuck)
- [x] Eta-expansion: non-VPLam families (e.g. `fun (i : I) => ...`) are eta-expanded to synthetic VPLam for decomposition
- [x] Quote: TTransp/VTransp/NTransp in all quote paths
- [x] Typechecker infer: `A : I → Type, r : I, x : A i0 ⊢ A r`
- [x] Per-typeformer decomposition at `i1` via `do_transport` VPLam branch (Pi, Sigma, Path, data, Glue)
- [x] All exhaustive matches (equality, transport, termination, errors, driver)
- [x] `examples/transp_basic.owl` — exercises constant-family, function-lambda, Sigma, Pi, nested transport

**Files**: `syntax/mod.rs`, `parser/grammar.rs`, `nbe/eval.rs`, `nbe/transport.rs`, `nbe/quote.rs`, `nbe/value.rs`, `nbe/meta.rs`, `syntax/positivity.rs`, `typechecker/mod.rs`, `typechecker/errors.rs`, `typechecker/termination.rs`, `equality.rs`, `examples/transp_basic.owl`.

#### A2. Indexed inductive type transport ✅

A consequence of A1. Cubical Agda's `transp` computes through indexed types by substituting indices. Example: `transp (λi. Vec A (add n i)) i1 v` reduces when `n` is a constructor.

**Done**: Fixed all four transport functions (`transport_data_con`, `transport_data_pcon`, `transport_data_sqcon`, `transport_data_cellcon`). The old approach tried to extract Pi types from `VData(d, params_at_i)`, which immediately fell through. The new approach: evaluate the closure at the formal interval variable to get `VData(d, params_at_i)`, then for each constructor arg type `T_k`, substitute each data type param variable `TVar(n + m - j)` with `quote(params_at_i[j])` — the param's interval-dependent value. This correctly builds type families where the data type parameters change along the interval.

**Test**: `examples/indexed_transp_test.owl` exercises the non-constant path (`is_constant = false`) by constructing `Bool ≃ Bool'` via `mkEquiv`, using `ua` to build a `Path U0 Bool Bool'`, then transporting `cons tt nil : List Bool` through `List (ua bool_bool' @ i)` to produce `List Bool'`. Also added `VUa` PApp endpoint reduction (`ua e @ 0 = equiv_dom(e)`, `ua e @ 1 = equiv_cod(e)`) in `elim.rs` so that `is_constant` correctly detects non-constant families. All 254 tests pass.

- [x] **A3 — Frontier-of-instability Phase 4 (quoting).** ✅ Made `try_destabilize` `pub(super)` in `elim.rs`. In `quote_case_body`, the `_ => quote(...)` fallback now checks if the value is a `VNeutral` with a satisfied frontier and attempts destabilization before quoting. Defensive — kernel re-checks everything. `src/cubical/nbe/quote.rs`, `src/cubical/nbe/elim.rs`. 256/256 tests pass.

#### A4. Cubical identity types (`Id`) ✅

Cubical Agda has a separate `Id` type where `J` computes **definitionally** on `refl` (unlike `Path`-based `J`). `Id` and `Path` are equivalent but `Id` has better computational behavior for Martin-Löf-style proofs.

**Plan**:
1. ~~Add `Id A a b` term constructor with `refl : Id A a a`.~~ ✅
2. ~~Add `J` eliminator that computes on `refl`.~~ ✅
3. Prove `Id ≃ Path` in the standard library. (Future work)

**Files**: `syntax/mod.rs`, `nbe/value.rs`, `nbe/eval.rs`, `nbe/quote.rs`, `parser/grammar.rs`, `typechecker/mod.rs`, `typechecker/errors.rs`, `typechecker/termination.rs`, `syntax/pretty.rs`, `syntax/positivity.rs`, `equality.rs`, `nbe/meta.rs`, `nbe/transport.rs`. **Example**: `examples/id_types.owl`.

#### A5. Higher-dimensional `hcomp` ✅

**Done**: Added Path type decomposition to `hcomp`, `comp`, `fill`, and `hfill` in `nbe/hcomp.rs`. When the carrier type is `VPath(A, x, y)`, the operations decompose by composing at each point of the interval:

- `hcomp (Path A x y) [phi => t, ...] p ≡ <i> hcomp A [phi => t @ i] (p @ i)`
- `comp (Path A x y) sys p` — same decomposition, applied to the evaluated type family
- `fill (Path A x y) sys p ≡ <j> hfill A [sys @ j] (p @ j)`
- `hfill (Path A x y) [phi => t, ...] p ≡ <i> hcomp A [phi => t @ i] (p @ i)`

This enables square composition (2D hcomp): composing paths whose type is itself a Path type. The decomposition recursively pushes hcomp through the Path structure until a non-Path type is reached.

**Files**: `nbe/hcomp.rs`. **Example**: `examples/higher_dim_hcomp.owl` (tests empty system, constant tube, two-tube, fill, hfill, nested hcomp through Path types). 258/258 tests pass.

---

### B. Pattern Matching — Cubical Agda Parity 🟡

#### B1. Path application patterns 🟡

Cubical Agda matches on `p i0` and `p i1` in patterns:
```agda
f : (p : Path A a b) → B
f p with p i0 | p i1
... | a' | b' = ...
```

**Plan**: Add path-application as a pattern form in `match`. When the scrutinee is `p @ i0` or `p @ i1`, reduce at typechecking time.

#### B2. Absurd patterns (`()`) ✅

Cubical Agda has `()` for empty pattern matching on types with no constructors. Owl handles `Empty` via `match e return A with` (zero cases) but lacks syntactic `()`.

**Plan**: Add `()` as syntactic sugar for `match x return A with` (zero cases). Verify the kernel already handles this (it does).

**Done** (2026-09-02): Added `absurd: bool` field to `MatchArm` in `patterns.rs`. Parser detects `()` in `parse_match_arm`, sets `absurd: true`; `parse_match_cases` returns empty cases when arm is absurd. `lib/logic.owl` updated to use new syntax. File: `examples/absurd_pattern.owl`. 261/261 tests pass.

#### B3. With-patterns 🟡

Cubical Agda's `with` abstraction:
```agda
f x with g x
... | zero = ...
... | suc n = ...
```

**Plan**: Add `with` as syntactic sugar that introduces a local definition and case-splits on it. Parser-level desugaring into nested `match`.

#### B4. Forced (dot) patterns 🟢

Cubical Agda's `.` patterns for forced arguments. Lower priority — mostly for error messages.

---

### C. Module System — Cubical Agda Parity 🟡

#### C1. Datatypes/records inside parameterized modules 🟡

Currently rejected. Cubical Agda allows data declarations inside parameterized modules.

**Plan**: Extend `process_data`/`process_record` in the driver to close over module parameters (similar to how `process_def` already works).

#### C2. Private / abstract declarations 🟡

Cubical Agda has `private` and `abstract` modifiers. Owl has no access control.

**Plan**: Add `private` modifier to declarations. `private` defs are visible only within their module. `abstract` defs normalize only to themselves (not to their body).

#### C3. Mutual blocks (general) 🟢

Cubical Agda supports general `mutual { ... }` blocks. Owl only has mutual inductives.

**Plan**: Extend the parser/driver to support general mutual definitions (not just inductives).

---

### D. Universe System — Cubical Agda Parity 🟡

#### D1. Universe polymorphism ✅

Cubical Agda inherits Agda's full universe polymorphism: `Level`, `_⊔_`, `lsuc`. Owl has fixed-level universes `U0 : U1 : U2 : ...` with cumulativity.

**Done**: Added `LevelExpr` enum (`LVar`, `LConst`, `LSuc`, `LMax`) to represent universe levels as a sub-language of terms. `TUniv` and `TLift` now hold `LevelExpr` instead of bare `i32`. Level expressions support `shift`/`subst`/`max_var` (level vars share the term variable de Bruijn namespace). Parser: `U (lsuc l)`, `U (max l1 l2)`, `U l`, `U0`/`U1` backward compat. `Level` keyword recognized as a type (`TLevelTy`/`VLevelTy`). `lift` and `lower` are prefix keywords. NbE: `VUniv`/`VLift` hold `LevelExpr`. Typechecker: `type_level_dt` returns `LevelExpr`, `U_n : U_{n+1}` via `LevelExpr::suc`, Pi/Sigma/Glue use `LevelExpr::max`. Cumulativity: `leq` with fallback to structural equality for stuck level variables. 257/257 tests pass, `examples/universe_poly.owl` exercises concrete levels, `Level` type, `lsuc`, `max`, `lift`.

**Deferred**: Full implicit level variable substitution (level vars crossing term binders are shifted but not substituted — `id_poly 0 x` works but `id_poly l x` with level variable `l` does not fully reduce). This requires a separate level context or level-to-term conversion.

#### D2. Fine-grained predicativity control 🟢

Cubical Agda can restrict `--cumulativity`, `--level-universe`, etc. Owl's Prop is impredicative but there's no fine-grained control.

---

### E. Metaprogramming / Extensibility 🟡

#### E1. Reflection API ✅

Cubical Agda exposes `Agda.Builtin.Reflection` for meta-programming: `TC` monad, quotation, unquotation, typeclass resolution, custom solvers.

**Phase 1 ✅** (2026-09-03): Quote/unquote kernel primitives.

**Phase 2 ✅** (2026-09-03): getContext/getType kernel primitives.

**Phase 3 ✅** (2026-09-03): TC monad and unify. Added `TUnify` keyword `unify_ast` — checks definitional equality of two terms' types via `definitionally_equal_ctx_r`, returns Unit on success or type error on failure. `lib/reflection.owl` postulates `TC` (identity monad), `tc_return`, `tc_bind`, `unify`, `tc_guard`. All 263 tests pass.

#### E2. Postulates ✅

Cubical Agda supports `postulate` — declared but unimplemented constants. Useful for assuming axioms (carefully).

**Plan**: Add `postulate x : T` declaration. Typecheck `T` but skip body checking. Mark the name as postulated so normalization doesn't try to evaluate it.

**Done** (2026-09-02): Added `Decl::Postulate { name, ty }` variant, parser (`postulate name : T`), `Env::postulate()`, `process_postulate()` in driver, `sync_from_env` integration. Postulates store `TVar(0)` placeholder as NbE value; a post-evaluation fixup in `build_definition_values` corrects the NVar level so quoting produces correct de Bruijn indices in any context. Postulates are opaque neutrals that never reduce. File: `examples/postulate.owl`. 259/259 tests pass.

#### E3. Rewriting 🟢

Cubical Agda's `REWRITE` mechanism: declare `f` and a proof `law : f x = e`, then all occurrences of `f x` reduce to `e`.

#### E4. Custom tactics 🟢

Depends on E1 (reflection API). Users define tactics via the TC monad.

---

### F. Ergonomics 🟡

#### F1. Interactive REPL proof sessions 🟡

`:proof` / `:goals` / `:admit` / `:done` commands. Builds on existing hole (`?name`) and tactic infrastructure.

#### F2. `forall` after `->` ✅

`forall` / `∀` binders can now appear directly after `->`:
```
Path Nat a b -> forall (m : Nat), Path Nat m m
```
Parser-level: `forall` binds looser than `->` and absorbs everything to its
right. `examples/forall_after_arrow.owl` tests the new syntax.
**Files**: `parser/grammar.rs`. Documented in `docs/reference.md`.

#### F3. Implicit lambda syntax 🟢

`fun {x} => ...` for constructing implicit functions. Currently only `fun x => ...` is supported.

#### F4. Bidirectional type checking 🟢

Could simplify the existing infer/check split. Worth revisiting if elaboration perf becomes an issue.

#### F5. Erasure analysis 🟢

Cubical Agda's `--cubical=erased` for performance. Not critical for correctness.

---

### G. Standard Library 🟡

Cubical Agda has `agda/cubical` with Nat, Int, List, Vector, algebra, topology, category theory. Owl is building from scratch.

#### G1. Core data types 🟡

- [x] Nat (suc/zero, +, *, comparison) — in `lib/ring_laws.owl`, used across all examples
- [ ] Int (add, mul, neg, sub, abs, sign) — `examples/int_sign_magnitude.owl` has operations but no laws
- [ ] List (append, reverse, map, fold, length)
- [ ] Vector (indexed, map, zip, append)
- [ ] Maybe / Option
- [x] Bool (and, or, not, if-then-else) — ad-hoc in examples, no shared library

#### G2. Algebra 🟡

- [x] Monoid, Group, Ring, CommRing, Field, Module — in `lib/algebra.owl` and `lib/field_laws.owl`
- [ ] Lattice, Boolean algebra
- [ ] Ordered structures (DecTotalOrder, etc.)

#### G3. Logic 🟡

- [ ] Propositional logic (And, Or, Not, Implies, Iff)
- [x] Not — in `lib/logic.owl`
- [ ] Quantifiers (Forall, Exists)
- [ ] Decidability
- [x] Truncation (PropTrunc) — `Trunc` HIT in `lib/truncation.owl` (no general eliminator yet)
- [ ] SetTrunc
- [ ] Propositional extensionality (from univalence)

#### G4. Topology / Homotopy ✅

- [x] Topological spaces (as types + open predicates) — `lib/topology.owl` (Topology record, discrete_opens/discrete_topology, product_opens type, coproduct_topology proof, continuous_comp, discrete_continuous)
- [x] Continuous maps — `lib/topology.owl` (ContinuousMap record, composition, universal properties)
- [x] Homotopy groups — `lib/homotopy.owl` defines loop spaces, Omega, Omega2
- [x] Path spaces, loop spaces — `lib/homotopy.owl` (refl, sym, trans, cong, Homotopy, IsEquiv), `lib/circle.owl` (S1 HIT), `lib/suspension.owl` (Susp HIT)

#### G5. Category theory 🟢

- [ ] Category, Functor, Natural transformation
- [ ] Adjunctions, limits, colimits
- [ ] Yoneda lemma
- [ ] Presheaves, sheaves

#### G6. Algebraic geometry 🔴

- [ ] Ideal predicates
- [ ] Polynomial rings R[X]
- [ ] Quotient rings R/I
- [ ] Localization S⁻¹R
- [ ] Prime/maximal ideals
- [ ] Finite fields F_p
- [ ] Categories of rings / Spec R (functor of points)
- [ ] Zariski site, sheaves
- [ ] Affine schemes, projective space

---

### H. Cubical TT Foundation — Research-Level 🟢

#### H1. Higher-dimensional `hcomp` 🟢

Already listed as A5. Research-level; not needed for practical work.

#### H2. Spectrum / stabilization 🟢

Spectrum types for stable homotopy theory. Research-level.

---

## Suggested Attack Order

1. ~~**A1 (generalized transport)**~~ — ✅ done.
2. ~~**A3 (frontier Phase 4)**~~ — ✅ done.
3. ~~**A4 (cubical identity types)**~~ — ✅ done.
4. ~~**F2 (`forall` after `->`)**~~ — ✅ done.
5. ~~**B2 (absurd patterns)**~~ — ✅ done.
6. **F1 (interactive REPL)** — biggest UX win once holes/tactics exist.
7. ~~**E2 (postulates)**~~ — ✅ done.
8. **E1 (reflection API)** — large but enables all subsequent automation.
9. ~~**D1 (universe polymorphism)**~~ — ✅ done.
10. **G1–G6 (standard library)** — breadth work, can proceed in parallel.
