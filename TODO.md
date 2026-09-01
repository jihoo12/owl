# TODO.md — Owl: Closing the Gap with Cubical Agda

> **Goal**: Make Owl a competitive cubical type theory proof assistant.
> Checklist format: `[x]` = done, `[ ]` = open.
> Priority: 🔴 blocks core features · 🟡 important for parity · 🟢 polish / nice-to-have.

---

## Completed

- [x] **A3 — Frontier-of-instability Phase 4 (quoting).** ✅ Made `try_destabilize` `pub(super)` in `elim.rs`. In `quote_case_body`, the `_ => quote(...)` fallback now checks if the value is a `VNeutral` with a satisfied frontier and attempts destabilization before quoting. This hardens quoting for stuck elim case bodies that capture interval-bound neutrals. Defensive — kernel re-checks everything. 256/256 tests pass, `cargo fmt` clean.

- [x] **NbE eval depth guard + Arc-based O(1) clone + TApp spine trampoline.** `EVAL_NBE_MAX_DEPTH=2000` in `eval.rs` prevents stack overflow. All `Term`/`Value`/`Neutral`/`I`/`Frontier` subterms migrated from `Box` to `Arc` — `Term::clone()` is now O(1) (atomic refcount). `meta.rs` zonk rewritten as recursive rebuild (no in-place mutation). TApp evaluation collects the left spine iteratively: `TApp(TApp(TApp(f, a1), a2), a3)` → head=f, spine=[a1,a2,a3], then iteratively apply. This eliminates O(n) stack depth for deep application chains. Deep TApp chains (2,500+ applications) work on a 2 MiB stack thread. 256/256 tests pass, `cargo fmt` clean.

- [x] **A2 — Indexed inductive type transport.** Fixed `transport_data_con`/`pcon`/`sqcon`/`cellcon` in `transport.rs`. The old indexed path tried to extract Pi types from `VData(d, params_at_i)`, which immediately fell through (VData is not VPi). The new approach: evaluate the closure at the formal interval variable to get `VData(d, params_at_i)`, then for each constructor arg type `T_k`, substitute each data type param variable `TVar(n + m - j)` with `quote(params_at_i[j])`. This correctly builds type families where data type parameters change along the interval. Creating a test for the non-constant path requires a `Path Type A B` with `A ≠ B`, which needs Glue/univalence — deferred. 253/253 tests pass, `cargo fmt` clean.

- [x] **A1 — Generalized transport (`transp`) primitive.** ✅ Full implementation: `TTransp(A, r, x)` AST, `VTransp`/`NTransp` values, parser syntax, eval with endpoint reduction (`i0`→base, `i1`→`do_transport`, non-concrete→stuck), eta-expansion for non-VPLam families, quote/quote_neutral/quote_case_body, typechecker infer rule, per-typeformer decomposition via `do_transport` VPLam branch (Pi, Sigma, Path, data, Glue). `examples/transp_basic.owl` exercises constant-family, function-lambda, Sigma, Pi, nested transport. 253/253 tests pass.

- [x] **Frontier-of-instability — Phases 1–3.** `Frontier` enum in `value.rs` (`False`, `IntervalEq`, `Or`, `And`), `Neutral` struct with `{ inner, frontier }`, 15 convenience constructors with correct frontier propagation. `try_destabilize` in `elim.rs` checks `frontier.is_satisfied(interval_bindings)` and recursively destabilizes neutrals (NPApp, NApp, NFst, NSnd, NProj, NForce, NElim). `IClosure::apply_interval_value` populates `Session::interval_bindings`. 253/253 tests pass. Phase 4 (quoting update) remains.

- [x] **H4 — Implicit arguments + instance search.** `{x : A}` implicit binder syntax. Typechecker auto-fills via context/global `Env.instances` DB. `ring`/`field`/`group` tactics resolve instances.

- [x] **Performance pass.** opt-level-2 dev/test, verify-once policy, 256 MiB CLI stack, `OWL_TIMINGS=1`. `cargo test` ~31–54 s.

- [x] **H5 started — `lib/algebra.owl`.** `CommRing`/`Group`/`Field`/`Module` records. `NatCommRing` bundled. `examples/module_demo.owl`.

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

#### A4. Cubical identity types (`Id`) 🟡

Cubical Agda has a separate `Id` type where `J` computes **definitionally** on `refl` (unlike `Path`-based `J`). `Id` and `Path` are equivalent but `Id` has better computational behavior for Martin-Löf-style proofs.

**Plan**:
1. Add `Id A a b` term constructor with `refl : Id A a a`.
2. Add `J` eliminator that computes on `refl`.
3. Prove `Id ≃ Path` in the standard library.

**Files**: `src/cubical/syntax/mod.rs`, `src/cubical/parser/grammar.rs`, `src/cubical/nbe/eval.rs`, `src/cubical/typechecker/mod.rs`.

#### A5. Higher-dimensional `hcomp` 🟢

Research-level. Cubical Agda handles `hcomp` in higher cubes (beyond 1D). Owl explicitly defers this as research-level. Not needed for practical algebraic geometry.

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

#### B2. Absurd patterns (`()`) 🟡

Cubical Agda has `()` for empty pattern matching on types with no constructors. Owl handles `Empty` via `match e return A with` (zero cases) but lacks syntactic `()`.

**Plan**: Add `()` as syntactic sugar for `match x return A with` (zero cases). Verify the kernel already handles this (it does).

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

#### D1. Universe polymorphism 🟡

Cubical Agda inherits Agda's full universe polymorphism: `Level`, `_⊔_`, `lsuc`. Owl has fixed-level universes `U0 : U1 : U2 : ...` with cumulativity.

**Plan**: Add `Level` type with `_⊔_` (max) and `lsuc`. Universe-polymorphic definitions: `def f : {ℓ : Level} → Uℓ → Uℓ`. This is a significant parser + typechecker change.

#### D2. Fine-grained predicativity control 🟢

Cubical Agda can restrict `--cumulativity`, `--level-universe`, etc. Owl's Prop is impredicative but there's no fine-grained control.

---

### E. Metaprogramming / Extensibility 🟡

#### E1. Reflection API 🟡

Cubical Agda exposes `Agda.Builtin.Reflection` for meta-programming: `TC` monad, quotation, unquotation, typeclass resolution, custom solvers.

**Plan**: Add a `Reflection` module with primitives:
- `quote : A → Term` / `unquote : Term → A`
- `getType : Name → TC Type` / `getContext : TC Context`
- `unify : Term → Term → TC Unit` (constraint solving)

This is a large feature but enables all subsequent automation.

#### E2. Postulates 🟡

Cubical Agda supports `postulate` — declared but unimplemented constants. Useful for assuming axioms (carefully).

**Plan**: Add `postulate x : T` declaration. Typecheck `T` but skip body checking. Mark the name as postulated so normalization doesn't try to evaluate it.

#### E3. Rewriting 🟢

Cubical Agda's `REWRITE` mechanism: declare `f` and a proof `law : f x = e`, then all occurrences of `f x` reduce to `e`.

#### E4. Custom tactics 🟢

Depends on E1 (reflection API). Users define tactics via the TC monad.

---

### F. Ergonomics 🟡

#### F1. Interactive REPL proof sessions 🟡

`:proof` / `:goals` / `:admit` / `:done` commands. Builds on existing hole (`?name`) and tactic infrastructure.

#### F2. `forall` after `->` 🟡

Currently `forall` cannot follow `->` — all binders must precede the arrow chain. Cubical Agda has no such restriction.

**Plan**: In the parser, after seeing `->`, continue parsing binders as implicit Pi.

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

- [ ] Nat (suc/zero, +, *, ^, comparison)
- [ ] Int (add, mul, neg, sub, abs, sign)
- [ ] List (append, reverse, map, fold, length)
- [ ] Vector (indexed, map, zip, append)
- [ ] Maybe / Option
- [ ] Bool (and, or, not, if-then-else)

#### G2. Algebra 🟡

- [ ] Monoid, Group, Ring, CommRing, Field, Module
- [ ] Lattice, Boolean algebra
- [ ] Ordered structures (DecTotalOrder, etc.)

#### G3. Logic 🟡

- [ ] Propositional logic (And, Or, Not, Implies, Iff)
- [ ] Quantifiers (Forall, Exists)
- [ ] Decidability
- [ ] Truncation (PropTrunc, SetTrunc)
- [ ] Propositional extensionality (from univalence)

#### G4. Topology / Homotopy 🟢

- [ ] Topological spaces (as types + open predicates)
- [ ] Continuous maps
- [ ] Homotopy groups
- [ ] Path spaces, loop spaces

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

1. ~~**A1 (generalized transport)**~~ — ✅ done. AST/value/eval/quote/typecheck, eta-expansion, per-typeformer decomposition.
2. ~~**A3 (frontier Phase 4)**~~ — ✅ done. `try_destabilize` made `pub(super)`, `quote_case_body` now attempts destabilization for frontier-satisfied neutrals. Defensive — kernel re-checks.
3. **B2 (absurd patterns)** — trivial parser sugar, immediate ergonomic win.
4. **A4 (cubical identity types)** — moderate cost, good for Martin-Löf compatibility.
5. **F2 (`forall` after `->`)** — parser fix, immediate ergonomics improvement.
6. **F1 (interactive REPL)** — biggest UX win once holes/tactics exist.
7. **E2 (postulates)** — small, useful for assuming axioms in algebraic geometry.
8. **E1 (reflection API)** — large but enables all subsequent automation.
9. **D1 (universe polymorphism)** — significant but necessary for library scale.
10. **G1–G6 (standard library)** — breadth work, can proceed in parallel.
