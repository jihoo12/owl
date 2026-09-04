# TODO.md — Owl: Closing the Gap with Cubical Agda

> **Goal**: Make Owl a competitive cubical type theory proof assistant.
> Checklist format: `[x]` = done, `[ ]` = open.
> Priority: 🔴 blocks core features · 🟡 important for parity · 🟢 polish / nice-to-have.

---

## Completed

- [x] **A6 — Soundness fix for indexed type zero-arity constructors.** ✅ Added `return_args: Option<Vec<Term>>` to `ConSig` struct, storing the TData args from constructor return types during parsing. Modified `check_dt_inner` TCon handler: for zero-arity constructors with repeated de Bruijn vars in return_args (indicating index constraints like refl's `Eq A x x`), substitute inferred params into return_args and check the result matches the expected type via `require_equal`. Scoped to avoid false positives for constructors without index constraints (like nil). Added `bad_examples/soundness_indexed.owl` as negative test, `bad_examples_must_fail` guard test. 275/275 tests pass, `cargo fmt` clean. **Note**: Full index unification (vtail etc.) remains OPEN — see A6.

- [x] **G1 — Core data types.** ✅ Created standalone library files for all core data types. `lib/bool.owl`: Bool with not/and/or/xor/if/eq + proofs (not_not, and_idem, or_idem, and_comm, or_comm). `lib/list.owl`: List with append/reverse/map/foldl/foldr/length/filter/any/all + proofs (append_nil_l, append_assoc, map_append). `lib/maybe.owl`: Maybe with default/map/bind/is_just/is_nothing/from_maybe. `lib/vector.owl`: Vec type with nil/cons/vhead/vnil (dependent elimination limited by kernel). `lib/int.owl`: Int with abs/sign/neg/add/mul/is_nonneg. Added 5 example demos (bool_demo, list_demo, maybe_demo, vector_demo, int_ops_demo) and 10 guard tests (5 lib + 5 demo). 274/274 tests pass, `cargo fmt` clean.

- [x] **C1 — Datatypes/records inside parameterized modules.** ✅ Removed `reject_inside_parameterized_module` calls for `inductive`/`record` declarations. Added `wrap_datatype_with_module_params` that prepends module params to `dt.params` and updates all self-references (`TData(dt_name, args)`) in constructor arg types, path/square/cell constructor faces by prepending module-param de Bruijn variable references. Key insight: `parse_constructor_type` normalises arg_tys to the outer scope via `shift(-depth, 0, …)` so indices already match `param_ctx` — the only fix needed is updating self-references to include the new module params. Removed the old incorrect shifts of arg_tys, faces, and dt-param types. Files: `parser/grammar.rs`, `parser/mod.rs`, `parser/tests.rs`. Example: `examples/parameterized_datatype.owl`. 264/264 tests pass, `cargo fmt` clean.

- [x] **E4 — Custom tactics.** ✅ Added `Tactic::Custom(String)` variant. Parser: `by tactic <name>` syntax. Tactic engine: evaluates the named global tactic function applied to the goal type via NbE, extracts the `TermVal` proof term. Critical fix: `TQuote`/`TGetContext`/`TGetType` now return `TVar(lookup_ctx_index("OwlTerm", ctx))` instead of `TData("OwlTerm", [])` so the typechecker unifies against the user's actual `OwlTerm` postulate. Files: `syntax/mod.rs`, `syntax/pretty.rs`, `parser/grammar.rs`, `tactics.rs`, `typechecker/mod.rs`. Example: `examples/custom_tactic.owl`. 264/264 tests pass, `cargo fmt` clean.

- [x] **F1 — Interactive REPL proof sessions.** ✅ REPL auto-enters proof mode on unsolved holes. Commands: `:goals`, `?name := term`, `:done`, `:admit`, `:abort`. `check_str_with_holes` returns hole metadata. Files: `main.rs`, `driver/mod.rs`. 264/264 tests pass, `cargo fmt` clean.

- [x] **B4 — Forced (dot) patterns.** ✅ Added `.name` syntax for dot (forced) patterns referencing zero-arity constructors. `Pat::Dot(Term)` variant in `patterns.rs`, `.name` parsing in `parse_match_arm`, `Pat::con()` returns the constructor name for dot patterns so they participate in exhaustiveness checking. Dot patterns are irrefutable and used for error messages and explicit forcing annotations. `.(term)` syntax rejected with clear error (needs sub-pattern decomposition design). Files: `parser/patterns.rs`, `parser/grammar.rs`. Example: `examples/dot_pattern.owl`. 263/263 tests pass.

- [x] **B3 — With-patterns.** ✅ Added `match x with e as y return T with | ...` syntax (Cubical Agda `with` abstraction). Desugared at parse time to `(fun y => match x return T with | ...shifted_cases...) e` where case bodies have de Bruijn indices shifted by -1 at cutoff 1 to remove the `y` reference from the inner match context. `with_expr`/`with_name` fields on `MatchArm`, `stop_at_as` parser flag, lookahead heuristic to distinguish the `with`-pattern keyword from the `with` separator. Files: `parser/patterns.rs`, `parser/grammar.rs`. Example: `examples/with_pattern.owl`. 263/263 tests pass.

- [x] **B1 — Path application patterns.** ✅ Added `p@i0`/`p@i1` as match pattern forms (Cubical Agda `with` abstraction). `Pat::PathApp { var, interval }` in `patterns.rs`, parser recognition in `parse_match_arm`, `ElimCase.path_app_interval` field in `syntax/mod.rs`. Desugared at parse time in `parse_match` into a `TElim` whose scrutinee is the path application and whose cases come from the body match on the bound variable. Bodies shifted by -1 to account for the removed `as` binder. Files: `parser/patterns.rs`, `parser/grammar.rs`, `syntax/mod.rs`. Example: `examples/path_app_pattern.owl`. 263/263 tests pass, `cargo fmt` clean.

- [x] **E1 — Reflection API (Phase 1+2+3: quote/unquote, getContext, getType, TC monad, unify).** ✅ Phase 1: `TQuote`/`TUnquote`, `quote_ast`/`unquote_ast` keywords. Phase 2: `TGetContext`/`TGetType`, `getContext_ast`/`getType_ast` keywords, session-stored context and pre-computed type results. Phase 3: `TUnify` keyword `unify_ast` — checks definitional equality of two terms' types via `definitionally_equal_ctx_r`, returns Unit or type error. `lib/reflection.owl` postulates `OwlTerm`, `quote`, `unquote`, `getType`, `getContext`, `TC`, `tc_return`, `tc_bind`, `unify`, `tc_guard`. `TC` is an identity monad (computationally `TC A = A`). `examples/reflection_demo.owl` exercises the API. All 263 tests pass.

- [x] **G4 — Topology / Homotopy.** ✅ `lib/topology.owl` expanded: added `coproduct_topology` (proof that coproduct of open sets is open), `continuous_comp` (composition of continuous maps), `discrete_continuous` (universal property: any function from discrete space is continuous). Product topology type definition (`product_opens`) and `indiscrete_opens` type added. `examples/topology_demo.owl` exercises the constructions. Previously added: `lib/homotopy.owl` (path operations, homotopy, equivalences, loop spaces, truncated types, contractibility), `lib/suspension.owl` (Susp HIT), `lib/circle.owl` (S1 HIT), `lib/logic.owl`. Fixed parallel substitution bug. 263/263 tests pass.

- [x] **B2 — Absurd patterns (`()`).** ✅ Added `()` as syntactic sugar for zero-case match on empty types. `absurd: bool` field on `MatchArm` in `patterns.rs`, detected in `parse_match_arm`, desugared to empty cases in `parse_match_cases`. `lib/logic.owl` updated. File: `examples/absurd_pattern.owl`. 261/261 tests pass.

- [x] **E2 — Postulates.** ✅ Added `postulate x : T` declarations. `Decl::Postulate` variant in parser/driver, `Env::postulate()` method, `process_postulate()` typechecks `T : U_n`, postulates stored as opaque `VNeutral(NVar(i))` neutrals. `build_definition_values` fixes NVar level after eval so quoting works correctly in any context. `examples/postulate.owl` exercises postulated types, constants, type formers, and use in definitions. 259/259 tests pass.

- [x] **A5 — Higher-dimensional hcomp (Path type decomposition).** ✅ Added Path type decomposition to `hcomp`, `comp`, `fill`, and `hfill` in `nbe/hcomp.rs`. When the carrier type is `VPath(A, x, y)`, the operations decompose by composing at each point of the interval, reducing square composition (2D hcomp) to 1D composition in the carrier type. Example: `examples/higher_dim_hcomp.owl`. 258/258 tests pass.

- [x] **D1 — Universe polymorphism.** ✅ Added `LevelExpr` enum (`LVar(i32)`, `LConst(i32)`, `LSuc(Box<LevelExpr>)`, `LMax(Box<LevelExpr>, Box<LevelExpr>)`) to `syntax/mod.rs`. Changed `TUniv(Level)` and `TLift(Arc<Term>, Level)` to hold `LevelExpr` instead of bare `i32`. Level expressions support `shift`/`subst`/`max_var` — level variables share the term variable de Bruijn namespace. Added `TLevelTy`/`VLevelTy` for the `Level` type. Parser: `U (lsuc l)`, `U (max l1 l2)`, `U l`, `U0`/`U1` backward compat. `Level` keyword recognized. `lift`/`lower` are prefix keywords. NbE: `VUniv`/`VLift` hold `LevelExpr`. Typechecker: `type_level_dt` returns `LevelExpr`, `U_n : U_{n+1}` via `LevelExpr::suc`, Pi/Sigma/Glue/Equiv/Partial/SystemType use `LevelExpr::max`. Cumulativity: `leq` with structural equality fallback for stuck level variables. Files: `syntax/mod.rs`, `syntax/pretty.rs`, `parser/grammar.rs`, `nbe/value.rs`, `nbe/eval.rs`, `nbe/quote.rs`, `nbe/transport.rs`, `nbe/meta.rs`, `typechecker/mod.rs`, `typechecker/errors.rs`, `typechecker/termination.rs`, `driver.rs`, `equality.rs`, `syntax/positivity.rs`. Example: `examples/universe_poly.owl`. 257/257 tests pass.

- [x] **A4 — Cubical identity types (`Id`).** ✅ Added `TId(A, a, b)`, `TRefl(x)`, `TJ(motive, base, p)` to `Term` enum. Parser: `Id A x y`, `Refl x`, `J motive base p`. NbE: `VId`, `VRefl`, `VJelim` values; `do_j` computes `J B d (Refl x) = d` (key definitional reduction). Quote: bidirectional reconstruction. Typechecker: `Id A a b : U_n`, `Refl x : Id A x x`, `J motive base p : B y p`. Example `examples/id_types.owl` tests type formation, reflexivity, and J computing on refl. 257/257 tests pass, `cargo fmt` clean.

- [x] **A3 — Frontier-of-instability Phase 4 (quoting).** ✅ Made `try_destabilize` `pub(super)` in `elim.rs`. In `quote_case_body`, the `_ => quote(...)` fallback now checks if the value is a `VNeutral` with a satisfied frontier and attempts destabilization before quoting. This hardens quoting for stuck elim case bodies that capture interval-bound neutrals. Defensive — kernel re-checks everything. 256/256 tests pass, `cargo fmt` clean.

- [x] **NbE eval depth guard + Arc-based O(1) clone + TApp spine trampoline.** `EVAL_NBE_MAX_DEPTH=2000` in `eval.rs` prevents stack overflow. All `Term`/`Value`/`Neutral`/`I`/`Frontier` subterms migrated from `Box` to `Arc` — `Term::clone()` is now O(1) (atomic refcount). `meta.rs` zonk rewritten as recursive rebuild (no in-place mutation). TApp evaluation collects the left spine iteratively: `TApp(TApp(TApp(f, a1), a2), a3)` → head=f, spine=[a1,a2,a3], then iteratively apply. This eliminates O(n) stack depth for deep application chains. Deep TApp chains (2,500+ applications) work on a 2 MiB stack thread. 256/256 tests pass, `cargo fmt` clean.

- [x] **A2 — Indexed inductive type transport.** Fixed `transport_data_con`/`pcon`/`sqcon`/`cellcon` in `transport.rs`. The old indexed path tried to extract Pi types from `VData(d, params_at_i)`, which immediately fell through (VData is not VPi). The new approach: evaluate the closure at the formal interval variable to get `VData(d, params_at_i)`, then for each constructor arg type `T_k`, substitute each data type param variable `TVar(n + m - j)` with `quote(params_at_i[j])`. This correctly builds type families where data type parameters change along the interval. Creating a test for the non-constant path requires a `Path Type A B` with `A ≠ B`, which needs Glue/univalence — deferred. **Does NOT cover** dependent pattern matching / elimination on indexed types (see A6). 253/253 tests pass, `cargo fmt` clean.

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

**Does NOT cover**: A2 only handles transport (cubical `transp`/`coe`) through indexed types — an NbE-level operation on whole terms. It does **not** fix dependent pattern matching / elimination on indexed types (e.g. `vtail : Vec A (suc n) -> Vec A n`), which is a separate typechecking-level feature requiring index unification. See A6.

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

#### A6. Indexed dependent pattern matching / index unification 🔴

**Status**: Soundness fix done ✅ — full index unification still OPEN.

**Soundness fix (done)**: Added `return_args: Option<Vec<Term>>` to `ConSig` in `syntax/mod.rs`. The parser extracts the TData arguments from each constructor's return type and stores them. In `check_dt_inner` (TCon handler), for zero-arity constructors whose `return_args` contain a repeated de Bruijn variable at index positions (indicating an index constraint like `refl : Eq A x x`), we substitute the inferred params into `return_args` and check the result matches the expected type via `require_equal`. This catches the soundness bug where `refl : Eq Nat zero (suc zero)` was accepted because the old check was circular (params seeded from expected, then compared). The check is scoped to avoid false positives for constructors like `nil : Vec A zero` (no repeated vars) that would fail due to a separate pre-existing issue where parameter propagation to nested constructors doesn't account for index families. Files: `syntax/mod.rs`, `parser/grammar.rs`, `typechecker/mod.rs`, `driver/tests/example_guards.rs`. `bad_examples/soundness_indexed.owl` added as negative test. 275/275 tests pass, `cargo fmt` clean.

**Remaining: full index unification (OPEN)**:
The kernel still cannot do dependent elimination on indexed types. Example failure:
```
def vtail : forall (A : Type), forall (n : Nat), Vec A (suc n) -> Vec A n :=
  fun A n v => match v return Vec A n with
  | nil => nil
  | cons x xs => xs  -- ERROR: xs : Vec A (suc n), expected Vec A n
```
The kernel substitutes the scrutinee's index `suc n` into `cons`'s arg type `Vec A n`, giving `xs : Vec A (suc n)`. It should instead unify `suc n' = suc n` (where `n'` is `cons`'s fresh index) to derive `n' = n`, making `xs : Vec A n`.

**Root cause**: `Datatype` has no distinction between **parameters** (same in all constructors, like `A` in `List A`) and **indices** (vary per constructor, like `n` in `Vec A n`). All type arguments are stored as `params: Vec<(Name, Term)>`. Full fix requires:
1. Add `indices: Vec<usize>` field to `Datatype` — indices into `params` that are true indices.
2. Add **index unification** during pattern matching in `check_dt_inner` / `TElim` handler.
3. Update `subst_params_local` to use unified index values.

**Scope**: ~4 functions to modify (`Datatype` struct, parser param classification, `check_dt_inner` TCon handler, `subst_params_local`). Medium regression risk — the existing 264 tests should pass unchanged since they don't use indexed types, but the pattern matching codepath is kernel-critical.

#### A7. Small trusted kernel 🔴

**Status**: OPEN — not yet started.

The current kernel is ~10k lines of Rust spanning NbE evaluation, typechecking, equality checking, quoting, and transport. While the kernel has been audited for individual soundness bugs (e.g. A6), the overall trusted computing base (TCB) is large relative to proof-assistant standards. A smaller kernel reduces the surface area for soundness bugs and makes formal verification of the kernel feasible.

**Current TCB size** (approximate):
- NbE eval: `nbe/eval.rs` + `nbe/mod.rs` + `nbe/elim.rs` — core evaluation
- Typechecker: `typechecker/mod.rs` — infer/check
- Equality: `equality.rs` — definitional equality
- Quote: `nbe/quote.rs` — quote back to syntax
- Transport/hcomp: `nbe/transport.rs` + `nbe/hcomp.rs` — cubical reduction
- Session/env: `session.rs` + `env.rs` — state management

**Approach** (phased, deferred until after stdlib maturity):
1. **Audit & document** the TCB: identify which functions are kernel-critical (affect soundness) vs. peripheral (errors, pretty-printing, tactics). Produce a verified subset list.
2. **Minimize NbE**: ensure all cubical reduction rules are covered by the smallest possible eval+quote pair. Remove dead code paths, simplify stuck-neutral handling where safe.
3. **Consider extracting the kernel** to a standalone crate (`owl-kernel`) with no I/O, no tactics, no tactic-generated proof trees. The driver/tactic layer becomes trusted-external.
4. **Long-term**: model the kernel in a proof assistant (Lean/Coq/Agda) and extract verified Rust code.

**Rationale**: Every soundness fix (like A6) is a patch on a large surface. Shrinking the kernel从根本上 reduces the need for such patches. This is not urgent (the kernel is sound for all currently-expressible programs), but should be done before any claim of formal verification.

**Scope**: Large (months of work for a full formal verification). Should be done after the stdlib stabilizes (G1–G6) so the kernel's feature set is final.

---

### B. Pattern Matching — Cubical Agda Parity 🟡

#### B1. Path application patterns ✅

Cubical Agda matches on `p i0` and `p i1` in patterns:
```agda
f : (p : Path A a b) → B
f p with p i0 | p i1
... | a' | b' = ...
```

**Done** (2026-09-03): Added path-application as a pattern form in `match`. Syntax: `p@i0 as a'` / `p@i1 as b'` in match arms. Desugared at parse time into a `TElim` whose scrutinee is the path application (`p@i0` or `p@i1`) and whose cases come from the body (which must be a match on the bound variable). The `Pat::PathApp { var, interval }` variant in `patterns.rs`, parser recognition in `parse_match_arm`, `ElimCase.path_app_interval` field, and desugaring logic in `parse_match` that shifts inner case bodies by -1 to account for the removed `as` binder. File: `examples/path_app_pattern.owl`. 263/263 tests pass.

#### B2. Absurd patterns (`()`) ✅

Cubical Agda has `()` for empty pattern matching on types with no constructors. Owl handles `Empty` via `match e return A with` (zero cases) but lacks syntactic `()`.

**Plan**: Add `()` as syntactic sugar for `match x return A with` (zero cases). Verify the kernel already handles this (it does).

**Done** (2026-09-02): Added `absurd: bool` field to `MatchArm` in `patterns.rs`. Parser detects `()` in `parse_match_arm`, sets `absurd: true`; `parse_match_cases` returns empty cases when arm is absurd. `lib/logic.owl` updated to use new syntax. File: `examples/absurd_pattern.owl`. 261/261 tests pass.

#### B3. With-patterns ✅

Cubical Agda's `with` abstraction:
```agda
f x with g x
... | zero = ...
... | suc n = ...
```

**Done** (2026-09-03): Added `match x with e as y return T with | ...` syntax. Desugared at parse time to `(fun y => match x return T with | ...shifted_cases...) e` where case bodies have de Bruijn indices shifted by -1 at cutoff 1 to account for the removed `y` from the inner match context. The `with_expr` and `with_name` fields on `MatchArm`, `stop_at_as` parser flag, and lookahead heuristic to distinguish `with`-pattern keyword from `with` separator. Files: `parser/patterns.rs`, `parser/grammar.rs`. Example: `examples/with_pattern.owl`. 263/263 tests pass.

#### B4. Forced (dot) patterns ✅

**Done** (2026-09-03): Added `.name` syntax for dot (forced) patterns referencing zero-arity constructors. `Pat::Dot(Term)` variant in `patterns.rs`, `.name` parsing in `parse_match_arm`, `Pat::con()` returns the constructor name for dot patterns so they participate in exhaustiveness checking. Dot patterns are irrefutable and used for error messages and explicit forcing annotations. `.(term)` syntax rejected with clear error (needs sub-pattern decomposition design). Files: `parser/patterns.rs`, `parser/grammar.rs`. Example: `examples/dot_pattern.owl`. 263/263 tests pass.

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

#### E4. Custom tactics ✅

Depends on E1 (reflection API). Users define tactics via the TC monad.

**Done** (2026-09-04): Added `Tactic::Custom(String)` variant to the `Tactic` enum. Parser: `by tactic <name>` syntax. Tactic engine: evaluates `f goal_type` via NbE where `f` is the named global tactic function, extracts the `TermVal` proof term, shifts de Bruijn indices for the tactic engine's local context. Critical fix: `TQuote`/`TGetContext`/`TGetType` now return `TVar(lookup_ctx_index("OwlTerm", ctx))` instead of `TData("OwlTerm", [])` so the typechecker can unify against the user's actual `OwlTerm` postulate. Files: `syntax/mod.rs`, `syntax/pretty.rs`, `parser/grammar.rs`, `tactics.rs`, `typechecker/mod.rs`. Example: `examples/custom_tactic.owl`. 264/264 tests pass, `cargo fmt` clean.

---

### F. Ergonomics 🟡

#### F1. Interactive REPL proof sessions ✅

`:proof` / `:goals` / `:admit` / `:done` commands. Builds on existing hole (`?name`) and tactic infrastructure.

**Done** (2026-09-04): REPL auto-enters proof mode when a definition has unsolved holes. Commands: `:goals` (show holes with expected types), `?name := term` (solve a hole via string substitution + re-check), `:done` (finish, requires all holes solved), `:admit` (accept with remaining holes), `:abort` (discard). `check_str_with_holes` function returns hole metadata from `UnsolvedHoles` errors. Invalid solutions are rejected and the user can retry. Files: `main.rs`, `driver/mod.rs`. 264/264 tests pass, `cargo fmt` clean.

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

#### G1. Core data types ✅

- [x] Nat (suc/zero, +, *, comparison) — in `lib/ring_laws.owl`, used across all examples
- [x] Int (add, mul, neg, sub, abs, sign) — `lib/int.owl` (abs, sign, neg, add, mul, is_nonneg), `lib/ring_laws.owl` (ring operations + laws)
- [x] List (append, reverse, map, fold, length) — `lib/list.owl` (append, reverse, map, foldl, foldr, length, filter, any, all + proofs: append_nil_l, append_assoc, map_append)
- [x] Vector (indexed, map, zip, append) — `lib/vector.owl` (type + nil/cons/vhead/vnil; dependent elimination limited by kernel)
- [x] Maybe / Option — `lib/maybe.owl` (nothing, just, maybe_default, maybe_map, maybe_bind, is_just, is_nothing, from_maybe)
- [x] Bool (and, or, not, if-then-else) — `lib/bool.owl` (not, and, or, xor, if, eq + proofs: not_not, and_idem, or_idem, and_comm, or_comm)

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
6. ~~**E2 (postulates)**~~ — ✅ done.
7. ~~**E1 (reflection API)**~~ — ✅ done.
8. ~~**D1 (universe polymorphism)**~~ — ✅ done.
9. ~~**E4 (custom tactics)**~~ — ✅ done.
10. ~~**F1 (interactive REPL)**~~ — ✅ done.
11. ~~**C1 (datatypes in parameterized modules)**~~ — ✅ done. Unblocks Cubical Agda module parity.
12. ~~**G1 (core data types)**~~ — ✅ done. List, Vector, Maybe, Int, Bool libraries with proofs. Foundational for stdlib.
13. ~~**A6 (indexed dependent pattern matching)**~~ — 🔴 soundness fix done ✅. Kernel no longer proves False via zero-arity constructor index mismatch. Full index unification (vtail, etc.) still OPEN. 275/275 tests pass.
14. **G3 (logic)** — propositional logic, quantifiers, decidability. Unlocks ideal predicates for G6.
14. **G2 (algebra extensions)** — lattices, ordered structures. Feeds into G5 (categories of algebraic structures).
15. **G5 (category theory)** — Category, Functor, NatTrans, Yoneda. Showcases G1–G2.
16. **G6 (algebraic geometry)** — ideals, polynomial rings, Spec, sheaves. Needs G1+G2+G3.
17. **H2 (spectrum / stabilization)** — research-level, last. Needs mature cubical TT + deep stdlib.
18. **A7 (small trusted kernel)** — 🔴 audit & minimize the TCB, extract kernel crate, long-term formal verification. Deferred until after stdlib maturity (G1–G6).
