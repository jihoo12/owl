# TODO.md — Remaining improvements for owl

> The checklist below is the live status tracker (`[x]` = done, `[ ]` = open).

## Completed (implementation log)

- [x] Multiplicative algebra over `Nat` — `examples/stress_mul_algebra.owl` now proves the classic hard theorems (`_owl_mul_zero_r`, `_owl_mul_suc_r`, `_owl_mul_one_r`, `_owl_mul_comm`, `_owl_mul_add_r` right-distributivity, `_owl_mul_assoc`, `_owl_mul_double`, and the consumer lemma `_owl_double_double`), composing the additive laws with `by omega` for the definitional / direct-lemma-instance subgoals. One contained kernel fix in `src/cubical/equality.rs` (the eliminator-congruence arm of `eta_eq`): a stuck elim suspends its case bodies, so a reducible global application (e.g. `mul b c`) substituted into a case body is never reduced by whole-term normalization — leaving `(mul b) c` in the normal form while the same value entered as an eagerly-evaluated function argument appears folded. Each elim case body is now normalized **once** in isolation and compared structurally, falling back to the original raw comparison when the single pass does not converge (re-normalizing recursively would unfold recursive definitions one level per pass and never reach a fixed point — the transient stack overflow this fix replaced). Covered by `stress_mul_algebra_example_checks` in the driver (runs on a 64 MiB stack since the deep elim/hcomp normal forms exceed the default 2 MiB test-thread stack); all 175 tests stay green.

- [x] hcomp-based transitivity on the pristine kernel — The full Nat lemma suite typechecks and computes with **zero kernel changes** (`src/cubical/typechecker/mod.rs` left byte-for-byte original). The suite: `_owl_cong_suc`, `_owl_sym`, hcomp-based `_owl_trans` (`fun a b c p q => <i> hcomp Nat [~i => <j> a, i => q] (p @ i)`), `_owl_add_0_r`, `_owl_add_suc_r`, `_owl_cong_add_r`, `_owl_add_comm`, `_owl_cong_add_l`, `_owl_add_assoc`. The real blockers were **surface-syntax** constraints, not the kernel: (1) integer literals `0`/`1` parse as the interval endpoints `i0`/`i1`, so Nat terms must use the `zero`/`suc` constructors (see `src/cubical/parser/grammar.rs`, `TokenKind::Int`); (2) `forall` is only recognized at term top-level, so it cannot follow a `->` — all binders must be declared before the arrow chain (`forall (a : Nat), forall (b : Nat), Path Nat a b -> ...`). An earlier experiment that normalized hcomp faces inside `check_faces` was **reverted**: the kernel already handles interval-variable hcomp faces soundly via `check_dt`'s infer → `nbe_eval`-normalize → retry path (the raw-face `check_faces` fallback error is swallowed, then cube-normalized faces pass the sound checks). Verified with `owl check` and `owl run` (`add_comm 2 3 @ i1 = 5`, `add_assoc 3 2 3 @ i1 = 8`, trans of refl paths `@ i1 = 1`); all 169 tests stay green.

- [x] Idempotent normalization with global definitions — `nbe_eval_ctx` now builds the evaluation environment from **local binders only**; global references resolve through the global definition value vector (`global_offset + (i - env.len())`) instead of being placed in the environment. Keeping globals out of the env is load-bearing: a stuck eliminator created during evaluation captures the env, and `quote_case_body` re-anchors a raw case-body global ref as a *reference below the quoting frame* precisely when the ref lands beyond `env.len()`. If globals were in the env, those refs would land inside `env.len()` and get inlined by re-evaluation, re-opening recursive definitions (e.g. `add`'s case body calling `add`) on every normalization pass — unbounded term growth that exhausted eta-equality fuel (`EtaFuelExhausted`). With the locals-only env, normalization is idempotent: quoting a term twice yields the same normal form. Verified on a `Path Nat ((add_0_r n) 0) n` recursive proof that previously failed at fuel exhaustion; all 36 `examples/*.owl` and 169 tests stay green.

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

- [x] **Omega / Linear arithmetic** — decision procedure for linear arithmetic over Nat/Int. *(🔴 — most general-purpose payoff; underlies many other proofs.)* Implemented in `src/cubical/omega.rs`: `by omega` proves `Path Nat u v` goals by (1) definitional reflexivity (normalization unfolds `add`/etc. on constructor-headed arguments) and (2) direct application of a previously verified global lemma to the context's variables, both re-checked by the kernel. Worked example in `examples/omega_demo.owl`. *Remaining: on-demand induction synthesis (structural recursion via the current definition) and `Int` support.*
- [x] **Ring solver** — decision procedure for ring identities (normalize + compare polynomial forms). *(🔴 — classic high-value tactic, e.g. Coq/Agda's `ring`.)* Implemented in `src/cubical/ring.rs`: `by ring` proves `Path Nat u v` goals by normalizing both sides to polynomial normal form over the commutative semiring over `Nat` (`add`/`mul`/`zero`/`one`, recognized by the shape of the normal forms their eliminators unfold to) and, when the normal forms agree, building a proof tree by applying ring laws resolved from the context. `lib/ring_laws.owl` supplies the required law names (`add_comm`, `add_assoc`, `add_0_l/r`, `mul_comm`, `mul_assoc`, `mul_1_l/r`, `mul_0_l/r`, `mul_add_l/r`) and the structural lemmas (`trans`, `sym`, `cong_add_l/r`, `cong_mul_l/r`); `examples/ring_demo.owl` exercises it. The generated proof is a raw law-application tree that the kernel re-checks; the structural-recursion guard is skipped for ring output because law bodies unfold to elims on compound neutral scrutinees in the normal form. The final blocker was an ill-typed `trans` in `expand_single` — its proof chain already landed on `sum_term(products)`, but a trailing `sum_concat` step re-wrapped the LHS with an extra `add _ zero`, so the emitted `trans` mismatched the chain's actual endpoint and the kernel re-check normalize-and-retry loop overflowed the stack; dropping the redundant step fixed all three demos. *Remaining: `Int`/additive-group support (neg/sub).* Abstract-ring support (`by ring with C`) landed as part of the H1 work — see §H.1.
- [ ] **Group solver** — decision procedure for group identities (associativity, identity, inverses). *(🟡 — narrower scope than ring, useful once ring solver exists.)*
- [ ] **Field solver** — decision procedure for field identities (ring + division/inverse reasoning). *(🟡 — natural follow-on to ring solver; depends on it.)*
- [ ] **Decision procedure for propositional equality** — automate reflexivity/symmetry/transitivity chains. *(🟡)*

### C. Pattern Matching 🟡

- [ ] **Nested constructor patterns** — e.g. `suc (suc zero)` matching a literal 2 (requires a full pattern AST rather than the current flat-binder matching). *(🟡 — meaningful ergonomics win, moderate implementation cost.)*

  **Plan (agreed 2026-08-10, user-approved):**

  *Phase 1 — parser-side compilation (ordinary constructors, kernel untouched).*
  1. Pattern AST in `src/cubical/parser/patterns.rs` (optional module): `Pat::Var(Name)` / `Pat::Con { con, args: Vec<Pat> }`; parse each arm's leading column into `Vec<(Vec<Pat>, Option<Name> /* as_name */, Term /* body */)>` in `parse_match_cases` (`grammar.rs:1274`), resolving constructor heads by name via `find_constructor` (`grammar.rs:1508`).
  2. Compile step: group arms by constructor head → same-head groups merge (vars nest into a nested eliminator); for each constructor `con` with arity `a`, bind all args as fresh vars in one `ElimCase` (`binders = [v0..v_{a-1}]`) and where a nested constructor pattern occupies argument position `k`, replace that var's use inside the case body by a nested `TElim`:
     `nested(k) = TElim(TAbs(v, TApp(shift(k,0,motive), TCon(con))) , cases, TVar(k + extra))`
     — each nested elim adds exactly one binder above its body; bodies shifted by compile-tree depth; refined-column scrutinee `TVar((a-1-k)+extra+n_refined_before)`; De Bruijn-consistent. Flat (all-var) cases emit byte-identical `ElimCase`s to today (source order preserved) so `parses_match` etc. are unchanged.
  3. Parser completeness check: infer scrutinee datatype from constructor heads via `constructor_arity`; require full constructor coverage (all cons + pcons + sqcons + cellcons at top level; ordinary cons for nested columns); dedicated `ParseError` when incomplete; skip check if heads resolve inconsistently (typechecker `MissingCase` remains the soundness backstop).
  4. Mixed var+con columns inside the same head group → parse error; inconsistent as-names across merged groups → parse error.
  5. Tests: parser unit tests (nested / deep-nested / multi-arg `cons x (cons y zs)` / as+nested / or+nested / merged heads / flat-identical); `examples/stress_nested_patterns.owl` + driver test `nested_patterns_example_checks` (64 MiB stack); `bad_examples/incomplete_nested_match.owl` + `bad_examples/mixed_pattern_columns.owl` + driver assertions.

  *Phase 2 — HIT-case refinement (kernel change, user-chosen).*
  1. Small `ElimCase` marker field (e.g. `refinements: Option<Vec<Option<Vec<Name>>>>`): for path/square/cell constructor cases, layout `binders = [whole-args] + [leaf-vars] + [interval-vars(dim)]` with PLam body whose PLam body is the nested `TElim` chain; NBE `do_elim` unchanged (drives off constructor-arg values, not `binders`); `shift_cases`/`quote_cases`/nbe arms plumb the field.
  2. Typechecker: `pcon`/`sqcon`/`cellcon` arms (`typechecker/mod.rs:2043/2160/2292`) build nested motives from `motive` + constructor + substituted faces; boundary coherence via `require_equal_endpt`; verify `reduce_pcon_endpoints_dt` reduces pcon applications inside nested `TElim`s (extend if not). Start with single-interval `pcon`; then `sqcon`/`cellcon`. `eval_elim_face` beta-chain application is why this must be a kernel change (a refined body is a nested `TElim`, not a beta-chain).
  3. Docs (`docs/reference.md`) + examples; full `cargo test`; `uvx rust-analyzer-db scan src`; check off C.1.

  *Backward compat note:* no existing owl example/library pattern binder collides with a constructor name (audited), so constructor-named identifiers in pattern position becoming constructor patterns is safe; behavior change to document.

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

### H. Algebraic Geometry 🔴

> Goal: make Owl handle algebraic geometry well. AG is ~95% **set-level commutative
> algebra + 1-categorical diagram chasing**; almost nothing uses the higher-categorical
> part of cubical type theory. "AG well" = (1) automatic ring/field computation,
> (2) ergonomic set truncation/quotients, (3) a commutative-algebra + scheme layer.
> Direction: **classical schemes first, homotopical/derived AG as the long tail** that
> the cubical core uniquely enables. Items B.3/B.4 (group solver, field solver) and the
> Int side of B.1 (omega) are folded in here.

- [x] **H1. Generic `by ring`** *(🔴 — the single highest-leverage feature; Coq/Lean AG is built on a ring tactic over arbitrary rings.)* Landed as a **Structured mode** in `Ring` (`Mode::Structured`), with the syntax **`by ring with C`** where `C : CommRing A add mul zero one` bundles the operations as parameters and the law/structural lemmas as fields:
  - In Structured mode, ops are recognized by **head-symbol equality** with the resolved `add`/`mul`/`zero`/`one` terms (via `nbe_eval_ctx` at the resolve-time context length) instead of Nat-eliminator normal-form shape; the Concrete mode keeps the original Nat path.
  - Numerals are built as iterated `one + …` over the abstract `one`; `numeral_add_eq`/`numeral_mul_eq`/`numeral_one_left_mul_eq` prove numeral arithmetic propositionally from the record's laws (Concrete mode still computes it definitionally over Nat).
  - The proof tree is assembled from `C`'s law projections and the kernel re-checks it (structural guard skipped) — the soundness backstop that caught two real solver bugs during development: an inverted `sym`-wrapped `mul_1_l` in `numeral_mul_eq`, and a systematic swap of the two distributive laws (`mul_add_l` distributes over `mul a (add b c)`, `mul_add_r` over `mul (add a b) c`) that the Nat path masked by definitional computation.
  - The `by` block must sit at the **top level** of the `def` — `resolve_tactics` only replaces a root `TBy` (a nested `fun … => by ring with C` panics at NbE).
  - `examples/comm_ring_demo.owl` proves `add_comm`, `mul_comm`, distributivity, associativity, `mul (add one one) x = add x x`, and `add (mul one x) zero = mul x one` over an abstract `CommRing`; guarded by `comm_ring_demo_example_checks` in the driver (64 MiB stack).
  - *Remaining: `neg`/`sub` (additive group) support is folded into H3; implicit instance search is H4 (the explicit `with C` form works without it).*
- [x] **H2. `by field`** *(🔴 — field identities with inverse reasoning; needed for residue/function fields. Builds on H1.)* Landed as **`by field with F`** for `F : Field A add mul inv zero one`, with `a ≠ 0` encoded as `Path A zero a -> Empty`:
  - *Part 0 — kernel `Empty` type*: constructor-less inductive types now parse (grammar.rs no longer errors on all-empty cons, and `parse_match_cases` accepts zero cases), so `lib/field_laws.owl` defines `def absurd : forall (A : Type), Empty -> A := fun A e => match e return A with`. Every other kernel path already handled zero cases.
  - *Part 1 — `lib/field_laws.owl`*: `Empty`, `absurd`, and a `Field` record whose law fields carry the exact names `Ring::resolve` projects (`trans, sym, cong_add_l/r, cong_mul_l/r, add_comm, add_assoc, add_0_l/r, mul_comm, mul_assoc, mul_1_l/r, mul_0_l/r, mul_add_l/r`) plus `inv_mul` (`nz a -> Path A (mul a (inv a)) one`), `inv_one`, `inv_mul_dist`, `inv_div`, `cong_inv`, `nz_one`, `nz_mul`. Ops are record parameters named `add`/`mul`/`inv`/`zero`/`one`.
  - *Part 2 — `src/cubical/field.rs`*: reifies each side of the goal to a fraction `(N, D)` with a proof `t = mul (canon N) (inv (canon D))` (denominator always a single raw monomial). Add/mul/inv cases reuse ring.rs's `decomp`/`expand`/`poly_merge`/`sum_canon`/`regroup`/`numeral_*` machinery (exposed `pub(crate)`, incl. `prod_term`). The inverse case (`reify_inv`) swaps numerator/denominator via `inv_div` and requires the numerator to be a single coefficient-1 monomial. The **final step** (`frac_eq`) proves `mul n0 (inv d0) = mul n1 (inv d1)` from the ring-proved cross-multiplication `mul n0 d1 = mul n1 d0` in 12 steps (`mul_1_r`, `inv_mul` insert, `mul_assoc` regroups, `mul_comm`, `inv_mul_dist`). **Nonzero discharge is structural** — normalize, reject `zero`, base case `one` via `nz_one`, strip canonical wrappers, decompose products with `nz_mul`, and match a context hypothesis whose type normalizes to `(Path A zero x -> Empty)`. The constructed proof is re-checked by the kernel (structural guard skipped, exactly like ring). *Scope: no `neg`/`sub`; `inv` of sums/numeral multiples is an explicit error; hypotheses must be per-atom (e.g. `hb : b ≠ 0`, `hd : d ≠ 0`).*
  - **Two subtle bugs the kernel backstop caught** (both about *stuck* local-variable terms): (1) **stale hypothesis indices** — tactic-introduced hypotheses are stored in the pre-push index frame, so `nz_hypothesis` must re-anchor each stored type with `shift(p + 1, 0, ty)` before normalizing (un-shifted, the codomain `Path zero b` normalizes to the wrong variable and never matches); (2) **denominators must be raw** — `discharge` and the law arguments structurally decompose a term, so denominators must be built with `prod_term` (not `canon_term`); where canonical and raw forms meet (`scale_frac`, `reify_inv`), explicit `ring_eq` bridges are inserted. Also fixed a systematic `cong_mul_l`/`cong_mul_r` confusion in `frac_eq`/`scale_frac` (left-append vs right-append) that left adjacent chain steps unconnected.
  - *Part 3 — plumbing*: `Tactic::Field(Option<Term>)` in `syntax/mod.rs` (+`shift_tactic`/`subst_tactic`), `show_tactic` in `pretty.rs`, `parse_tactic` (`field [with <term>]`), `"field"` in `is_tactic_keyword`, `Tactic::Field` arm in `tactics.rs` mirroring the `Ring` arm, `pub mod field;` in `mod.rs`. (The `by` block must sit at the root of the `def`, like `by ring`.)
  - *Part 4 — demo/tests*: `examples/field_demo.owl` proves `(a/b)·(c/d) = (ac)/(bd)`, `(a/b)+(c/d) = (ad+bc)/(bd)`, `(a/b)/(c/d) = (ad)/(bc)`, `inv (inv a) = a`, `inv (a·b) = inv a · inv b`, `a·inv a = one` (each with per-atom `≠ 0` hypotheses); `field_demo_example_checks` + `field_laws_lib_checks` in the driver on 64 MiB stacks. The demo re-check is slow in debug builds (~1 min for the biggest theorem per kernel pass, ~5 min total for the demo).
  - *Remaining: `neg`/`sub` (additive group) support is folded into H3.*
- [ ] **H3. Int `by omega` + group solver** *(🟡 — omega-Int for valuation/residue computations; group solver is the base of the field ladder.)*
- [ ] **H4. Bundled algebra records + lightweight instance search** *(🔴 — without typeclasses, every theorem must thread `CommRing R` explicitly. Minimal implicit-argument + instance-search layer, Lean/Coq-style, on top of the existing record system.)*
- [ ] **H5. Commutative algebra library** *(🔴)*: `CommRing`/`Field`/`Module`/`Ideal` structures; quotient rings `R/I` and localization `S⁻¹R` via the existing HIT quotients; polynomial rings `R[X]`; prime/maximal ideals; finite fields `F_p`.
- [ ] **H6. Set-level foundation polish** *(🟡)*: quotient elimination ergonomics, proof irrelevance for Prop, `isSet` stability — AG objects are all sets.
- [ ] **H7. Category + sheaf core** *(🔴)*: categories, functors, natural transformations, Yoneda; presheaves and sheaves; the Zariski site.
- [ ] **H8. Schemes** *(🔴)*: **functor-of-points route** — `Spec R := Hom(R, −)` on `CommRing^op`; a scheme is a Zariski sheaf locally represented by affines (the UniMath approach). Avoids building the structure sheaf on a point-set, which is far costlier in type theory. Targets: `Spec R`, Zariski opens `D(f)`, affine cover, products/pullbacks, projective space `P^n`, closed/open immersions.
- [ ] **H9. Long tail — derived schemes / higher stacks** *(🟢 — where cubical/HoTT genuinely shines over vanilla ITT: simplicial rings, homotopy limits/colimits, higher truncation. Research-level.)*
- [ ] **H10. Ergonomics blockers at library scale** *(🟡)*: `forall` cannot follow `->` (`docs/reference.md:213` — all binders must precede the arrow chain) and the basic module/import system (§D) become painful for a growing AG library.

---

## Suggested Order of Attack

1. 🔴 **Cumulativity for Σ/Π and records** — closes soundness gaps in an already-partial feature; cheap relative to payoff.
2. 🔴 **Omega (linear arithmetic)** — `by omega` landed (see §B.1); **Ring solver** landed (see §B.2, `by ring` over `Nat`) with the generic abstract-ring form `by ring with C` landed under H1 — Group/Field solvers are the remaining automation ladder.
3. 🟡 **Module system basics** (`module M where`) + **qualified imports** — needed before the standard library work in §G can scale.
4. 🟡 **Nested constructor patterns** — moderate-cost ergonomics fix, independent of everything else.
5. 🟡 **Interactive REPL proof sessions** — biggest remaining UX win, builds on existing hole/tactic machinery.
6. 🟢 Remaining items (Group/Field solver, reflection API, custom tactics, incremental normalization, stdlib, docs) — valuable but can proceed in parallel/opportunistically once the above land.
7. 🔴 **Algebraic geometry** — follow §H in order: H1 (generic `by ring`) has landed (see §H.1 / §B.2); proceed with H4 (instance search) → H2 (`by field`) → H5 (comm algebra) → H7 (categories/sheaves) → H8 (schemes). H6/H10 unlock as library size grows.
