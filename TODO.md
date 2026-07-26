# TODO.md — Remaining improvements for owl

## Done

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

- [x] Stress test and documentation — `examples/stress_mutual_and_ir.owl` exercises all 5 new features. `docs/reference.md` updated with Prop/SSet, lift/lower, mutual inductives, induction-recursion, termination guard, and worked examples.

---

## Remaining — Cubical Type Theory Completeness

### 1. Core Cubical Features

- [x] **Face implication** — `a ⇒ b` (implication between DNF face conditions). Added `dnf_leq` in `interval.rs` for checking whether one face condition implies another.

- [x] **Cofibration subtyping** — `[_ | phi] A <= [_ | psi] A` when `phi <= psi`. Uses `dnf_leq` for face implication checking. Implemented in `cumulativity_check`.

- [x] **Glue type β-reduction** — `VGlueElem(phi, t, a) @ 0 = a`, `VGlueElem(phi, t, a) @ 1 = t`. Path application on glue elements reduces at interval endpoints.

- [x] **Comp/fill computation for data types** — Transport through data types: `transport_data_con`, `transport_data_pcon`, `transport_data_sqcon` in `nbe/mod.rs`. Each constructor argument is transported through its substituted type via telescope-aware substitution.

- [x] **System types as first-class types** — `[phi => a, psi => b]` as a type (not just in comp/hfill). Added `TSystemType(System)` term variant, `VSystemType(DNFSystem)` value, full eval/quote/parser/pretty-printing. Coherence checking via `dnf_meet` on overlapping faces. Parser: `[phi => A, psi => B]` syntax.

- [x] **Regularity** — `comp A [ ] base` (empty system) reduces to `base`. Empty systems in `hcomp`, `comp`, `fill`, and `hfill` all reduce: `fill` and `hfill` produce constant paths. Empty systems arise when all faces evaluate to ⊥ (e.g. `[0 => ...]`).

### 2. Type Theory Features

- **Universe polymorphism** — Already has stratified U0, U1, U2...

- [x] **Universe lifting/lowering** — `TLower`/`TLift` for moving terms between universe levels.

- [x] **Impredicative Prop** — `TProp` at U0, closed under Pi/Sigma/Path when both sides are Prop.

- [x] **SSet (strict sets)** — `TSSet` at U1, predicative.

- **Cumulativity** — `A : U_n` and `U_n : U_m` when `n <= m`. Currently basic, could be extended with:
  - Cumulativity for Sigma/Pi types
  - Cumulativity for record types

- [x] **Cumulativity for inductive types** — `TData(d, ps) <= TData(d, ps')` with covariant parameter checking.

- [x] **Induction-induction** — Mutual inductive types via `with inductive` syntax. Forward references, multi-way mutual blocks.

- [x] **Induction-recursion** — Simultaneous datatype + function definition via `with f : T := e` syntax.

- [x] **Termination / Guard checking** — Structural recursion guard via `termination.rs`. Recursive calls must pass a case binder as scrutinee.

- [x] **Well-founded recursion** — `by_wf` annotation on `def` disables structural guard check.

- [x] **Coinduction** — `Delay A` type with `Next` constructor and `Force` destructor.

### 3. HIT Improvements

- **Higher-dimensional HIT cells** — Currently support path (1D) and square (2D) constructors. Add:
  - Cube constructors (3D cells)
  - n-dimensional cell constructors
  - General boundary specification syntax

- **HIT computation rules** — Transport/fill through HITs should compute:
  - Transport along path constructors
  - Transport along square constructors
  - Fill operations for HIT constructors

- **HIT elimination improvements** — Better support for:
  - Nested pattern matching on HITs
  - Dependent elimination with complex motives
  - Higher-dimensional pattern matching

### 4. Proof Assistant Features

- **Interactive mode / Hole-driven development** — `?hole` syntax for incomplete proofs. Tactic mode fills holes.

- **Better error messages** — More detailed type mismatch errors:
  - Show normalized expected/got types (done for TypeMismatch)
  - ~~Point to exact location of mismatch~~ (partial: shows term + type in debug scope)
  - Suggest possible fixes (done for CannotInfer tip)

- **Decision procedures** — Automated proving for:
  - Propositional equality (reflexivity, symmetry, transitivity)
  - Arithmetic (for Nat/Int types)
  - Ring/field solver

- **Omega / Linear arithmetic** — Decision procedure for linear arithmetic over Nat/Int.

- **Ring solver** — Decision procedure for ring identities.

- **Import system improvements** —
  - Qualified imports (`import M as mod`)
  - Selective imports (`import M only [x, y]`)
  - Unification of same-name imports

- **Module system** — Namespaces for organizing definitions:
  - `module M where ...`
  - Module parameters
  - Module instantiation

- **Record types** — Named sigma types with projections:
  - `record R where field x : A; field y : B`
  - Automatic projection functions
  - Record update syntax

- **Pattern matching improvements** —
  - Nested patterns
  - Or-patterns
  - As-patterns
  - Record patterns

### 5. Cubical-Specific Improvements

- **Face lattice operations** — Better support for:
  - Face conjunction/disjunction
  - Face implication
  - Face negation
  - Face equivalence checking

- **Comp/hfill system types** — Full support for:
  - Multi-face systems in all Kan operations
  - System compatibility checking
  - System reduction rules

- **Transport computation** — Transport should reduce:
  - Along constant paths (already done)
  - Along ua (already done)
  - Through Pi types (partially done)
  - Through Sigma types (partially done)
  - Through Path types (partially done)
  - Through inductive types (not done)
  - Through record types (not done)

### 6. Performance and Metaprogramming

- **Normalization improvements** —
  - Sharing in NbE
  - Incremental normalization
  - Memoization

- **Type checking improvements** —
  - Constraint-based type inference
  - Bidirectional type checking
  - Pattern unification

- **Metaprogramming** —
  - Reflection API
  - Tactic language
  - Custom tactics
  - Proof automation

### 7. Library and Ecosystem

- **Standard library** — Cubical equivalents of:
  - Data types (Nat, Int, List, Vector, etc.)
  - Algebra (groups, rings, fields, modules)
  - Order theory (posets, lattices)
  - Topology (continuous maps, homotopy)
  - Category theory (functors, natural transformations)

- **Documentation** —
  - Tutorial / Getting started guide
  - API reference
  - Example gallery
  - Comparison with other cubical systems (Agda cubical, cubicaltt)
