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

---

## Remaining — Cubical Type Theory Completeness

### 1. Core Cubical Features

- **System types** — `[phi => a, psi => b]` as a type (not just in comp/hfill). System types represent partial functions and are fundamental to cubical type theory.

- **Glue type reduction rules** — Complete computation rules for Glue:
  - `Glue A [phi -> (B, f)]` reduces to `A` when `phi = 0`
  - `Glue A [phi -> (B, f)]` reduces to `B` when `phi = 1`
  - `unglue [phi, te] (glue [phi, t, a])` reduces to `t`
  - `glue [phi, (unglue [phi, te] b), b]` reduces to `b` when `phi = 1`

- **Comp/fill computation for data types** — Kan operations should compute through inductive types (transport/fill along constructors). Currently comp/hcomp work but don't reduce through data type structure.

- **Regularity** — `comp A [ ] base` (empty system) should reduce to `base`. Currently may not compute.

- **Cofibration subtyping** — `[_ | phi] A <= [_ | psi] A` when `phi <= psi`. Needed for partial element subtyping.

### 2. Type Theory Features

- **Universe polymorphism** — Already has stratified U0, U1, U2... Could add:
  - Impredicative universe (Prop) for proof-irrelevant types
  - Universe of small types (sSet)
  - Cumulativity constraints beyond simple level comparison
  - Universe lifting/lowering operations

- **Cumulativity** — `A : U_n` and `U_n : U_m` when `n <= m`. Currently basic, could be extended with:
  - Cumulativity for Sigma/Pi types
  - Cumulativity for record types
  - Cumulativity for inductive types

- **Induction-induction** — Mutual definition of a type family and a type indexed by it. Needed for:
  - Well-founded recursion
  - Custom induction principles
  - Complex algebraic structures

- **Induction-recursion** — Definition of a type simultaneously with a function on it. Needed for:
  - Universe definitions
  - Modal type theory
  - Custom elimination principles

- **Termination / Guard checking** — Currently no termination checking. Add:
  - Structural recursion checking
  - Well-founded recursion support
  - Coinduction for infinite data types

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
