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

## Remaining

- **Universe polymorphism** — Already has a stratified U0, U1, U2... cumulative hierarchy. Could be extended with:
  - Impredicative universe (Prop)
  - Universe of small types
  - Cumulativity constraints beyond simple level comparison

- **Partial types / cubical Satisfies** — Support for partial elements and subtyping into types, needed for Glue and more advanced cubical constructions.
