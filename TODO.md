# TODO.md — Remaining improvements for owl

## Done

- [x] PathP (dependent path types) — Added as syntactic sugar over TPath. `PathP (<i> A i) u v` parses to `TPath(PLam("i", A i), u, v)`. Type families work correctly with endpoint checking.

- [x] General systems for hcomp/comp/fill/hfill — Multi-face system syntax `[phi => tube, ...]` using `=>` (FatArrow) separator. Old single-face syntax `comp A phi tube base` still works (desugars to single-entry system). The `System` type is `Vec<(Term, Term)>`. Top-face reduction applies tube at i1 (not raw VPLam). Constant type families handled correctly for comp/fill. Compatibility checking delegated to face-by-face `check_faces` calls.

## Remaining

- **HITs are minimal** — Only simple point/path constructors shown (no square/higher-cell constructors, no truncation constructors like those needed for set-quotients or n-types). Potential additions:
  - Higher inductive types with higher-dimensional constructors (squares, cubes)
  - Truncation types (isProp, isSet, isGroupoid)
  - Set-quotients / quotient types
  - Pushouts, suspensions, join

- **Universe polymorphism** — Already has a stratified U0, U1, U2... cumulative hierarchy. Could be extended with:
  - Impredicative universe (Prop)
  - Universe of small types
  - Cumulativity constraints beyond simple level comparison

- **Partial types / cubical Satisfies** — Support for partial elements and subtyping into types, needed for Glue and more advanced cubical constructions.

- [x] Better error cascade in check_dt — Added specific `check_dt` arms for `THComp`, `TComp`, `TFill`, `THFill`. Expected type is checked first (via cumulativity) before delegating sub-term checking to `infer_dt`. On `infer_dt` failure, retries with `nbe_eval` to handle cases where the Kan operation reduces. This gives clearer error messages for type mismatches while preserving correct handling of face compatibility.

## Remaining

- **HITs are minimal** — Only simple point/path constructors shown (no square/higher-cell constructors, no truncation constructors like those needed for set-quotients or n-types). Potential additions:
  - Higher inductive types with higher-dimensional constructors (squares, cubes)
  - Truncation types (isProp, isSet, isGroupoid)
  - Set-quotients / quotient types
  - Pushouts, suspensions, join

- **Universe polymorphism** — Already has a stratified U0, U1, U2... cumulative hierarchy. Could be extended with:
  - Impredicative universe (Prop)
  - Universe of small types
  - Cumulativity constraints beyond simple level comparison

- **Partial types / cubical Satisfies** — Support for partial elements and subtyping into types, needed for Glue and more advanced cubical constructions.
