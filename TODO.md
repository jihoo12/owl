# TODO.md — Remaining improvements for owl

## Done

- [x] PathP (dependent path types) — Added as syntactic sugar over TPath. `PathP (<i> A i) u v` parses to `TPath(PLam("i", A i), u, v)`. Type families work correctly with endpoint checking.

## Remaining

- **Single-face composition, not general systems** — hcomp/comp/fill/hfill take one phi face rather than an arbitrary system of multiple compatible faces, which is how "open box" filling normally works in full cubical theories. Implementing systems would require:
  - A `System` type holding multiple (face, tube) pairs
  - Compatibility checking: for each pair of faces phi_i, phi_j, the tubes must agree on phi_i /\ phi_j
  - Modified reduction rules for hcomp/comp/fill/hfill
  - Parser support for system syntax (e.g., `[ phi1 -> tube1, phi2 -> tube2 ]`)

- **HITs are minimal** — Only simple point/path constructors shown (no square/higher-cell constructors, no truncation constructors like those needed for set-quotients or n-types). Potential additions:
  - Higher inductive types with higher-dimensional constructors (squares, cubes)
  - Truncation types (isProp, isSet, isGroupoid)
  - Set-quotients / quotient types
  - Pushouts, suspensions, join

- **Universe polymorphism** — Already has a stratified U0, U1, U2... cumulative hierarchy. Could be extended with:
  - Impredicative universe (Prop)
  - Universe of small types
  - Cumulativity constraints beyond simple level comparison
