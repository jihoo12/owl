# Source-level conventions for `src/`

This file contains Rust source-level conventions specific to the `src/` tree.
Read the top-level `AGENTS.md` first for project state, workflow, and testing;
consult this file once you're editing `.rs` files.

## Code style

- Mirror the existing style: this codebase is heavily documented about **why**
  (invariants, scope tricks, soundness reasoning). Add that kind of comment where
  a non-obvious invariant exists; don't add noise.
- Reuse established patterns: `TypeError`/`ContextualError::with_def` for errors,
  thread-locals + `RefCell` for `CURRENT_DTS` / decl-name-position tables,
  `debug_log!` for tracing, `clear_nbe_cache()` between declarations.
- Tests: prefer a driver-level integration test plus an `examples/*.owl` guard
  over inlining a huge owl program in a test string.
- Commit messages use conventional prefixes: `feat:`, `fix:`, `refactor:`,
  `docs:`, `test:`. Keep the imperative, summary line under ~72 chars, and only
  commit what the user asks you to.

## Module layout

```
src/cubical/
  driver/            file I/O pipeline, integration tests
  env.rs             global definition environment
  session.rs         Session struct — NbE/typechecker thread-local state
  interval.rs        interval algebra
  equality.rs        eta/definitional equality
  eq.rs              legacy equality helpers (prefer equality.rs)
  omega.rs           omega tactic decision procedure
  ring.rs            ring tactic decision procedure
  field.rs           field tactic decision procedure
  group.rs           group tactic decision procedure
  tactics.rs         tactic engine (by omega/ring/field/group)
  debug.rs           debug_log! plumbing
  test_helpers.rs    shared test utilities
  parser/            lexer, grammar, pattern parsing
  syntax/            AST, pretty-printer, positivity
  typechecker/       infer/check, cumulativity, termination, errors
  nbe/               NbE evaluation, quoting, hcomp/transport, trace
```

## Kernel-critical invariants

When editing `nbe/`, `equality.rs`, or `typechecker/`, reason carefully about
de Bruijn index arithmetic. Shift/scope bugs are the most common failure class.
