# AGENTS.md — Owl

Owl is a small experimental **cubical type theory proof assistant** written in
Rust (edition 2024, zero external crates). The kernel supports dependent
functions, path types and interval operations, transport/univalence, inductive
and higher-inductive types, records, cubical subtypes, quotients (via HITs),
holes, and a tactic layer (`intro/exact/apply/split/…`, `by omega`, `by ring`,
`by ring with C`, `by field with F`).

This file is the operating manual for AI agents working in this repo. Read it
fully before changing code.

---

## 1. Repository layout

```
src/main.rs                 CLI: check / eval / repl / help (+ --debug)
src/cubical/                the kernel and frontend
  driver.rs                 file I/O pipeline + integration tests (see §4)
  env.rs                    global definition environment
  parser/                   lexer, grammar, parser tests
  syntax/                   AST, pretty-printer, positivity, syntax tests
  typechecker/              infer/check, cumulativity, termination, errors
  nbe/                      NbE evaluation, quoting, trace
  equality.rs               eta/definitional equality (kernel-critical)
  omega.rs, ring.rs, field.rs, tactics.rs   tactic decision procedures
  interval.rs, dependent_pi_transport_test.rs
examples/*.owl              demos — every file must typecheck (guarded by tests)
lib/*.owl                   libraries resolved by-name by tactics (ring_laws, field_laws)
bad_examples/*.owl          negative tests — every file must FAIL to typecheck
docs/reference.md           the language reference manual
TODO.md                     live project tracker (single source of truth, §3)
rust-analyzer-db.md         how to query the code-analysis SQLite db (§5)
```

## 2. Build / test / run commands

```sh
cargo build                        # build the binary
cargo test                         # full suite (see §4 for timing caveats)
cargo test <name>                  # targeted test
cargo run -- check examples/nat.owl   # typecheck a file
cargo run -- eval  examples/nat.owl   # typecheck + normalize main/last def
cargo run -- check lib/ring_laws.owl  # check a library
cargo fmt                          # format Rust (run after editing .rs files)
scripts/verify.sh                  # full verification pipeline (build+fmt+test+rescan)
scripts/verify.sh --quick          # fast iteration (skips the slow suites, §4)
```

`--debug` (or `-d`, or `OWL_DEBUG=1`) enables detailed typechecker/NbE traces —
use it when reducing or typechecking behaves unexpectedly.

## 3. TODO.md workflow (mandatory)

- `TODO.md` is the **single source of truth** for project state. At the start of
  a session, read it and work on the highest-priority open item you are asked to
  address.
- When you **finish** a piece of work:
  1. Mark the item's checkbox `[ ]` → `[x]`.
  2. Move a one-paragraph summary to the **top** of the `## Completed
     (implementation log)` section, in the existing style: what changed, why,
     how it was verified (test names / examples / commands), any invariants the
     fix relies on. Put the most recent entry first.
- If you **start** an item, annotate it briefly so the file reflects reality.
- Never fabricate completions. Only mark an item done after the verification in
  §6 has actually passed.
- The `/sync-todo` opencode command (§7) drives this workflow from the TUI.

## 4. Tests

- Everything is exercised through `cargo test` (mostly integration tests in
  `driver.rs`, parser/syntax unit tests elsewhere).
- The `examples/*.owl` guards run on **64 MiB stack threads** — deep elim/hcomp
  normal forms overflow the default 2 MiB test-thread stack. Keep this pattern
  when adding an example guard:
  ```rust
  let handle = std::thread::Builder::new()
      .stack_size(64 * 1024 * 1024)
      .spawn(move || check(&path))?;
  handle.join()??;
  ```
- `bad_examples/*.owl` are negative tests: typechecking them must **fail**.
- **Slow in debug builds:** `field_demo_example_checks` / `field_laws_lib_checks`
  (~5 min total; the biggest field theorem ~1 min per kernel pass) and the
  `stress_*` / ring demos. Use `scripts/verify.sh --quick` for fast iteration
  and the full `cargo test` when you touch the kernel, NbE, or equality.
- When you add a kernel feature or fix, add a **dedicated example guard test** so
  it can't silently regress.

## 5. Code analysis: rust-analyzer-db

Use the SQLite code database for navigation instead of guessing:

```sh
uvx rust-analyzer-db scan src --db rust_code.db   # rescan after editing .rs files
uvx rust-analyzer-db list --kind function --name parse --db rust_code.db
uvx rust-analyzer-db show <id> --db rust_code.db
uvx rust-analyzer-db methods <Type> --db rust_code.db
uvx rust-analyzer-db search "phrase" --db rust_code.db
uvx rust-analyzer-db stats --db rust_code.db
uvx rust-analyzer-db complexity --db rust_code.db
uvx rust-analyzer-db graph --root <fn> --depth 3 --db rust_code.db
```

The db is registered as an opencode **MCP server**, so tools like
`list_items`, `get_item`, `search_code`, `methods_of`, `call_graph_info` are
available directly. See `rust-analyzer-db.md` for the full command list. The
`/rescan` and `/analyze` commands in §7 wrap the common cases.

## 6. Verification protocol — run this after EVERY code change

1. `cargo build` — the change compiles.
2. `cargo fmt --check` — formatting is clean (or run `cargo fmt`).
3. Run tests: targeted `cargo test <name>` first, then the full suite
   (`scripts/verify.sh --quick` for iteration, full `cargo test` for kernel/
   NbE/equality changes).
4. `cargo run -- check` on the `.owl` files you touched or added.
5. `uvx rust-analyzer-db scan src --db rust_code.db` so the db reflects the new
   source.
6. Update `TODO.md` per §3.
7. **Never claim a change works without actually running the commands.** A
   passing claim must be backed by observed output.

## 7. OpenCode automation (see `opencode.jsonc`)

| Command   | What it does                                        |
|-----------|-----------------------------------------------------|
| `/verify` | run the full verification pipeline and fix failures |
| `/test`   | run `cargo test $ARGUMENTS`                         |
| `/rescan` | rescan the rust-analyzer-db and summarize stats     |
| `/analyze`| deep-dive one item/function via the db (source, complexity, callers) |
| `/sync-todo` | reconcile `TODO.md` with the actual state of the work |

## 8. Owl language gotchas (kernel-facing invariants)

- **Integer literals `0`/`1` parse as the interval endpoints `i0`/`i1`**, not Nat
  numerals. Nat terms must use the `zero`/`suc` constructors.
- **`forall` is only recognized at term top-level** — it cannot follow `->`.
  Declare all binders before the arrow chain
  (`forall (a : Nat), forall (b : Nat), Path Nat a b -> …`).
- **Tactic `by` blocks must sit at the root of a `def`** (a top-level `TBy`).
  `fun … => by ring with C` nested inside a body panics at NbE — don't write it.
- `by_wf` is a trusted escape hatch that disables the structural-recursion
  guard; only use where the user approves.
- **Tactic output is re-checked by the kernel** — the proof trees from
  omega/ring/field are constructed as raw law-application chains and the kernel
  is the soundness backstop. Don't weaken that re-check.
- The kernel is **de Bruijn-index based**. Shift/scope bugs are the most common
  failure class; when editing `nbe/`, `equality.rs`, or `typechecker/`, reason
  carefully about where references land relative to `env.len()` and quote frames
  (see `nbe/mod.rs` comments on locals-only envs and stuck eliminators).
- Keep **global definitions out of the NbE eval environment** (locals-only env);
  globals resolve through the global definition value vector. Inlining globals
  into the env re-opens recursive definitions and causes unbounded term growth /
  `EtaFuelExhausted`.
- **Deep normal forms overflow the 2 MiB test stack** — see §4.

## 9. Rust conventions

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

## 10. Environment

- Nix shell (`shell.nix`) provides `python3`, `uv`, and the Rust toolchain
  (`cargo`, `rustc`, `rustfmt`, `clippy`).
- `rust-analyzer-db` lives in `.venv/` (run it via `uvx` or directly).
- `.venv/`, `target/`, `rust_code.db`, `AGENTS.md`, `opencode.jsonc`, and
  `.opencode/` are git-ignored (local tooling, not committed).
