# Owl

Owl is a small experimental **cubical type theory proof assistant** written in
Rust. Its kernel supports dependent functions, path types and interval operations,
transport and univalence primitives, inductive types (including higher inductive
types with path, square, and n-dimensional cell constructors), records, coinductive
types, and a tactic mode.

## Features

- **Dependent types** with Pi (forall) and Sigma types
- **Cubical type theory** core: path types, interval algebra, Glue types, univalence
- **Higher inductive types** (HITs): path constructors, square constructors, n-dimensional cells
- **Transport and Kan operations**: `transport`, `hcomp`, `comp`, `fill`, `hfill`
- **Inductive types**: parameterized, recursive, mutual (induction-induction), induction-recursion
- **Record types** with field projection, dot notation, and record update
- **Coinductive types** via `Delay`/`Next`/`Force`
- **Pattern matching**: nested patterns, or-patterns, as-patterns, record patterns
- **Tactic mode**: `intro`, `exact`, `apply`, `assumption`, `split`, `constructor`, `destruct`, `reflexivity`, `symmetry`, `transitivity`, `compute`, `trivial`
- **Decision procedures**: `by omega` (linear arithmetic), `by ring` / `by ring with C` (polynomial identities), `by field with F` (fraction identities), `by group with G` (word problems), `by eq` (equality chaining)
- **Module system**: parameterized modules, qualified imports, selective imports
- **Universes**: `U0`, `U1`, `U2`, ..., `Prop` (impredicative), `SSet` (strict), with cumulativity

## Quick Start

### Prerequisites

- Rust toolchain (edition 2024)
- `cargo` for building

### Build

```sh
cargo build
```

### Check a file

```sh
cargo run -- check examples/nat.owl
```

### Evaluate a file

```sh
cargo run -- eval examples/nat.owl
```

### Start the REPL

```sh
cargo run -- repl
```

## Command Line

```text
cargo run -- check <file>       Typecheck a source file
cargo run -- eval  <file>       Typecheck and normalize main/last def
cargo run -- repl               Start an interactive session
cargo run -- <file>             Alias for eval
```

The `check` command validates every declaration and allows library files with no
entry point. `eval` checks the program and normalizes `main`; when `main` is
absent, it normalizes the last definition.

### Debug logging

Pass `--debug` (or `-d`) to any command to enable detailed trace output from
the typechecker and NbE reduction engine:

```sh
cargo run -- --debug eval examples/nat.owl
OWL_DEBUG=1 cargo run -- check examples/nat.owl
```

### Performance timing

Set `OWL_TIMINGS=1` to print per-definition phase timings to stderr:

```sh
OWL_TIMINGS=1 cargo run -- check examples/nat.owl
```

## Examples

Source files live in `examples/`. Every file typechecks successfully:

```sh
cargo run -- check examples/nat.owl
cargo run -- check examples/tactics.owl
cargo run -- check examples/ring_demo.owl
cargo run -- check examples/comm_ring_demo.owl
cargo run -- check examples/field_demo.owl
```

See [`docs/reference.md`](docs/reference.md) for the complete language reference
with worked examples.

## Libraries

Library files in `lib/` are resolved by-name by the tactic engine:

- `lib/ring_laws.owl` — commutative ring laws for `by ring`
- `lib/field_laws.owl` — field laws for `by field`
- `lib/algebra.owl` — `CommRing`, `Group`, `Field`, `Module` records
- `lib/logic.owl` — `Empty` type and `Not`
- `lib/truncation.owl` — truncation types

## Testing

```sh
cargo test                 # run full test suite
cargo test <name>          # run targeted test
scripts/verify.sh          # full verification pipeline (build+fmt+test+rescan)
scripts/verify.sh --quick  # quick verification (no slow suites)
```

## Documentation

- [`docs/reference.md`](docs/reference.md) — complete language reference manual
- [`AGENTS.md`](AGENTS.md) — operating manual for AI agents
- [`TODO.md`](TODO.md) — project tracker and roadmap
- [`rust-analyzer-db.md`](rust-analyzer-db.md) — code analysis database guide

## License

See [`LICENSE`](LICENSE) for details.
