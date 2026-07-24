# Owl

Owl is a small experimental cubical type theory proof assistant.  Its kernel
supports dependent functions, paths and interval operations, transport and
univalence primitives, inductive types, and higher inductive constructors.

## Command line

```text
cargo run -- check examples/nat.owl
cargo run -- eval examples/nat.owl
cargo run -- repl
```

`check` validates every declaration and allows library files with no entry
point. `eval` checks the program and normalizes `main`; when `main` is absent,
it normalizes the last definition. Source files can import relative modules:

```text
import "nat.owl"

def main : Nat = suc zero
```

The REPL accepts one complete top-level declaration per line. Use `:load FILE`
to add a source file to the session, `:help` for the command summary, and
`:quit` to exit.

## Debug logging

Pass `--debug` (or `-d`) to any command to enable detailed trace output from
the typechecker and NbE reduction engine. The same behaviour can be activated
via the `OWL_DEBUG` environment variable:

```text
cargo run -- --debug eval examples/nat.owl
OWL_DEBUG=1 cargo run -- check examples/nat.owl
```

Typechecker output shows every `infer` and `check` entry with the term being
checked and the current context depth.  NbE output records every reduction
step (beta, eliminator, transport, …) and prints the full trace at the end of
execution.
