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
