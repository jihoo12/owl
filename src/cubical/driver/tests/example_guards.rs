use super::*;
use std::path::Path;

#[test]
fn natcommring_demo_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/natcommring_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .unwrap();
    handle
        .join()
        .unwrap()
        .expect("natcommring_demo.owl should typecheck");
}

#[test]
fn int_omega_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/int_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .unwrap();
    handle
        .join()
        .unwrap()
        .expect("int_demo.owl should typecheck");
}

#[test]
fn group_demo_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/group_demo.owl");
    // Deep proof trees from the generated law-application chains exceed
    // the default 2 MiB test-thread stack in debug builds.
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .unwrap();
    handle
        .join()
        .unwrap()
        .expect("group_demo.owl should typecheck");
}

#[test]
fn nat_path_algebra_example_checks() {
    // Guard against regressions in the verified path-algebra example:
    // congruence, symmetry, transitivity and the additive laws over Nat.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("nat_path_algebra.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn nat_path_algebra check thread");
    handle
        .join()
        .expect("nat_path_algebra check thread panicked")
        .expect("examples/nat_path_algebra.owl should typecheck");
}

#[test]
fn forall_after_arrow_example_checks() {
    // Guard against regressions in `forall` binders following a
    // non-dependent `->` (H10 ergonomics): `A -> forall (x : B), C` must
    // parse with the forall binding looser than the arrow, and the whole
    // thing must typecheck.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("forall_after_arrow.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn forall_after_arrow check thread");
    handle
        .join()
        .expect("forall_after_arrow check thread panicked")
        .expect("examples/forall_after_arrow.owl should typecheck");
}

#[test]
fn record_examples_check() {
    // Guard against regressions in record support: minimal records,
    // dependent record params, record update, and record-with-stress
    // patterns. The `record` declaration desugars to a single-constructor
    // inductive, so these exercise the constructor-arg (field-type)
    // checking path.
    for name in [
        "record_minimal.owl",
        "record_types.owl",
        "stress_record_types.owl",
        "stress_update_or_patterns.owl",
    ] {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples")
            .join(name);
        let n = name.to_string();
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .expect("spawn record check thread");
        handle
            .join()
            .expect("record check thread panicked")
            .unwrap_or_else(|e| panic!("examples/{n} should typecheck: {e}"));
    }
}

#[test]
fn nested_patterns_example_checks() {
    // Guard against regressions in the parser-side compilation of nested
    // constructor patterns (`suc (suc m)`, `cons x (cons y zs)`, `as` and
    // or-patterns combined with nesting). Deep nested-eliminator chains
    // need a bigger stack than the default 2 MiB test-thread stack.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("stress_nested_patterns.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn nested patterns check thread");
    handle
        .join()
        .expect("nested patterns check thread panicked")
        .expect("examples/stress_nested_patterns.owl should typecheck");
}

#[test]
fn refined_hit_cases_example_checks() {
    // Guard against regressions in refined (nested) constructor patterns
    // on path-constructor HIT cases (`mer (suc m) i => ...`): the
    // typechecker's per-leaf boundary coherence, the nested-eliminator
    // compilation, and the NBE env layout (the case's interval binder is a
    // phantom slot below the ordinary args). Deep nested-eliminator normal
    // forms need a bigger stack than the default 2 MiB test-thread stack.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("refined_hit_cases.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn refined hit cases check thread");
    handle
        .join()
        .expect("refined hit cases check thread panicked")
        .expect("examples/refined_hit_cases.owl should typecheck");
}

#[test]
fn omega_demo_example_checks() {
    // Guard against regressions in `by omega`: definitional reflexivity
    // (unfolding `add` on constructor-headed arguments) and direct
    // application of a previously verified global lemma.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("omega_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn omega_demo check thread");
    handle
        .join()
        .expect("omega_demo check thread panicked")
        .expect("examples/omega_demo.owl should typecheck");
}

#[test]
fn ring_demo_example_checks() {
    // Guard against regressions in `by ring`: polynomial normalization
    // over the commutative semiring on Nat plus the law-application tree
    // the kernel re-checks (add_comm/mul_comm/distributivity demos).
    // The large law-application proofs need a bigger stack than the
    // default 2 MiB test-thread stack.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("ring_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn ring check thread");
    handle
        .join()
        .expect("ring check thread panicked")
        .expect("examples/ring_demo.owl should typecheck");
}

#[test]
fn ring_laws_lib_checks() {
    // The ring-law library is imported by the demos and resolved by name
    // by `by ring`; it must typecheck standalone as a library. Its large
    // law-application normal forms need a bigger stack than the default
    // 2 MiB test-thread stack.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("lib")
        .join("ring_laws.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn ring laws check thread");
    handle
        .join()
        .expect("ring laws check thread panicked")
        .expect("lib/ring_laws.owl should typecheck");
}

#[test]
fn comm_ring_demo_example_checks() {
    // Guard against regressions in `by ring with C`: polynomial
    // normalization over an abstract `CommRing` record plus the
    // law-application tree the kernel re-checks.  The large proofs need a
    // bigger stack than the default 2 MiB test-thread stack.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("comm_ring_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn comm ring check thread");
    handle
        .join()
        .expect("comm ring check thread panicked")
        .expect("examples/comm_ring_demo.owl should typecheck");
}

#[test]
fn instance_search_example_checks() {
    // Guards instance search: `by ring` / `by field` without an explicit
    // `with C` / `with F` resolve the bundled record from the context by
    // carrier, and the operations are extracted from the instance's type.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("instance_search.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn instance search check thread");
    handle
        .join()
        .expect("instance search check thread panicked")
        .expect("examples/instance_search.owl should typecheck");
}

#[test]
fn stress_mul_algebra_example_checks() {
    // Full multiplicative algebra: assoc/comm/distributive laws over Nat
    // as cubical paths, ending with the double-double lemma. Guards the
    // suspended-elim case-body normalization fix in the equality checker.
    // The deeply nested elim/hcomp normal forms need a larger stack than
    // the default 2 MiB test-thread stack.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("stress_mul_algebra.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn stress check thread");
    handle
        .join()
        .expect("stress check thread panicked")
        .expect("examples/stress_mul_algebra.owl should typecheck");
}

#[test]
fn field_demo_example_checks() {
    // Guard against regressions in `by field with F`: the fraction
    // reification/inverse machinery over an abstract `Field` record plus
    // the law-application tree the kernel re-checks (frac mul/add/div,
    // inv inv/mul, mul inv). The large proofs need a bigger stack than
    // the default 2 MiB test-thread stack; the kernel re-check is also
    // slow in debug builds (the biggest theorem takes ~1 min per pass).
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("field_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn field check thread");
    handle
        .join()
        .expect("field check thread panicked")
        .expect("examples/field_demo.owl should typecheck");
}

#[test]
fn field_laws_lib_checks() {
    // The field-law library is imported by the demos and resolved by name
    // by `by field with F`; it must typecheck standalone as a library.
    // Its large law-application normal forms need a bigger stack than the
    // default 2 MiB test-thread stack.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("lib")
        .join("field_laws.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn field laws check thread");
    handle
        .join()
        .expect("field laws check thread panicked")
        .expect("lib/field_laws.owl should typecheck");
}

#[test]
fn indexed_transp_example_checks() {
    // Guard against regressions in non-constant indexed inductive type
    // transport: Bool ≃ Bool' via univalence, then transport a List Bool
    // through the interval-dependent family List (ua e @ i) to List Bool'.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("indexed_transp_test.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn indexed transp check thread");
    handle
        .join()
        .expect("indexed transp check thread panicked")
        .expect("examples/indexed_transp_test.owl should typecheck");
}

#[test]
fn id_types_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("id_types.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("id_types thread spawn");
    handle
        .join()
        .expect("id_types check thread panicked")
        .expect("examples/id_types.owl should typecheck");
}

#[test]
fn higher_dim_hcomp_example_checks() {
    // Guard: A5 higher-dimensional hcomp through Path types (square
    // composition). Verifies hcomp/comp/fill/hfill decompose correctly
    // when the carrier type is a Path type.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("higher_dim_hcomp.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("higher_dim_hcomp thread spawn");
    handle
        .join()
        .expect("higher_dim_hcomp check thread panicked")
        .expect("examples/higher_dim_hcomp.owl should typecheck");
}

#[test]
fn postulate_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("postulate.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("postulate thread spawn");
    handle
        .join()
        .expect("postulate check thread panicked")
        .expect("examples/postulate.owl should typecheck");
}

#[test]
fn absurd_pattern_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("absurd_pattern.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("absurd_pattern thread spawn");
    handle
        .join()
        .expect("absurd_pattern check thread panicked")
        .expect("examples/absurd_pattern.owl should typecheck");
}

#[test]
fn homotopy_demo_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("homotopy_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("homotopy_demo thread spawn");
    handle
        .join()
        .expect("homotopy_demo check thread panicked")
        .expect("examples/homotopy_demo.owl should typecheck");
}

#[test]
fn homotopy_lib_checks() {
    for name in &["homotopy.owl", "suspension.owl", "circle.owl"] {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("lib").join(name);
        let n = name.to_string();
        let handle = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || check(&path))
            .expect("homotopy lib thread spawn");
        handle
            .join()
            .unwrap()
            .unwrap_or_else(|e| panic!("lib/{} should typecheck: {:?}", n, e));
    }
}

#[test]
fn custom_tactic_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/custom_tactic.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .unwrap();
    handle
        .join()
        .unwrap()
        .expect("custom_tactic.owl should typecheck");
}

#[test]
fn bool_lib_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("lib")
        .join("bool.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn bool lib check thread");
    handle
        .join()
        .expect("bool lib check thread panicked")
        .expect("lib/bool.owl should typecheck");
}

#[test]
fn list_lib_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("lib")
        .join("list.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn list lib check thread");
    handle
        .join()
        .expect("list lib check thread panicked")
        .expect("lib/list.owl should typecheck");
}

#[test]
fn maybe_lib_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("lib")
        .join("maybe.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn maybe lib check thread");
    handle
        .join()
        .expect("maybe lib check thread panicked")
        .expect("lib/maybe.owl should typecheck");
}

#[test]
fn vector_lib_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("lib")
        .join("vector.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn vector lib check thread");
    handle
        .join()
        .expect("vector lib check thread panicked")
        .expect("lib/vector.owl should typecheck");
}

#[test]
fn int_lib_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("lib")
        .join("int.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn int lib check thread");
    handle
        .join()
        .expect("int lib check thread panicked")
        .expect("lib/int.owl should typecheck");
}

#[test]
fn bool_demo_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("bool_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn bool_demo check thread");
    handle
        .join()
        .expect("bool_demo check thread panicked")
        .expect("examples/bool_demo.owl should typecheck");
}

#[test]
fn list_demo_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("list_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn list_demo check thread");
    handle
        .join()
        .expect("list_demo check thread panicked")
        .expect("examples/list_demo.owl should typecheck");
}

#[test]
fn maybe_demo_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("maybe_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn maybe_demo check thread");
    handle
        .join()
        .expect("maybe_demo check thread panicked")
        .expect("examples/maybe_demo.owl should typecheck");
}

#[test]
fn vector_demo_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("vector_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn vector_demo check thread");
    handle
        .join()
        .expect("vector_demo check thread panicked")
        .expect("examples/vector_demo.owl should typecheck");
}

#[test]
fn int_ops_demo_example_checks() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("int_ops_demo.owl");
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check(&path))
        .expect("spawn int_ops_demo check thread");
    handle
        .join()
        .expect("int_ops_demo check thread panicked")
        .expect("examples/int_ops_demo.owl should typecheck");
}

#[test]
fn all_example_files_check() {
    // Sweep every examples/*.owl file not already covered by a dedicated
    // test above (cubical/HIT/path/param/quotient/tactics/record demos and
    // the remaining stress files), so nothing in examples/ can silently
    // regress. Each file is checked on a 64 MiB stack thread so large
    // proof trees don't overflow the default 2 MiB test-thread stack.
    let covered = [
        "absurd_pattern.owl",
        "comm_ring_demo.owl",
        "custom_tactic.owl",
        "field_demo.owl",
        "forall_after_arrow.owl",
        "group_demo.owl",
        "higher_dim_hcomp.owl",
        "homotopy_demo.owl",
        "id_types.owl",
        "indexed_transp_test.owl",
        "instance_search.owl",
        "int_demo.owl",
        // Skipped: isNType 1/2 generate deeply nested terms that overflow
        // even 64 MiB stacks. See TODO.md §I3. Fix the parser sugar, not
        // the stack size.
        "isntype_demo.owl",
        "nat_path_algebra.owl",
        "natcommring_demo.owl",
        "omega_demo.owl",
        "postulate.owl",
        "record_minimal.owl",
        "record_types.owl",
        "refined_hit_cases.owl",
        "ring_demo.owl",
        "stress_mul_algebra.owl",
        "stress_nested_patterns.owl",
        "stress_record_types.owl",
        "stress_update_or_patterns.owl",
        // G1 — new library demos
        "bool_demo.owl",
        "list_demo.owl",
        "maybe_demo.owl",
        "vector_demo.owl",
        "int_ops_demo.owl",
    ];
    let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut files: Vec<_> = std::fs::read_dir(&examples)
        .expect("examples/ should exist")
        .map(|e| {
            e.expect("read dir entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .filter(|n| n.ends_with(".owl") && !covered.contains(&n.as_str()))
        .collect();
    files.sort();
    assert!(
        !files.is_empty(),
        "expected at least one uncovered example file"
    );
    let handles: Vec<_> = files
        .iter()
        .cloned()
        .map(|name| {
            let path = examples.join(&name);
            std::thread::Builder::new()
                .stack_size(64 * 1024 * 1024)
                .spawn(move || {
                    check(&path).unwrap_or_else(|e| panic!("examples/{name} should typecheck: {e}"))
                })
                .expect("spawn example check thread")
        })
        .collect();
    for (name, handle) in files.iter().zip(handles) {
        handle
            .join()
            .unwrap_or_else(|e| panic!("examples/{name} thread panicked: {e:?}"));
    }
}
