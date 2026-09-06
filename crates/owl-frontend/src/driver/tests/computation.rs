use super::*;
use std::fs;

#[test]
fn run_plus_on_nat() {
    let src = "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
               def plus : Nat -> Nat -> Nat := fun m n => match m return Nat with \
               | zero => n | suc m' => suc (plus m' n)\n\
               def four : Nat := plus (suc (suc zero)) (suc (suc zero))";
    let dir = temp_dir("cubical_plus_test");
    fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.owl");
    fs::write(&path, src).unwrap();
    let output = run(&path).expect("plus should typecheck");
    assert_eq!(output.name, "four");
    cleanup(&dir);
}

#[test]
fn transport_over_ua_still_works() {
    let src = "\
def id : forall (A : U0), A -> A := fun A x => x\n\
def transportExample : forall (A : U0), forall (B : U0), Equiv A B -> A -> B :=\n\
  fun A B e a => transport (<i> ua e @ i) a\n\
def main : forall (A : U0), forall (B : U0), Equiv A B -> A -> B := transportExample\n";
    let dir = temp_dir("cubical_transport_ua");
    fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.owl");
    fs::write(&path, src).unwrap();
    let output = run(&path).expect("transport over ua should typecheck");
    // `run()` prefers `main` over earlier definitions
    assert_eq!(output.name, "main");
    cleanup(&dir);
}

#[test]
fn run_mul_via_run_path() {
    let src = "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
               def add : Nat -> Nat -> Nat := fun m n => match m return Nat with \
               | zero => n | suc k => suc (add k n)\n\
               def mul : Nat -> Nat -> Nat := fun m n => match m return Nat with \
               | zero => zero | suc k => add n (mul k n)\n\
               def main : Nat := mul (suc (suc zero)) (suc (suc (suc zero)))";
    let dir = temp_dir("cubical_mul_test");
    fs::create_dir_all(&dir).unwrap();
    let path = dir.join("main.owl");
    fs::write(&path, src).unwrap();
    let _output = run(&path).expect("mul should compute");
    cleanup(&dir);
}

#[test]
fn run_normalizes_global_definitions() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def add : Nat -> Nat -> Nat := fun m n => match m return Nat with | zero => n | suc k => suc (add k n)\n\
         def main : Nat := add (suc (suc zero)) (suc (suc zero))",
    )
    .expect("program should evaluate");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(4)
    );
}

#[test]
fn check_accepts_library_without_definition() {
    let dir = temp_dir("cubical_check_test");
    fs::create_dir_all(&dir).unwrap();
    let path = dir.join("nat.owl");
    fs::write(
        &path,
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n",
    )
    .unwrap();

    check(&path).expect("a datatype-only library should check");
    cleanup(&dir);
}

#[test]
fn mutual_inductive_even_odd() {
    // Even/Odd as mutually-defined inductive types.
    // even zero, even (suc (suc n)) when even n
    // odd (suc zero), odd (suc (suc n)) when odd n
    let output = run_str(
        "inductive even where \
         | even_zero : even \
         | even_suc : even -> even \
         with inductive odd where \
         | odd_one : odd \
         | odd_suc : odd -> odd\n\
         def main : even := even_zero",
    )
    .expect("mutual inductive even/odd should typecheck");
    assert_eq!(output.name, "main");
}

#[test]
fn mutual_inductive_forward_reference() {
    // B references A's constructors (forward reference).
    let output = run_str(
        "inductive A where \
         | a1 : A \
         | a2 : A \
         with inductive B where \
         | b1 : A -> B \
         | b2 : B\n\
         def main : B := b2",
    )
    .expect("mutual inductive with forward reference should typecheck");
    assert_eq!(output.name, "main");
}

#[test]
fn induction_recursion_basic() {
    // Induction-recursion: define a datatype and a function simultaneously.
    let output = run_str(
        "inductive Nat where \
         | zero : Nat \
         | suc : Nat -> Nat \
         with isZero : Nat -> Nat := fun n => match n return Nat with \
         | zero => suc zero \
         | suc _ => zero\n\
         def main : Nat := isZero zero",
    )
    .expect("induction-recursion should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(1)
    );
}

#[test]
fn refined_pcon_arms_reject_incoherent_endpoints() {
    // A refined pcon arm whose body is not endpoint-coherent must be
    // rejected: the leaf body `<j> zero` violates the boundary at the
    // constructor's faces (the refined binder `suc m` carries the
    // constraint), so it cannot typecheck.
    let source = "inductive Nat where\n\
         | zero : Nat\n\
         | suc : Nat -> Nat\n\
         inductive SuspX where\n\
         | ntr : Nat -> SuspX\n\
         | sso : Nat -> SuspX\n\
         | mer : Nat -> SuspX [ ntr mer_0 , sso mer_0 ]\n\
         def bad : SuspX -> Nat :=\n\
           fun s =>\n\
           match s return Nat with\n\
           | ntr n => n\n\
           | sso n => n\n\
           | mer zero i => <j> zero\n\
           | mer (suc m) i => <j> zero\n\
         def main : Nat := bad (mer (suc zero) @ i1)";
    let err = run_str(source).expect_err("incoherent refined arm must be rejected");
    assert!(err.to_string().contains("Type mismatch"));
}

#[test]
fn hit_constructor_endpoints_reduce_to_faces() {
    // Square/cell/path constructors applied at concrete endpoints are
    // definitionally their faces: `square @ i0 @ i1 = base` (face_j0 at
    // the outer interval, applied to the second), and `cube3 @ i0 @ i1 @
    // i0 = base` (the outermost face pair, then the remaining interval
    // args applied outermost-first). This must hold in the NBE normal
    // form, not just in the typechecker's endpoint checks.
    let header = "inductive Cube where\n\
         | base : Cube\n\
         | line1 : Cube [ base , base ]\n\
         | line2 : Cube [ base , base ]\n\
         | square : Cube [[ base , base , line2 , line2 ]]\n\
         | cube3 : Cube [[[ base , base , line2 , line2 , square , square ]]]\n";
    let base = Term::TCon("Cube".to_string(), "base".to_string(), vec![]);
    for combo in [
        "square @ i0 @ i0",
        "square @ i0 @ i1",
        "square @ i1 @ i0",
        "square @ i1 @ i1",
        "cube3 @ i0 @ i0 @ i0",
        "cube3 @ i1 @ i1 @ i1",
        "cube3 @ i0 @ i1 @ i0",
        "cube3 @ i0 @ i1 @ i1",
        "cube3 @ i1 @ i0 @ i1",
    ] {
        let source = format!("{}def main : Cube := {}", header, combo);
        let output = run_str(&source).unwrap_or_else(|e| panic!("{} should evaluate: {e}", combo));
        assert_eq!(output.value, base, "{} should reduce to base", combo);
    }
}

#[test]
fn nested_patterns_reject_mixed_columns() {
    // A variable pattern and a constructor pattern in the same column
    // cannot be compiled into the kernel's first-matching-case eliminator
    // (the variable arm would silently shadow the constructor arms).
    let source = "inductive Nat where\n\
         | zero : Nat\n\
         | suc : Nat -> Nat\n\
         def bad : Nat -> Nat := fun n =>\n\
           match n return Nat with\n\
           | zero        => zero\n\
           | suc (suc m) => m\n\
           | suc m       => m\n\
         def main : Nat := bad (suc zero)";
    let err = run_str(source).expect_err("mixed columns must be rejected");
    assert!(
        err.to_string()
            .contains("mixed variable and constructor patterns")
    );
}

#[test]
fn nested_patterns_reject_incomplete_match() {
    // Phase 1.3 completeness check: an open match must cover every
    // constructor of the scrutinee datatype.
    let source = "inductive Nat where\n\
         | zero : Nat\n\
         | suc : Nat -> Nat\n\
         def bad : Nat -> Nat := fun n =>\n\
           match n return Nat with\n\
           | zero => zero\n\
         def main : Nat := bad (suc zero)";
    let err = run_str(source).expect_err("incomplete matches must be rejected");
    assert!(err.to_string().contains("incomplete pattern match"));
}
