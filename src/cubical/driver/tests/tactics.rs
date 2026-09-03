use super::*;

#[test]
fn eq_tactic_refl_sym_chain() {
    // `by eq` closes reflexive goals, single hypotheses (either
    // orientation, via inline symmetry), and multi-hop chains through a
    // context-provided transitivity lemma.
    let src = "inductive Nat where\n\
 \x20 | zero : Nat\n\
 \x20 | suc : Nat -> Nat\n\
def trans : forall (a : Nat), forall (b : Nat), forall (c : Nat),\n\
 \x20 Path Nat a b -> Path Nat b c -> Path Nat a c :=\n\
 \x20 fun a b c p q => <i> hcomp Nat [~i => <j> a, i => q] (p @ i)\n\
def t_refl : forall (a : Nat), Path Nat a a := by intro a; eq\n\
def t_direct : forall (a : Nat), forall (b : Nat),\n\
 \x20 Path Nat a b -> Path Nat b a := by intro a b p; eq\n\
def t_chain : forall (a : Nat), forall (b : Nat), forall (c : Nat),\n\
 \x20 Path Nat a b -> Path Nat b c -> Path Nat a c :=\n\
 \x20 by intro a b c p q; eq\n\
def t_long : forall (a : Nat), forall (b : Nat), forall (c : Nat), forall (d : Nat),\n\
 \x20 Path Nat a b -> Path Nat b c -> Path Nat c d -> Path Nat a d :=\n\
 \x20 by intro a b c d p q r; eq\n";
    let output = run_str(src).expect("by eq programs should check");
    assert_eq!(output.name, "t_long");
}

#[test]
fn eq_tactic_needs_trans_lemma_for_chains() {
    let src = "inductive Nat where\n\
 \x20 | zero : Nat\n\
 \x20 | suc : Nat -> Nat\n\
def t_chain : forall (a : Nat), forall (b : Nat), forall (c : Nat),\n\
 \x20 Path Nat a b -> Path Nat b c -> Path Nat a c :=\n\
 \x20 by intro a b c p q; eq\n";
    match run_str(src) {
        Err(RunError::Type(e)) => {
            let msg = format!("{}", e);
            assert!(
                msg.contains("transitivity lemma"),
                "expected missing-trans error, got: {}",
                msg
            );
        }
        other => panic!(
            "expected missing-trans-lemma rejection, got: {:?}",
            other.map(|o| o.name)
        ),
    }
}

#[test]
fn group_solver_rejects_non_identity() {
    let src = "\
record Group (A : Type) (mul : A -> A -> A) (inv : A -> A) (one : A) where\n\
 \x20 field trans : forall (a : A), forall (b : A), forall (c : A), Path A a b -> Path A b c -> Path A a c\n\
 \x20 field sym : forall (a : A), forall (b : A), Path A a b -> Path A b a\n\
 \x20 field cong_mul_l : forall (a : A), forall (b : A), forall (n : A), Path A a b -> Path A (mul a n) (mul b n)\n\
 \x20 field cong_mul_r : forall (a : A), forall (b : A), forall (m : A), Path A a b -> Path A (mul m a) (mul m b)\n\
 \x20 field cong_inv : forall (a : A), forall (b : A), Path A a b -> Path A (inv a) (inv b)\n\
 \x20 field mul_assoc : forall (a : A), forall (b : A), forall (c : A), Path A (mul (mul a b) c) (mul a (mul b c))\n\
 \x20 field one_mul : forall (a : A), Path A (mul one a) a\n\
 \x20 field mul_one : forall (a : A), Path A (mul a one) a\n\
 \x20 field inv_l : forall (a : A), Path A (mul (inv a) a) one\n\
 \x20 field inv_r : forall (a : A), Path A (mul a (inv a)) one\n\
 \x20 field inv_one : Path A (inv one) one\n\
 \x20 field inv_inv : forall (a : A), Path A (inv (inv a)) a\n\
 \x20 field inv_mul : forall (a : A), forall (b : A), Path A (inv (mul a b)) (mul (inv b) (inv a))\n\
def bad :\n\
 \x20 forall (A : Type), forall (mul : A -> A -> A), forall (inv : A -> A),\n\
 \x20 forall (one : A),\n\
 \x20 forall (G : Group A mul inv one), forall (a : A), forall (b : A),\n\
 \x20 Path A (mul a b) (mul b a) :=\n\
 \x20 by intro A mul inv one G a b; group with G\n";
    match run_str(src) {
        Err(RunError::Type(e)) => {
            assert!(
                format!("{}", e).contains("words do not match"),
                "expected word-mismatch error, got: {}",
                e
            );
        }
        other => panic!(
            "expected word-mismatch rejection, got: {:?}",
            other.map(|o| o.name)
        ),
    }
}

#[test]
fn tactic_id_typechecks() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def id : forall (A : U0), A -> A := by intro A x; exact x\n\
         def main : Nat := id Nat zero",
    )
    .expect("tactic id should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(0)
    );
}

#[test]
fn tactic_assumption_typechecks() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def id_nat : Nat -> Nat := by intro x; assumption\n\
         def main : Nat := id_nat (suc zero)",
    )
    .expect("tactic assumption should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(1)
    );
}

#[test]
fn tactic_apply_typechecks() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def id_nat : Nat -> Nat := fun x => x\n\
         def apply_test : Nat -> Nat := by intro x; apply id_nat; exact x\n\
         def main : Nat := apply_test (suc (suc zero))",
    )
    .expect("tactic apply should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(2)
    );
}

#[test]
fn tactic_apply_then_exact_typechecks() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def add_one : Nat -> Nat := fun n => suc n\n\
         def apply_chain_test : Nat -> Nat := by intro x; apply add_one; apply add_one; exact x\n\
         def main : Nat := apply_chain_test (suc zero)",
    )
    .expect("tactic chained apply should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(3)
    );
}

#[test]
fn tactic_exact_nat_typechecks() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def const_zero : Nat := by exact zero\n\
         def main : Nat := const_zero",
    )
    .expect("tactic exact should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(0)
    );
}

#[test]
fn tactic_reflexivity_typechecks() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def refl_zero : Path Nat zero zero := by reflexivity\n\
         def main : Nat := zero",
    )
    .expect("tactic reflexivity should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(0)
    );
}

#[test]
fn tactic_symmetry_typechecks() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def sym_test : Path Nat zero zero := by symmetry; reflexivity\n\
         def main : Nat := zero",
    )
    .expect("tactic symmetry + reflexivity should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(0)
    );
}

#[test]
fn tactic_split_typechecks() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def pair_test : Nat * Nat := by split; exact zero; exact (suc zero)\n\
         def main : Nat := fst pair_test",
    )
    .expect("tactic split should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(0)
    );
}

#[test]
fn tactic_split_snd_typechecks() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def pair_test2 : Nat * Nat := by split; exact (suc zero); exact (suc (suc zero))\n\
         def main : Nat := snd pair_test2",
    )
    .expect("tactic split snd should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(2)
    );
}

#[test]
fn tactic_constructor_zero_args() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def my_zero : Nat := by constructor\n\
         def main : Nat := my_zero",
    )
    .expect("tactic constructor (zero args) should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(0)
    );
}

#[test]
fn tactic_constructor_one_arg() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def my_suc : Nat := by constructor suc; exact zero\n\
         def main : Nat := my_suc",
    )
    .expect("tactic constructor (one arg) should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(1)
    );
}

#[test]
fn tactic_constructor_named() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def my_two : Nat := by constructor suc; exact (suc zero)\n\
         def main : Nat := my_two",
    )
    .expect("tactic constructor (named) should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(2)
    );
}

#[test]
fn tactic_constructor_chain() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def three : Nat := by constructor suc; exact (suc (suc zero))\n\
         def main : Nat := three",
    )
    .expect("tactic constructor chain should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(3)
    );
}

#[test]
fn tactic_trivial_path() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def trivial_path : Path Nat zero zero := by trivial\n\
         def main : Nat := zero",
    )
    .expect("tactic trivial on reflexive path should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(0)
    );
}

#[test]
fn tactic_trivial_datatype() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def trivial_nat : Nat := by trivial\n\
         def main : Nat := trivial_nat",
    )
    .expect("tactic trivial on zero-arg constructor should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(0)
    );
}

#[test]
fn tactic_compute_simplifies() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def id : Nat -> Nat := fun x => x\n\
         def compute_test : Nat := by compute; exact (id zero)\n\
         def main : Nat := compute_test",
    )
    .expect("tactic compute should typecheck");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(0)
    );
}

#[test]
fn tactic_transitivity_typechecks() {
    // transitivity is hard to test with Nat since we don't have
    // path constructors.  Test that it at least parses and gives
    // a meaningful error when the goal isn't a path.
    let err = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def bad : Nat := by transitivity",
    );
    assert!(err.is_err());
}

#[test]
fn omega_rejects_unproved_comm() {
    // Without a pre-proved comm lemma omega cannot synthesize induction
    // yet; it must fail with a clear error rather than accept a circular
    // proof.
    let source = "inductive Nat where\n\
         | zero : Nat\n\
         | suc : Nat -> Nat\n\
         def add : Nat -> Nat -> Nat := fun m n =>\n\
           match m return Nat with\n\
           | zero => n\n\
           | suc m' => suc (add m' n)\n\
         def bad : forall (m : Nat), forall (n : Nat), Path Nat (add m n) (add n m) := by intro m n; omega";
    let err = run_str(source).expect_err("omega should reject an unproved comm goal");
    assert!(err.to_string().contains("omega: unable to solve goal"));
}
