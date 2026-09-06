use super::*;

#[test]
fn unsolved_named_hole_is_reported() {
    let err = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def x : Nat := ?hole",
    )
    .unwrap_err();
    let msg = err.to_string();
    assert!(msg.contains("Unsolved holes"), "msg: {}", msg);
    assert!(msg.contains("?hole"), "msg: {}", msg);
    assert!(msg.contains("Nat"), "msg: {}", msg);
}

#[test]
fn unsolved_underscore_hole_is_reported() {
    let err = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def x : Nat := _",
    )
    .unwrap_err();
    assert!(err.to_string().contains("Unsolved holes"));
}

#[test]
fn hole_inside_term_is_reported() {
    let err = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def x : Nat := suc ?n",
    )
    .unwrap_err();
    assert!(err.to_string().contains("?n"));
}

#[test]
fn type_hole_solved_by_unification() {
    let output = run_str(
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
         def x : ?ty := zero\n\
         def main : Nat := x",
    )
    .expect("type hole should be solved by unification");
    assert_eq!(
        crate::cubical::syntax::pretty::nat_to_int(&output.value),
        Some(0)
    );
}
