
#[test]
fn beta_debug_tsqcon() {
    use super::*;
    // Simulate beta(body, I0) where body = TSqCon("T", "sq", [], TVar(1), TVar(0))
    // TVar(1) = free var from outer PLam, TVar(0) = bound by inner PLam
    let body = Term::TSqCon(
        "T".into(), "sq".into(), vec![],
        Box::new(Term::TVar(1)),
        Box::new(Term::TVar(0)),
    );
    let arg = Term::TInterval(I::I0);
    let result = beta(&body, &arg);
    eprintln!("beta result: {:?}", result);
    // Expected after removing the PLam binder:
    // TSqCon("T", "sq", [], TVar(0), I0)
    // where TVar(0) is the free var (originally at TVar(1))
    assert_eq!(result, Term::TSqCon(
        "T".into(), "sq".into(), vec![],
        Box::new(Term::TVar(0)),
        Box::new(Term::TInterval(I::I0)),
    ));
}
