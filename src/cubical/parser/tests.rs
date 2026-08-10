use super::grammar::Parser;
use super::lexer::{Lexer, TokenKind};
use super::*;
use crate::cubical::interval::I;
use crate::cubical::syntax::{Tactic, Term, show_term};

#[test]
fn parses_lambda_identity() {
    assert_eq!(
        parse_term("fun x => x").unwrap(),
        Term::TAbs("x".to_string(), Box::new(Term::TVar(0)))
    );
}

#[test]
fn parses_dependent_pi() {
    assert_eq!(
        parse_term("∀ (x : U0), x").unwrap(),
        Term::TPi(
            "x".to_string(),
            Box::new(Term::TUniv(0)),
            Box::new(Term::TVar(0))
        )
    );
}

#[test]
fn parses_path_lambda() {
    assert_eq!(
        parse_term("<i> i0").unwrap(),
        Term::PLam("i".to_string(), Box::new(Term::TInterval(I::I0)))
    );
}

#[test]
fn parses_path_application() {
    let mut parser = Parser::new(Lexer::new("p @ i0").lex().unwrap());
    parser.term_env.push("p".to_string());
    let term = parser.parse_term().unwrap();
    assert_eq!(
        term,
        Term::PApp(Box::new(Term::TVar(0)), Box::new(Term::TInterval(I::I0)))
    );
}

#[test]
fn parses_import_declaration() {
    let decls = parse_program("import \"foo.owl\"").unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::Import { path } => assert_eq!(path, "foo.owl"),
        _ => panic!("expected import declaration"),
    }
}

#[test]
fn parses_string_literal_with_escapes() {
    let tokens = Lexer::new("\"foo\\\"bar\\\\baz\"").lex().unwrap();
    assert_eq!(
        tokens[0].kind,
        TokenKind::String("foo\"bar\\baz".to_string())
    );
}

#[test]
fn import_without_string_is_parse_error() {
    let err = parse_program("import foo").unwrap_err();
    assert!(err.message.contains("string literal"));
}

#[test]
fn typecheck_program_rejects_import() {
    let err = typecheck_program("import \"foo.owl\"").unwrap_err();
    assert!(err.contains("import requires a file path"));
}

#[test]
fn parses_nat_declaration() {
    let decls = parse_program("inductive Nat where | zero : Nat | suc : Nat -> Nat").unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::Data(dt) => {
            assert_eq!(dt.name, "Nat");
            assert_eq!(dt.cons.len(), 2);
            assert_eq!(dt.cons[0].name, "zero");
            assert_eq!(dt.cons[1].name, "suc");
            assert_eq!(
                dt.cons[1].arg_tys,
                vec![Term::TData("Nat".to_string(), vec![])]
            );
        }
        _ => panic!("expected data declaration"),
    }
}

#[test]
fn parses_def_then_data() {
    let src = "def main : U1 := U0\ninductive Nat where | zero : Nat | suc : Nat -> Nat";
    let decls = parse_program(src).unwrap();
    assert_eq!(decls.len(), 2);
    match &decls[1] {
        Decl::Data(dt) => assert_eq!(dt.name, "Nat"),
        _ => panic!("expected data declaration"),
    }
}

#[test]
fn parses_named_hole() {
    let term = parse_term("?goal").unwrap();
    match term {
        Term::Meta(id) => {
            assert_eq!(
                crate::cubical::nbe::get_meta_name(id),
                Some("goal".to_string())
            );
        }
        _ => panic!("expected Meta, got {:?}", term),
    }
}

#[test]
fn parses_anonymous_hole() {
    let term = parse_term("?").unwrap();
    match term {
        Term::Meta(_) => {}
        _ => panic!("expected Meta, got {:?}", term),
    }
}

#[test]
fn pretty_prints_named_hole() {
    let term = parse_term("?goal").unwrap();
    let shown = show_term(&[], &term);
    assert!(shown.contains("?goal"), "got: {}", shown);
}

#[test]
fn parses_system_type() {
    let src = "[0 => U0, 1 => U1]";
    let term = parse_term(src).unwrap();
    match term {
        Term::TSystemType(sys) => {
            assert_eq!(sys.len(), 2);
        }
        other => panic!("expected TSystemType, got: {:?}", other),
    }
}

#[test]
fn system_type_in_function_type() {
    let src = "forall (_ : [0 => U0, 1 => U0]), U0";
    let term = parse_term(src).unwrap();
    match term {
        Term::TPi(_, _, _) => {}
        other => panic!("expected TPi, got: {:?}", other),
    }
}

#[test]
fn cofibration_subtyping_cumulativity() {
    let src = r#"
        def test1 : U0 := U0
    "#;
    let decls = parse_program(src).unwrap();
    assert_eq!(decls.len(), 1);
}

#[test]
fn parses_lean_style_declarations() {
    let src = "inductive Nat where\n| zero : Nat\n| succ : Nat -> Nat\n\
               def id : ∀ (A : Type), A -> A := fun (A : Type) (n : A) => n";
    let decls = parse_program(src).unwrap();
    assert_eq!(decls.len(), 2);
    assert!(matches!(&decls[0], Decl::Data(dt) if dt.name == "Nat"));
    assert!(matches!(&decls[1], Decl::Def { name, .. } if name == "id"));
    typecheck_program(src).expect("Lean-style declarations should typecheck");
}

#[test]
fn parses_unicode_binders() {
    assert!(matches!(
        parse_term("∀ (A : Type), A -> A").unwrap(),
        Term::TPi(_, _, _)
    ));
    assert!(matches!(
        parse_term("Σ (A : Type), A").unwrap(),
        Term::TSigma(_, _, _)
    ));
}

#[test]
fn rejects_retired_syntax_aliases() {
    for source in [
        "data Nat = | zero : Nat",
        "theorem id : Type = Type",
        "def id : Type = Type",
    ] {
        assert!(parse_program(source).is_err(), "should reject: {source}");
    }
    for source in [
        "\\x. x",
        "λx. x",
        "Π (A : Type). A",
        "Pi (A : Type). A",
        "Sigma (A : Type). A",
        "∃ (A : Type), A",
        "elim motive { | zero => body } scrutinee",
    ] {
        assert!(parse_term(source).is_err(), "should reject: {source}");
    }
}

#[test]
fn parses_data_then_def() {
    let src = "inductive Nat where | zero : Nat | suc : Nat -> Nat\ndef main : U1 := U0";
    let decls = parse_program(src).unwrap();
    assert_eq!(decls.len(), 2);
    match &decls[0] {
        Decl::Data(dt) => assert_eq!(dt.name, "Nat"),
        _ => panic!("expected data declaration"),
    }
    match &decls[1] {
        Decl::Def { name, .. } => assert_eq!(name, "main"),
        _ => panic!("expected def declaration"),
    }
}

#[test]
fn parses_two_defs() {
    let src = "def a : U0 := U0\ndef b : U0 := U0";
    let decls = parse_program(src).unwrap();
    assert_eq!(decls.len(), 2);
    match &decls[0] {
        Decl::Def { name, .. } => assert_eq!(name, "a"),
        _ => panic!("expected def declaration"),
    }
    match &decls[1] {
        Decl::Def { name, .. } => assert_eq!(name, "b"),
        _ => panic!("expected def declaration"),
    }
}

#[test]
fn parses_match() {
    let src = "match n return Nat with | zero => z | suc m => s";
    let mut parser = Parser::new(Lexer::new(src).lex().unwrap());
    parser.global_env = vec![
        "s".to_string(),
        "z".to_string(),
        "Nat".to_string(),
        "n".to_string(),
    ];
    let term = parser.parse_term().unwrap();
    match term {
        Term::TElim(motive, cases, scrut) => {
            assert_eq!(*scrut, Term::TVar(3));
            assert_eq!(
                *motive,
                Term::TAbs("n".to_string(), Box::new(Term::TVar(3)))
            );
            assert_eq!(cases.len(), 2);
            assert_eq!(cases[0].con, "zero");
            assert_eq!(cases[0].binders, Vec::<String>::new());
            assert_eq!(cases[1].con, "suc");
            assert_eq!(cases[1].binders, vec!["m".to_string()]);
        }
        _ => panic!("expected match to desugar to eliminator"),
    }
}

#[test]
fn parses_match_dependent_return_type() {
    let src = "match n return n with | zero => z | suc m => s";
    let mut parser = Parser::new(Lexer::new(src).lex().unwrap());
    parser.global_env = vec!["s".to_string(), "z".to_string(), "n".to_string()];
    let term = parser.parse_term().unwrap();
    match term {
        Term::TElim(motive, _, _) => {
            assert_eq!(
                *motive,
                Term::TAbs("n".to_string(), Box::new(Term::TVar(0)))
            );
        }
        _ => panic!("expected match to desugar to eliminator"),
    }
}

#[test]
fn parses_or_patterns() {
    let src = "match n return Nat with | zero | suc m => z";
    let mut parser = Parser::new(Lexer::new(src).lex().unwrap());
    parser.global_env = vec!["z".to_string(), "Nat".to_string(), "n".to_string()];
    let term = parser.parse_term().unwrap();
    match term {
        Term::TElim(_, cases, scrut) => {
            assert_eq!(*scrut, Term::TVar(2));
            assert_eq!(cases.len(), 2);
            assert_eq!(cases[0].con, "zero");
            assert_eq!(cases[0].binders, Vec::<String>::new());
            assert_eq!(cases[1].con, "suc");
            assert_eq!(cases[1].binders, vec!["m".to_string()]);
        }
        _ => panic!("expected match to desugar to eliminator"),
    }
}

fn parse_let_with_globals(src: &str, globals: &[&str]) -> Term {
    let mut parser = Parser::new(Lexer::new(src).lex().unwrap());
    parser.global_env = globals.iter().map(|s| s.to_string()).collect();
    parser.parse_term().unwrap()
}

#[test]
fn parses_let() {
    let term = parse_let_with_globals("let x := t in x", &["t"]);
    assert_eq!(
        term,
        Term::TApp(
            Box::new(Term::TAbs("x".to_string(), Box::new(Term::TVar(0)))),
            Box::new(Term::TVar(0))
        )
    );
}

#[test]
fn let_desugars_to_application_of_lambda() {
    let from_let = parse_let_with_globals("let x := a in b", &["a", "b"]);

    let mut parser = Parser::new(Lexer::new("(fun x => b) a").lex().unwrap());
    parser.global_env = vec!["a".to_string(), "b".to_string()];
    let from_lambda = parser.parse_term().unwrap();

    assert_eq!(from_let, from_lambda);
}

#[test]
fn parses_s1_declaration() {
    let decls =
        parse_program("inductive S1 where | base : S1 | loop : S1 [ base , base ]").unwrap();
    match &decls[0] {
        Decl::Data(dt) => {
            assert_eq!(dt.name, "S1");
            assert_eq!(dt.cons.len(), 1);
            assert_eq!(dt.pcons.len(), 1);
            assert_eq!(
                dt.pcons[0].face0,
                Term::TCon("S1".to_string(), "base".to_string(), vec![])
            );
        }
        _ => panic!("expected data declaration"),
    }
}

#[test]
fn round_trip_with_show_term() {
    let term = parse_term("fun x => (x , x)").unwrap();
    let printed = show_term(&[], &term);
    let reparsed = parse_term(&printed).unwrap();
    assert_eq!(term, reparsed);
}
#[test]
fn dependent_arrow_type_typechecks() {
    use crate::cubical::typechecker::infer;
    let ctx = Vec::new();
    let ty = parse_term("∀ (A : U0), A -> A").unwrap();
    let inferred = infer(&ctx, &ty).expect("type should be well-formed");
    assert_eq!(inferred, Term::TUniv(0));
}

#[test]
fn multi_binder_lambda_matches_nested() {
    let nested = parse_term("fun A => fun x => x").unwrap();
    let multi = parse_term("fun A x => x").unwrap();
    assert_eq!(nested, multi);
}

#[test]
fn id_definition_typechecks() {
    use crate::cubical::typechecker::{check, infer};
    let ctx = Vec::new();
    let ty = parse_term("∀ (A : U0), A -> A").unwrap();
    let val = parse_term("fun A x => x").unwrap();
    infer(&ctx, &ty).expect("id type");
    check(&ctx, &val, &ty).expect("id body");
}

#[test]
fn recursive_definition_parses() {
    let src = "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
               def plus : Nat -> Nat -> Nat := fun m n => plus";
    let decls = parse_program(src).expect("recursive def should parse");
    assert_eq!(decls.len(), 2);
}

#[test]
fn recursive_plus_case_parses_global_reference() {
    let src = "inductive Nat where | zero : Nat | suc : Nat -> Nat\n\
               def plus : Nat -> Nat -> Nat := fun m n => match m return Nat with \
               | zero => n | suc m' => suc (plus m' n)";
    let decls = parse_program(src).expect("recursive def should parse");
    assert_eq!(decls.len(), 2);
}

#[test]
fn cumulativity_universe_levels() {
    // Test cumulativity: a term inferred at a lower universe level should be
    // accepted at a higher universe level.
    use crate::cubical::typechecker::check;
    let ctx = Vec::new();

    // The identity lambda has inferred type ∀ (A : U0), A -> A : U0.
    // Check it against (A : U1) -> A -> A — should succeed because the
    // lambda just binds A and the body checks against the codomain.
    let val = parse_term("fun A x => x").unwrap();
    let ty = parse_term("∀ (A : U1), A -> A").unwrap();
    check(&ctx, &val, &ty).expect("identity should be accepted at type ∀ (A : U1), A -> A");

    // Negative: a term that doesn't match the expected Pi should fail.
    let val2 = parse_term("U0").unwrap();
    let result = check(&ctx, &val2, &ty);
    assert!(
        result.is_err(),
        "U0 should not be accepted at (A : U1) -> A -> A"
    );
}

#[test]
fn cumulativity_pi_types() {
    use crate::cubical::typechecker::check;
    let ctx = Vec::new();
    let val = parse_term("fun A x => x").unwrap();
    let ty = parse_term("∀ (A : U1), A -> A").unwrap();
    check(&ctx, &val, &ty)
        .expect("the lower-universe identity should be accepted at ∀ (A : U1), A -> A");
}

#[test]
fn cumulativity_sigma_types() {
    use crate::cubical::driver::run_str;
    // Σ components are covariant: B -> U0 <= B -> U1, and the first
    // component's universe is covariant too.
    run_str(
        r#"
        inductive Nat where | zero : Nat | suc : Nat -> Nat
        def pair0 : Σ (B : U0), B -> U0 := (Nat, fun x => Nat)
        def up0  : Σ (B : U1), B -> U1 := pair0
        "#,
    )
    .expect("sigma component cumulativity should typecheck");

    // Negative: the components are covariant, not contravariant.
    let err = run_str(
        r#"
        inductive Nat where | zero : Nat | suc : Nat -> Nat
        def pair1 : Σ (B : U0), B -> U1 := (Nat, fun x => Nat)
        def bad  : Σ (B : U0), B -> U0 := pair1
        "#,
    )
    .unwrap_err();
    assert!(
        err.to_string().contains("Type mismatch") || err.to_string().contains("not"),
        "negative sigma cumulativity should fail, got: {err}"
    );
}

#[test]
fn cumulativity_record_types() {
    use crate::cubical::driver::run_str;
    // A record holding a Σ at U0 can be coerced (via record update) into a
    // record holding the same Σ at U1, because record (datatype) parameters
    // are covariant.
    run_str(
        r#"
        inductive Nat where | zero : Nat | suc : Nat -> Nat
        record Box (A : Type) where field content : A
        def pair0 : Σ (B : U0), B -> U0 := (Nat, fun x => Nat)
        def b0 : Box (Σ (B : U0), B -> U0) := mkBox pair0
        def b1 : Box (Σ (B : U0), B -> U1) := b0 { content = pair0 }
        "#,
    )
    .expect("record param cumulativity should typecheck");

    // Negative: universes are not contravariant, so this must fail.
    let err = run_str(
        r#"
        inductive Nat where | zero : Nat | suc : Nat -> Nat
        record Box (A : Type) where field content : A
        def pair0 : Σ (B : U0), B -> U0 := (Nat, fun x => Nat)
        def b0 : Box (Σ (B : U0), B -> U0) := mkBox pair0
        def b1 : Box (Σ (B : U0), B -> U1) := b0 { content = pair0 }
        def bad : Box (Σ (B : U0), B -> U0) := b1 { content = pair0 }
        "#,
    )
    .unwrap_err();
    assert!(
        err.to_string().contains("Type mismatch") || err.to_string().contains("not"),
        "negative record cumulativity should fail, got: {err}"
    );
}

#[test]
fn record_params_referenced_inside_field_binders() {
    use crate::cubical::driver::run_str;
    // Regression test: a record whose parameter types depend on earlier
    // parameters, and whose field types reference parameters under a nested
    // binder (e.g. `add z` inside `forall (a : R), Path R (add z a) a`).
    // Previously the constructor-arg context shifted param types, producing
    // wrong de Bruijn indices (`Type mismatch expected #7 got #5`).
    run_str(
        r#"
        inductive Nat where | zero : Nat | suc : Nat -> Nat
        inductive Eq (A : Type) (x : A) (y : A) where | refl : Eq A x y

        record CR (R : Type) (z : R) (o : R) (add : R -> R -> R) where
          field add_0_l : forall (a : R), Eq R (add z a) a
          field add_0_r : forall (a : R), Eq R (add a z) a

        def mk : forall (R : Type), forall (z : R), forall (o : R),
          forall (add : R -> R -> R),
          (forall (a : R), Eq R (add z a) a) ->
          (forall (a : R), Eq R (add a z) a) -> CR R z o add :=
          fun R z o add l r => mkCR l r

        def use : forall (R : Type), forall (z : R), forall (o : R),
          forall (add : R -> R -> R),
          forall (C : CR R z o add),
          forall (a : R), Eq R (add z a) a :=
          fun R z o add C a => C.add_0_l a
        "#,
    )
    .expect("record field types referencing params under binders should typecheck");
}

#[test]
fn record_construction_with_params_under_field_binders() {
    use crate::cubical::driver::run_str;
    // Regression test: constructing a record value whose field types
    // reference the datatype parameters under the field's own binders (e.g.
    // `f a` inside `forall (a : A), Path A (f a) (f a)`).  The universe-level
    // check of the type annotation used to beta-substitute the parameters
    // from the head, which shifted all free variables and produced `Unit a`
    // (the `f` reference collapsed onto `A`), failing with
    // "Expected a Π-type, but found: U0".
    run_str(
        r#"
        inductive Unit where | tt : Unit
        def uf : Unit -> Unit := fun _ => Unit.tt

        record R (A : Type) (f : A -> A) where
          field g : forall (a : A), Path A (f a) (f a)

        def r : R Unit uf := mkR (fun a => <i> uf a)
        "#,
    )
    .expect("record construction with params referenced under field binders should typecheck");
}

#[test]
fn cumulativity_contravariant_datatype() {
    use crate::cubical::driver::run_str;
    // Bad (A) with `mkb : (A -> Nat) -> Bad A` is contravariant in A: the
    // parameter occurs in an arrow domain.  Covariant-only checking would
    // unsoundly accept `Bad U0 <= Bad U1` (it needs U1 <= U0, which is false).
    run_str(
        r#"
        inductive Nat where | zero : Nat | suc : Nat -> Nat
        inductive Bad (A : Type) where
          | mkb : (A -> Nat) -> Bad A
        def b1 : Bad U1 := mkb (fun x => zero)
        def good : Bad U0 := b1
        "#,
    )
    .expect("contravariant direction Bad U1 <= Bad U0 should typecheck");

    let err = run_str(
        r#"
        inductive Nat where | zero : Nat | suc : Nat -> Nat
        inductive Bad (A : Type) where
          | mkb : (A -> Nat) -> Bad A
        def b0 : Bad U0 := mkb (fun x => zero)
        def bad : Bad U1 := b0
        "#,
    )
    .unwrap_err();
    assert!(
        err.to_string().contains("Type mismatch") || err.to_string().contains("not"),
        "Bad U0 <= Bad U1 must be rejected for the contravariant datatype, got: {err}"
    );
}

#[test]
fn cumulativity_invariant_datatype() {
    use crate::cubical::driver::run_str;
    // A parameter occurring both positively and negatively makes the datatype
    // invariant: neither subtyping direction is allowed.
    let err = run_str(
        r#"
        inductive Nat where | zero : Nat | suc : Nat -> Nat
        inductive BadI (A : Type) where
          | mkb : A -> (A -> Nat) -> BadI A
        def c0 : BadI U0 := mkb Nat (fun x => zero)
        def bad : BadI U1 := c0
        "#,
    )
    .unwrap_err();
    assert!(
        err.to_string().contains("Type mismatch") || err.to_string().contains("not"),
        "BadI U0 <= BadI U1 must be rejected for the invariant datatype, got: {err}"
    );

    let err = run_str(
        r#"
        inductive Nat where | zero : Nat | suc : Nat -> Nat
        inductive BadI (A : Type) where
          | mkb : A -> (A -> Nat) -> BadI A
        def c1 : BadI U1 := mkb U0 (fun x => zero)
        def bad : BadI U0 := c1
        "#,
    )
    .unwrap_err();
    assert!(
        err.to_string().contains("Type mismatch") || err.to_string().contains("not"),
        "BadI U1 <= BadI U0 must be rejected for the invariant datatype, got: {err}"
    );
}

#[test]
fn cumulativity_nested_datatype_variance() {
    use crate::cubical::driver::run_str;
    // Foo (A) wraps `Bar A`, and Bar is contravariant in A; Foo inherits the
    // contravariance through the nested application.
    run_str(
        r#"
        inductive Nat where | zero : Nat | suc : Nat -> Nat
        inductive Bar (A : Type) where
          | b : (A -> Nat) -> Bar A
        inductive Foo (A : Type) where
          | mk : Bar A -> Foo A
        def f1 : Foo U1 := mk (b (fun x => zero))
        def good : Foo U0 := f1
        "#,
    )
    .expect("nested contravariant direction Foo U1 <= Foo U0 should typecheck");

    let err = run_str(
        r#"
        inductive Nat where | zero : Nat | suc : Nat -> Nat
        inductive Bar (A : Type) where
          | b : (A -> Nat) -> Bar A
        inductive Foo (A : Type) where
          | mk : Bar A -> Foo A
        def f0 : Foo U0 := mk (b (fun x => zero))
        def bad : Foo U1 := f0
        "#,
    )
    .unwrap_err();
    assert!(
        err.to_string().contains("Type mismatch") || err.to_string().contains("not"),
        "Foo U0 <= Foo U1 must be rejected (inherited contravariance), got: {err}"
    );
}

#[test]
fn data_universe_annotation_parses() {
    let src = "inductive D : U1 where | mk : D";
    let decls = parse_program(src).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::Data(dt) => {
            assert_eq!(dt.name, "D");
            assert_eq!(dt.universe_level, Some(1));
        }
        _ => panic!("expected data declaration"),
    }
}

#[test]
fn data_without_universe_annotation() {
    let src = "inductive Nat where | zero : Nat | suc : Nat -> Nat";
    let decls = parse_program(src).unwrap();
    match &decls[0] {
        Decl::Data(dt) => {
            assert_eq!(dt.universe_level, None);
        }
        _ => panic!("expected data declaration"),
    }
}

#[test]
fn parses_exact_tactic() {
    let term = parse_term("by exact fun x => x").unwrap();
    match term {
        Term::TBy(tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                Tactic::Exact(Term::TAbs(x, _)) => assert_eq!(x, "x"),
                other => panic!("expected exact tactic with lambda, got {:?}", other),
            }
        }
        other => panic!("expected TBy, got {:?}", other),
    }
}

#[test]
fn parses_semicolon_separated_tactics() {
    let term = parse_term("by intro x; exact x").unwrap();
    match term {
        Term::TBy(tactics) => {
            assert_eq!(tactics.len(), 2);
            assert!(matches!(&tactics[0], Tactic::Intro(names) if names == &vec!["x".to_string()]));
            assert!(matches!(&tactics[1], Tactic::Exact(Term::TVar(0))));
        }
        other => panic!("expected TBy, got {:?}", other),
    }
}

#[test]
fn parses_assumption_tactic() {
    let term = parse_term("by assumption").unwrap();
    match term {
        Term::TBy(tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(matches!(&tactics[0], Tactic::Assumption));
        }
        other => panic!("expected TBy, got {:?}", other),
    }
}

#[test]
fn parses_apply_tactic() {
    let mut parser = Parser::new(Lexer::new("by apply f").lex().unwrap());
    parser.term_env.push("f".to_string());
    let term = parser.parse_term().unwrap();
    match term {
        Term::TBy(tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(matches!(&tactics[0], Tactic::Apply(Term::TVar(0))));
        }
        other => panic!("expected TBy, got {:?}", other),
    }
}

#[test]
fn tactic_def_typechecks() {
    let src = r#"
        inductive Nat where
          | zero : Nat
          | suc : Nat -> Nat
        def id : ∀ (A : U0), A -> A := by intro A x; exact x
    "#;
    let decls = parse_program(src).unwrap();
    assert_eq!(decls.len(), 2);
}

#[test]
fn tactic_def_exact_typechecks() {
    let src = r#"
        inductive Nat where
          | zero : Nat
          | suc : Nat -> Nat
        def const : ∀ (A : U0), ∀ (B : U0), A -> B -> A := by intro A B a b; exact a
    "#;
    let decls = parse_program(src).unwrap();
    assert_eq!(decls.len(), 2);
}

#[test]
fn tactic_def_assumption_typechecks() {
    let src = r#"
        inductive Nat where
          | zero : Nat
          | suc : Nat -> Nat
        def id_nat : Nat -> Nat := by intro x; assumption
    "#;
    let decls = parse_program(src).unwrap();
    assert_eq!(decls.len(), 2);
}

#[test]
fn parses_constructor_less_datatype() {
    let src = "inductive Empty where";
    let decls = parse_program(src).unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::Data(dt) => {
            assert_eq!(dt.name, "Empty");
            assert!(dt.cons.is_empty());
            assert!(dt.pcons.is_empty());
            assert!(dt.sqcons.is_empty());
            assert!(dt.cellcons.is_empty());
        }
        _ => panic!("expected data declaration"),
    }
}

#[test]
fn parses_empty_match_elimination() {
    let src = "inductive Empty where\ndef absurd : forall (A : U0), Empty -> A := fun A e => match e return A with";
    let decls = parse_program(src).unwrap();
    assert_eq!(decls.len(), 2);
    match &decls[1] {
        Decl::Def { name, val, .. } => {
            assert_eq!(name, "absurd");
            match val {
                Term::TAbs(_, inner) => match inner.as_ref() {
                    Term::TAbs(_, body) => {
                        if let Term::TElim(motive, cases, scrut) = body.as_ref() {
                            assert!(cases.is_empty());
                            assert!(matches!(motive.as_ref(), Term::TAbs(_, _)));
                            assert!(matches!(scrut.as_ref(), Term::TVar(0)));
                        } else {
                            panic!("expected TElim, got: {:?}", body);
                        }
                    }
                    _ => panic!("expected inner TAbs"),
                },
                _ => panic!("expected outer TAbs"),
            }
        }
        _ => panic!("expected def declaration"),
    }
}
