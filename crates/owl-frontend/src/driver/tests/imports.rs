use super::*;
use std::fs;
use std::io::Write;

#[test]
fn run_with_import_merges_declarations() {
    let dir = temp_dir("cubical_import_test");
    fs::create_dir_all(&dir).unwrap();

    let nat_path = dir.join("nat.owl");
    let main_path = dir.join("main.owl");

    fs::write(
        &nat_path,
        "inductive Nat where | zero : Nat | suc : Nat -> Nat\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import \"nat.owl\"\n\ndef main : Nat -> Nat := fun n => n\n",
    )
    .unwrap();

    let output = run(&main_path).expect("imported program should run");
    assert_eq!(output.name, "main");

    cleanup(&dir);
}

#[test]
fn run_reports_circular_import() {
    let dir = temp_dir("cubical_cycle_test");
    fs::create_dir_all(&dir).unwrap();

    let a_path = dir.join("a.owl");
    let b_path = dir.join("b.owl");

    let mut a_file = fs::File::create(&a_path).unwrap();
    writeln!(a_file, "import \"b.owl\"").unwrap();
    writeln!(a_file, "def a : U0 := U0").unwrap();

    let mut b_file = fs::File::create(&b_path).unwrap();
    writeln!(b_file, "import \"a.owl\"").unwrap();
    writeln!(b_file, "def b : U0 := U0").unwrap();

    let err = run(&a_path).unwrap_err();
    assert!(matches!(err, RunError::Import(_)));

    cleanup(&dir);
}

#[test]
fn run_aliased_import_qualifies_names() {
    let dir = temp_dir("cubical_alias_test");
    fs::create_dir_all(&dir).unwrap();

    let arith_path = dir.join("arith.owl");
    let main_path = dir.join("main.owl");

    fs::write(
        &arith_path,
        "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
         def add : Nat -> Nat -> Nat := fun m n => match m return Nat with\n\
         \x20 | zero => n\n  | suc m' => suc (add m' n)\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import \"arith.owl\" as A\n\
         def four : A.Nat := A.add (A.suc (A.suc A.zero)) (A.suc (A.suc A.zero))\n",
    )
    .unwrap();

    let output = run(&main_path).expect("aliased import should run");
    assert_eq!(output.name, "four");

    cleanup(&dir);
}

#[test]
fn run_nested_modules_and_aliased_folding() {
    let dir = temp_dir("cubical_module_test");
    fs::create_dir_all(&dir).unwrap();

    let outer_path = dir.join("outer.owl");
    let plain_path = dir.join("plain.owl");
    let aliased_path = dir.join("aliased.owl");

    // Library with nested modules; self-references are unqualified so the
    // file works both plainly imported and folded under an alias.
    fs::write(
        &outer_path,
        "module Outer where\n\
         \x20 module Inner where\n\
         \x20   inductive T where\n\
         \x20     | mk : T\n\
         \x20 end\n\
         \x20 def get : T := mk\n\
         end\n",
    )
    .unwrap();
    // Plain import keeps the file's own module names.
    fs::write(
        &plain_path,
        "import \"outer.owl\"\n\
         def v : Outer.Inner.T := Outer.Inner.mk\n\
         def w : Outer.Inner.T := Outer.get\n",
    )
    .unwrap();
    // Aliased import folds the file's modules into the alias, so nested
    // datatypes become `O.T` (flattened) — visible unqualified as `T`.
    fs::write(
        &aliased_path,
        "import \"outer.owl\" as O\n\
         def v : O.T := O.mk\n\
         def w : O.T := O.get\n",
    )
    .unwrap();

    let plain = run(&plain_path).expect("plain nested import should run");
    assert_eq!(plain.name, "w");
    let aliased = run(&aliased_path).expect("aliased nested import should run");
    assert_eq!(aliased.name, "w");

    cleanup(&dir);
}

#[test]
fn run_selective_import_keeps_selected_names() {
    let dir = temp_dir("cubical_only_test");
    fs::create_dir_all(&dir).unwrap();

    let arith_path = dir.join("arith.owl");
    let main_path = dir.join("main.owl");

    fs::write(
        &arith_path,
        "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
         def add : Nat -> Nat -> Nat := fun m n => match m return Nat with\n\
         \x20 | zero => n\n  | suc m' => suc (add m' n)\n\
         def sub : Nat -> Nat -> Nat := fun m n => m\n",
    )
    .unwrap();
    // `Nat` and `add` are listed (dependencies included); `sub` is not
    // selected and must be invisible afterwards.
    fs::write(
        &main_path,
        "import \"arith.owl\" only [Nat, add]\n\
         def two : Nat := add (suc zero) (suc zero)\n",
    )
    .unwrap();

    let output = run(&main_path).expect("selective import should run");
    assert_eq!(output.name, "two");

    cleanup(&dir);
}

#[test]
fn run_selective_import_hides_unselected_names() {
    let dir = temp_dir("cubical_only_hide_test");
    fs::create_dir_all(&dir).unwrap();

    let arith_path = dir.join("arith.owl");
    let main_path = dir.join("main.owl");

    fs::write(
        &arith_path,
        "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
         def add : Nat -> Nat -> Nat := fun m n => match m return Nat with\n\
         \x20 | zero => n\n  | suc m' => suc (add m' n)\n",
    )
    .unwrap();
    // `zero`/`suc` are not in the selection, so referencing them must fail.
    fs::write(
        &main_path,
        "import \"arith.owl\" only [add]\n\
         def bad : U0 := zero\n",
    )
    .unwrap();

    assert!(
        run(&main_path).is_err(),
        "unselected imported name should not resolve"
    );

    cleanup(&dir);
}

#[test]
fn run_selective_import_module_member_selection() {
    let dir = temp_dir("cubical_only_module_test");
    fs::create_dir_all(&dir).unwrap();

    let lib_path = dir.join("lib.owl");
    let member_path = dir.join("member.owl");
    let module_path = dir.join("module_sel.owl");

    fs::write(
        &lib_path,
        "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
         module M where\n\
         \x20 def one : Nat := suc zero\n\
         end\n",
    )
    .unwrap();
    // Selecting a dotted member path keeps just that declaration.
    fs::write(
        &member_path,
        "import \"lib.owl\" only [Nat, M.one]\n\
         def v : Nat := M.one\n",
    )
    .unwrap();
    // Selecting the whole module keeps everything inside it.
    fs::write(
        &module_path,
        "import \"lib.owl\" only [Nat, M]\n\
         def v : Nat := M.one\n",
    )
    .unwrap();

    let out1 = run(&member_path).expect("dotted member selection should run");
    assert_eq!(out1.name, "v");
    let out2 = run(&module_path).expect("whole-module selection should run");
    assert_eq!(out2.name, "v");

    cleanup(&dir);
}

#[test]
fn run_selective_import_avoids_name_collisions() {
    let dir = temp_dir("cubical_only_collision_test");
    fs::create_dir_all(&dir).unwrap();

    // Two libraries exposing a same-named `helper`; selective imports pull
    // disjoint members from each so both coexist.
    let a_path = dir.join("liba.owl");
    let b_path = dir.join("libb.owl");
    let main_path = dir.join("main.owl");

    fs::write(
        &a_path,
        "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
         def helper : Nat -> Nat := fun n => suc n\n\
         def from_a : Nat -> Nat := fun n => helper n\n",
    )
    .unwrap();
    fs::write(
        &b_path,
        "inductive Bool where | true : Bool | false : Bool\n\
         def helper : Bool -> Bool := fun b => b\n\
         def from_b : Bool -> Bool := fun b => helper b\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import \"liba.owl\" only [Nat, suc, zero, from_a]\n\
         import \"libb.owl\" only [Bool, false, from_b]\n\
         def va : Nat := from_a (suc zero)\n\
         def vb : Bool := from_b false\n",
    )
    .unwrap();

    // The collision-prone `helper` names are never both exposed: each
    // import only merges its selected (visible) members.
    let output = run(&main_path).expect("disjoint selective imports should run");
    assert_eq!(output.name, "vb");

    cleanup(&dir);
}

#[test]
fn run_same_name_imports_from_different_files_rejected() {
    // Even byte-identical content conflicts when two different files
    // claim the same name: provenance is the disambiguation criterion,
    // not content. Re-merges of the SAME file (diamond imports) are
    // tolerated because origins track the defining file.
    let dir = temp_dir("cubical_dup_ok_test");
    fs::create_dir_all(&dir).unwrap();

    let shared_body = "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
                       def add : Nat -> Nat -> Nat := fun m n => match m return Nat with\n\
                       \x20 | zero => n\n  | suc m' => suc (add m' n)\n";
    let shared_path = dir.join("shared.owl");
    let a_path = dir.join("dupa.owl");
    let b_path = dir.join("dupb.owl");
    let main_path = dir.join("main.owl");

    fs::write(&shared_path, shared_body).unwrap();
    // dupa and dupb each pull Nat/add from shared.owl (single origin) but
    // both declare their own `double`, so it exists under two defining
    // files — a genuine conflict even though the texts are identical.
    let double_def = "def double : Nat -> Nat := fun n => add n n\n";
    fs::write(&a_path, format!("import \"shared.owl\"\n{double_def}")).unwrap();
    fs::write(&b_path, format!("import \"shared.owl\"\n{double_def}")).unwrap();
    fs::write(
        &main_path,
        "import \"dupa.owl\"\n\
         import \"dupb.owl\"\n\
         def main : U0 -> U0 := fun A => A\n",
    )
    .unwrap();

    match run(&main_path) {
        Err(RunError::Import(msg)) => {
            assert!(
                msg.contains("double"),
                "error should name the conflicting symbol, got: {}",
                msg
            );
        }
        other => panic!(
            "expected import conflict error, got: {:?}",
            other.map(|o| o.name)
        ),
    }

    cleanup(&dir);
}

#[test]
fn run_diamond_import_of_same_file_tolerated() {
    // main imports da.owl and db.owl; both import shared.owl. shared's
    // names arrive twice but from the same defining file, so no conflict.
    let dir = temp_dir("cubical_diamond_test");
    fs::create_dir_all(&dir).unwrap();

    let shared_path = dir.join("shared.owl");
    let a_path = dir.join("da.owl");
    let b_path = dir.join("db.owl");
    let main_path = dir.join("main.owl");

    fs::write(&shared_path, "def idty : U0 -> U0 := fun A => A\n").unwrap();
    fs::write(
        &a_path,
        "import \"shared.owl\"\ndef a_v : U0 -> U0 := idty\n",
    )
    .unwrap();
    fs::write(
        &b_path,
        "import \"shared.owl\"\ndef b_v : U0 -> U0 := idty\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import \"da.owl\"\n\
         import \"db.owl\"\n\
         def main : U0 -> U0 := idty\n",
    )
    .unwrap();

    let output = run(&main_path).expect("diamond import of same file should unify");
    assert_eq!(output.name, "main");

    cleanup(&dir);
}

#[test]
fn run_conflicting_imported_definitions_rejected() {
    let dir = temp_dir("cubical_dup_bad_test");
    fs::create_dir_all(&dir).unwrap();

    let nat_decl = "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n";
    let a_path = dir.join("confa.owl");
    let b_path = dir.join("confb.owl");
    let main_path = dir.join("main.owl");

    fs::write(
        &a_path,
        format!("{nat_decl}def helper : Nat -> Nat := fun n => suc n\n"),
    )
    .unwrap();
    fs::write(
        &b_path,
        // confa's declarations arrive transitively (same origin, no
        // conflict); confb's own `helper` genuinely differs.
        "import \"confa.owl\"\ndef helper : Nat -> Nat := fun n => suc (suc n)\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import \"confa.owl\"\n\
         import \"confb.owl\"\n\
         def main : U0 -> U0 := fun A => A\n",
    )
    .unwrap();

    match run(&main_path) {
        Err(RunError::Import(msg)) => {
            assert!(
                msg.contains("helper"),
                "error should name the conflicting symbol, got: {}",
                msg
            );
        }
        other => panic!(
            "expected import conflict error, got: {:?}",
            other.map(|o| o.name)
        ),
    }

    cleanup(&dir);
}

#[test]
fn run_conflicting_imported_datatypes_rejected() {
    let dir = temp_dir("cubical_dup_dt_test");
    fs::create_dir_all(&dir).unwrap();

    let a_path = dir.join("dta.owl");
    let b_path = dir.join("dtb.owl");
    let main_path = dir.join("main.owl");

    fs::write(&a_path, "inductive Mode where | on : Mode | off : Mode\n").unwrap();
    fs::write(
        &b_path,
        "inductive Mode where | on : Mode | flip : Mode -> Mode\n",
    )
    .unwrap();
    fs::write(
        &main_path,
        "import \"dta.owl\"\n\
         import \"dtb.owl\"\n\
         def main : U0 -> U0 := fun A => A\n",
    )
    .unwrap();

    match run(&main_path) {
        Err(RunError::Import(msg)) => {
            assert!(
                msg.contains("'Mode'"),
                "error should name the conflicting datatype, got: {}",
                msg
            );
        }
        other => panic!(
            "expected import conflict error, got: {:?}",
            other.map(|o| o.name)
        ),
    }

    cleanup(&dir);
}

#[test]
fn run_parameterized_module_defs_typecheck_and_compute() {
    // Defs inside `module M (A : Type) where` become globals closed over
    // the parameter; sibling references apply it automatically; consumers
    // instantiate explicitly.
    let src = "\
inductive Nat where\n\
 \x20 | zero : Nat\n\
 \x20 | suc : Nat -> Nat\n\
def one : Nat := suc zero\n\
module Semi (A : Type) where\n\
 \x20 def idty : A -> A := fun x => x\n\
 \x20 def twice_id : A -> A := fun x => idty (idty x)\n\
end\n\
def v : Nat := ((Semi.twice_id Nat) one)\n\
def main : Nat := v\n";

    let output = run_str(src).expect("parameterized module program should run");
    assert_eq!(output.name, "main");
}

#[test]
fn run_parameterized_module_rejects_datatype_inside() {
    let src = "\
module M (A : Type) where\n\
 \x20 inductive T where | mk : T\n\
end\n";
    assert!(
        run_str(src).is_err(),
        "datatype in parameterized module must be rejected"
    );
}

#[test]
fn run_aliased_import_folds_parameterized_module_member() {
    let dir = temp_dir("cubical_param_alias_test");
    fs::create_dir_all(&dir).unwrap();

    let lib_path = dir.join("plib.owl");
    let plain_path = dir.join("plain.owl");
    let aliased_path = dir.join("aliased.owl");

    fs::write(
        &lib_path,
        "inductive Nat where\n  | zero : Nat\n  | suc : Nat -> Nat\n\
         module Semi (A : Type) where\n\
         \x20 def idty : A -> A := fun x => x\n\
         end\n",
    )
    .unwrap();
    // Plain import keeps the module path: Semi.idty.
    fs::write(
        &plain_path,
        "import \"plib.owl\"\n\
         def v : Nat := ((Semi.idty Nat) (suc zero))\n",
    )
    .unwrap();
    // Aliased import folds the file's own modules: P.idty.
    fs::write(
        &aliased_path,
        "import \"plib.owl\" as P\n\
         def v : P.Nat := ((P.idty P.Nat) (P.suc P.zero))\n",
    )
    .unwrap();

    let out1 = run(&plain_path).expect("plain import of param-module lib should run");
    assert_eq!(out1.name, "v");
    let out2 = run(&aliased_path).expect("aliased folding of param module should run");
    assert_eq!(out2.name, "v");

    cleanup(&dir);
}

#[test]
fn run_module_instantiation_typechecks_and_computes() {
    // Parameterized instantiation: N.x behaves like the source member at
    // the given arguments, without explicit parameter application.
    let src = "\
inductive Nat where\n\
 \x20 | zero : Nat\n\
 \x20 | suc : Nat -> Nat\n\
def one : Nat := suc zero\n\
module Semi (A : Type) where\n\
 \x20 def idty : A -> A := fun x => x\n\
end\n\
module NatSemi = Semi (Nat)\n\
def v : Nat := (NatSemi.idty one)\n\
def main : Nat := v\n";

    let output = run_str(src).expect("instantiated module program should run");
    assert_eq!(output.name, "main");
}

#[test]
fn run_module_instantiation_of_plain_module() {
    let src = "\
inductive Nat where\n\
 \x20 | zero : Nat\n\
 \x20 | suc : Nat -> Nat\n\
module Plain where\n\
 \x20 def two : Nat := suc (suc zero)\n\
end\n\
module N2 = Plain\n\
def v : Nat := N2.two\n\
def main : Nat := v\n";

    let output = run_str(src).expect("plain module instantiation should run");
    assert_eq!(output.name, "main");
}
