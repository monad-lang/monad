/// The one test that used to live inline in `codegen::link`.

use lib::link {compile_defs_to_ir}
use lib::test::support {check_contains}
use lang::types {
    DebugName, Def, Identifier, Literal, NamePath, NumSuffix, SortLevel, Term,
    Visibility, binder_named,
}

#[test]
def test_link_compile_defs_to_ir : Bool :=
    let id_val := Identifier.id "test" in
    let x_id := Identifier.id "x" in
    let two := Term.lit (Literal.num 2 NumSuffix.i64) in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    let body := Term.app (Term.app add_var x_var) two in
    let term_ := Term.lam (binder_named x_id) (Term.sort (SortLevel.concrete 1)) body in
    let def_ := Def.mk (NamePath.mk [id_val]) (Term.sort (SortLevel.concrete 1)) term_ List.empty List.empty Visibility.package_private List.empty in
    let text := compile_defs_to_ir (List.cons def_ List.empty) in
    check_contains text "add i64"
