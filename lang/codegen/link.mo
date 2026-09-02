use lang.types {Def, app, i64, id, lam, lit, mk, mp, named, num, type_, var}
use lang.codegen.ir {emit_module, mk}
use lang.codegen.emit {check_contains, compile_db_decls_ir, mk}

open Term {app, lam, lit, type_, var}
open Literal {num}
open Identifier {id}
open NumSuffix {i64}
open Param {mk}
open Def {mk}
open ModulePath {mp}

/// Build a List String from four strings.
#[partial]
def args4 (a : String) (b : String) (c : String) (d : String) : List String :=
    List.cons a (List.cons b (List.cons c (List.cons d List.empty)))

/// Generate LLVM IR text from a list of Defs.
#[partial]
def compile_defs_to_ir (defs : List Def) : String :=
    let module_ := compile_db_decls_ir defs in
    emit_module module_

#[test]
def test_link_compile_defs_to_ir : Bool :=
    let id_val := Identifier.id "test" in
    let x_id := Identifier.id "x" in
    let two := Term.lit (Literal.num 2 NumSuffix.i64) in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    let body := Term.app (Term.app add_var x_var) two in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) body in
    let def_ := Def.mk (ModulePath.mp (List.cons id_val List.empty)) (Term.type_ 1) term_ List.empty List.empty Visibility.package_private in
    let text := compile_defs_to_ir (List.cons def_ List.empty) in
    check_contains text "add i64"
