use lang.types
use lang.codegen.ir
use lang.codegen.emit

open Term
open Literal
open Identifier
open DebugName
open NumSuffix
open Param
open Def
open ModulePath

/// Test that we can compile a simple function and verify it produces LLVM IR
@[test]
def test_compile_simple_function : Bool :=
    let id := Identifier.id "simple" in
    let body := Term.lit (Literal.num 42 NumSuffix.i64) in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "simple"

/// Test that we can compile a function with arithmetic
@[test]
def test_compile_arithmetic : Bool :=
    let id := Identifier.id "add_values" in
    let x_id := Identifier.id "x" in
    let one := Term.lit (Literal.num 1 NumSuffix.i64) in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    let body := Term.app (Term.app add_var x_var) one in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "add i64"

/// Test that we can compile multiple definitions
@[test]
def test_compile_multiple_defs : Bool :=
    let id1 := Identifier.id "const1" in
    let def1 := Def.mk
        (ModulePath.mp (List.cons id1 List.empty))
        (Term.type_ 1)
        (Term.lit (Literal.num 1 NumSuffix.i64))
        List.empty
        List.empty in
    let id2 := Identifier.id "const2" in
    let def2 := Def.mk
        (ModulePath.mp (List.cons id2 List.empty))
        (Term.type_ 1)
        (Term.lit (Literal.num 2 NumSuffix.i64))
        List.empty
        List.empty in
    let defs := List.cons def1 (List.cons def2 List.empty) in
    let mod_ := lang.codegen.emit.compile_db_decls_ir defs in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "const1" && check_contains text "const2"

/// Test that compilation produces valid LLVM module structure
@[test]
def test_llvm_module_structure : Bool :=
    let mod_ := lang.codegen.emit.compile_db_decls_ir List.empty in
    let text := lang.codegen.ir.emit_module mod_ in
    if check_contains text "; ModuleID"
    then check_contains text "Type Definitions"
    else false

@[partial]
def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text)) needle

def main : I64 := 42
