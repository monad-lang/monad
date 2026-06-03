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

/// Test compilation of subtraction
@[test]
def test_compile_subtraction : Bool :=
    let id := Identifier.id "subtract" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let sub_var := Term.var 0 (DebugName.named (Identifier.id "I64_sub")) in
    let body := Term.app (Term.app sub_var x_var) y_var in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) (Term.lam (DebugName.named y_id) (Term.type_ 1) body) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "sub i64"

/// Test compilation of multiplication
@[test]
def test_compile_multiplication : Bool :=
    let id := Identifier.id "multiply" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let mul_var := Term.var 0 (DebugName.named (Identifier.id "I64_mul")) in
    let body := Term.app (Term.app mul_var x_var) y_var in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) (Term.lam (DebugName.named y_id) (Term.type_ 1) body) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "mul i64"

/// Test compilation of division
@[test]
def test_compile_division : Bool :=
    let id := Identifier.id "divide" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let div_var := Term.var 0 (DebugName.named (Identifier.id "I64_div")) in
    let body := Term.app (Term.app div_var x_var) y_var in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) (Term.lam (DebugName.named y_id) (Term.type_ 1) body) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "sdiv i64"

/// Test compilation of equality comparison
@[test]
def test_compile_equality : Bool :=
    let id := Identifier.id "equals" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let eq_var := Term.var 0 (DebugName.named (Identifier.id "I64_eq")) in
    let body := Term.app (Term.app eq_var x_var) y_var in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) (Term.lam (DebugName.named y_id) (Term.type_ 1) body) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "icmp eq i64"

/// Test compilation of nested arithmetic expressions
@[test]
def test_compile_nested_arithmetic : Bool :=
    let id := Identifier.id "nested" in
    let x_id := Identifier.id "x" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    let mul_var := Term.var 0 (DebugName.named (Identifier.id "I64_mul")) in
    let two := Term.lit (Literal.num 2 NumSuffix.i64) in
    let three := Term.lit (Literal.num 3 NumSuffix.i64) in
    // (x * 2) + 3
    let mul_result := Term.app (Term.app mul_var x_var) two in
    let body := Term.app (Term.app add_var mul_result) three in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "mul i64" && check_contains text "add i64"

/// Test compilation with string literals
@[test]
def test_compile_string_literal : Bool :=
    let id := Identifier.id "greet" in
    let body := Term.lit (Literal.str "hello") in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "hello"

/// Test that main function is renamed to main_monad
@[test]
def test_main_renaming : Bool :=
    let id := Identifier.id "main" in
    let body := Term.lit (Literal.num 0 NumSuffix.i64) in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "main_monad"

/// Test compilation with if-then-else (using native equality)
@[test]
def test_compile_if_then_else : Bool :=
    let id := Identifier.id "if_test" in
    let one := Term.lit (Literal.num 1 NumSuffix.i64) in
    let two := Term.lit (Literal.num 2 NumSuffix.i64) in
    let eq_var := Term.var 0 (DebugName.named (Identifier.id "I64_eq")) in
    let cond := Term.app (Term.app eq_var one) two in
    // if 1 == 2 then 10 else 20
    let then_val := Term.lit (Literal.num 10 NumSuffix.i64) in
    let else_val := Term.lit (Literal.num 20 NumSuffix.i64) in
    let body := Term.lit (Literal.if_ cond then_val else_val) in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    // Should contain branch instruction
    check_contains text "br i1"

@[partial]
def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text)) needle

def main : I64 := 42
