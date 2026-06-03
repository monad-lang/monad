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

/// Test compilation of less-than comparison
@[test]
def test_compile_less_than : Bool :=
    let id := Identifier.id "less_than" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let lt_var := Term.var 0 (DebugName.named (Identifier.id "I64_lt")) in
    let body := Term.app (Term.app lt_var x_var) y_var in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) (Term.lam (DebugName.named y_id) (Term.type_ 1) body) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "icmp slt i64"

/// Test compilation of greater-than comparison
@[test]
def test_compile_greater_than : Bool :=
    let id := Identifier.id "greater_than" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let gt_var := Term.var 0 (DebugName.named (Identifier.id "I64_gt")) in
    let body := Term.app (Term.app gt_var x_var) y_var in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) (Term.lam (DebugName.named y_id) (Term.type_ 1) body) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "icmp sgt i64"

/// Test compilation of not-equal comparison
@[test]
def test_compile_not_equal : Bool :=
    let id := Identifier.id "not_equal" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let ne_var := Term.var 0 (DebugName.named (Identifier.id "I64_ne")) in
    let body := Term.app (Term.app ne_var x_var) y_var in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) (Term.lam (DebugName.named y_id) (Term.type_ 1) body) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "icmp ne i64"

/// Test compilation of nested function application with multiple parameters
@[test]
def test_compile_multi_param_function : Bool :=
    let id := Identifier.id "add_three" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let z_id := Identifier.id "z" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let z_var := Term.var 2 (DebugName.named z_id) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    // x + y + z
    let add_xy := Term.app (Term.app add_var x_var) y_var in
    let body := Term.app (Term.app add_var add_xy) z_var in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) (
        Term.lam (DebugName.named y_id) (Term.type_ 1) (
        Term.lam (DebugName.named z_id) (Term.type_ 1) body)) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "add i64"

/// Test compilation of nested lambdas (currying)
@[test]
def test_compile_nested_lambdas : Bool :=
    let id := Identifier.id "make_adder" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 0 (DebugName.named y_id) in
    let add_var := Term.var 1 (DebugName.named (Identifier.id "I64_add")) in
    let inner_body := Term.app (Term.app add_var x_var) y_var in
    let inner_lam := Term.lam (DebugName.named y_id) (Term.type_ 1) inner_body in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) inner_lam in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "make_adder"

/// Test compilation with constant folding for arithmetic
@[test]
def test_compile_constant_folding : Bool :=
    let id := Identifier.id "const_add" in
    let five := Term.lit (Literal.num 5 NumSuffix.i64) in
    let three := Term.lit (Literal.num 3 NumSuffix.i64) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    let body := Term.app (Term.app add_var five) three in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    // Should be optimized to just return 8
    check_contains text "8"

/// Test compilation of if-then-else with greater-than condition
@[test]
def test_compile_if_with_gt : Bool :=
    let id := Identifier.id "if_gt_test" in
    let ten := Term.lit (Literal.num 10 NumSuffix.i64) in
    let five := Term.lit (Literal.num 5 NumSuffix.i64) in
    let gt_var := Term.var 0 (DebugName.named (Identifier.id "I64_gt")) in
    let cond := Term.app (Term.app gt_var ten) five in
    // if 10 > 5 then 100 else 200
    let then_val := Term.lit (Literal.num 100 NumSuffix.i64) in
    let else_val := Term.lit (Literal.num 200 NumSuffix.i64) in
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

/// Test compilation of constructor application
@[test]
def test_compile_constructor : Bool :=
    let id := Identifier.id "make_pair" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let pair_name := Identifier.id "Pair" in
    let pair_typ := ModulePath.mp (List.cons pair_name List.empty) in
    let pair_con := Con.mk pair_name pair_typ 2 (List.cons (Option.some x_var) (List.cons (Option.some y_var) List.empty)) in
    let body := Term.con pair_con in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) (Term.lam (DebugName.named y_id) (Term.type_ 1) body) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "make_pair"

/// Test compilation of nested let-like expressions via lambda application
@[test]
def test_compile_complex_expression : Bool :=
    let id := Identifier.id "complex" in
    let x_id := Identifier.id "x" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    let mul_var := Term.var 1 (DebugName.named (Identifier.id "I64_mul")) in
    // (x + 10) * (x + 20)
    let ten := Term.lit (Literal.num 10 NumSuffix.i64) in
    let twenty := Term.lit (Literal.num 20 NumSuffix.i64) in
    let add1 := Term.app (Term.app add_var x_var) ten in
    let add2 := Term.app (Term.app add_var x_var) twenty in
    let body := Term.app (Term.app mul_var add1) add2 in
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

/// Test compilation with all four arithmetic operations
@[test]
def test_compile_all_arithmetic : Bool :=
    let id := Identifier.id "arith_all" in
    let a_id := Identifier.id "a" in
    let b_id := Identifier.id "b" in
    let a_var := Term.var 0 (DebugName.named a_id) in
    let b_var := Term.var 1 (DebugName.named b_id) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    let sub_var := Term.var 0 (DebugName.named (Identifier.id "I64_sub")) in
    let mul_var := Term.var 0 (DebugName.named (Identifier.id "I64_mul")) in
    let div_var := Term.var 0 (DebugName.named (Identifier.id "I64_div")) in
    // (a + b) - (a * b) / a
    let add_ab := Term.app (Term.app add_var a_var) b_var in
    let mul_ab := Term.app (Term.app mul_var a_var) b_var in
    let div_mul_a := Term.app (Term.app div_var mul_ab) a_var in
    let body := Term.app (Term.app sub_var add_ab) div_mul_a in
    let term_ := Term.lam (DebugName.named a_id) (Term.type_ 1) (Term.lam (DebugName.named b_id) (Term.type_ 1) body) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "add i64" && check_contains text "sub i64" && 
    check_contains text "mul i64" && check_contains text "sdiv i64"

/// Test compilation of deeply nested if-then-else
@[test]
def test_compile_nested_if : Bool :=
    let id := Identifier.id "nested_if" in
    let one := Term.lit (Literal.num 1 NumSuffix.i64) in
    let two := Term.lit (Literal.num 2 NumSuffix.i64) in
    let eq_var := Term.var 0 (DebugName.named (Identifier.id "I64_eq")) in
    let lt_var := Term.var 0 (DebugName.named (Identifier.id "I64_lt")) in
    // if 1 == 2 then 10 else (if 1 < 2 then 20 else 30)
    let cond1 := Term.app (Term.app eq_var one) two in
    let cond2 := Term.app (Term.app lt_var one) two in
    let then_val1 := Term.lit (Literal.num 10 NumSuffix.i64) in
    let then_val2 := Term.lit (Literal.num 20 NumSuffix.i64) in
    let else_val2 := Term.lit (Literal.num 30 NumSuffix.i64) in
    let inner_if := Term.lit (Literal.if_ cond2 then_val2 else_val2) in
    let body := Term.lit (Literal.if_ cond1 then_val1 inner_if) in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    // Should contain multiple branch instructions
    check_contains text "br i1"

@[partial]
def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text)) needle

def main : I64 := 42
