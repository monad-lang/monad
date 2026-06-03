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

/// Test compilation of boolean true literal (constructor)
@[test]
def test_compile_bool_true : Bool :=
    let id := Identifier.id "bool_true" in
    let bool_name := Identifier.id "Bool" in
    let bool_typ := ModulePath.mp (List.cons bool_name List.empty) in
    let true_con := Con.mk (Identifier.id "true") bool_typ 0 List.empty in
    let body := Term.con true_con in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "bool_true"

/// Test compilation of boolean false literal (constructor)
@[test]
def test_compile_bool_false : Bool :=
    let id := Identifier.id "bool_false" in
    let bool_name := Identifier.id "Bool" in
    let bool_typ := ModulePath.mp (List.cons bool_name List.empty) in
    let false_con := Con.mk (Identifier.id "false") bool_typ 0 List.empty in
    let body := Term.con false_con in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "bool_false"

/// Test compilation of Bool.not function call
@[test]
def test_compile_bool_not : Bool :=
    let id := Identifier.id "test_not" in
    let x_id := Identifier.id "x" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let bool_name := Identifier.id "Bool" in
    let bool_typ := ModulePath.mp (List.cons bool_name List.empty) in
    // Bool.not is a function: Bool -> Bool
    // We need to represent it as a variable reference
    let not_name := Identifier.id "Bool_not" in
    let not_var := Term.var 0 (DebugName.named not_name) in
    let body := Term.app not_var x_var in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "test_not"

/// Test compilation of if-then-else with boolean literals
@[test]
def test_compile_if_with_bool_literals : Bool :=
    let id := Identifier.id "if_bool" in
    let bool_name := Identifier.id "Bool" in
    let bool_typ := ModulePath.mp (List.cons bool_name List.empty) in
    let true_con := Con.mk (Identifier.id "true") bool_typ 0 List.empty in
    let true_val := Term.con true_con in
    let ten := Term.lit (Literal.num 10 NumSuffix.i64) in
    let twenty := Term.lit (Literal.num 20 NumSuffix.i64) in
    // if true then 10 else 20
    let body := Term.lit (Literal.if_ true_val ten twenty) in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "br i1"

/// Test compilation of List.empty constructor
@[test]
def test_compile_list_empty : Bool :=
    let id := Identifier.id "list_empty" in
    let list_name := Identifier.id "List" in
    let list_typ := ModulePath.mp (List.cons list_name List.empty) in
    let empty_con := Con.mk (Identifier.id "empty") list_typ 0 List.empty in
    let body := Term.con empty_con in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "list_empty"

/// Test compilation of List.cons constructor
@[test]
def test_compile_list_cons : Bool :=
    let id := Identifier.id "list_cons" in
    let x_id := Identifier.id "x" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let list_name := Identifier.id "List" in
    let list_typ := ModulePath.mp (List.cons list_name List.empty) in
    let empty_con := Con.mk (Identifier.id "empty") list_typ 0 List.empty in
    let empty_val := Term.con empty_con in
    let cons_name := Identifier.id "cons" in
    let cons_con := Con.mk cons_name list_typ 2 (List.cons (Option.some x_var) (List.cons (Option.some empty_val) List.empty)) in
    let body := Term.con cons_con in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "list_cons"

/// Test compilation of match expression with boolean
@[test]
def test_compile_match_bool : Bool :=
    let id := Identifier.id "match_bool" in
    let x_id := Identifier.id "x" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let bool_name := Identifier.id "Bool" in
    let bool_typ := ModulePath.mp (List.cons bool_name List.empty) in
    // Match on bool with cases for true and false
    let true_case := MatchCase.mc (Identifier.id "true") List.empty (Term.lit (Literal.num 1 NumSuffix.i64)) in
    let false_case := MatchCase.mc (Identifier.id "false") List.empty (Term.lit (Literal.num 0 NumSuffix.i64)) in
    let cases := List.cons true_case (List.cons false_case List.empty) in
    let body := Term.lit (Literal.match_ x_var cases) in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "match_bool"

/// Test compilation of recursive factorial function
@[test]
def test_compile_recursive_factorial : Bool :=
    let id := Identifier.id "factorial" in
    let n_id := Identifier.id "n" in
    let n_var := Term.var 0 (DebugName.named n_id) in
    let one := Term.lit (Literal.num 1 NumSuffix.i64) in
    let zero := Term.lit (Literal.num 0 NumSuffix.i64) in
    let eq_var := Term.var 0 (DebugName.named (Identifier.id "I64_eq")) in
    let mul_var := Term.var 0 (DebugName.named (Identifier.id "I64_mul")) in
    let sub_var := Term.var 0 (DebugName.named (Identifier.id "I64_sub")) in
    // Check if n == 0
    let cond := Term.app (Term.app eq_var n_var) zero in
    // if n == 0 then 1 else n * factorial (n - 1)
    let factorial_var := Term.var 1 (DebugName.named id) in
    let n_minus_1 := Term.app (Term.app sub_var n_var) one in
    let recursive_call := Term.app factorial_var n_minus_1 in
    let mul_result := Term.app (Term.app mul_var n_var) recursive_call in
    let body := Term.lit (Literal.if_ cond one mul_result) in
    let term_ := Term.lam (DebugName.named n_id) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "factorial"

/// Test compilation of nested boolean expressions
@[test]
def test_compile_nested_bool_expr : Bool :=
    let id := Identifier.id "nested_bool" in
    let a_id := Identifier.id "a" in
    let b_id := Identifier.id "b" in
    let a_var := Term.var 0 (DebugName.named a_id) in
    let b_var := Term.var 1 (DebugName.named b_id) in
    let bool_name := Identifier.id "Bool" in
    let bool_typ := ModulePath.mp (List.cons bool_name List.empty) in
    let true_con := Con.mk (Identifier.id "true") bool_typ 0 List.empty in
    let false_con := Con.mk (Identifier.id "false") bool_typ 0 List.empty in
    // Create a nested if: if a == true then (if b == true then true else false) else false
    let eq_var := Term.var 0 (DebugName.named (Identifier.id "I64_eq")) in
    let true_lit := Term.con true_con in
    let false_lit := Term.con false_con in
    let a_eq_true := Term.app (Term.app eq_var a_var) true_lit in
    let b_eq_true := Term.app (Term.app eq_var b_var) true_lit in
    let inner_if := Term.lit (Literal.if_ b_eq_true true_lit false_lit) in
    let body := Term.lit (Literal.if_ a_eq_true inner_if false_lit) in
    let term_ := Term.lam (DebugName.named a_id) (Term.type_ 1) (Term.lam (DebugName.named b_id) (Term.type_ 1) body) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "br i1"

/// Test compilation of Option.some constructor
@[test]
def test_compile_option_some : Bool :=
    let id := Identifier.id "option_some" in
    let x_id := Identifier.id "x" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let option_name := Identifier.id "Option" in
    let option_typ := ModulePath.mp (List.cons option_name List.empty) in
    let some_con := Con.mk (Identifier.id "some") option_typ 1 (List.cons (Option.some x_var) List.empty) in
    let body := Term.con some_con in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "option_some"

/// Test compilation of Option.none constructor
@[test]
def test_compile_option_none : Bool :=
    let id := Identifier.id "option_none" in
    let option_name := Identifier.id "Option" in
    let option_typ := ModulePath.mp (List.cons option_name List.empty) in
    let none_con := Con.mk (Identifier.id "none") option_typ 0 List.empty in
    let body := Term.con none_con in
    let term_ := Term.lam (DebugName.named (Identifier.id "x")) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "option_none"

/// Test compilation of Pair.pair constructor
@[test]
def test_compile_pair : Bool :=
    let id := Identifier.id "make_pair" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let pair_name := Identifier.id "Pair" in
    let pair_typ := ModulePath.mp (List.cons pair_name List.empty) in
    let pair_con := Con.mk (Identifier.id "pair") pair_typ 2 (List.cons (Option.some x_var) (List.cons (Option.some y_var) List.empty)) in
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

/// Test compilation of Result.ok constructor
@[test]
def test_compile_result_ok : Bool :=
    let id := Identifier.id "result_ok" in
    let x_id := Identifier.id "x" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let result_name := Identifier.id "Result" in
    let result_typ := ModulePath.mp (List.cons result_name List.empty) in
    let ok_con := Con.mk (Identifier.id "ok") result_typ 1 (List.cons (Option.some x_var) List.empty) in
    let body := Term.con ok_con in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "result_ok"

/// Test compilation of Result.err constructor
@[test]
def test_compile_result_err : Bool :=
    let id := Identifier.id "result_err" in
    let e_id := Identifier.id "e" in
    let e_var := Term.var 0 (DebugName.named e_id) in
    let result_name := Identifier.id "Result" in
    let result_typ := ModulePath.mp (List.cons result_name List.empty) in
    let err_con := Con.mk (Identifier.id "err") result_typ 1 (List.cons (Option.some e_var) List.empty) in
    let body := Term.con err_con in
    let term_ := Term.lam (DebugName.named e_id) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "result_err"

/// Test compilation with multiple nested constructors (Pair of Options)
@[test]
def test_compile_nested_constructors : Bool :=
    let id := Identifier.id "nested_pair_option" in
    let x_id := Identifier.id "x" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let pair_name := Identifier.id "Pair" in
    let pair_typ := ModulePath.mp (List.cons pair_name List.empty) in
    let option_name := Identifier.id "Option" in
    let option_typ := ModulePath.mp (List.cons option_name List.empty) in
    // Create some(5) and none
    let five := Term.lit (Literal.num 5 NumSuffix.i64) in
    let some_con := Con.mk (Identifier.id "some") option_typ 1 (List.cons (Option.some five) List.empty) in
    let some_val := Term.con some_con in
    let none_con := Con.mk (Identifier.id "none") option_typ 0 List.empty in
    let none_val := Term.con none_con in
    // Create pair(some(5), none)
    let pair_con := Con.mk (Identifier.id "pair") pair_typ 2 (List.cons (Option.some some_val) (List.cons (Option.some none_val) List.empty)) in
    let body := Term.con pair_con in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) body in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "nested_pair_option"

/// Test compilation of mutually recursive functions (even and odd)
@[test]
def test_compile_mutual_recursion : Bool :=
    let even_id := Identifier.id "even" in
    let odd_id := Identifier.id "odd" in
    let n_id := Identifier.id "n" in
    let n_var := Term.var 0 (DebugName.named n_id) in
    let zero := Term.lit (Literal.num 0 NumSuffix.i64) in
    let one := Term.lit (Literal.num 1 NumSuffix.i64) in
    let eq_var := Term.var 0 (DebugName.named (Identifier.id "I64_eq")) in
    let sub_var := Term.var 0 (DebugName.named (Identifier.id "I64_sub")) in
    // even(n) = if n == 0 then true else odd(n - 1)
    // odd(n) = if n == 1 then true else even(n - 1)
    let even_body := Term.lit (Literal.if_ (Term.app (Term.app eq_var n_var) zero) (Term.con (Con.mk (Identifier.id "true") (ModulePath.mp (List.cons (Identifier.id "Bool") List.empty)) 0 List.empty)) (Term.app (Term.var 1 (DebugName.named odd_id)) (Term.app (Term.app sub_var n_var) one))) in
    let even_term := Term.lam (DebugName.named n_id) (Term.type_ 1) even_body in
    let even_def := Def.mk (ModulePath.mp (List.cons even_id List.empty)) (Term.type_ 1) even_term List.empty List.empty in
    
    let odd_body := Term.lit (Literal.if_ (Term.app (Term.app eq_var n_var) one) (Term.con (Con.mk (Identifier.id "true") (ModulePath.mp (List.cons (Identifier.id "Bool") List.empty)) 0 List.empty)) (Term.app (Term.var 1 (DebugName.named even_id)) (Term.app (Term.app sub_var n_var) one))) in
    let odd_term := Term.lam (DebugName.named n_id) (Term.type_ 1) odd_body in
    let odd_def := Def.mk (ModulePath.mp (List.cons odd_id List.empty)) (Term.type_ 1) odd_term List.empty List.empty in
    
    let defs := List.cons even_def (List.cons odd_def List.empty) in
    let mod_ := lang.codegen.emit.compile_db_decls_ir defs in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "even" && check_contains text "odd"

/// Test compilation with complex control flow (multiple nested ifs and arithmetic)
@[test]
def test_compile_complex_control_flow : Bool :=
    let id := Identifier.id "complex_flow" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    let sub_var := Term.var 0 (DebugName.named (Identifier.id "I64_sub")) in
    let mul_var := Term.var 0 (DebugName.named (Identifier.id "I64_mul")) in
    let lt_var := Term.var 0 (DebugName.named (Identifier.id "I64_lt")) in
    let gt_var := Term.var 0 (DebugName.named (Identifier.id "I64_gt")) in
    let zero := Term.lit (Literal.num 0 NumSuffix.i64) in
    let ten := Term.lit (Literal.num 10 NumSuffix.i64) in
    // if x < 0 then (x + 10) * y else (if x > 0 then x * (y - 5) else y)
    let x_lt_zero := Term.app (Term.app lt_var x_var) zero in
    let x_plus_10 := Term.app (Term.app add_var x_var) ten in
    let mul_xy10 := Term.app (Term.app mul_var x_plus_10) y_var in
    let x_gt_zero := Term.app (Term.app gt_var x_var) zero in
    let y_minus_5 := Term.app (Term.app sub_var y_var) ten in
    let mul_xy5 := Term.app (Term.app mul_var x_var) y_minus_5 in
    let inner_if := Term.lit (Literal.if_ x_gt_zero mul_xy5 y_var) in
    let body := Term.lit (Literal.if_ x_lt_zero mul_xy10 inner_if) in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) (Term.lam (DebugName.named y_id) (Term.type_ 1) body) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "br i1"

/// Test compilation of constructor with multiple fields (3-element tuple via nested Pairs)
@[test]
def test_compile_triple : Bool :=
    let id := Identifier.id "triple" in
    let x_id := Identifier.id "x" in
    let y_id := Identifier.id "y" in
    let z_id := Identifier.id "z" in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let y_var := Term.var 1 (DebugName.named y_id) in
    let z_var := Term.var 2 (DebugName.named z_id) in
    let pair_name := Identifier.id "Pair" in
    let pair_typ := ModulePath.mp (List.cons pair_name List.empty) in
    // Create nested pairs: pair(x, pair(y, z))
    let inner_pair_con := Con.mk (Identifier.id "pair") pair_typ 2 (List.cons (Option.some y_var) (List.cons (Option.some z_var) List.empty)) in
    let inner_pair_val := Term.con inner_pair_con in
    let outer_pair_con := Con.mk (Identifier.id "pair") pair_typ 2 (List.cons (Option.some x_var) (List.cons (Option.some inner_pair_val) List.empty)) in
    let body := Term.con outer_pair_con in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) (Term.lam (DebugName.named y_id) (Term.type_ 1) (Term.lam (DebugName.named z_id) (Term.type_ 1) body)) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        term_
        List.empty
        List.empty in
    let mod_ := lang.codegen.emit.compile_db_decls_ir (List.cons def_ List.empty) in
    let text := lang.codegen.ir.emit_module mod_ in
    check_contains text "triple"

@[partial]
def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text)) needle

def main : I64 := 42
