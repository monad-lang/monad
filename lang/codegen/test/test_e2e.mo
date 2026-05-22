use lang.types
use lang.codegen.ir
use lang.codegen.emit

open TermV0
open Literal
open LLVMType
open LLVMValue
open LLVMInstruction
open Identifier
open NameRef
open NumSuffix
open ParamV0
open DefV0
open ModulePath

@[test]
def test_e2e_simple_literal : Bool :=
    let id := Identifier.id "myfunc" in
    let def_ := DefV0.mk
        (ModulePath.mp (List.cons id empty_ids))
        (TermV0.type_ 1)
        (TermV0.lit (LiteralV0.num 42 NumSuffix.i64))
        empty_cons
        empty_attrs in
    let mod_ := lang.codegen.emit.compile_decls_ir (List.cons def_ empty_defs) in
    let text := emit_module mod_ in
    check_contains text "myfunc"

@[test]
def test_e2e_function_with_param : Bool :=
    let id := Identifier.id "add5" in
    let param := param_many_v0 (Identifier.id "x") (TermV0.type_ 1) in
    let body := TermV0.lit (LiteralV0.num 99 NumSuffix.i64) in
    let def_ := DefV0.mk
        (ModulePath.mp (List.cons id empty_ids))
        (TermV0.type_ 1)
        (TermV0.lam param body)
        empty_cons
        empty_attrs in
    let mod_ := lang.codegen.emit.compile_decls_ir (List.cons def_ empty_defs) in
    let text := emit_module mod_ in
    check_contains text "add5"

@[test]
def test_e2e_module_structure : Bool :=
    let mod_ := lang.codegen.emit.compile_decls_ir empty_defs in
    let text := emit_module mod_ in
    if check_contains text "; ModuleID"
    then check_contains text "Type Definitions"
    else false

@[test]
def test_e2e_runtime_decls_present : Bool :=
    let mod_ := lang.codegen.emit.compile_decls_ir empty_defs in
    let text := emit_module mod_ in
    check_contains text "monad_alloc"

@[test]
def test_e2e_calling_convention : Bool :=
    let id := Identifier.id "f" in
    let def_ := DefV0.mk
        (ModulePath.mp (List.cons id empty_ids))
        (TermV0.type_ 1)
        (TermV0.lit (LiteralV0.num 1 NumSuffix.i64))
        empty_cons
        empty_attrs in
    let mod_ := lang.codegen.emit.compile_decls_ir (List.cons def_ empty_defs) in
    let text := emit_module mod_ in
    check_contains text "cc 9"

@[partial]
def empty_defs : List DefV0 := List.empty

@[partial]
def empty_ids : List Identifier := List.empty

@[partial]
def empty_cons : List TypeConstraint := List.empty

@[partial]
def empty_attrs : List String := List.empty

@[partial]
def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text)) needle

def main : I64 := 42
