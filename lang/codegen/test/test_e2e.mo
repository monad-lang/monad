use lang.types
use lang.codegen.ir
use lang.codegen.emit

open Term
open Literal
open LLVMType
open LLVMValue
open LLVMInstruction
open Identifier
open NameRef
open NumSuffix
open Param
open Def
open ModulePath

@[test]
def test_e2e_simple_literal : Bool :=
    let id := Identifier.id "myfunc" in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id empty_ids))
        (Term.type_ 1)
        (Term.lit (Literal.num 42 NumSuffix.i64))
        empty_cons
        empty_attrs in
    let mod_ := lang.codegen.emit.compile_decls_ir (List.cons def_ empty_defs) in
    let text := emit_module mod_ in
    check_contains text "myfunc"

@[test]
def test_e2e_function_with_param : Bool :=
    let id := Identifier.id "add5" in
    let param := param_many (Identifier.id "x") (Term.type_ 1) in
    let body := Term.lit (Literal.num 99 NumSuffix.i64) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id empty_ids))
        (Term.type_ 1)
        (Term.lam param body)
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
    let def_ := Def.mk
        (ModulePath.mp (List.cons id empty_ids))
        (Term.type_ 1)
        (Term.lit (Literal.num 1 NumSuffix.i64))
        empty_cons
        empty_attrs in
    let mod_ := lang.codegen.emit.compile_decls_ir (List.cons def_ empty_defs) in
    let text := emit_module mod_ in
    check_contains text "cc 9"

@[partial]
def empty_defs : List Def := List.empty

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
