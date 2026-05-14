use lang.types
use process
use lang.codegen.ir
use lang.codegen.emit

open LLVMType
open LLVMValue

/// Generate LLVM IR text from a list of Defs.
def compile_defs_to_ir (defs : List Def) : String :=
    let module_ := compile_decls_ir defs in
    lang.codegen.ir.emit_module module_

@[test]
def test_link_compile_defs_to_ir : Bool :=
    let id_val := lang.types.Identifier.id "test" in
    let nid := lang.types.NameRef.nid (lang.types.Identifier.id "I64_add") in
    let one := lang.types.Term.lit (lang.types.Literal.num 1 lang.types.NumSuffix.i64) in
    let two := lang.types.Term.lit (lang.types.Literal.num 2 lang.types.NumSuffix.i64) in
    let var_ := lang.types.Term.var nid in
    let app1 := lang.types.Term.app var_ one in
    let body := lang.types.Term.app app1 two in
    let def_ := lang.types.Def.mk (lang.types.ModulePath.mp (List.cons id_val List.empty)) (lang.types.Term.type_ 1) body List.empty List.empty in
    let text := compile_defs_to_ir (List.cons def_ List.empty) in
    check_contains text "add i64"

def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text)) needle

def main : I64 := 42
