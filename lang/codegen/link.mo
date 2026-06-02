use lang.types
use io
use process
use lang.codegen.ir
use lang.codegen.emit

open LLVMType
open LLVMValue
open Term
open Literal
open Identifier
open NameRef
open NumSuffix
open Param
open Def
open ModulePath

/// Build a List String from four strings.
@[partial]
def args4 (a : String) (b : String) (c : String) (d : String) : List String :=
    List.cons a (List.cons b (List.cons c (List.cons d List.empty)))

/// An empty List String, explicitly typed to avoid forall leakage.
@[partial]
def empty_str_list : List String := List.empty

/// Generate LLVM IR text from a list of Defs.
@[partial]
def compile_defs_to_ir (defs : List Def) : String :=
    let module_ := compile_db_decls_ir defs in
    lang.codegen.ir.emit_module module_

/// Full pipeline: compile Defs to IR, write to file, run llc,
/// compile runtime, link, run the binary, return exit code.
@[partial]
def compile_and_run (defs : List Def) (output_dir : String) (output_name : String) : IO I64 {
    let ir_path := String.concat output_dir (String.concat "/" (String.concat output_name ".ll"));
    let obj_path := String.concat output_dir (String.concat "/" (String.concat output_name ".o"));
    let runtime_obj := String.concat output_dir "/monad_runtime.o";
    let output_path := String.concat output_dir (String.concat "/" output_name);

    let ir_text := compile_defs_to_ir defs;

    IO.write_file ir_path ir_text;

    let _ <- exec_cmd "llc" (args4 "-filetype=obj" ir_path "-o" obj_path);
    let _ <- exec_cmd "clang" (args4 "-c" "lang/codegen/runtime.c" "-o" runtime_obj);
    let _ <- exec_cmd "clang" (args4 obj_path runtime_obj "-o" output_path);

    exec_cmd output_path empty_str_list
}

@[test]
def test_link_compile_defs_to_ir : Bool :=
    let id_val := Identifier.id "test" in
    let x_id := Identifier.id "x" in
    let two := Term.lit (Literal.num 2 NumSuffix.i64) in
    let x_var := Term.var 0 (DebugName.named x_id) in
    let add_var := Term.var 0 (DebugName.named (Identifier.id "I64_add")) in
    let body := Term.app (Term.app add_var x_var) two in
    let term_ := Term.lam (DebugName.named x_id) (Term.type_ 1) body in
    let def_ := Def.mk (ModulePath.mp (List.cons id_val List.empty)) (Term.type_ 1) term_ List.empty List.empty in
    let text := compile_defs_to_ir (List.cons def_ List.empty) in
    check_contains text "add i64"

@[partial]
def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text)) needle

def main : IO I64 {
    IO.println "LLVM codegen linker module loaded. Use compile_and_run for e2e compilation.";
    return 0
}
