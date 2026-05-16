use lang.types
use io
use process
use lang.codegen.ir
use lang.codegen.emit

open LLVMType
open LLVMValue

/// Generate LLVM IR text from a list of Defs.
def compile_defs_to_ir (defs : List Def) : String :=
    let module_ := compile_decls_ir defs in
    lang.codegen.ir.emit_module module_


/// Build a List String from four strings.
def args4 (a : String) (b : String) (c : String) (d : String) : List String :=
    List.cons a (List.cons b (List.cons c (List.cons d List.empty)))

/// An empty List String, explicitly typed to avoid forall leakage.
def empty_str_list : List String := List.empty

/// Full pipeline: compile Defs to IR, write to file, run llc,
/// compile runtime, link, run the binary, return exit code.
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

def main : IO I64 {
    IO.println "LLVM codegen linker module loaded. Use compile_and_run for e2e compilation.";
    return 0
}
