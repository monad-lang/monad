use lang.types {Def, app, i64, id, lam, lit, mk, mp, named, num, type_, var}
use io {IO}
use std.process {exec_cmd}
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

/// An empty List String, explicitly typed to avoid forall leakage.
#[partial]
def empty_str_list : List String := List.empty

/// Generate LLVM IR text from a list of Defs.
#[partial]
def compile_defs_to_ir (defs : List Def) : String :=
    let module_ := compile_db_decls_ir defs in
    lang.codegen.ir.emit_module module_

/// Full pipeline: compile Defs to IR, write to file, run llc,
/// compile runtime, link, run the binary, return exit code.
#[partial]
pub def compile_and_run (defs : List Def) (output_dir : Path) (output_name : Path) : IO I64 {
    // `Path.join` here is THE fix for the mangled-double-slash bug this
    // whole `Path` type exists to prevent -- see `lang/main.mo`'s own
    // `link_ir` doc comment.
    let target := Path.join output_dir output_name;
    let ir_path := Path.with_suffix target ".ll";
    let obj_path := Path.with_suffix target ".o";
    let runtime_obj := Path.join output_dir (Path.path "monad_runtime.o");
    let output_path := target;
    let ir_path_s := Path.to_string ir_path;
    let obj_path_s := Path.to_string obj_path;
    let runtime_obj_s := Path.to_string runtime_obj;
    let output_path_s := Path.to_string output_path;

    let ir_text := compile_defs_to_ir defs;

    IO.write_file ir_path ir_text;

    let _ <- exec_cmd "llc" (args4 "-filetype=obj" ir_path_s "-o" obj_path_s);
    let _ <- exec_cmd "clang" (args4 "-c" "lang/codegen/runtime.c" "-o" runtime_obj_s);
    let _ <- exec_cmd "clang" (args4 obj_path_s runtime_obj_s "-o" output_path_s);

    exec_cmd output_path_s empty_str_list
}

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

def main : IO I64 {
    IO.println "LLVM codegen linker module loaded. Use compile_and_run for e2e compilation.";
    return 0
}
