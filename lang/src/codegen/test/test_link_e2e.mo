use io {IO}
open IO {println, write_file}
use std.process {exec_cmd}
use lang.types {Def, i64, id, lit, mk, mp, num, type_}
use llvm.ir {emit_module, mk}
use llvm.link {compile_ir_to_obj, compile_runtime_obj, link_objects}
use runtime {}
use lang.codegen.emit {compile_db_decls_ir, mk}

open Term {lit, type_}
open Literal {num}
open Identifier {id}
open NumSuffix {i64}
open Param {mk}
open Def {mk}
open ModulePath {mp}

/// Build a minimal program: def main : I64 := 42
def build_main42 : List Def :=
    let id := Identifier.id "main" in
    let body := Term.lit (Literal.num 42 NumSuffix.i64) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (Term.type_ 1)
        body
        List.empty
        List.empty
        Visibility.package_private in
    List.cons def_ List.empty

/// Full e2e: compile 42 to LLVM IR, write file, run llc, link, execute.
def main : IO I64 {
    let output_dir := "/tmp";
    let output_name := "monad_test_42";

    let ir_path := String.concat output_dir (String.concat "/" (String.concat output_name ".ll"));
    let obj_path := String.concat output_dir (String.concat "/" (String.concat output_name ".o"));
    let runtime_obj := String.concat output_dir "/monad_runtime.o";
    let output_path := String.concat output_dir (String.concat "/" output_name);

    let defs := build_main42;

    let mod_ := lang.codegen.emit.compile_db_decls_ir defs;
    let ir_text := llvm.ir.emit_module mod_;

    // `ir_path` is always non-empty by construction -- `Path.path` directly.
    IO.write_file (Path.path ir_path) ir_text;

    let _llc <- compile_ir_to_obj ir_path obj_path;
    let _rt <- compile_runtime_obj Runtime.c_path [] runtime_obj;
    let _link <- link_objects [obj_path, runtime_obj] output_path [];

    let bin_args := List.empty;
    let exit_code <- exec_cmd output_path bin_args;
    IO.println (String.concat "exit code: " (I64.to_string exit_code));
    return exit_code
}
