use io
open IO
use process
use lang.types
use lang.codegen.ir
use lang.codegen.emit

open LLVMType
open LLVMValue
open TermV0
open Literal
open Identifier
open NameRef
open NumSuffix
open Param
open Def
open ModulePath

/// Build a List String from four strings.
def args4 (a : String) (b : String) (c : String) (d : String) : List String :=
    List.cons a (List.cons b (List.cons c (List.cons d List.empty)))

/// Build a minimal program: def main : I64 := 42
def build_main42 : List Def :=
    let id := Identifier.id "main" in
    let body := TermV0.lit (LiteralV0.num 42 NumSuffix.i64) in
    let def_ := Def.mk
        (ModulePath.mp (List.cons id List.empty))
        (TermV0.type_ 1)
        body
        List.empty
        List.empty in
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

    let mod_ := lang.codegen.emit.compile_decls_ir defs;
    let ir_text := lang.codegen.ir.emit_module mod_;

    IO.write_file ir_path ir_text;

    let llc_args := args4 "-filetype=obj" ir_path "-o" obj_path;
    let _ <- exec_cmd "llc" llc_args;

    let rt_args := args4 "-c" "lang/codegen/runtime.c" "-o" runtime_obj;
    let _ <- exec_cmd "clang" rt_args;

    let ld_args := args4 obj_path runtime_obj "-o" output_path;
    let _ <- exec_cmd "clang" ld_args;

    let bin_args := List.empty;
    let exit_code <- exec_cmd output_path bin_args;
    IO.println (String.concat "exit code: " (I64.to_string exit_code));
    return exit_code
}
