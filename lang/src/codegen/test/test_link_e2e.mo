open IO {println, write_file}
use std::process {exec_cmd, process_id}
use lang::types {Def, i64, id, lit, num, package_private, sort_n}
use llvm::ir {emit_module}
use llvm::link {compile_ir_to_obj, compile_runtime_obj, link_objects}
use runtime {}
use lib::codegen::emit {compile_db_decls_ir}
use lib::module {resolve_runtime_src}

open Term {lit}
open Literal {num}
open Identifier {id}
open NumSuffix {i64}
open Param {mk}
open Def {mk}

/// Build a minimal program: def main : I64 := 42
def build_main42 : List Def :=
    let id := Identifier.id "main" in
    let body := Term.lit (Literal.num 42 NumSuffix.i64) in
    let def_ := Def.mk
        (NamePath.mk (List.cons id List.empty))
        (sort_n 1)
        body
        List.empty
        List.empty
        Visibility.package_private List.empty in
    List.cons def_ List.empty

/// Full e2e: compile 42 to LLVM IR, write file, run llc, link, execute.
def main : IO I64 {
    // Per-process output directory, like every other codegen harness
    // (`lang/src/codegen/test/e2e_harness.mo`, `compile_tests.mo`): a bare
    // `/tmp` would put `monad_test_42`, its `.ll`/`.o` and the shared
    // `monad_runtime.o` at fixed absolute paths, so two `monad test` runs
    // on one machine -- or this file alongside any of them -- would link
    // and execute each other's objects.
    let output_dir := "/tmp/monad_e2e_" ++ I64.to_string process_id;
    let output_name := "monad_test_42";

    exec_cmd "mkdir" ["-p", output_dir];

    let ir_path := String.concat output_dir (String.concat "/" (String.concat output_name ".ll"));
    let obj_path := String.concat output_dir (String.concat "/" (String.concat output_name ".o"));
    let runtime_obj := String.concat output_dir "/monad_runtime.o";
    let output_path := String.concat output_dir (String.concat "/" output_name);

    let defs := build_main42;

    let mod_ := compile_db_decls_ir defs;
    let ir_text := emit_module mod_;

    // `ir_path` is always non-empty by construction -- `Path.path` directly.
    IO.write_file (Path.path ir_path) ir_text;

    let _llc <- compile_ir_to_obj ir_path obj_path;
    // The C runtime comes from the shared resolver, like every other
    // consumer now: `Runtime.c_path` on its own is checkout-root-relative,
    // so it names nothing when the working directory is not that root. This
    // harness builds its program in memory rather than writing a source
    // file, so the working directory is the only anchor it has -- which is
    // what the resolver's workspace tier already uses.
    let runtime_src <- resolve_runtime_src "";
    let _rt <- compile_runtime_obj runtime_src [] runtime_obj;
    let _link <- link_objects [obj_path, runtime_obj] output_path [];

    let bin_args := List.empty;
    let exit_code <- exec_cmd output_path bin_args;
    IO.println (String.concat "exit code: " (I64.to_string exit_code));
    return exit_code
}
