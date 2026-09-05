/// Shared end-to-end codegen harness: write a `.mo` source string to
/// disk, run it through the self-hosted pipeline (load -> compile to
/// LLVM IR -> `llc` -> `clang` runtime -> link), execute the resulting
/// binary, and compare its exit code against `expected`.
///
/// This existed as EIGHT near-identical copies before (seven under
/// `slow_tests/`, one in `test_closure_capture_e2e.mo`) -- three
/// distinct hashes, but diffing them showed the only differences were
/// `println` vs `IO.println` and two comments. They are unified here.
///
/// Lives under `lang/codegen/test/` rather than `slow_tests/` because
/// both directories consume it and this is codegen test infrastructure;
/// cross-directory `use` resolves fine (search paths are anchored at the
/// repo root).
use io {IO}
open IO {println}
use std.process {exec_cmd, process_id}
use lang.module {LoadedModules, load_file_modules}
use lang.codegen.ir {emit_module}
use lang.codegen.emit {compile_loaded_modules_to_ir}

#[partial]
pub def compile_source_run_expect (source : String) (basename : String) (expected : I64) : IO Bool := do {
    let output_dir := "/tmp/monad_e2e_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/" ++ basename ++ ".mo";
    let ir_path := output_dir ++ "/" ++ basename ++ ".ll";
    let obj_path := output_dir ++ "/" ++ basename ++ ".o";
    let runtime_obj := output_dir ++ "/" ++ basename ++ "_runtime.o";
    let output_path := output_dir ++ "/" ++ basename;

    let _ <- exec_cmd "mkdir" ["-p", output_dir];
    IO.write_file (Path.path src_path) source;

    let loaded_result : Result String LoadedModules <- load_file_modules src_path;
    match loaded_result {
        Result.err e => do {
            println (basename ++ ": failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            match mod_result {
                Result.err e => do {
                    println (basename ++ ": failed to resolve class-method calls: " ++ e);
                    return false
                },
                Result.ok mod_ => do {
                    let ir_text := emit_module mod_;
                    IO.write_file (Path.path ir_path) ir_text;

                    let llc_result <- exec_cmd "llc" ["-filetype=obj", ir_path, "-o", obj_path];
                    if not (llc_result == 0) then do {
                        println (basename ++ ": llc failed");
                        return false
                    } else do {
                        let rt_result <- exec_cmd "clang" ["-c", "lang/codegen/runtime.c", "-o", runtime_obj];
                        if not (rt_result == 0) then do {
                            println (basename ++ ": compiling runtime failed");
                            return false
                        } else do {
                            let link_args := [obj_path, runtime_obj, "-lgc"];
                            let link_result <- exec_cmd "clang" (List.append link_args ["-o", output_path]);
                            if not (link_result == 0) then do {
                                println (basename ++ ": clang linker failed");
                                return false
                            } else do {
                                let exec_result <- exec_cmd output_path [];
                                let _ <- exec_cmd "rm" ["-f", src_path, ir_path, obj_path, runtime_obj, output_path];
                                println (basename ++ ": expected " ++ I64.to_string expected ++ ", got " ++ I64.to_string exec_result);
                                return (exec_result == expected)
                            }
                        }
                    }
                },
            }
        },
    }
}
