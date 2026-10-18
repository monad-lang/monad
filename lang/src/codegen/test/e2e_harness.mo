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
/// The llc/clang/link steps themselves are NOT reimplemented here: they
/// come from `llvm.link`, which the compiler's own CLI uses too. This file
/// had its own inlined copy of them until the llvm mote was extracted, and
/// the two had already drifted apart on flags.
///
/// Lives under `lang/src/codegen/test/` rather than `slow_tests/` because
/// both directories consume it and this is codegen test infrastructure;
/// cross-directory `use` resolves fine (search paths are anchored at the
/// repo root).
open IO {println}
use std::process {exec_cmd, process_id}
use lang::module {
  LoadedModules, extract_directory, load_file_modules, resolve_runtime_src,
}
use llvm::ir {emit_module}
use llvm::link {compile_ir_to_obj, compile_runtime_obj, link_objects}
use runtime {}
use lib::codegen::emit {compile_loaded_modules_to_ir}

/// Build `source` to a native binary through the self-hosted pipeline:
/// `Result.ok <binary path>` with the intermediates already removed, or
/// `Result.err <which stage failed>`. The caller runs and removes the
/// binary.
#[partial]
pub def build_source_binary (source : String) (basename : String) : IO (Result String String) := do {
    let output_dir := "/tmp/monad_e2e_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/" ++ basename ++ ".mo";
    let ir_path := output_dir ++ "/" ++ basename ++ ".ll";
    let obj_path := output_dir ++ "/" ++ basename ++ ".o";
    let runtime_obj := output_dir ++ "/" ++ basename ++ "_runtime.o";
    let output_path := output_dir ++ "/" ++ basename;

    exec_cmd "mkdir" ["-p", output_dir];
    IO.write_file (Path.path src_path) source;

    let loaded_result <- load_file_modules src_path false;
    match loaded_result {
        Result.err e => return (Result.err ("failed to load: " ++ e)),
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            match mod_result {
                Result.err e => return (Result.err ("failed to resolve class-method calls: " ++ e)),
                Result.ok mod_ => do {
                    let ir_text := emit_module mod_;
                    IO.write_file (Path.path ir_path) ir_text;

                    let llc_result <- compile_ir_to_obj ir_path obj_path;
                    if not (llc_result == 0) then do {
                        return (Result.err "llc failed")
                    } else do {
                        let runtime_src <- resolve_runtime_src (extract_directory src_path);
                        let rt_result <- compile_runtime_obj runtime_src [] runtime_obj;
                        if not (rt_result == 0) then do {
                            return (Result.err "compiling runtime failed")
                        } else do {
                            let link_result <- link_objects [obj_path, runtime_obj] output_path [];
                            exec_cmd "rm" ["-f", src_path, ir_path, obj_path, runtime_obj];
                            if not (link_result == 0) then do {
                                return (Result.err "clang linker failed")
                            } else do {
                                return (Result.ok output_path)
                            }
                        }
                    }
                },
            }
        },
    }
}

/// Build `source`, run the binary, and compare its exit code against
/// `expected`.
#[partial]
pub def compile_source_run_expect (source : String) (basename : String) (expected : I64) : IO Bool := do {
    let built <- build_source_binary source basename;
    match built {
        Result.err e => do {
            println (basename ++ ": " ++ e);
            return false
        },
        Result.ok bin => do {
            let exec_result <- exec_cmd bin [];
            exec_cmd "rm" ["-f", bin];
            println (basename ++ ": expected " ++ I64.to_string expected ++ ", got " ++ I64.to_string exec_result);
            return (exec_result == expected)
        },
    }
}

/// Like `compile_source_run_expect`, but the binary's stdout is piped
/// into `head -n 1`, which exits after the first line. `expected` is
/// compared against the BINARY's exit status (bash's `PIPESTATUS[0]`),
/// not head's: what a program does once its stdout reader has gone,
/// 141 being death by SIGPIPE.
#[partial]
pub def compile_source_run_piped_expect (source : String) (basename : String) (expected : I64) : IO Bool := do {
    let built <- build_source_binary source basename;
    match built {
        Result.err e => do {
            println (basename ++ ": " ++ e);
            return false
        },
        Result.ok bin => do {
            let exec_result <- exec_cmd "bash" ["-c", "\"$0\" | head -n 1 >/dev/null; exit \"${PIPESTATUS[0]}\"", bin];
            exec_cmd "rm" ["-f", bin];
            println (basename ++ ": expected " ++ I64.to_string expected ++ ", got " ++ I64.to_string exec_result);
            return (exec_result == expected)
        },
    }
}

/// Like `compile_source_run_expect`, but the binary's stdin is the output
/// of the shell command `feed` (`<feed> | bin`; the pipeline's status is
/// the binary's).
#[partial]
pub def compile_source_run_stdin_expect (source : String) (basename : String) (feed : String) (expected : I64) : IO Bool := do {
    let built <- build_source_binary source basename;
    match built {
        Result.err e => do {
            println (basename ++ ": " ++ e);
            return false
        },
        Result.ok bin => do {
            let exec_result <- exec_cmd "bash" ["-c", feed ++ " | \"$0\"", bin];
            exec_cmd "rm" ["-f", bin];
            println (basename ++ ": expected " ++ I64.to_string expected ++ ", got " ++ I64.to_string exec_result);
            return (exec_result == expected)
        },
    }
}
