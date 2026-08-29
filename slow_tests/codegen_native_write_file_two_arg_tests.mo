/// Regression tests for `NativeOp.op_write_file` reaching
/// `compile_native_app_db`'s 2-arg "inline native" fast path
/// (`lang/codegen/emit.mo`, `try_compile_inline_native_db` ->
/// `compile_native_app_db`).
///
/// `IO.write_file (path : String) (content : String) : IO Unit`
/// (`init/io.mo`) is a curried, saturated 2-arg call to a name registered
/// in `native_op_table`, so it reaches the SAME dispatch as `I64.add`-style
/// arithmetic ops -- but `compile_native_val`/`fold_native_const` (the
/// functions that dispatch used to call unconditionally) only cover the 8
/// arithmetic/comparison `NativeOp` variants, panicking the RUST HOST
/// INTERPRETER with `non-exhaustive match: NativeOp.op_write_file was
/// constructed but not covered by this match` the moment a real call
/// (`lang/main.mo`'s own `link_ir`: `IO.write_file ir_path ir_text;`) was
/// reached -- this blocked `bootstrap compile lang/main.mo monad`'s
/// self-compile, filed as `implementations/2026-08-29-native-io-op-non-
/// exhaustive-match-crash.md`.
///
/// Fixed by routing non-arithmetic ops in `compile_native_app_db` to
/// `emit_native_call2_instr`, which calls the real `monad_write_file`
/// runtime function -- special-cased to first compute the byte length via
/// `monad_string_length` (the C function's real signature is `(path, data,
/// len)`, `lang/codegen/runtime.c`, but the mo-level call only supplies 2
/// args), since a missing/garbage length silently corrupts the write
/// (reads whatever the register happened to hold) rather than crashing.
///
/// Uses non-literal (`let`-bound) path/content so this can't be hidden by
/// any constant-folding. The COMPILED half only proves the original crash
/// stays fixed (write, then a bare `return 0`); byte-exact content
/// verification happens in THIS (interpreted, Rust-host-run) test itself
/// afterward, reading the file the compiled binary wrote.
///
/// NOTE: the compiled program deliberately does NOT itself consume any
/// native call's `<-`-bound result (e.g. `let x <- IO.read_file p; ...
/// (use x) ...`, or `let n <- exec_cmd ...; return n`) -- isolating this
/// test found that doing so, in NATIVELY COMPILED code specifically,
/// either segfaults or silently returns the wrong value, even though
/// merely binding-and-ignoring such a result does not. This is a separate,
/// newly-found, not-yet-filed bug, unrelated to `write_file`'s own arity-2
/// dispatch gap -- out of scope here.
use io {IO}
use process {exec_cmd}
use lang.types {LoadedModules}
use lang.module {load_file_modules}
use lang.codegen.ir {emit_module}
use lang.codegen.emit {compile_loaded_modules_to_ir}

#[partial]
def compile_source_run_expect (source : String) (basename : String) (expected : I64) : IO Bool := do {
    let output_dir := "/tmp/monad_e2e";
    let src_path := output_dir ++ "/" ++ basename ++ ".mo";
    let ir_path := output_dir ++ "/" ++ basename ++ ".ll";
    let obj_path := output_dir ++ "/" ++ basename ++ ".o";
    let runtime_obj := output_dir ++ "/" ++ basename ++ "_runtime.o";
    let output_path := output_dir ++ "/" ++ basename;

    let _ <- exec_cmd "mkdir" ["-p", output_dir];
    IO.write_file src_path source;

    let loaded_result : Result String LoadedModules <- load_file_modules src_path;
    match loaded_result {
        Result.err e => do {
            IO.println (basename ++ ": failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            match mod_result {
                Result.err e => do {
                    IO.println (basename ++ ": failed to resolve class-method calls: " ++ e);
                    return false
                },
                Result.ok mod_ => do {
                    let ir_text := emit_module mod_;
                    IO.write_file ir_path ir_text;

                    let llc_result <- exec_cmd "llc" ["-filetype=obj", ir_path, "-o", obj_path];
                    if not (llc_result == 0) then do {
                        IO.println (basename ++ ": llc failed");
                        return false
                    } else do {
                        let rt_result <- exec_cmd "clang" ["-c", "lang/codegen/runtime.c", "-o", runtime_obj];
                        if not (rt_result == 0) then do {
                            IO.println (basename ++ ": compiling runtime failed");
                            return false
                        } else do {
                            let link_args := [obj_path, runtime_obj];
                            let link_result <- exec_cmd "clang" (List.append link_args ["-o", output_path]);
                            if not (link_result == 0) then do {
                                IO.println (basename ++ ": clang linker failed");
                                return false
                            } else do {
                                let exec_result <- exec_cmd output_path [];
                                let _ <- exec_cmd "rm" ["-f", src_path, ir_path, obj_path, runtime_obj, output_path];
                                IO.println (basename ++ ": expected " ++ I64.to_string expected ++ ", got " ++ I64.to_string exec_result);
                                return (exec_result == expected)
                            }
                        }
                    }
                },
            }
        },
    }
}

/// `IO.write_file path content;` as a bare do-block statement (exactly
/// `link_ir`'s own shape) with non-literal `path`/`content`. Guards the
/// original crash (compiled program must exit 0) AND a silently-wrong-
/// length write (the byte-exact content check after it).
#[test]
def test_write_file_two_arg_native_dispatch_roundtrip : IO Bool := do {
    let write_path := "/tmp/monad_e2e/write_file_roundtrip_out.txt";
    let content := "hello from the native write_file fast path";
    let source := r#"use io {IO}
def main (args : List String) : IO I64 := do {
    let path := "/tmp/monad_e2e/write_file_roundtrip_out.txt";
    let content := "hello from the native write_file fast path";
    IO.write_file path content;
    return 0
}
"#;
    let compiled_ok <- compile_source_run_expect source "test_write_file_two_arg_native_dispatch_roundtrip" 0;
    let written <- IO.read_file write_path;
    let content_matches := String.beq written content;
    return (compiled_ok && content_matches)
}
