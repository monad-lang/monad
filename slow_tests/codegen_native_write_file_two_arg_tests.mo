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
use std.process {process_id}
use lang.codegen.test.e2e_harness {compile_source_run_expect}


/// `IO.write_file path content;` as a bare do-block statement (exactly
/// `link_ir`'s own shape) with non-literal `path`/`content`. Guards the
/// original crash (compiled program must exit 0) AND a silently-wrong-
/// length write (the byte-exact content check after it).
#[test]
def test_write_file_two_arg_native_dispatch_roundtrip : IO Bool := do {
    let write_path := "/tmp/monad_e2e_" ++ I64.to_string process_id ++ "/write_file_roundtrip_out.txt";
    let content := "hello from the native write_file fast path";
    let source := r#"use io {IO}
def main (args : List String) : IO I64 := do {
    let path := ""# ++ write_path ++ r#"";
    let content := "hello from the native write_file fast path";
    IO.write_file_native path content;
    return 0
}
"#;
    let compiled_ok <- compile_source_run_expect source "test_write_file_two_arg_native_dispatch_roundtrip" 0;
    let written <- IO.read_file (Path.path write_path);
    let content_matches := String.beq written content;
    return (compiled_ok && content_matches)
}
