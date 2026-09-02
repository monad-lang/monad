/// Regression test for `validate_no_unwired_natives`'s fail-fast check
/// (`lang/codegen/emit.mo`): a reachable bodyless `#[native X]` def whose
/// X is wired nowhere must produce a `Result.err` naming the native
/// target and enclosing def, not a silently-miscompiled "return Unit"
/// stub that only surfaces as a runtime SIGSEGV in the resulting binary.
///
/// This exact bug class cost two multi-hour runtime-debugging sessions
/// before the check existed: `String.length` ("printed a garbage heap
/// address instead of `3`") and, much worse, the self-compiled v25
/// binary's immediate `monad_get_tag` SIGSEGV inside
/// `List_reverse_append` -- `String_to_list` had silently stubbed to
/// Unit, so `String.ends_with`/`String.reverse` pattern-matched a Unit
/// object and walked a wild pointer out of `monad_get_field`. Both were
/// structurally valid IR: `llc`'s verifier passes them, only running the
/// binary finds them. See `validate_no_unwired_natives`'s own doc
/// comment for the full story.
///
/// The test exercises the mechanism directly with a program-DECLARED
/// native that by construction has no runtime implementation, rather
/// than pinning any specific init/std native (which could later get
/// wired for real and silently flip this test to the wrong reason).
///
/// The unwired native MUST be reachable from `main` -- the check runs on
/// the REACHABLE decls only (see `validate_no_unwired_natives`'s own doc
/// comment), so an unreferenced `use_it` would be filtered out by
/// `filter_reachable_decls` before the check ever saw it, silently
/// passing for the wrong reason.
use io {IO}
use std.process {exec_cmd}
use lang.module {LoadedModules, load_file_modules}
use lang.codegen.emit {compile_loaded_modules_to_ir}

#[test]
def test_unwired_native_fails_fast : IO Bool := do {
    let output_dir := "/tmp/monad_e2e";
    let src_path := output_dir ++ "/unwired_native.mo";
    let source := r#"#[native definitely_not_a_real_native]
def use_it (x : I64) : I64
def main (args : List String) : IO I64 := do {
    let _ := use_it 42;
    return 0
}
"#;
    let _ <- exec_cmd "mkdir" ["-p", output_dir];
    IO.write_file (Path.path src_path) source;

    let loaded_result : Result String LoadedModules <- load_file_modules src_path;
    match loaded_result {
        Result.err e => do {
            IO.println ("test_unwired_native_fails_fast: failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            let _ <- exec_cmd "rm" ["-f", src_path];
            match mod_result {
                Result.err msg => do {
                    let names_native := String.contains msg "definitely_not_a_real_native";
                    let names_def := String.contains msg "use_it";
                    if names_native && names_def then return true
                    else do {
                        IO.println ("test_unwired_native_fails_fast: error message missing native/def name: " ++ msg);
                        return false
                    }
                },
                Result.ok _ => do {
                    IO.println "test_unwired_native_fails_fast: expected Result.err (native has no runtime implementation), got Result.ok";
                    return false
                },
            }
        },
    }
}