/// Regression tests for `needs_io_wrap` (`lang/codegen/emit.mo`):
/// `IO.read_file`/`IO.file_exists`'s raw call result must be wrapped in a
/// real `IO.io`-tagged constructor before it can be used as an `IO` value,
/// same as `IO.println`/`IO.write_file` already were.
///
/// `is_void_native` was previously the ONLY signal deciding whether a
/// native op's result needed this wrap, conflating "the C function is
/// declared `void`" (true for `print_str`/`write_file`) with "the Monad
/// type is `IO _`" (also true for `read_file`/`file_exists`, which return
/// a real `char*`, not void). `read_file`/`file_exists`'s raw call result
/// was used AS-IS wherever an `IO` value was expected -- `Monad_IO_bind`'s
/// own generated body calls `monad_get_field(io_val, 0)` on it, misreading
/// the raw pointer as if it were a tagged constructor object.
///
/// Found while verifying `implementations/2026-08-29-native-io-op-non-
/// exhaustive-match-crash.md`'s own regression test more thoroughly than a
/// bare crash-freedom check: binding a native call's result via `<-` and
/// merely IGNORING it compiled/ran fine (no consumer ever touches the
/// mis-shaped value), but using it in ANY way afterward (a call argument,
/// a comparison) segfaulted or returned a silently wrong value --
/// confirmed pre-existing (unrelated to `write_file`) via `git worktree`
/// bisection, filed as
/// `implementations/2026-08-29-native-bind-result-use-crash.md`, then
/// root-caused and fixed here.
use io {IO}
use std.process {exec_cmd}
use lang.module {LoadedModules, load_file_modules}
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
    IO.write_file (Path.path src_path) source;

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
                    IO.write_file (Path.path ir_path) ir_text;

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

/// Binds `IO.read_file`'s result via `<-` and then ACTUALLY USES it
/// (passed as a real function argument, compared against a literal) --
/// the exact shape that used to segfault (or, for pure-value consumers,
/// silently misbehave) before `read_file`'s result was `IO.io`-wrapped.
#[test]
def test_read_file_bind_result_used_downstream : IO Bool :=
    let source := r#"use io {IO}
def main (args : List String) : IO I64 := do {
    let path := "/tmp/monad_e2e/io_result_wrap_fixture.txt";
    let content := "needs io wrap";
    IO.write_file_native path content;
    let read_back <- IO.read_file_native path;
    let matched := String.beq read_back content;
    let result := if matched then 1 else 0;
    return result
}
"# in
    compile_source_run_expect source "test_read_file_bind_result_used_downstream" 1

// NOTE: an equivalent `IO.file_exists` test was attempted here (same
// shape, `Bool`-producing instead of `String`-producing, to exercise
// `needs_io_wrap` for a different inner type) but found a SEPARATE,
// pre-existing, deeper bug: `monad_file_exists` (`lang/codegen/runtime.c`)
// returns a raw C string literal ("1" or NULL), not a real heap-allocated
// Bool constructor via `alloc_constructor` -- so `if exists then ... else
// ...` (which reads the value's TAG via `monad_get_tag`, expecting a
// genuine boxed Bool object) reads garbage from whatever address that
// static string happens to be at, not a real tag. Confirmed via direct
// repro: `IO.file_exists` on a file that genuinely exists still took the
// `else` branch. Unrelated to `needs_io_wrap`/this fix -- the IO-wrapping
// itself is correct either way, the INNER value it wraps is wrong. Not
// yet filed as its own dated plan; out of scope here.
