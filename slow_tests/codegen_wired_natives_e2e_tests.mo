/// End-to-end tests for the natives wired in the bootstrap-ladder pass:
/// the GENERATED ones (`lang/codegen/runtime.mo` -- LLVM IR built in
/// Monad itself) and the C-shaped ones (`lang/codegen/runtime.c`).
///
/// Each compiles real `.mo` source through the same pipeline
/// `lang/main.mo`'s own `compile_file_codegen` uses, links it against
/// the real runtime, RUNS the binary, and asserts its exit code --
/// following `codegen_string_repr_tests.mo`'s
/// `compile_source_run_expect` convention (reused verbatim).
///
/// Running the binary is the whole point: every bug in this family was
/// invisible to `llc`'s verifier. `String_to_list` silently compiling to
/// a "return Unit" stub produced structurally valid IR and a binary that
/// SIGSEGV'd inside `List_reverse_append` the moment `String.reverse`
/// walked the Unit object as if it were a cons cell -- see
/// `validate_no_unwired_natives`'s own doc comment for that story.
/// `String.reverse` is therefore deliberately exercised below.
use io {IO}
open IO {println}
use std.process {exec_cmd}
use lang.types {LoadedModules}
use lang.module {load_file_modules}
use lang.codegen.ir {emit_module}
use lang.codegen.emit {compile_loaded_modules_to_ir}

#[partial]
def compile_natives_run_expect (source : String) (basename : String) (expected : I64) : IO Bool := do {
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
            println (basename ++ ": failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            match mod_result {
                Result.err e => do {
                    println (basename ++ ": compile_loaded_modules_to_ir failed: " ++ e);
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
                            let link_args := [obj_path, runtime_obj];
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

/// The generated `monad_string_starts_with` byte loop. A too-long
/// prefix must fall out through the byte comparison against the NUL
/// terminator, not a bounds check -- hence the "hello!" case.
#[test]
def test_generated_string_starts_with : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let yes := String.starts_with "he" "hello";
    let no := String.starts_with "xy" "hello";
    let too_long := String.starts_with "hello!" "hello";
    let empty_prefix := String.starts_with "" "hello";
    return (if yes && not no && not too_long && empty_prefix then 7 else 1)
}
"# in
    compile_natives_run_expect source "gen_starts_with" 7

/// `String.reverse` -- the exact path that SIGSEGV'd in v25. Routes
/// through the generated `string_to_list`, `List.reverse`, and the C
/// `string_from_list`, so it covers the cons-chain marshaling across
/// the generated/C boundary in both directions.
#[test]
def test_generated_to_list_reverse_round_trip : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let there_and_back := String.beq (String.reverse (String.reverse "bootstrap")) "bootstrap";
    let reversed := String.beq (String.reverse "abc") "cba";
    let empty_ok := String.beq (String.reverse "") "";
    return (if there_and_back && reversed && empty_ok then 7 else 1)
}
"# in
    compile_natives_run_expect source "gen_reverse_round_trip" 7

/// `String.ends_with` builds directly on reverse + starts_with, and is
/// what `module_name_from_path` (lang/module.mo) calls on EVERY module
/// load -- the first thing a self-compiled compiler binary executes.
#[test]
def test_generated_ends_with : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let yes := String.ends_with "lang/main.mo" ".mo";
    let no := String.ends_with "lang/main.rs" ".mo";
    return (if yes && not no then 7 else 1)
}
"# in
    compile_natives_run_expect source "gen_ends_with" 7

/// The generated `monad_string_get`: `Option U8` tags (none 3, some 4)
/// through `alloc_constructor`, plus both out-of-bounds directions.
#[test]
def test_generated_string_get_option : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let at_1 := match String.get "hello" 1 { Option.some b => U8.beq b 101u8, Option.none => false };
    let past_end := match String.get "hello" 99 { Option.some _ => false, Option.none => true };
    let negative := match String.get "hello" (0 - 1) { Option.some _ => false, Option.none => true };
    return (if at_1 && past_end && negative then 7 else 1)
}
"# in
    compile_natives_run_expect source "gen_string_get" 7

/// The generated unsigned ops, including the zero-divisor guard both
/// `u8_div` and `u64_mod` carry (the reference returns 0 rather than
/// trapping). `U64.mod` backs `std/map.mo`'s own bucket arithmetic, so
/// the compiler's every HashMap depends on it.
#[test]
def test_generated_unsigned_ops : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let m := U64.beq (U64.mod 17u64 5u64) 2u64;
    let m0 := U64.beq (U64.mod 17u64 0u64) 0u64;
    let d := U8.beq (U8.div 17u8 5u8) 3u8;
    let d0 := U8.beq (U8.div 17u8 0u8) 0u8;
    let cmp := U8.lt 3u8 7u8 && U8.gt 7u8 3u8;
    return (if m && m0 && d && d0 && cmp then 7 else 1)
}
"# in
    compile_natives_run_expect source "gen_unsigned_ops" 7

/// The C `monad_string_to_lowercase` and `monad_u64_to_string`. The
/// unsigned formatting cannot share `monad_i64_to_string`: a U64 near
/// the top of its range is a negative i64 in this backend's uniform
/// representation.
#[test]
def test_c_lowercase_and_unsigned_to_string : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let lower := String.beq (String.to_lowercase "MiXeD Case") "mixed case";
    let u := String.beq (U64.to_string 42u64) "42";
    let b := String.beq (U8.to_string 255u8) "255";
    return (if lower && u && b then 7 else 1)
}
"# in
    compile_natives_run_expect source "c_lowercase_to_string" 7

/// The C `monad_exec_cmd` -- THE load-bearing native for the bootstrap
/// ladder (`lang/codegen/link.mo` invokes `llc`/`clang` through it, so
/// a self-compiled compiler cannot run its own `compile` command
/// without it). Asserts real exit-code passthrough from a real child
/// process, including a non-zero code and a nonexistent binary.
#[test]
def test_c_exec_cmd_exit_codes : IO Bool :=
    let source := r#"use std.process {exec_cmd}
def main (args : List String) : IO I64 := do {
    let ok <- exec_cmd "true" [];
    let bad <- exec_cmd "false" [];
    let seven <- exec_cmd "sh" ["-c", "exit 7"];
    let missing <- exec_cmd "definitely_no_such_binary_xyz" [];
    return (if ok == 0 && bad == 1 && seven == 7 && missing == 127 then 7 else 1)
}
"# in
    compile_natives_run_expect source "c_exec_cmd" 7

/// The C `monad_list_dir`: bare names, one level, SORTED. The sort is
/// load-bearing rather than cosmetic -- readdir order is
/// filesystem-dependent, and the reference sorts, so an unsorted
/// implementation would make a compiled binary and the interpreter
/// disagree on any directory walk.
#[test]
def test_c_list_dir_sorted : IO Bool :=
    let source := r#"use io {IO}
use std.process {exec_cmd}
def main (args : List String) : IO I64 := do {
    let dir := "/tmp/monad_e2e_listdir";
    let _ <- exec_cmd "rm" ["-rf", dir];
    let _ <- exec_cmd "mkdir" ["-p", dir];
    let _ <- exec_cmd "touch" [dir ++ "/zeta", dir ++ "/alpha", dir ++ "/mid"];
    let entries <- IO.list_dir (Path.path dir);
    let _ <- exec_cmd "rm" ["-rf", dir];
    let at := \i => match List.get i entries { Option.some e => e, Option.none => "<missing>" };
    // Index 3 must be absent -- that plus the three names below pins
    // both the contents and the sort order, without `List.length`
    // (which needs an explicit `use std.list` import to compile).
    let sorted := String.beq (at 0) "alpha" && String.beq (at 1) "mid" && String.beq (at 2) "zeta";
    let no_extra := String.beq (at 3) "<missing>";
    return (if sorted && no_extra then 7 else 1)
}
"# in
    compile_natives_run_expect source "c_list_dir" 7
