/// Regression test for the struct-literal-in-constructor-argument
/// miscompile (AGENTS.md's "known pitfall when applying rule 1").
///
/// A bare struct literal written directly as a constructor ARGUMENT --
/// `Option.some { field := val, ... }` -- has no concrete expected type
/// at that point, and the checker does not reliably desugar it to a
/// real constructor there. The REFERENCE interpreter tolerates it. This
/// backend did not: it compiled to a value whose fields were then read
/// at the wrong offsets.
///
/// That cost a full ladder rung. A self-compiled compiler binary
/// SIGSEGV'd in `__strlen_avx2`, reached via `String_length` <-
/// `string_find_last_slash` <- `extract_directory` <-
/// `load_file_modules` -- i.e. on the FIRST module load, so every
/// `check` and every `compile` the compiler ran on itself. The culprit
/// was one `Option.some { ... }` in `load_module_with_info`
/// (lang/module.mo); the emitted IR read fields 0/1/2 straight off the
/// `Option` payload, and the closure env slot holding `file_path` came
/// back as 0x31 -- a small integer that `String.length` then
/// dereferenced as a `char*`.
///
/// `check` stays completely silent about this, and so does `llc` --
/// only RUNNING a compiled binary finds it, which is why this test
/// compiles, links and executes rather than inspecting IR text.
use io {IO}
open IO {println}
use std.process {exec_cmd}
use lang.types {LoadedModules}
use lang.module {load_file_modules}
use lang.codegen.ir {emit_module}
use lang.codegen.emit {compile_loaded_modules_to_ir}

#[partial]
def compile_struct_lit_run_expect (source : String) (basename : String) (expected : I64) : IO Bool := do {
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

/// The safe form, and the one every site in `lang/` now uses: bind the
/// literal to a local with an explicit type annotation first, then pass
/// the local. A multi-field struct reached through an `Option` -- the
/// exact shape of `load_module_with_info`'s `ModuleInfo` -- with a
/// String field read back after the round trip.
///
/// Exit code 7 means the String field survived; a crash (139) or 1 means
/// it was read at the wrong offset.
#[test]
def test_struct_literal_via_annotated_local_round_trips : IO Bool :=
    let source := r#"use io {IO}
struct Info { tag_ : I64, name : String, count : I64 }
def build : IO (Option Info) :=
    let info : Info := { tag_ := 1, name := "examples/hello.mo", count := 3 } in
    return (Option.some info)
def main (args : List String) : IO I64 := do {
    let m <- build;
    match m {
        Option.some i =>
            match i {
                Info.mk _t nm _c =>
                    return (if String.length nm == 17 && String.beq nm "examples/hello.mo" then 7 else 1)
            },
        Option.none => return 1,
    }
}
"# in
    compile_struct_lit_run_expect source "struct_lit_annotated" 7

/// The same shape one level deeper: a struct built inside a `return
/// match ...`, which is precisely how `load_module_with_info` produced
/// its `ModuleInfo`, and with the String field consumed by a native
/// (`String.length`) rather than just compared -- that native call is
/// what actually dereferenced the bad pointer and crashed.
#[test]
def test_struct_from_return_match_field_reaches_native : IO Bool :=
    let source := r#"use io {IO}
struct Rec { first : String, second : String }
def pick (which : Option I64) : IO (Option Rec) := do {
    let chosen : String := match which { Option.some _ => "chosen/path.mo", Option.none => "fallback.mo" };
    return match which {
        Option.some _ =>
            let r : Rec := { first := chosen, second := "tail" } in
            Option.some r,
        Option.none => Option.none
    }
}
def main (args : List String) : IO I64 := do {
    let m <- pick (Option.some 1);
    match m {
        Option.some r =>
            match r {
                Rec.mk f s => do {
                    let lens := String.length f + String.length s;
                    return (if lens == 18 && String.beq f "chosen/path.mo" then 7 else 1)
                }
            },
        Option.none => return 1,
    }
}
"# in
    compile_struct_lit_run_expect source "struct_lit_return_match" 7
