/// Regression tests for a family of related codegen gaps found while
/// chasing `bootstrap compile lang/main.mo monad`'s self-compile past the
/// string phi-merge fix: values that reach a `phi` (an `if`/`match`
/// merge point) or a bare `ret` need the SAME materialization call
/// arguments already get (`materialize_void`/`materialize_native_bool_
/// arg`, `lang/codegen/emit.mo`) -- neither `build_db_if_blocks`/
/// `build_merge_result` (if/else merges), `build_match_case_block`
/// (match-arm merges), nor `compile_db_def_ir_body` (a def's own bare
/// return value) called them until this session's fixes.
///
/// Also exercises the adjacent `I64.beq` native-dispatch fix:
/// `lookup_native`'s table hardcoded `"I64_eq"`, an identifier that
/// doesn't exist in real source (`I64.eq` is "unknown variable" --
/// confirmed) -- the real, only I64 equality function throughout the
/// whole corpus is `I64.beq` (`init/number.mo`'s `BEq I64` instance),
/// which never matched the table at all and silently miscompiled to a
/// "return Unit" stub, both as a bare call and as an `if`'s own
/// condition.
use io {IO, println}
open IO {println}
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
            println (basename ++ ": failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_ <- compile_loaded_modules_to_ir loaded false;
            let ir_text := emit_module mod_;
            IO.write_file ir_path ir_text;

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
}

/// `I64.beq` used directly as an `if`'s own condition and as an
/// ordinary comparison -- exercises `lookup_native`'s fixed dispatch
/// table entry (was `"I64_eq"`, now `"I64_beq"`). Uses a `do`-block
/// `let`/`return` rather than a bare `IO.io (if ...)` body -- the latter
/// hits a SEPARATE, already-filed, pre-existing bug (`implementations/
/// 2026-08-29-io-wrap-dropped-after-branching-argument.md`), unrelated
/// to what this test guards.
#[test]
def test_i64_beq_native_dispatch : IO Bool :=
    let source := r#"use io {IO}
def main (args : List String) : IO I64 := do {
    let r := if I64.beq 5 5 then 1 else 0;
    return r
}
"# in
    compile_source_run_expect source "test_i64_beq_native_dispatch" 1

/// An outer `if` whose `else` branch is ITSELF a nested `if` -- the
/// nested if's own compiled body ends in ITS OWN branch instruction
/// (not a `jump` to the outer merge block), so the outer merge's `phi`
/// must have only ONE incoming edge (from `then`), not two. Before the
/// fix, `build_merge_result` always built a 2-entry phi regardless,
/// producing a phi edge from a non-predecessor block -- `llc`: "PHINode
/// should have one entry for each predecessor of its parent basic
/// block!" / "Instruction does not dominate all uses!". Mirrors the
/// exact shape that blocked `lang/parser/position.mo`'s
/// `line_col_scan_direct` during the self-compile.
#[test]
def test_nested_if_in_else_branch_phi_arity : IO Bool :=
    let source := r#"use io {IO}
def classify (n : I64) (m : I64) : I64 :=
    if I64.beq n 0
    then 100
    else
        if I64.gt m 0 then 1 else 2
def main (args : List String) : IO I64 := do {
    let a := classify 0 5;
    let b := classify 3 5;
    let c := classify 3 (0 - 5);
    return (I64.add a (I64.add b c))
}
"# in
    compile_source_run_expect source "test_nested_if_in_else_branch_phi_arity" 103

/// A def whose whole body is a BARE native comparison (no wrapping
/// `if`/call) -- `compile_db_def_ir_body`'s own `ret val_r` used to pass
/// a raw, unboxed `i1` straight through when `val_r` came from a native
/// comparison with no materialization step, matching the exact shape of
/// `lang/parser/position.mo`'s own `is_all_ascii_direct`/`String.is_
/// empty`-style helpers (a comparison as a function's entire
/// implementation). `llc`: "'%tN' defined with type 'i1' but expected
/// 'i64'" at the `ret` itself.
#[test]
def test_def_body_bare_native_comparison_return : IO Bool :=
    let source := r#"use io {IO}
def is_five (n : I64) : Bool := I64.beq n 5
def main (args : List String) : IO I64 := do {
    let r := if is_five 5 then 1 else 0;
    return r
}
"# in
    compile_source_run_expect source "test_def_body_bare_native_comparison_return" 1
