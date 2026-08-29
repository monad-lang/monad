/// Regression tests for the native-boolean-comparison-as-ORDINARY-VALUE
/// boxing fix (`materialize_native_bool_arg`, `lang/codegen/emit.mo`).
///
/// A native comparison (`I64.lt`/`.gt`/`.eq`/`.ne`) compiles, via
/// `emit_arith_instr`, to a raw `icmp`-produced `i1` materialized into a
/// `var_` temp -- deliberately left UNBOXED there so `ensure_i1_cond`'s
/// "is this condition already a genuine i1" fast path can use it
/// directly as a branch condition with no unboxing round-trip. That's
/// correct for an `if`'s own condition, but wrong the moment the SAME
/// comparison is used as an ORDINARY VALUE (a function-call argument, a
/// constructor field, ...) -- this backend tracks no real per-register
/// type (`llvm_value_type (var_ x)` is hardcoded `i64_`), so nothing
/// downstream could tell "this `var_` is secretly `i1`" apart from a
/// genuine `i64`. Found via `bootstrap compile lang/main.mo monad`'s own
/// self-compile reaching (for the first time, after the string-phi fix)
/// `lang/parser/diagnostic.mo`'s `line_end_after_go`, whose `not (a < b)`
/// produced `call i64 @Bool_not(i64 %tN)` where `%tN` was actually
/// declared `i1` -- `llc: '%tN' defined with type 'i1' but expected
/// 'i64'`. Fixed by boxing into a genuine tagged Bool object (mirroring
/// `NativeWrapKind.bool_result`'s existing `zext` + `2 - raw` pattern)
/// whenever a native comparison is compiled as a call argument, in
/// `compile_spine_args_go` (ordinary def calls) and `compile_ntv_args_go`
/// (native/constructor calls).
///
/// Uses `check` (a real, non-inlined top-level def taking two params) to
/// force a genuine runtime `icmp`, not a compile-time-folded `bool_`
/// constant -- `Bool.not (I64.lt 3 5)` on two LITERALS folds to
/// `zext i1 true to i64` at compile time, which is valid IR regardless
/// of whether the fix is present; only a REAL `icmp`-produced register
/// exercises the bug this test guards.
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

/// `Bool.not (I64.lt a b)` where `a > b`: `I64.lt` is false, `Bool.not`
/// flips it to true. Passing a real runtime comparison as `Bool.not`'s
/// own argument is exactly the boxing site this fix covers.
#[test]
def test_native_comparison_as_ordinary_bool_arg_true : IO Bool :=
    let source := r#"use io {IO}
def check (a : I64) (b : I64) : I64 :=
    if Bool.not (I64.lt a b) then 1 else 0
def main (args : List String) : IO I64 := do {
    let r := check 5 3;
    return r
}
"# in
    compile_source_run_expect source "test_native_comparison_as_ordinary_bool_arg_true" 1

/// Same shape, `a < b` this time: `I64.lt` is true, `Bool.not` flips it
/// to false. Covers both `icmp`-result truth values through the fix's
/// `zext`/`2 - raw` tag mapping.
#[test]
def test_native_comparison_as_ordinary_bool_arg_false : IO Bool :=
    let source := r#"use io {IO}
def check (a : I64) (b : I64) : I64 :=
    if Bool.not (I64.lt a b) then 1 else 0
def main (args : List String) : IO I64 := do {
    let r := check 3 5;
    return r
}
"# in
    compile_source_run_expect source "test_native_comparison_as_ordinary_bool_arg_false" 0

/// A native comparison bound via `let` and REUSED (as two separate later
/// `if`-conditions) -- `try_compile_let_beta_db` (`lang/codegen/emit.mo`)
/// binds the let's compiled RHS value directly with no boxing step of
/// its own, so every later reference is just `Term.var name`, losing the
/// "this came from a native comparison" term-shape signal
/// `ensure_i1_cond` needs -- found via `bootstrap compile lang/main.mo
/// monad`'s own self-compile (`render_source_context`, `lang/parser/
/// diagnostic.mo`): a let-bound comparison reused as a LATER `if`'s own
/// condition hit `ensure_i1_cond`'s "needs unboxing" branch (correctly,
/// since `Term.var name` isn't itself a native-op application) and
/// called `monad_get_tag` on a still-raw `i1` -- `llc: '%tN' defined
/// with type 'i1' but expected 'i64'`. `3 < 5` is true: `r1` picks 1,
/// `r2` picks 10 => 11.
#[test]
def test_let_bound_native_comparison_reused_true : IO Bool :=
    let source := r#"use io {IO}
def check (a : I64) (b : I64) : I64 :=
    let too_small := I64.lt a b in
    let r1 := if too_small then 1 else 0 in
    let r2 := if too_small then 10 else 20 in
    I64.add r1 r2
def main (args : List String) : IO I64 := do {
    let r := check 3 5;
    return r
}
"# in
    compile_source_run_expect source "test_let_bound_native_comparison_reused_true" 11

/// Same shape, `5 < 3` (false) this time: `r1` picks 0, `r2` picks 20
/// => 20.
#[test]
def test_let_bound_native_comparison_reused_false : IO Bool :=
    let source := r#"use io {IO}
def check (a : I64) (b : I64) : I64 :=
    let too_small := I64.lt a b in
    let r1 := if too_small then 1 else 0 in
    let r2 := if too_small then 10 else 20 in
    I64.add r1 r2
def main (args : List String) : IO I64 := do {
    let r := check 5 3;
    return r
}
"# in
    compile_source_run_expect source "test_let_bound_native_comparison_reused_false" 20
