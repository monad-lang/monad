/// Regression tests for the closure free-variable-capture fix
/// (`plans/implementations/2026-08-28-codegen-closure-free-var-capture.md`).
///
/// `compile_db_lam_ir` (`lang/codegen/emit.mo`) lifts a nested `Term.lam`
/// (every do-notation continuation is exactly this shape -- `let x <- e1;
/// e2` desugars to `Monad.bind e1 (\x -> e2)`, `lang/types.mo`'s
/// `desugar_do_inner`) into a brand-new, independent top-level LLVM
/// function. Before this fix, `alloc_closure` was always called with an
/// EMPTY capture list, so any reference inside the lifted body to a name
/// bound in the ENCLOSING function (e.g. an earlier do-statement's own
/// bound name) silently resolved to a register that belongs to the outer
/// function and doesn't exist inside the lifted one -- `llc: use of
/// undefined value`.
///
/// These tests write real `.mo` source to disk and drive it through the
/// SAME pipeline `lang/main.mo`'s own `compile_file_codegen` uses
/// (`load_file_modules` -> `compile_loaded_modules_to_ir` -> `emit_module`
/// -> `llc`/`clang`), rather than hand-building a `Term`/`Def` AST --
/// do-notation desugaring, dictionary-passing promotion, and typeclass
/// call resolution all need to run for real to reach the actual bug (a
/// hand-built AST would have to fake all of that, and would risk testing
/// a shape that doesn't match what the parser/desugarer actually produce).
///
/// A plain `let x := 5 in ...` does NOT reach `compile_db_lam_ir` at all
/// -- `try_compile_let_beta_db` beta-reduces it to a literal/direct
/// binding in the SAME function, so it would falsely "pass" even against
/// the pre-fix buggy code. Only a genuine monadic bind (`let x <- e1; e2`,
/// or an escaping first-class lambda) forces real lambda-lifting, which is
/// why every test below uses `<-`, not `:=`.
use io {IO}
open IO {println, write_file}
use std.process {exec_cmd}
use lang.module {LoadedModules, load_file_modules}
use lang.codegen.ir {emit_module}
use lang.codegen.emit {compile_loaded_modules_to_ir}

/// Shared write-source -> load -> typecheck-gate -> compile -> llc ->
/// clang -> link -> run -> compare-exit-code helper. Mirrors
/// `lang/main.mo`'s own `compile_file`/`compile_file_codegen`/`link_ir`
/// pipeline closely enough to exercise the real bug, without depending on
/// `lang/main.mo` itself (this test file must stand alone).
#[partial]
def compile_source_run_expect (source : String) (basename : String) (expected : I64) : IO Bool := do {
    let output_dir := "/tmp/monad_e2e";
    let src_path := output_dir ++ "/" ++ basename ++ ".mo";
    let ir_path := output_dir ++ "/" ++ basename ++ ".ll";
    let obj_path := output_dir ++ "/" ++ basename ++ ".o";
    let runtime_obj := output_dir ++ "/" ++ basename ++ "_runtime.o";
    let output_path := output_dir ++ "/" ++ basename;

    let _ <- exec_cmd "mkdir" ["-p", output_dir];
    // Both always non-empty by construction -- `Path.path` directly.
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
                    // `ir_path` is always non-empty by construction --
                    // `Path.path` directly.
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

/// Primary regression test: `b`'s own bind-continuation transitively
/// captures `a` from the enclosing lifted lambda. Uses `I64.add`
/// directly (not `+`) to isolate the closure-capture fix from an
/// unrelated, pre-existing `HAdd`/typeclass-dispatch gap for the plain
/// operator form. Expect 5 + 10 = 15.
#[test]
def test_bind_capture : IO Bool :=
    let source :=
        "use io {IO, println}\n" ++
        "def main (args : List String) : IO I64 := do {\n" ++
        "    let a <- IO.io 5;\n" ++
        "    let b <- IO.io 10;\n" ++
        "    return (I64.add a b)\n" ++
        "}\n"
    in
    compile_source_run_expect source "test_bind_capture" 15

/// 3-level nesting: transitive capture must compose across more than
/// one level (`c`'s continuation captures both `a` and `b`, each
/// itself captured one level down from where it was originally bound).
/// Expect 1 + 2 + 3 = 6.
#[test]
def test_bind_capture_3level : IO Bool :=
    let source :=
        "use io {IO, println}\n" ++
        "def main (args : List String) : IO I64 := do {\n" ++
        "    let a <- IO.io 1;\n" ++
        "    let b <- IO.io 2;\n" ++
        "    let c <- IO.io 3;\n" ++
        "    return (I64.add (I64.add a b) c)\n" ++
        "}\n"
    in
    compile_source_run_expect source "test_bind_capture_3level" 6

/// Sibling-lambda regression test: a plain `let n := 5` (beta-reduced
/// inline, NOT lifted) followed by a NESTED do-block (`if verbose then
/// do { println ... } else return unit`, itself producing its own
/// lifted lambda for its trailing `pure hole` continuation) followed by
/// a SECOND, later statement that references `n` (also lifted, as
/// every do-notation continuation is). `compile_db_lam_ir` resets its
/// own ctx's `locals` to compile a lifted function's body in isolation
/// (`ctx_reset_locals`) -- but was returning that RESET ctx straight
/// back to its caller instead of restoring the caller's own original
/// locals (`ctx_restore_locals`), so `n`'s binding was silently lost
/// from the enclosing function's own ctx the moment the FIRST nested
/// lambda (the `if`'s own do-block) finished compiling -- the SECOND
/// lambda (`return n`) then couldn't find `n` as a local at all (not
/// merely failing to capture it -- `n` resolved as an unknown GLOBAL
/// name and silently miscompiled into a bogus 0-arg call,
/// `llc: use of undefined value '@n'`). This exact shape --
/// `compile_loaded_modules_to_ir`'s own `if verbose then do {...}
/// else return unit;` pattern, repeated across several successive
/// stages -- is what blocked `bootstrap compile lang/main.mo monad`'s
/// own self-compile. Expect 5 (verbose=false, so `n` survives
/// untouched through the discarded `if`/`else` branch).
#[test]
def test_sibling_lambda_preserves_outer_locals : IO Bool :=
    let source :=
        "use io {IO, println}\n" ++
        "def helper (verbose : Bool) : IO I64 := do {\n" ++
        "    let n := 5;\n" ++
        "    if verbose then do {\n" ++
        "        println \"hi\"\n" ++
        "    } else return unit;\n" ++
        "    return n\n" ++
        "}\n" ++
        "def main (args : List String) : IO I64 := helper false\n"
    in
    compile_source_run_expect source "test_sibling_lambda_preserves_outer_locals" 5

/// Shim-path regression test: a top-level (arity>0) def referenced as a
/// first-class VALUE -- passed to another function and applied
/// indirectly via `apply_closureN` -- must still work once
/// `apply_closureN` uniformly expects every boxed entry to accept a
/// leading `self` param. `add_one`'s own DIRECT-call signature (unused
/// in this program, but exercised implicitly by every other top-level
/// def in the whole corpus) must stay untouched, so this only passes if
/// `build_closure_shim_func`'s forwarding shim (not `add_one`'s own
/// entry point) is what actually gets boxed and invoked here.
/// Deliberately avoids `List`/`Option`/`+` machinery (all of which hit
/// unrelated, pre-existing gaps -- `List.cons`'s own constructor
/// wrapper isn't reachable via this minimal-corpus compile path, and
/// `+`'s `HAdd` dispatch has a separate gap) by hand-writing a tiny
/// `apply_fn`/`add_one` pair: `apply_fn add_one 8` must produce 9.
#[test]
def test_shim_boxed_def_as_value : IO Bool :=
    let source :=
        "use io {IO, println}\n" ++
        "def add_one (x : I64) : I64 := I64.add x 1\n" ++
        "def apply_fn (f : I64 -> I64) (x : I64) : I64 := f x\n" ++
        "def main (args : List String) : IO I64 :=\n" ++
        "    IO.io (apply_fn add_one 8)\n"
    in
    compile_source_run_expect source "test_shim_boxed_def_as_value" 9
