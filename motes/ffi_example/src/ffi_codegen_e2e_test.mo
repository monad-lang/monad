// ffi_example / ffi_codegen_e2e_test — AUTOMATED LLVM-path E2E test for
// the `#[extern "c"]` codegen (Phase 3 part 2 of
// `plans/implementations/c-rust-ffi.md`).
//
// `ffi_test.mo` (this directory) already exercises the same path, but
// only as a program a human runs by hand and eyeballs -- nothing in the
// test suite ran it. That gap is why a whole class of codegen bugs
// survived a rebase onto main undetected: the ONLY automated FFI test
// was `ffi_eval_test.mo`, which dispatches through the Rust interpreter
// (`core/src/ffi.rs::extern_execute`) and never reaches
// `lang/codegen/emit.mo` at all. Every bug below produced a clean
// `ffi_eval_test` pass and a broken compiler.
//
// This test drives the REAL backend end to end -- load -> codegen ->
// `llc` -> `clang` -> execute the binary -> check its exit code. Bugs
// 1, 2 and 4 below are caught by that pipeline (each one either makes
// `llc` reject the module or makes the link fail); bug 3 is invisible
// to it and needs its own assertion on the emitted text, for the reason
// given in `test_extern_f64_return_type_declares_double`. All four were
// re-verified by reverting each fix in turn and confirming the specific
// test that covers it goes red:
//
//   1. `llc` accepting the module at all. The extern wrapper's ABI
//      casts were invalid LLVM three separate ways: a `bitcast` with no
//      source type, a `bitcast` between `i64` and a pointer (LLVM
//      allows neither direction -- `inttoptr`/`ptrtoint` are the only
//      legal casts, `llc: invalid cast opcode for cast from 'i64' to
//      'ptr'`), and a cast written inline inside a call argument rather
//      than as its own instruction.
//   2. The `double`-typed call argument. `llvm_value_type` hardcodes
//      `i64` for any `var_`, so `sin`'s bitcast temp was emitted as
//      `call double @sin(i64 %t3)` until `LLVMValue.typed` was added to
//      carry a cast temp's real SSA type.
//   3. `sin : F64 -> F64` mapping to `double`, not `i64`. A def's `typ`
//      is the FULL pi type, so `return_llvm_type` has to peel
//      `Term.pi`; without that the module declared `i64 @sin(double)`.
//   4. `-lm` reaching the linker, from the mote's `[link] libs` rather
//      than from any attribute. Without it the compile succeeds and the
//      LINK fails with `undefined reference to 'sin'`. Asserted here by
//      linking `sin` for real, and directly on the collected libs in
//      `test_extern_link_libs_flag` below (a plain wrong-flags bug
//      would otherwise only ever surface as a link failure).
//
// The compiled program returns `strlen "hello"` (5) as its exit code
// rather than printing: an exit code is what `exec_cmd` can actually
// observe, and it proves a real value crossed the C boundary and came
// back correct, not merely that the binary ran. `sin` is called and its
// result consumed so the `double` path is genuinely exercised; the value
// is not asserted on HERE because an exit code is this test's only
// channel back from the fixture program -- `ffi_link_test.mo` in this
// directory is where `sin`'s result, and the narrow-int round trips, are
// asserted on directly, from plain `#[test]` defs.
use io {IO}
open IO {println}
use std::process {exec_cmd, process_id}
use lang::types {LoadedModules}
use lang::module {collect_link_libs, get_loaded_all, load_file_modules}
use llvm::ir {emit_module}
use lang::codegen::emit {compile_loaded_modules_to_ir}
use llvm::link {compile_ir_to_obj, compile_runtime_obj, link_objects, map_dash_l}
use runtime {}

/// The fixture program: exercises all four extern shapes the wrapper
/// has to adapt -- `puts` (`String` -> `I32`: `inttoptr` in, `sext`
/// out), `strlen` (`String` -> `I64`: `inttoptr` in, no-op out),
/// `sin` (`F64` -> `F64`: `bitcast` both ways, plus `-lm`) and `abs`
/// (`I32` -> `I32`: `trunc` in, `sext` out). `abs` is fed by `puts`'s
/// own `I32` result (the corpus has no `I32` literal yet); its wrapper
/// is what proves the narrow-integer casts -- before the review fixes,
/// a narrow param emitted `bitcast i64 %p0 to i32` (`llc: invalid cast
/// opcode`) and an `i32` return was `zext`-widened, corrupting C's
/// signed values (`puts` yields EOF = -1).
/// NOTE ON WHY THIS FIXTURE INLINES ITS OWN EXTERN DECLS rather than
/// writing `use ffi_example.libc {puts, strlen, sin}` like the
/// eval-path test next door does: the self-hosted compiler cannot
/// resolve a mote-qualified import yet. Calling a mote-imported def
/// through `lang/main.mo compile` fails at TYPECHECK, before codegen is
/// ever reached (`error: unknown variable 'strlen' in main`) -- the
/// mote's decls never enter the target file's scope. The eval path
/// resolves the identical import fine (`run motes/ffi_example/src/
/// ffi_test.mo` prints all four lines), so this is a module-resolution
/// gap in the self-hosted path, upstream of and unrelated to the FFI
/// codegen this file tests. `ffi_test.mo` in this directory is the
/// mote-import form and is blocked on that gap; keeping THIS fixture
/// inline is what lets the extern codegen itself be tested today
/// instead of waiting on it. The declarations below mirror `libc.mo`'s
/// exactly -- when mote imports start working in the self-hosted path,
/// this fixture should collapse to the one-line `use` and
/// `ffi_test.mo` should be folded into it.
#[partial]
def ffi_fixture_source : String := r#"
#[extern "c"]
def puts (s : String) : I32

#[extern "c" {link_name := "strlen"}]
def strlen (s : String) : I64

#[extern "c"]
def sin (x : F64) : F64

#[extern "c"]
def abs (x : I32) : I32

def main (args : List String) : IO I64 := do {
    let greeted := puts "llvm ffi works";
    let cleaned := abs (puts "narrow casts work");
    let n := strlen "hello";
    let sine := sin 0.0;
    return n
}
"#

/// The temp mote's manifest. `sin` lives in libm, and THAT is what
/// `[link] libs` declares -- the fixture's own `#[extern "c"]` says only
/// which symbol to bind. Writing a real `mote.toml` beside the fixture
/// is what makes this test exercise the manifest path rather than a
/// hardcoded flag list.
#[partial]
def ffi_fixture_manifest : String := r#"
[mote]
name = "ffi_probe"
version = "0.1.0"
edition = "2026"

[link]
libs = ["m"]
"#

/// Compiles `ffi_fixture_source` through the self-hosted backend and
/// runs the result, threading the mote's declared `[link] libs` into the
/// `clang` invocation exactly as `cli/src/main.mo` does. Returns the
/// binary's exit code, or a negative marker for each stage that failed
/// (so a failure says WHICH stage broke rather than just "not 5").
#[partial]
def compile_ffi_fixture_exit_code : IO I64 := do {
    let output_dir := "/tmp/monad_ffi_e2e_" ++ I64.to_string process_id;
    let basename := "ffi_codegen_e2e";
    let src_path := output_dir ++ "/src/" ++ basename ++ ".mo";
    let ir_path := output_dir ++ "/" ++ basename ++ ".ll";
    let obj_path := output_dir ++ "/" ++ basename ++ ".o";
    let runtime_obj := output_dir ++ "/" ++ basename ++ "_runtime.o";
    let output_path := output_dir ++ "/" ++ basename;

    // A real mote, not a loose file: `collect_link_libs` walks up from
    // the source to the nearest `mote.toml`, so the fixture only gets
    // `-lm` if the manifest beside it actually declares it.
    let _ <- exec_cmd "mkdir" ["-p", output_dir ++ "/src"];
    IO.write_file (Path.path (output_dir ++ "/mote.toml")) ffi_fixture_manifest;
    IO.write_file (Path.path src_path) ffi_fixture_source;

    let loaded_result : Result String LoadedModules <- load_file_modules src_path false;
    match loaded_result {
        Result.err e => do {
            println ("ffi_codegen_e2e: failed to load: " ++ e);
            return (0 - 1)
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            match mod_result {
                Result.err e => do {
                    println ("ffi_codegen_e2e: codegen failed: " ++ e);
                    return (0 - 2)
                },
                Result.ok mod_ => do {
                    let link_libs : List String <- collect_link_libs (get_loaded_all loaded);
                    let ir_text := emit_module mod_;
                    IO.write_file (Path.path ir_path) ir_text;

                    // Stage 1: `llc`. This is the assertion that the
                    // wrapper's ABI casts are legal LLVM at all.
                    let llc_result <- compile_ir_to_obj ir_path obj_path;
                    if not (llc_result == 0) then do {
                        println "ffi_codegen_e2e: llc rejected the module (invalid extern wrapper IR)";
                        return (0 - 3)
                    } else do {
                        let rt_result <- compile_runtime_obj Runtime.c_path List.empty runtime_obj;
                        if not (rt_result == 0) then do {
                            println "ffi_codegen_e2e: compiling runtime.c failed";
                            return (0 - 4)
                        } else do {
                            // Stage 2: link WITH `link_libs`. Without
                            // `-lm` this is where `sin` fails to resolve.
                            // `link_objects` is the compiler's OWN linker
                            // step (`llvm::link`, the module written to end
                            // the drifted copy this test used to hold), so
                            // `-lgc` and the argv shape come from one place.
                            let link_result <- link_objects [obj_path, runtime_obj] output_path (map_dash_l link_libs);
                            if not (link_result == 0) then do {
                                println "ffi_codegen_e2e: clang link failed (missing -l flag for an extern's lib?)";
                                return (0 - 5)
                            } else do {
                                // Stage 3: run it. Exit code is
                                // `strlen "hello"` -- a real value
                                // round-tripped through the C boundary.
                                let exec_result <- exec_cmd output_path [];
                                let _ <- exec_cmd "rm" ["-rf", output_dir];
                                return exec_result
                            }
                        }
                    }
                },
            }
        },
    }
}

/// `sin : F64 -> F64` must declare as `double @sin(double)`.
///
/// This one needs its own assertion on the emitted TEXT because it is
/// invisible to every other check here: `return_llvm_type` failing to
/// peel the `Term.pi` chain (a def's `typ` is the FULL pi type, so the
/// bare `term_to_llvm_type` hits its `_ =>` i64 fallback) yields
/// `declare i64 @sin(double)` -- wrong at the C ABI, but internally
/// SELF-CONSISTENT, so `llc` accepts the module, the linker resolves
/// `sin` against libm, and the binary runs and exits 5. Verified by
/// reverting the pi-peel fix: the E2E test below still passed while
/// the declaration was wrong. Only the declared return type shows it.
#[test]
def test_extern_f64_return_type_declares_double : IO Bool := do {
    let output_dir := "/tmp/monad_ffi_e2e_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/ffi_f64_decl_probe.mo";
    let _ <- exec_cmd "mkdir" ["-p", output_dir];
    IO.write_file (Path.path src_path) ffi_fixture_source;

    let loaded_result : Result String LoadedModules <- load_file_modules src_path false;
    match loaded_result {
        Result.err e => do {
            println ("test_extern_f64_return_type_declares_double: failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            let _ <- exec_cmd "rm" ["-f", src_path];
            match mod_result {
                Result.err e => do {
                    println ("test_extern_f64_return_type_declares_double: codegen failed: " ++ e);
                    return false
                },
                Result.ok mod_ => do {
                    let ir_text := emit_module mod_;
                    if String.contains ir_text "declare double @sin(double)" then return true
                    else do {
                        println "test_extern_f64_return_type_declares_double: expected `declare double @sin(double)` -- an `i64` return type here means return_llvm_type stopped peeling Term.pi";
                        return false
                    }
                },
            }
        },
    }
}

/// The end-to-end assertion: the compiled binary exits with 5, i.e.
/// `strlen "hello"` really crossed into libc and came back. Covers
/// every stage above; a negative return names the stage that broke.
#[test]
def test_extern_llvm_path_compiles_links_and_runs : IO Bool := do {
    let code <- compile_ffi_fixture_exit_code;
    if I64.beq code 5 then return true
    else do {
        println ("test_extern_llvm_path_compiles_links_and_runs: expected exit 5, got " ++ I64.to_string code);
        return false
    }
}

/// `[link] libs = ["m"]` in the mote's manifest must reach the linker as
/// `-lm`. Asserted directly, not just via the link succeeding: a
/// manifest that fails to parse, or a closure walk that misses the
/// fixture's own mote, silently yields an EMPTY lib list, and a direct
/// check names that cause immediately instead of leaving a bare
/// "undefined reference to 'sin'" to be diagnosed by hand.
#[test]
def test_extern_link_libs_flag : IO Bool := do {
    let output_dir := "/tmp/monad_ffi_libs_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/src/ffi_link_libs_probe.mo";
    let _ <- exec_cmd "mkdir" ["-p", output_dir ++ "/src"];
    IO.write_file (Path.path (output_dir ++ "/mote.toml")) ffi_fixture_manifest;
    IO.write_file (Path.path src_path) ffi_fixture_source;

    let loaded_result : Result String LoadedModules <- load_file_modules src_path false;
    match loaded_result {
        Result.err e => do {
            println ("test_extern_link_libs_flag: failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let link_libs : List String <- collect_link_libs (get_loaded_all loaded);
            let _ <- exec_cmd "rm" ["-rf", output_dir];
            let flags := map_dash_l link_libs;
            match flags {
                List.empty => do {
                    println "test_extern_link_libs_flag: no link libs -- `[link] libs = [\"m\"]` never reached the linker";
                    return false
                },
                List.cons hd _ => do {
                    if String.beq hd "-lm" then return true
                    else do {
                        println ("test_extern_link_libs_flag: expected -lm, got " ++ hd);
                        return false
                    }
                },
            }
        },
    }
}
