/// Regression test for `resolve_class_calls_decls`'s fail-fast check
/// (`lang/scope.mo`): a class-method call with no available instance must
/// produce a `Result.err` naming the class/method/enclosing def, not a
/// silently-unresolved reference that only surfaces later as a cryptic
/// `llc: undefined value '@ClassName_method'` error.
///
/// Guards against a regression of the check itself (e.g. someone reverting
/// `validate_no_unresolved_class_calls`'s own walk, or
/// `compile_loaded_modules_to_ir` no longer calling it) -- this session
/// found two genuine, previously-silent instances of exactly this bug
/// empirically (`instance Functor List`'s own recursive `Functor.map`
/// call, `init/prelude.mo`; `std/derive_tests.mo`'s `FromListLiteral.cons`)
/// once this check landed, both fixed/skipped separately -- this test
/// exercises the mechanism directly with a minimal, deliberately-
/// unresolvable class method call, independent of either of those.
///
/// The unresolved call MUST be reachable from `main` -- the check runs
/// on the REACHABLE decls only (`lang.codegen.emit`'s own
/// `compile_loaded_modules_to_ir` / `validate_no_unresolved_class_calls`'s
/// own doc comment explains why: validating the whole loaded graph
/// blocked a compile over a bug in dead code the program never actually
/// used), so an unreferenced `use_it` would get filtered out by
/// `filter_reachable_decls` before the check ever saw it, silently
/// passing this test for the wrong reason.
use io {IO}
use std.process {exec_cmd}
use lang.types {LoadedModules}
use lang.module {load_file_modules}
use lang.codegen.emit {compile_loaded_modules_to_ir}

#[test]
def test_unresolved_class_method_call_fails_fast : IO Bool := do {
    let output_dir := "/tmp/monad_e2e";
    let src_path := output_dir ++ "/unresolved_class_call.mo";
    let source := r#"class NoInstance A { def only_method : A -> A }
def use_it (x : Bool) : Bool := NoInstance.only_method x
def main (args : List String) : IO I64 := do {
    let _ := use_it true;
    return 0
}
"#;
    let _ <- exec_cmd "mkdir" ["-p", output_dir];
    IO.write_file (Path.path src_path) source;

    let loaded_result : Result String LoadedModules <- load_file_modules src_path;
    match loaded_result {
        Result.err e => do {
            IO.println ("test_unresolved_class_method_call_fails_fast: failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            let _ <- exec_cmd "rm" ["-f", src_path];
            match mod_result {
                Result.err msg => do {
                    let names_class := String.contains msg "NoInstance";
                    let names_method := String.contains msg "only_method";
                    if names_class && names_method then return true
                    else do {
                        IO.println ("test_unresolved_class_method_call_fails_fast: error message missing class/method name: " ++ msg);
                        return false
                    }
                },
                Result.ok _ => do {
                    IO.println "test_unresolved_class_method_call_fails_fast: expected Result.err (no NoInstance instance exists), got Result.ok";
                    return false
                },
            }
        },
    }
}
