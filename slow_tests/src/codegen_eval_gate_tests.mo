/// Pins `monad eval`'s reachable-elaboration gate over a REAL loaded graph
/// (standing checker-gaps Item 11, the unconditional flip in PR #120).
///
/// `eval_file_typechecked` (`cli/src/main.mo`) roots the gate at the BARE
/// `"main"`, because it runs before codegen's `qualify_modules`. If that
/// root ever stopped matching -- the graph qualified earlier, or the loader
/// started prefixing def names -- the closure would be empty and the now
/// UNCONDITIONAL gate would silently pass everything. `filter_reachable_decls`
/// keeps every Inductive/Struct regardless, so "non-empty" is not evidence;
/// the unit test in `decls.mo` cannot see this either, because it hands the
/// filter synthetic decls.
///
/// The observable is the one the pipeline uses: a synthetic
/// `failed := ["main"]` report must be REJECTED against the real closure.
/// A vacuous closure returns `Result.ok` and fails this test. The synthetic
/// failure also keeps the pin independent of whether a real elaboration
/// failure can be provoked for this fixture (the gate logic itself is pinned
/// in `lang/codegen/emit.mo`'s own tests).
use std::test {Test.write_fixture}
use std::process {exec_cmd, process_id}
use lang::types {LocalScope}
use lang::module {
  BestEffortElab, best_effort_decls, elaborate_module_decls_reporting,
  elaborate_loaded_modules,
}
use lang::codegen::decls {filter_reachable_decls}
use lang::codegen::emit {validate_reachable_elaborated}

#[test]
def test_eval_gate_roots_at_the_real_bare_main : IO Bool := do {
    let output_dir := "/tmp/monad_eval_gate_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/main.mo";
    let source := r#"def helper (x : I64) : I64 := x + 1
def main (args : List String) : IO I64 := do {
    let y := helper 41;
    return y
}
"#;
    exec_cmd "mkdir" ["-p", output_dir];
    let _w <- Test.write_fixture (Path.path src_path) source;
    let loaded <- elaborate_loaded_modules src_path false false;
    exec_cmd "rm" ["-f", src_path];
    match loaded {
        Result.err e => do {
            IO.println ("test_eval_gate_roots_at_the_real_bare_main: failed to load: " ++ e);
            return false
        },
        Result.ok em => do {
            // Exactly `eval_file_typechecked`'s own three calls.
            let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
            let report := elaborate_module_decls_reporting em.scope em.elaborated_decls empty_locs;
            let dispatched := best_effort_decls report;
            let reachable := filter_reachable_decls ["main"] dispatched;
            let synthetic : BestEffortElab := {
                decls := List.empty,
                failed := ["main"],
                errors := ["main: synthetic"],
            };
            match validate_reachable_elaborated synthetic reachable {
                Result.err _ => return true,
                Result.ok _ => do {
                    IO.println "test_eval_gate_roots_at_the_real_bare_main: filter_reachable_decls [\"main\"] found no main in the real eval graph -- the unconditional eval gate is vacuous";
                    return false
                },
            }
        },
    }
}
