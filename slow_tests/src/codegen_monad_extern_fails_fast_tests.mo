/// Regression test for `validate_no_monad_externs` (`lang/codegen/validate.mo`):
/// an `#[extern "c"]` declaration must not bind a Monad runtime symbol
/// (`monad_*`). Those have the uniform i64 native ABI and a safe
/// `#[native]` wrapper; an extern call bypasses both, and the earlier
/// SQLite work used exactly that shape (`monad_ptr_load`,
/// `monad_ptr_from_i64`) before the helpers moved into `std`/`init`.
///
/// The foreign-symbol rule is checked over the REACHABLE decls, so the
/// offending extern must be referenced from `main`; an unreferenced def is
/// filtered out before the validator sees it.
use std::test {Test.write_fixture}
use std::process {exec_cmd, process_id}
use lang::module {load_file_modules}
use lang::codegen::emit {compile_loaded_modules_to_ir}

#[test]
def test_monad_extern_link_fails_fast : IO Bool := do {
    let output_dir := "/tmp/monad_e2e_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/monad_extern.mo";
    let source := r#"#[extern "c" {link_name := "monad_ptr_null"}]
def use_it : I64
def main (args : List String) : IO I64 := do {
    let _ := use_it;
    return 0
}
"#;
    exec_cmd "mkdir" ["-p", output_dir];
    let _w <- Test.write_fixture (Path.path src_path) source;

    let loaded_result <- load_file_modules src_path false;
    match loaded_result {
        Result.err e => do {
            IO.println ("test_monad_extern_link_fails_fast: failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            exec_cmd "rm" ["-f", src_path];
            match mod_result {
                Result.err msg => do {
                    let names_symbol := String.contains msg "monad_ptr_null";
                    let names_def := String.contains msg "use_it";
                    if names_symbol && names_def then return true
                    else do {
                        IO.println ("test_monad_extern_link_fails_fast: error message missing symbol/def name: " ++ msg);
                        return false
                    }
                },
                Result.ok _ => do {
                    IO.println "test_monad_extern_link_fails_fast: expected Result.err (extern binds a Monad native), got Result.ok";
                    return false
                },
            }
        },
    }
}

/// The same rule for an extern with NO explicit `link_name`: the symbol
/// defaults to the def's own last name segment, so a def named
/// `monad_ptr_null` is equally forbidden.
#[test]
def test_bare_monad_extern_def_fails_fast : IO Bool := do {
    let output_dir := "/tmp/monad_e2e_" ++ I64.to_string process_id;
    let src_path := output_dir ++ "/bare_monad_extern.mo";
    let source := r#"#[extern "c"]
def monad_ptr_null : I64
def main (args : List String) : IO I64 := do {
    let _ := monad_ptr_null;
    return 0
}
"#;
    exec_cmd "mkdir" ["-p", output_dir];
    let _w <- Test.write_fixture (Path.path src_path) source;

    let loaded_result <- load_file_modules src_path false;
    match loaded_result {
        Result.err e => do {
            IO.println ("test_bare_monad_extern_def_fails_fast: failed to load: " ++ e);
            return false
        },
        Result.ok loaded => do {
            let mod_result <- compile_loaded_modules_to_ir loaded false;
            exec_cmd "rm" ["-f", src_path];
            match mod_result {
                Result.err msg => do {
                    let names_symbol := String.contains msg "monad_ptr_null";
                    if names_symbol then return true
                    else do {
                        IO.println ("test_bare_monad_extern_def_fails_fast: error message missing symbol: " ++ msg);
                        return false
                    }
                },
                Result.ok _ => do {
                    IO.println "test_bare_monad_extern_def_fails_fast: expected Result.err (extern binds a Monad native), got Result.ok";
                    return false
                },
            }
        },
    }
}
