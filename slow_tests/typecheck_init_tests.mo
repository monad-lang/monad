use io {IO}
use lang.types {LocalScope}
use lang.module {
  extract_directory, load_module_with_dependencies, parse_all_decls,
  typecheck_module_with_scope,
}

def empty_local_scope : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

/// Type check a file with its full dependency scope (ambient prelude/init
/// included) — reuses the same `lang.module` pipeline
/// `lang/tests/typecheck_lang_tests.mo`'s `test_typecheck_lang_main`
/// already proves correct, instead of this file's own previous
/// from-scratch reimplementation that only ever built scope from the
/// target file's own decls. That meant any def relying on a name defined
/// elsewhere in the ambient prelude/init chain (nearly everything, since
/// prelude/init are auto-opened for every file) genuinely couldn't
/// resolve — not a parser bug, but this test harness never exercising
/// the same dependency-loading real compilation goes through. `mod_name`
/// is used as the module's own path (matching `resolve_module_file`'s
/// "look up bare module names under init/std/lang/examples" convention);
/// `extract_directory file_path` is passed as the search base_dir so
/// files outside those top-level dirs (e.g. `lang/parser/combinators.mo`)
/// still resolve relative to their own directory.
def typecheck_file (file_path : String) (mod_name : String) : IO Bool := do {
    let content <- IO.read_file file_path;
    let mp := ModulePath.mp (List.cons (Identifier.id mod_name) List.empty);
    let base_dir := extract_directory file_path;
    let mb_scope <- load_module_with_dependencies base_dir mp;
    return match mb_scope {
        Option.some scope =>
            match parse_all_decls content {
                ParseResult.success _ decls =>
                    typecheck_module_with_scope scope decls empty_local_scope,
                ParseResult.fail _ => false
            },
        Option.none => false
    }
}

// --- Simple init/ files ---

#[test]
def test_typecheck_init_id : IO Bool := typecheck_file "init/id.mo" "id"

#[test]
def test_typecheck_init_io : IO Bool := typecheck_file "init/io.mo" "io"

#[test]
def test_typecheck_init_math : IO Bool := typecheck_file "init/math.mo" "math"

#[test]
def test_typecheck_init_number : IO Bool := typecheck_file "init/number.mo" "number"

// --- More complex init/ files ---

#[test]
def test_typecheck_init_string : IO Bool := typecheck_file "init/string.mo" "string"

// Skip process.mo for now - it has native functions with dependencies
// #[test]
// def test_typecheck_init_process : IO Bool := typecheck_file "init/process.mo" "process"

#[test]
def test_typecheck_init_init : IO Bool := typecheck_file "init/init.mo" "init"

#[test]
def test_typecheck_init_parser : IO Bool := typecheck_file "lang/parser/combinators.mo" "combinators"

// --- Most complex init/ file ---

#[test]
def test_typecheck_init_prelude : IO Bool := typecheck_file "init/prelude.mo" "prelude"

// --- Test files with type definitions ---

#[test]
def test_typecheck_init_foldable : IO Bool := typecheck_file "init/foldable.mo" "foldable"

#[test]
def test_typecheck_init_optics : IO Bool := typecheck_file "init/optics.mo" "optics"

#[test]
def test_typecheck_init_test_constraints : IO Bool := typecheck_file "init/test_constraints.mo" "test_constraints"

// --- Remaining non-test init/ files ---

#[test]
def test_typecheck_init_string_profile : IO Bool := typecheck_file "init/string_profile.mo" "string_profile"

// Test module dependency loading with init/process.mo which uses io
// Note: This test is commented out because IO.read_file has a working directory issue
// that affects init/process.mo and other files. This is a pre-existing issue.
// #[test]
// def test_typecheck_init_process_with_deps : IO Bool :=
//     typecheck_file_with_deps "init/process.mo" "process"

// Note: test files (foldable_tests*, optics_tests, tests.mo) require module loading
// and are skipped for now. They can be added once module dependency resolution is implemented.

// #[test]
// def test_typecheck_init_foldable_tests : IO Bool := typecheck_file "init/foldable_tests.mo" "foldable_tests"
//
// #[test]
// def test_typecheck_init_foldable_tests_fold : IO Bool := typecheck_file "init/foldable_tests_fold.mo" "foldable_tests_fold"
//
// #[test]
// def test_typecheck_init_foldable_tests_semi_monoid : IO Bool := typecheck_file "init/foldable_tests_semi_monoid.mo" "foldable_tests_semi_monoid"
//
// #[test]
// def test_typecheck_init_optics_tests : IO Bool := typecheck_file "init/optics_tests.mo" "optics_tests"
//
// #[test]
// def test_typecheck_init_tests : IO Bool := typecheck_file "init/tests.mo" "tests"
