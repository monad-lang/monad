use io {IO}
use lang.types {LocalScope}
use lang.module {elaborate_loaded_modules, typecheck_module_with_scope}

open IO {println}

def empty_local_scope : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

/// Type check a file with its full dependency scope (ambient prelude/init
/// included) — routes through `elaborate_loaded_modules`, the ONE
/// canonical front-end pipeline `check`/`compile`/`test` all now share
/// (see `bootstrapping/unify-check-compile-test-elaboration.md`), instead
/// of this file's own previously-independent `load_module_with_
/// dependencies` call (which, among other gaps, never seeded prelude/init
/// unless a file explicitly `use`d something that transitively reached
/// them, and never ran infix resolution/dictionary-passing setup at all).
/// `mod_name` is now unused — `elaborate_loaded_modules` derives the
/// module's own name from `file_path` directly (`module_name_from_path`,
/// inside `load_file_modules`) — kept as a parameter purely so every call
/// site below still documents which module it's exercising.
///
/// Passes `check_deps=false` (target-only) — matches the current default
/// everywhere else too (`check_deps=true` is not yet safe to turn on
/// anywhere, see `elaborate_loaded_modules`'s own doc comment). Kept
/// target-only/fast regardless: a per-file failure here is far more
/// useful for pinpointing which individual `init/` file broke than one
/// aggregate pass/fail would be, and staying target-only avoids paying
/// the full-closure cost 18 times over (once per test in this file) once
/// `check_deps=true` does become safe to use.
def typecheck_file (file_path : String) (mod_name : String) : IO Bool := do {
    let result <- elaborate_loaded_modules file_path false;
    match result {
        Result.ok em => typecheck_module_with_scope em.scope em.target_decls empty_local_scope,
        Result.err e => do {
            println ("error loading " ++ file_path ++ ": " ++ e);
            return false
        },
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

#[test]
def test_typecheck_init_process : IO Bool := typecheck_file "init/process.mo" "process"

#[test]
def test_typecheck_init_init : IO Bool := typecheck_file "init/lib.mo" "init"

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

// test_typecheck_init_process_with_deps removed: it called a
// `typecheck_file_with_deps` that was never even defined in this file
// (and its own "IO.read_file has a working directory issue" reasoning
// predates this file's rewrite to route through
// `load_module_with_dependencies`/`extract_directory`, per the doc
// comment on `typecheck_file` above) — genuinely dead, not a real
// second test. `test_typecheck_init_process` above already exercises
// `init/process.mo` through the real, working `typecheck_file`.

// The five tests below were disabled with "requires module loading...
// once module dependency resolution is implemented" — dependency
// resolution IS implemented (`typecheck_file` above already uses it,
// same as every other test in this file), so that reasoning is stale.
// Re-enabled and confirmed passing (2026-08-19).

#[test]
def test_typecheck_init_foldable_tests : IO Bool := typecheck_file "init/foldable_tests.mo" "foldable_tests"

#[test]
def test_typecheck_init_foldable_tests_fold : IO Bool := typecheck_file "init/foldable_tests_fold.mo" "foldable_tests_fold"

#[test]
def test_typecheck_init_foldable_tests_semi_monoid : IO Bool := typecheck_file "init/foldable_tests_semi_monoid.mo" "foldable_tests_semi_monoid"

#[test]
def test_typecheck_init_optics_tests : IO Bool := typecheck_file "init/optics_tests.mo" "optics_tests"

#[test]
def test_typecheck_init_tests : IO Bool := typecheck_file "init/tests.mo" "tests"
