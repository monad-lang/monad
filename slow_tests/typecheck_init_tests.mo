use io {IO}
use slow_tests.typecheck_harness {typecheck_file}
use lang.types {}
use lang.module {}

open IO {println}


// --- Simple init/ files ---

#[test]
def test_typecheck_init_id : IO Bool := typecheck_file "init/id.mo"

#[test]
def test_typecheck_init_io : IO Bool := typecheck_file "init/io.mo"

#[test]
def test_typecheck_init_math : IO Bool := typecheck_file "init/math.mo"

#[test]
def test_typecheck_init_number : IO Bool := typecheck_file "init/number.mo"

// --- More complex init/ files ---

#[test]
def test_typecheck_init_string : IO Bool := typecheck_file "init/string.mo"

#[test]
def test_typecheck_init_process : IO Bool := typecheck_file "init/process.mo"

#[test]
def test_typecheck_init_init : IO Bool := typecheck_file "init/lib.mo"

#[test]
def test_typecheck_init_parser : IO Bool := typecheck_file "lang/parser/combinators.mo"

// --- Most complex init/ file ---

#[test]
def test_typecheck_init_prelude : IO Bool := typecheck_file "init/prelude.mo"

// --- Test files with type definitions ---

#[test]
def test_typecheck_init_foldable : IO Bool := typecheck_file "init/foldable.mo"

#[test]
def test_typecheck_init_optics : IO Bool := typecheck_file "init/optics.mo"

#[test]
def test_typecheck_init_test_constraints : IO Bool := typecheck_file "init/test_constraints.mo"

// --- Remaining non-test init/ files ---

#[test]
def test_typecheck_init_string_profile : IO Bool := typecheck_file "init/string_profile.mo"

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
def test_typecheck_init_foldable_tests : IO Bool := typecheck_file "init/foldable_tests.mo"

#[test]
def test_typecheck_init_foldable_tests_fold : IO Bool := typecheck_file "init/foldable_tests_fold.mo"

#[test]
def test_typecheck_init_foldable_tests_semi_monoid : IO Bool := typecheck_file "init/foldable_tests_semi_monoid.mo"

#[test]
def test_typecheck_init_optics_tests : IO Bool := typecheck_file "init/optics_tests.mo"

#[test]
def test_typecheck_init_tests : IO Bool := typecheck_file "init/tests.mo"
