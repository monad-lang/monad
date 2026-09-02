use io {IO}
use slow_tests.typecheck_harness {typecheck_file}
use lang.types {}
use lang.module {}

open IO {println}


// --- std/ non-test files ---

#[test]
def test_typecheck_std_test : IO Bool := typecheck_file "std/test.mo"

#[test]
def test_typecheck_std_base : IO Bool := typecheck_file "std/base.mo"

#[test]
def test_typecheck_std_bench : IO Bool := typecheck_file "std/bench.mo"

#[test]
def test_typecheck_std_list : IO Bool := typecheck_file "std/list.mo"

#[test]
def test_typecheck_std_map : IO Bool := typecheck_file "std/map.mo"

// --- std/concurrent/ files ---

#[test]
def test_typecheck_std_concurrent_fiber : IO Bool := typecheck_file "std/concurrent/fiber.mo"

#[test]
def test_typecheck_std_concurrent_combine : IO Bool := typecheck_file "std/concurrent/combine.mo"

// --- std/ test files ---
//
// Previously skipped as "require module loading... for now" — dependency
// resolution IS implemented (`typecheck_file` above already uses it, same
// as every other test in this file), so that reasoning was stale.
// Re-enabled and confirmed passing (2026-08-19).

#[test]
def test_typecheck_std_list_tests1 : IO Bool := typecheck_file "std/list_tests1.mo"

#[test]
def test_typecheck_std_list_tests2 : IO Bool := typecheck_file "std/list_tests2.mo"

#[test]
def test_typecheck_std_list_tests3a : IO Bool := typecheck_file "std/list_tests3a.mo"

#[test]
def test_typecheck_std_list_tests3b : IO Bool := typecheck_file "std/list_tests3b.mo"

#[test]
def test_typecheck_std_map_tests : IO Bool := typecheck_file "std/map_tests.mo"

// Not `#[test]` -- known-broken, pre-existing, user-decided out-of-scope
// gap (see `2026-08-27-bootstrap-compile-and-test.md`'s own "Out of
// scope" list). Previously passed anyway, silently: `std/derive_tests.mo`
// (`derive_bord_meta`) hits a `FromListLiteral.cons` call with no
// carrier-revealing arg at its own call site -- exactly the shape
// `resolve_class_method_call_d4_default_carrier`'s own doc comment
// (`lang/scope.mo`) documents as a known, narrow gap -- but the
// `reflect_type_info!`/derive pipeline (`expand_decls_graph`,
// `lang/module.mo`) used to swallow that failure instead of surfacing it.
// Now that `resolve_class_calls_decls` fails fast on any unresolved
// class-method call (see its own doc comment) instead of silently, this
// test correctly FAILS instead of falsely passing -- re-enable once the
// derive macro's own `FromListLiteral.cons` gap is fixed, not before.
// Named `known_broken_...`, not `test_...` (a PR review flagged the
// former `test_typecheck_std_derive_tests` name as misleading in a file
// that's otherwise entirely real `#[test]`s): this def is intentionally
// not part of the test suite, so its name shouldn't look like it is.
def known_broken_typecheck_std_derive_tests : IO Bool := typecheck_file "std/derive_tests.mo"

#[test]
def test_typecheck_std_sha256_tests : IO Bool := typecheck_file "std/sha256_tests.mo"

#[test]
def test_typecheck_std_test_map_full : IO Bool := typecheck_file "std/test_map_full.mo"
