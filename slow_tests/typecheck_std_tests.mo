use io {IO}
use lang.types {LocalScope}
use lang.module {elaborate_loaded_modules, typecheck_module_with_scope}

open IO {println}

def empty_local_scope : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

/// See slow_tests/typecheck_init_tests.mo's `typecheck_file` doc comment
/// — same fix, same reason (routes through `elaborate_loaded_modules`,
/// the one canonical front-end pipeline `check`/`compile`/`test`/
/// `slow_tests` all now share), and same `check_deps=false` rationale.
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

// --- std/ non-test files ---

#[test]
def test_typecheck_std_test : IO Bool := typecheck_file "std/test.mo" "test"

#[test]
def test_typecheck_std_base : IO Bool := typecheck_file "std/base.mo" "base"

#[test]
def test_typecheck_std_bench : IO Bool := typecheck_file "std/bench.mo" "bench"

#[test]
def test_typecheck_std_list : IO Bool := typecheck_file "std/list.mo" "list"

#[test]
def test_typecheck_std_map : IO Bool := typecheck_file "std/map.mo" "map"

// --- std/concurrent/ files ---

#[test]
def test_typecheck_std_concurrent_fiber : IO Bool := typecheck_file "std/concurrent/fiber.mo" "fiber"

#[test]
def test_typecheck_std_concurrent_combine : IO Bool := typecheck_file "std/concurrent/combine.mo" "combine"

// --- std/ test files ---
//
// Previously skipped as "require module loading... for now" — dependency
// resolution IS implemented (`typecheck_file` above already uses it, same
// as every other test in this file), so that reasoning was stale.
// Re-enabled and confirmed passing (2026-08-19).

#[test]
def test_typecheck_std_list_tests1 : IO Bool := typecheck_file "std/list_tests1.mo" "list_tests1"

#[test]
def test_typecheck_std_list_tests2 : IO Bool := typecheck_file "std/list_tests2.mo" "list_tests2"

#[test]
def test_typecheck_std_list_tests3a : IO Bool := typecheck_file "std/list_tests3a.mo" "list_tests3a"

#[test]
def test_typecheck_std_list_tests3b : IO Bool := typecheck_file "std/list_tests3b.mo" "list_tests3b"

#[test]
def test_typecheck_std_map_tests : IO Bool := typecheck_file "std/map_tests.mo" "map_tests"

#[test]
def test_typecheck_std_derive_tests : IO Bool := typecheck_file "std/derive_tests.mo" "derive_tests"

#[test]
def test_typecheck_std_sha256_tests : IO Bool := typecheck_file "std/sha256_tests.mo" "sha256_tests"

#[test]
def test_typecheck_std_test_map_full : IO Bool := typecheck_file "std/test_map_full.mo" "test_map_full"
