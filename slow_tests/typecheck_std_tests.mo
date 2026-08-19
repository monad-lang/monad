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

/// See lang/tests/typecheck_init_tests.mo's `typecheck_file` doc comment —
/// same fix, same reason (ambient prelude/init dependency loading via
/// lang.module's own proven pipeline, instead of building scope from only
/// the target file's own decls).
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
def test_typecheck_std_concurrent_fiber : IO Bool := typecheck_file "std/concurrent/fiber.mo" "concurrent_fiber"

#[test]
def test_typecheck_std_concurrent_combine : IO Bool := typecheck_file "std/concurrent/combine.mo" "concurrent_combine"

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
