use lang::types {LocalScope, ModulePath, NameRef, Scope, ScopeData, id}
use std::test {Test.read_fixture}
use lang::module {parse_all_decls}
use parsec::core {fail, success}
use lang::scope {build_scope_from_decls, scope_resolve_name}

def empty_local_scope : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

def make_scope (path : ModulePath) (sd : ScopeData) : Scope := {
    module_id := path,
    scope := sd,
    parent := Option.none,
    incomplete_match_ok := false,
}

def name_ref (name : String) : NameRef := NameRef.nid (Identifier.id name)

/// Read `file_path` and report whether its module scope resolves `Type`.
///
/// An unreadable file fails, named on stderr (`Test.read_fixture`).
#[partial]
def build_scope_for_file (file_path : String) (mod_name : String) : IO Bool := do {
    let content <- Test.read_fixture file_path;
    return (match content {
        Option.none => false,
        Option.some text => build_scope_of_source text mod_name
    })
}

/// The pure half of `build_scope_for_file`: does `content`'s module scope
/// resolve the name `Type`?
def build_scope_of_source (content : String) (mod_name : String) : Bool :=
    match parse_all_decls content {
        success _ decls =>
            let path := ModulePath.mk (List.cons (Identifier.id mod_name) List.empty) in
            let sd := build_scope_from_decls path decls in
            let scope := make_scope path sd in
            let type_ref := name_ref "Type" in
            match scope_resolve_name type_ref scope empty_local_scope {
                ok _ => true,
                err _ => false
            },
        fail _ => false
    }

// --- All init/ files ---

#[test]
def test_scope_init_id : IO Bool := build_scope_for_file "init/src/id.mo" "id"

#[test]
def test_scope_init_init : IO Bool := build_scope_for_file "init/src/lib.mo" "init"

#[test]
def test_scope_init_io : IO Bool := build_scope_for_file "init/src/io.mo" "io"

#[test]
def test_scope_init_math : IO Bool := build_scope_for_file "init/src/math.mo" "math"

#[test]
def test_scope_init_number : IO Bool := build_scope_for_file "init/src/number.mo" "number"

#[test]
def test_scope_init_parser_file : IO Bool := build_scope_for_file "motes/parsec/src/combinators.mo" "combinators"

#[test]
def test_scope_init_prelude : IO Bool := build_scope_for_file "init/src/prelude.mo" "prelude"

#[test]
def test_scope_std_process : IO Bool := build_scope_for_file "std/src/process.mo" "process"

#[test]
def test_scope_init_string : IO Bool := build_scope_for_file "init/src/string.mo" "string"

#[test]
def test_scope_init_string_profile : IO Bool := build_scope_for_file "init/src/string_profile.mo" "string_profile"

#[test]
def test_scope_init_test_constraints : IO Bool := build_scope_for_file "init/src/test_constraints.mo" "test_constraints"

#[test]
def test_scope_init_tests : IO Bool := build_scope_for_file "init/src/tests.mo" "tests"

#[test]
def test_scope_init_foldable : IO Bool := build_scope_for_file "init/src/foldable.mo" "foldable"

#[test]
def test_scope_init_foldable_tests : IO Bool := build_scope_for_file "init/src/foldable_tests.mo" "foldable_tests"

#[test]
def test_scope_init_foldable_tests_fold : IO Bool := build_scope_for_file "init/src/foldable_tests_fold.mo" "foldable_tests_fold"

#[test]
def test_scope_init_foldable_tests_semi_monoid : IO Bool := build_scope_for_file "init/src/foldable_tests_semi_monoid.mo" "foldable_tests_semi_monoid"

#[test]
def test_scope_init_optics : IO Bool := build_scope_for_file "init/src/optics.mo" "optics"

#[test]
def test_scope_init_optics_tests : IO Bool := build_scope_for_file "init/src/optics_tests.mo" "optics_tests"

// --- All std/ files ---

#[test]
def test_scope_std_test : IO Bool := build_scope_for_file "std/src/test.mo" "test"

#[test]
def test_scope_std_base : IO Bool := build_scope_for_file "std/src/base.mo" "base"

#[test]
def test_scope_std_bench : IO Bool := build_scope_for_file "std/src/bench.mo" "bench"

#[test]
def test_scope_std_list : IO Bool := build_scope_for_file "std/src/list.mo" "list"

#[test]
def test_scope_std_list_tests1 : IO Bool := build_scope_for_file "std/src/list_tests1.mo" "list_tests1"

#[test]
def test_scope_std_list_tests2 : IO Bool := build_scope_for_file "std/src/list_tests2.mo" "list_tests2"

#[test]
def test_scope_std_list_tests3a : IO Bool := build_scope_for_file "std/src/list_tests3a.mo" "list_tests3a"

#[test]
def test_scope_std_list_tests3b : IO Bool := build_scope_for_file "std/src/list_tests3b.mo" "list_tests3b"

#[test]
def test_scope_std_map : IO Bool := build_scope_for_file "std/src/map.mo" "map"

#[test]
def test_scope_std_map_tests : IO Bool := build_scope_for_file "std/src/map_tests.mo" "map_tests"

#[test]
def test_scope_std_test_map_full : IO Bool := build_scope_for_file "std/src/test_map_full.mo" "test_map_full"

#[test]
def test_scope_std_concurrent_fiber : IO Bool := build_scope_for_file "std/src/concurrent/fiber.mo" "concurrent_fiber"

#[test]
def test_scope_std_concurrent_fiber_test : IO Bool := build_scope_for_file "std/src/concurrent/fiber_test.mo" "concurrent_fiber_test"

#[test]
def test_scope_std_concurrent_combine : IO Bool := build_scope_for_file "std/src/concurrent/combine.mo" "concurrent_combine"

#[test]
def test_scope_std_concurrent_combine_test : IO Bool := build_scope_for_file "std/src/concurrent/combine_test.mo" "concurrent_combine_test"

// --- All examples/ files ---

#[test]
def test_scope_examples_do_block : IO Bool := build_scope_for_file "examples/do_block.mo" "do_block"

#[test]
def test_scope_examples_factorial : IO Bool := build_scope_for_file "examples/factorial.mo" "factorial"

#[test]
def test_scope_examples_hello : IO Bool := build_scope_for_file "examples/hello.mo" "hello"

#[test]
def test_scope_examples_indexed_monads : IO Bool := build_scope_for_file "examples/indexed_monads.mo" "indexed_monads"

#[test]
def test_scope_examples_iteration : IO Bool := build_scope_for_file "examples/iteration.mo" "iteration"

#[test]
def test_scope_examples_iteration_advanced : IO Bool := build_scope_for_file "examples/iteration_advanced.mo" "iteration_advanced"

#[test]
def test_scope_examples_optics : IO Bool := build_scope_for_file "examples/optics.mo" "optics"

#[test]
def test_scope_examples_pattern_matching : IO Bool := build_scope_for_file "examples/pattern_matching.mo" "pattern_matching"

#[test]
def test_scope_examples_structs : IO Bool := build_scope_for_file "examples/structs.mo" "structs"

#[test]
def test_scope_examples_test_mote : IO Bool := build_scope_for_file "examples/test_mote.mo" "test_mote"

#[test]
def test_scope_examples_tests : IO Bool := build_scope_for_file "examples/tests.mo" "tests"

// --- All lang/ files ---

#[test]
def test_scope_lang_types : IO Bool := build_scope_for_file "lang/src/types.mo" "types"

#[test]
def test_scope_lang_parser : IO Bool := build_scope_for_file "lang/src/parser.mo" "parser"

#[test]
def test_scope_lang_elaborate : IO Bool := build_scope_for_file "lang/src/elaborate.mo" "elaborate"

#[test]
def test_scope_lang_main : IO Bool := build_scope_for_file "cli/src/main.mo" "main"

#[test]
def test_scope_lang_module : IO Bool := build_scope_for_file "lang/src/module.mo" "module"

#[test]
def test_scope_lang_pretty : IO Bool := build_scope_for_file "lang/src/pretty.mo" "pretty"

#[test]
def test_scope_lang_scope : IO Bool := build_scope_for_file "lang/src/scope.mo" "scope"

#[test]
def test_scope_lang_codegen_ir : IO Bool := build_scope_for_file "llvm/src/ir.mo" "codegen_ir"

#[test]
def test_scope_lang_codegen_emit : IO Bool := build_scope_for_file "lang/src/codegen/emit.mo" "codegen_emit"

#[test]
def test_scope_lang_codegen_link : IO Bool := build_scope_for_file "lang/src/codegen/link.mo" "codegen_link"

#[test]
def test_scope_lang_typecheck_infer : IO Bool := build_scope_for_file "lang/src/typecheck/infer.mo" "typecheck_infer"

#[test]
def test_scope_lang_typecheck_unify : IO Bool := build_scope_for_file "lang/src/typecheck/unify.mo" "typecheck_unify"

#[test]
def test_scope_lang_codegen_test_e2e : IO Bool := build_scope_for_file "lang/src/codegen/test/test_e2e.mo" "codegen_test_e2e"

#[test]
def test_scope_lang_codegen_test_link_e2e : IO Bool := build_scope_for_file "lang/src/codegen/test/test_link_e2e.mo" "codegen_test_link_e2e"
