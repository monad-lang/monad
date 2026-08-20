use io {io, read_file}
use lang.types {
  LocalScope, ModulePath, NameRef, Scope, ScopeData, id, mp, name, nid,
}
use lang.module {parse_all_decls}
use lang.parser.core {fail, success}
use lang.scope {build_scope_from_decls, scope_resolve_name}

open IO {io, read_file}

def empty_local_scope : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

def make_scope (path : ModulePath) (sd : ScopeData) : Scope := {
    module_id := path,
    scope := sd,
    parent := Option.none,
}

def name_ref (name : String) : NameRef := NameRef.nid (Identifier.id name)

#[partial]
def build_scope_for_file (file_path : String) (mod_name : String) : Bool := 
    match IO.read_file file_path {
        IO.io content => 
            match parse_all_decls content {
                success _ decls => 
                    let path := ModulePath.mp (List.cons (Identifier.id mod_name) List.empty) in
                    let sd := build_scope_from_decls path decls in
                    let scope := make_scope path sd in
                    let type_ref := name_ref "Type" in
                    match scope_resolve_name type_ref scope empty_local_scope {
                        ok _ => true,
                        err _ => false
                    },
                fail _ => false
            },
        _ => false
    }

// --- All init/ files ---

#[test]
def test_scope_init_id : Bool := build_scope_for_file "init/id.mo" "id"

#[test]
def test_scope_init_init : Bool := build_scope_for_file "init/init.mo" "init"

#[test]
def test_scope_init_io : Bool := build_scope_for_file "init/io.mo" "io"

#[test]
def test_scope_init_math : Bool := build_scope_for_file "init/math.mo" "math"

#[test]
def test_scope_init_number : Bool := build_scope_for_file "init/number.mo" "number"

#[test]
def test_scope_init_parser_file : Bool := build_scope_for_file "lang/parser/combinators.mo" "combinators"

#[test]
def test_scope_init_prelude : Bool := build_scope_for_file "init/prelude.mo" "prelude"

#[test]
def test_scope_init_process : Bool := build_scope_for_file "init/process.mo" "process"

#[test]
def test_scope_init_string : Bool := build_scope_for_file "init/string.mo" "string"

#[test]
def test_scope_init_string_profile : Bool := build_scope_for_file "init/string_profile.mo" "string_profile"

#[test]
def test_scope_init_test_constraints : Bool := build_scope_for_file "init/test_constraints.mo" "test_constraints"

#[test]
def test_scope_init_tests : Bool := build_scope_for_file "init/tests.mo" "tests"

#[test]
def test_scope_init_foldable : Bool := build_scope_for_file "init/foldable.mo" "foldable"

#[test]
def test_scope_init_foldable_tests : Bool := build_scope_for_file "init/foldable_tests.mo" "foldable_tests"

#[test]
def test_scope_init_foldable_tests_fold : Bool := build_scope_for_file "init/foldable_tests_fold.mo" "foldable_tests_fold"

#[test]
def test_scope_init_foldable_tests_semi_monoid : Bool := build_scope_for_file "init/foldable_tests_semi_monoid.mo" "foldable_tests_semi_monoid"

#[test]
def test_scope_init_optics : Bool := build_scope_for_file "init/optics.mo" "optics"

#[test]
def test_scope_init_optics_tests : Bool := build_scope_for_file "init/optics_tests.mo" "optics_tests"

// --- All std/ files ---

#[test]
def test_scope_std_test : Bool := build_scope_for_file "std/test.mo" "test"

#[test]
def test_scope_std_base : Bool := build_scope_for_file "std/base.mo" "base"

#[test]
def test_scope_std_bench : Bool := build_scope_for_file "std/bench.mo" "bench"

#[test]
def test_scope_std_list : Bool := build_scope_for_file "std/list.mo" "list"

#[test]
def test_scope_std_list_tests1 : Bool := build_scope_for_file "std/list_tests1.mo" "list_tests1"

#[test]
def test_scope_std_list_tests2 : Bool := build_scope_for_file "std/list_tests2.mo" "list_tests2"

#[test]
def test_scope_std_list_tests3a : Bool := build_scope_for_file "std/list_tests3a.mo" "list_tests3a"

#[test]
def test_scope_std_list_tests3b : Bool := build_scope_for_file "std/list_tests3b.mo" "list_tests3b"

#[test]
def test_scope_std_map : Bool := build_scope_for_file "std/map.mo" "map"

#[test]
def test_scope_std_map_tests : Bool := build_scope_for_file "std/map_tests.mo" "map_tests"

#[test]
def test_scope_std_test_map_full : Bool := build_scope_for_file "std/test_map_full.mo" "test_map_full"

#[test]
def test_scope_std_concurrent_fiber : Bool := build_scope_for_file "std/concurrent/fiber.mo" "concurrent_fiber"

#[test]
def test_scope_std_concurrent_fiber_test : Bool := build_scope_for_file "std/concurrent/fiber_test.mo" "concurrent_fiber_test"

#[test]
def test_scope_std_concurrent_combine : Bool := build_scope_for_file "std/concurrent/combine.mo" "concurrent_combine"

#[test]
def test_scope_std_concurrent_combine_test : Bool := build_scope_for_file "std/concurrent/combine_test.mo" "concurrent_combine_test"

// --- All examples/ files ---

#[test]
def test_scope_examples_do_block : Bool := build_scope_for_file "examples/do_block.mo" "do_block"

#[test]
def test_scope_examples_factorial : Bool := build_scope_for_file "examples/factorial.mo" "factorial"

#[test]
def test_scope_examples_hello : Bool := build_scope_for_file "examples/hello.mo" "hello"

#[test]
def test_scope_examples_indexed_monads : Bool := build_scope_for_file "examples/indexed_monads.mo" "indexed_monads"

#[test]
def test_scope_examples_iteration : Bool := build_scope_for_file "examples/iteration.mo" "iteration"

#[test]
def test_scope_examples_iteration_advanced : Bool := build_scope_for_file "examples/iteration_advanced.mo" "iteration_advanced"

#[test]
def test_scope_examples_optics : Bool := build_scope_for_file "examples/optics.mo" "optics"

#[test]
def test_scope_examples_pattern_matching : Bool := build_scope_for_file "examples/pattern_matching.mo" "pattern_matching"

#[test]
def test_scope_examples_structs : Bool := build_scope_for_file "examples/structs.mo" "structs"

#[test]
def test_scope_examples_test_mote : Bool := build_scope_for_file "examples/test_mote.mo" "test_mote"

#[test]
def test_scope_examples_tests : Bool := build_scope_for_file "examples/tests.mo" "tests"

// --- All lang/ files ---

#[test]
def test_scope_lang_types : Bool := build_scope_for_file "lang/types.mo" "types"

#[test]
def test_scope_lang_parser : Bool := build_scope_for_file "lang/parser.mo" "parser"

#[test]
def test_scope_lang_elaborate : Bool := build_scope_for_file "lang/elaborate.mo" "elaborate"

#[test]
def test_scope_lang_main : Bool := build_scope_for_file "lang/main.mo" "main"

#[test]
def test_scope_lang_module : Bool := build_scope_for_file "lang/module.mo" "module"

#[test]
def test_scope_lang_pretty : Bool := build_scope_for_file "lang/pretty.mo" "pretty"

#[test]
def test_scope_lang_scope : Bool := build_scope_for_file "lang/scope.mo" "scope"

#[test]
def test_scope_lang_codegen_ir : Bool := build_scope_for_file "lang/codegen/ir.mo" "codegen_ir"

#[test]
def test_scope_lang_codegen_emit : Bool := build_scope_for_file "lang/codegen/emit.mo" "codegen_emit"

#[test]
def test_scope_lang_codegen_link : Bool := build_scope_for_file "lang/codegen/link.mo" "codegen_link"

#[test]
def test_scope_lang_typecheck_infer : Bool := build_scope_for_file "lang/typecheck/infer.mo" "typecheck_infer"

#[test]
def test_scope_lang_typecheck_unify : Bool := build_scope_for_file "lang/typecheck/unify.mo" "typecheck_unify"

#[test]
def test_scope_lang_codegen_test_e2e : Bool := build_scope_for_file "lang/codegen/test/test_e2e.mo" "codegen_test_e2e"

#[test]
def test_scope_lang_codegen_test_link_e2e : Bool := build_scope_for_file "lang/codegen/test/test_link_e2e.mo" "codegen_test_link_e2e"
