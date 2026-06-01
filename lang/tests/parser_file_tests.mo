/// Integration tests for parsing Monad files
/// Tests that the self-hosted parser can parse all Monad source files

use io
open IO
open Monad
use lang.types
use lang.parser
use std.list

open ParseResult

/// All init/ files to parse (safe - no box-drawing characters)
@[partial]
def init_files_safe : List String :=
    ["init/id.mo",
     "init/init.mo",
     "init/io.mo",
     "init/math.mo",
     "init/number.mo",
     "init/string.mo",
     "init/tests.mo"]

/// All std/ files to parse
@[partial]
def std_files : List String :=
    ["std/test.mo"]

/// All examples/ files to parse (safe - no box-drawing characters)
@[partial]
def example_files_safe : List String :=
    ["examples/do_block.mo",
     "examples/factorial.mo",
     "examples/hello.mo",
     "examples/indexed_monads.mo",
     "examples/iteration.mo",
     "examples/iteration_advanced.mo",
     "examples/pattern_matching.mo",
     "examples/structs.mo",
     "examples/test_mote.mo",
     "examples/tests.mo"]

/// All lang/ files to parse (safe - no box-drawing characters)
@[partial]
def lang_files_safe : List String :=
    ["lang/elaborate.mo",
     "lang/main.mo",
     "lang/module.mo",
     "lang/pretty.mo",
     "lang/scope.mo"]

/// Parse a single file and return success status
@[partial]
def parse_file (path : String) : Bool :=
    match IO.read_file path {
        io content =>
            match t2_decls_parser content {
                success _ _ => true,
                fail _ => false
            },
        _ => false
    }

/// Parse multiple files
@[partial]
def parse_all (files : List String) : Bool :=
    match files {
        List.empty => true,
        List.cons f rest =>
            if parse_file f then parse_all rest else false
    }

// ================ init/ file tests ================

@[test]
def test_parse_init_all_safe : Bool := parse_all init_files_safe

@[test]
def test_parse_init_id : Bool := parse_file "init/id.mo"

@[test]
def test_parse_init_io : Bool := parse_file "init/io.mo"

@[test]
def test_parse_init_math : Bool := parse_file "init/math.mo"

@[test]
def test_parse_init_number : Bool := parse_file "init/number.mo"

@[test]
def test_parse_init_string : Bool := parse_file "init/string.mo"

@[test]
def test_parse_init_tests : Bool := parse_file "init/tests.mo"

// ================ std/ file tests ================

@[test]
def test_parse_std_all : Bool := parse_all std_files

@[test]
def test_parse_std_test : Bool := parse_file "std/test.mo"

// ================ examples/ file tests ================

@[test]
def test_parse_examples_all_safe : Bool := parse_all example_files_safe

@[test]
def test_parse_examples_hello : Bool := parse_file "examples/hello.mo"

@[test]
def test_parse_examples_factorial : Bool := parse_file "examples/factorial.mo"

@[test]
def test_parse_examples_do_block : Bool := parse_file "examples/do_block.mo"

@[test]
def test_parse_examples_pattern_matching : Bool := parse_file "examples/pattern_matching.mo"

@[test]
def test_parse_examples_structs : Bool := parse_file "examples/structs.mo"

@[test]
def test_parse_examples_iteration : Bool := parse_file "examples/iteration.mo"

// ================ lang/ file tests (self-hosting) ================

@[test]
def test_parse_lang_all_safe : Bool := parse_all lang_files_safe

@[test]
def test_parse_lang_elaborate : Bool := parse_file "lang/elaborate.mo"

@[test]
def test_parse_lang_main : Bool := parse_file "lang/main.mo"

@[test]
def test_parse_lang_module : Bool := parse_file "lang/module.mo"

@[test]
def test_parse_lang_pretty : Bool := parse_file "lang/pretty.mo"

@[test]
def test_parse_lang_scope : Bool := parse_file "lang/scope.mo"

// ================ Helper for counting declarations ================

/// Count declarations in a file
@[partial]
def count_decls_in_file (path : String) : I64 :=
    match IO.read_file path {
        io content =>
            match t2_decls_parser content {
                success _ decls => list_length decls,
                fail _ => 0
            },
        _ => 0
    }

/// Helper: get list length as I64
@[partial]
def list_length (xs : List A) : I64 :=
    list_length_help xs 0

@[partial]
def list_length_help (xs : List A) (acc : I64) : I64 :=
    match xs {
        List.empty => acc,
        List.cons _ rest => list_length_help rest (I64.add acc 1)
    }

// ================ Declaration count tests ================

@[test]
def test_hello_has_some_decls : Bool :=
    let count := count_decls_in_file "examples/hello.mo" in
    I64.gt count 0

@[test]
def test_string_has_some_decls : Bool :=
    let count := count_decls_in_file "init/string.mo" in
    I64.gt count 0

@[test]
def test_scope_has_some_decls : Bool :=
    let count := count_decls_in_file "lang/scope.mo" in
    I64.gt count 0
