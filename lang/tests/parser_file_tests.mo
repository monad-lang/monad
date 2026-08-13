/// Integration tests for parsing Monad files
/// Tests that the self hosted parser can parse all Monad source files

use io {io, read_file}
open IO {io, read_file}
use lang.types {Decl}
use lang.parser {decls_parser, open_parser, use_parser}
use lang.parser.core {ParseResult, fail, success}
use lang.pretty {show_decl}

open ParseResult {fail, success}

/// All init/ files to parse (safe - no box-drawing characters)
#[partial]
def init_files_safe : List String :=
    ["init/id.mo",
     "init/init.mo",
     "init/io.mo",
     "init/math.mo",
     "init/number.mo",
     "init/string.mo",
     "init/tests.mo"]

/// All std/ files to parse
#[partial]
def std_files : List String :=
    ["std/test.mo"]

/// All examples/ files to parse (safe - no box-drawing characters)
#[partial]
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
#[partial]
def lang_files_safe : List String :=
    ["lang/elaborate.mo",
     "lang/main.mo",
     "lang/module.mo",
     "lang/pretty.mo",
     "lang/scope.mo"]

/// All init/ files with UTF-8 characters (previously blocked by byte indexing)
#[partial]
def init_files_utf8 : List String :=
    ["init/string_profile.mo",
     "init/optics.mo"]

/// All std/ files with UTF-8 characters
#[partial]
def std_files_utf8 : List String :=
    ["std/test_map_full.mo",
     "std/list_tests3b.mo",
     "std/map.mo",
     "std/base.mo",
     "std/list.mo"]

/// All examples/ files with UTF-8 characters
#[partial]
def example_files_utf8 : List String :=
    ["examples/indexed_monads.mo",
     "examples/optics.mo"]

/// All lang/ files with UTF-8 characters (self hosting)
#[partial]
def lang_files_utf8 : List String :=
    ["lang/parser.mo",
     "lang/types.mo",
     "lang/eval.mo",
     "lang/eval_t2.mo",
     "lang/eval_term.mo",
     "lang/lower.mo",
     "lang/codegen/emit.mo"]

/// Parse a single file and return success status
#[partial]
def parse_file (path : String) : Bool :=
    match IO.read_file path {
        io content =>
            match decls_parser content {
                success _ _ => true,
                fail _ => false
            },
        _ => false
    }

/// Parse multiple files
#[partial]
def parse_all (files : List String) : Bool :=
    match files {
        List.empty => true,
        List.cons f rest =>
            if parse_file f then parse_all rest else false
    }

// ================ Aggregate parse tests ================
//
// Only the `parse_all` aggregate tests are kept here -- the per-file
// variants that used to sit alongside each of these (test_parse_init_id,
// test_parse_lang_module, etc.) checked nothing an aggregate test didn't
// already cover (`parse_all` fails the moment ANY listed file fails to
// parse), so they were pure redundant surface area, not extra coverage.

#[test]
def test_parse_init_all_safe : Bool := parse_all init_files_safe

#[test]
def test_parse_std_all : Bool := parse_all std_files

#[test]
def test_parse_examples_all_safe : Bool := parse_all example_files_safe

#[test]
def test_parse_lang_all_safe : Bool := parse_all lang_files_safe

#[test]
def test_parse_init_all_utf8 : Bool := parse_all init_files_utf8

#[test]
def test_parse_std_all_utf8 : Bool := parse_all std_files_utf8

#[test]
def test_parse_examples_all_utf8 : Bool := parse_all example_files_utf8

#[test]
def test_parse_lang_all_utf8 : Bool := parse_all lang_files_utf8

// test_parse_all_utf8_files removed: parsed the exact union of the four
// category lists above via parse_all (which short-circuits on the first
// failure), giving strictly worse debugging signal than the per-category
// tests on any failure while adding no new coverage.

// ================ Helper for counting declarations ================

/// Count declarations in a file
#[partial]
def count_decls_in_file (path : String) : I64 :=
    match IO.read_file path {
        io content =>
            match decls_parser content {
                success _ decls => list_length decls,
                fail _ => 0
            },
        _ => 0
    }

/// Helper: get list length as I64
#[partial]
def list_length (xs : List A) : I64 :=
    list_length_help xs 0

#[partial]
def list_length_help (xs : List A) (acc : I64) : I64 :=
    match xs {
        List.empty => acc,
        List.cons _ rest => list_length_help rest (I64.add acc 1)
    }

// ================ Declaration count tests ================

#[test]
def test_hello_has_some_decls : Bool :=
    let count := count_decls_in_file "examples/hello.mo" in
    I64.gt count 0

#[test]
def test_string_has_some_decls : Bool :=
    let count := count_decls_in_file "init/string.mo" in
    I64.gt count 0

#[test]
def test_scope_has_some_decls : Bool :=
    let count := count_decls_in_file "lang/scope.mo" in
    I64.gt count 0

// `lang/json.mo`/`lang/toml.mo` both open with a `//`/`///` comment
// containing an em dash (multi-byte UTF-8) before their very first real
// declaration — before the `take_while`/`string_body` UTF-8 stepping
// fix (see `utf8_char_width`'s doc comment, lang/parser/combinators.mo)
// this silently truncated the parse to ZERO declarations (verified by
// bisection while landing that fix). Both files still stop short of
// their true decl count today (~194/~167 respectively, going by a raw
// grep of top-level declaration keywords) — some other, not yet
// identified construct further down still trips `decls_try`'s
// silent-truncate-on-fail fallback — so these floors are deliberately
// conservative (verified non-regression against the *specific* UTF-8
// bug, not a claim of full-file completeness) rather than exact counts.
#[test]
def test_json_utf8_comment_does_not_truncate_to_zero : Bool :=
    let count := count_decls_in_file "lang/json.mo" in
    I64.gt count 5

#[test]
def test_toml_utf8_comment_does_not_truncate_to_zero : Bool :=
    let count := count_decls_in_file "lang/toml.mo" in
    I64.gt count 5

// ================ use/open brace syntax round-trip tests ================
// parse -> pretty-print -> re-parse should succeed for the new syntax.

#[partial]
def parse_decl_succeeds (r : ParseResult Decl) : Bool :=
    match r {
        success _ _ => true,
        fail _ => false
    }

#[test]
def test_roundtrip_use_glob : Bool :=
    match use_parser "use io {*}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl out)),
        fail _ => false
    }

#[test]
def test_roundtrip_use_nested : Bool :=
    match use_parser "use io {file {read}}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl out)),
        fail _ => false
    }

#[test]
def test_roundtrip_use_nested_rename : Bool :=
    match use_parser "use io {file as f {read}}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl out)),
        fail _ => false
    }

#[test]
def test_roundtrip_open_filtered : Bool :=
    match open_parser "open io {println}" {
        success _ out => parse_decl_succeeds (open_parser (show_decl out)),
        fail _ => false
    }

#[test]
def test_roundtrip_scoped_open : Bool :=
    match open_parser "open io {println} in def main : IO Unit := println \"hi\"" {
        success _ out => parse_decl_succeeds (open_parser (show_decl out)),
        fail _ => false
    }
