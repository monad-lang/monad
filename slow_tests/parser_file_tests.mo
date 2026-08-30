/// Integration tests for parsing Monad files
/// Tests that the self hosted parser can parse all Monad source files

use io {io}
open IO {io}
use lang.parser {decls_parser}
use lang.parser.core {fail, success}

open ParseResult {fail, success}

/// All init/ files to parse (safe - no box-drawing characters)
#[partial]
def init_files_safe : List String :=
    ["init/id.mo",
     "init/lib.mo",
     "init/list.mo",
     "init/io.mo",
     "init/math.mo",
     "init/number.mo",
     "init/string.mo",
     "init/tests.mo"]

/// All std/ files to parse
// `std/derive.mo` added here specifically as the real-corpus
// verification target for `defmacro`/decl-position macro-call parsing
// (plans/bootstrapping/self-hosted-compiler.md's metaprogramming-
// grammar plan, step 6) -- it has 4 real `defmacro NAME T := decls {
// reflect_type_info! T ...meta }` declarations (Form A, with a nested
// decl-position macro call inside each `decls{}` body), previously
// unparseable by this self-hosted parser at all.
#[partial]
def std_files : List String :=
    ["std/test.mo", "std/derive.mo", "std/path.mo", "std/io.mo", "std/process.mo", "std/lib.mo"]

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
     "lang/codegen/emit.mo"]

/// Parse a single file and return success status
#[partial]
def parse_file (path : String) : Bool :=
    match IO.read_file (Path.path path) {
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

// ================ Full-file-parse (no truncation) tests ================
//
// `decls_parser` is lenient: on a construct it can't parse, `decls_try`
// silently stops and returns whatever it got so far as `success`, not a
// `fail` — so a floor count like `I64.gt count 5` only proves "didn't
// truncate to (near) zero", not "parsed the whole file". Checking
// `success`'s own `remaining` field for emptiness is the actual contract
// these tests care about: every byte of the file got consumed. (See
// `lang/parser.mo`'s `decls_parser_strict` for the twin that turns
// truncation into a hard `fail` instead of a silent partial `success` —
// not used here so this file keeps exercising the lenient path real
// callers actually use, just checking its result more precisely.)

/// Whether a file's `decls_parser` run consumes the ENTIRE input, i.e.
/// nothing is left over in `success`'s own `remaining` field. A `fail` or
/// a non-empty remainder both count as "didn't fully parse."
#[partial]
def file_fully_parses (path : String) : Bool :=
    match IO.read_file (Path.path path) {
        io content =>
            match decls_parser content {
                success rem _ => String.is_empty rem,
                fail _ => false
            },
        _ => false
    }

#[test]
def test_hello_fully_parses : Bool :=
    file_fully_parses "examples/hello.mo"

#[test]
def test_string_fully_parses : Bool :=
    file_fully_parses "init/string.mo"

#[test]
def test_scope_fully_parses : Bool :=
    file_fully_parses "lang/scope.mo"

// `lang/json.mo`/`lang/toml.mo`/`std/map.mo` all open with a `//`/`///`
// comment containing an em dash (multi-byte UTF-8) before their very
// first real declaration — before the `take_while`/`string_body` UTF-8
// stepping fix (see `utf8_char_width`'s doc comment,
// `lang/parser/combinators.mo`) this silently truncated the parse to
// ZERO declarations (verified by bisection while landing that fix). All
// three used to additionally stop short of their true decl count for
// other reasons (juxtaposed list-literal application, `let` inside `if`
// branches, paren type ascriptions, multi-param lambdas, multi-name
// constructor fields, nested-paren class param types — each fixed
// separately, motivated by exactly these files) — confirmed (2026-08-19)
// that all three now parse to completion with zero bytes remaining, so
// these tests assert that directly instead of a conservative floor.
#[test]
def test_json_fully_parses : Bool :=
    file_fully_parses "lang/json.mo"

#[test]
def test_toml_fully_parses : Bool :=
    file_fully_parses "lang/toml.mo"

#[test]
def test_map_fully_parses : Bool :=
    file_fully_parses "std/map.mo"
