/// Parse -> pretty-print -> re-parse round-trip tests for the `use`/`open`
/// brace syntax. Moved here from `slow_tests/parser_file_tests.mo`: these
/// parse tiny inline snippets (sub-millisecond each), not real files, so
/// they don't belong in the directory reserved for expensive whole-file
/// parses -- they were just sitting outside the fast pre-commit sweep for
/// no reason.

use lang.types {Decl}
use lang.parser {open_parser, use_parser}
use lang.parser.lower_parse {lower_parse_decl}
use lang.parser.core {ParseResult, fail, success}
use lang.pretty {show_decl}

open ParseResult {fail, success}

#[partial]
def parse_decl_succeeds (r : ParseResult ParseDecl) : Bool :=
    match r {
        success _ _ => true,
        fail _ => false
    }

#[test]
def test_roundtrip_use_glob : Bool :=
    match use_parser "use io {*}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl (lower_parse_decl List.empty out))),
        fail _ => false
    }

#[test]
def test_roundtrip_use_nested : Bool :=
    match use_parser "use io {file {read}}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl (lower_parse_decl List.empty out))),
        fail _ => false
    }

#[test]
def test_roundtrip_use_nested_rename : Bool :=
    match use_parser "use io {file as f {read}}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl (lower_parse_decl List.empty out))),
        fail _ => false
    }

#[test]
def test_roundtrip_open_filtered : Bool :=
    match open_parser "open io {println}" {
        success _ out => parse_decl_succeeds (open_parser (show_decl (lower_parse_decl List.empty out))),
        fail _ => false
    }

#[test]
def test_roundtrip_scoped_open : Bool :=
    match open_parser "open io {println} in def main : IO Unit := println \"hi\"" {
        success _ out => parse_decl_succeeds (open_parser (show_decl (lower_parse_decl List.empty out))),
        fail _ => false
    }
