/// Parser tests for tuple-literal syntax `(a, b, c)`, which desugars to
/// right-nested `Pair.pair` applications (mirrors the Rust reference's
/// `desugar_tuple_literal`, rust/core/src/parser.rs:831-840). `Pair` is the
/// inductive in `init/prelude.mo:204`; `(x,)` and `(x)` both yield just `x`.

use lib::types {Identifier, ParseTerm}
use lib::parser {expression}
use lib::parser::lower_parse {lower_parse_term, lower_ctx_bare}
use parsec::core {ParseResult, Text}
use lib::pretty {show_term}

open ParseResult {fail, success}

/// Did `expression` parse the whole input (no remainder left to consume)?
#[partial]
def parse_full (r : ParseResult Text ParseTerm) (input : Text) : Bool :=
    match r {
        success rem out =>
            // Accept a trailing-whitespace-only remainder.
            String.trim (Text.rest rem) == "" &&
            // `out`'s show must be non-empty (sanity: actually parsed something).
            String.length (show_term (lower_parse_term lower_ctx_bare out)) > 0,
        fail _ => false
    }

#[test]
def test_parse_tuple_two : Bool :=
    // (x, y)  ->  Pair.pair x y  ->  show "(Pair.pair x y)"
    match expression (Text.of_string "(x, y)") {
        success _ out => show_term (lower_parse_term lower_ctx_bare out) == "(Pair.pair x y)",
        fail _ => false
    }

#[test]
def test_parse_tuple_three : Bool :=
    // (x, y, z)  ->  Pair.pair x (Pair.pair y z)  ->  "(Pair.pair x (Pair.pair y z))"
    match expression (Text.of_string "(x, y, z)") {
        success _ out => show_term (lower_parse_term lower_ctx_bare out) == "(Pair.pair x (Pair.pair y z))",
        fail _ => false
    }

#[test]
def test_parse_tuple_single_trailing_comma : Bool :=
    // (x,)  ->  just x  (matches the reference's desugar_tuple_literal([x]))
    match expression (Text.of_string "(x,)") {
        success _ out => show_term (lower_parse_term lower_ctx_bare out) == "x",
        fail _ => false
    }

#[test]
def test_parse_parens_no_comma : Bool :=
    // (x)  ->  just x  (unchanged single-element paren behaviour)
    match expression (Text.of_string "(x)") {
        success _ out => show_term (lower_parse_term lower_ctx_bare out) == "x",
        fail _ => false
    }

#[test]
def test_parse_tuple_trailing_comma : Bool :=
    // (x, y,)  ->  Pair.pair x y  (trailing comma optional)
    match expression (Text.of_string "(x, y,)") {
        success _ out => show_term (lower_parse_term lower_ctx_bare out) == "(Pair.pair x y)",
        fail _ => false
    }

#[test]
def test_parse_tuple_consumed : Bool :=
    // The tuple literal is consumed in full (no leftover after the closing `)`).
    parse_full (expression (Text.of_string "(1, 2, 3)")) (Text.of_string "(1, 2, 3)")
