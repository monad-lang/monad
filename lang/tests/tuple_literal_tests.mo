/// Parser tests for tuple-literal syntax `(a, b, c)`, which desugars to
/// right-nested `Pair.pair` applications (mirrors the Rust reference's
/// `desugar_tuple_literal`, core/src/parser.rs:831-840). `Pair` is the
/// inductive in `init/prelude.mo:204`; `(x,)` and `(x)` both yield just `x`.

use lang.types {Identifier, Term}
use lang.parser {expression}
use lang.parser.core {ParseResult}
use lang.pretty {show_term}

open ParseResult {fail, success}

def empty_ctx : List Identifier := List.empty

/// Did `expression` parse the whole input (no remainder left to consume)?
#[partial]
def parse_full (r : ParseResult Term) (input : String) : Bool :=
    match r {
        success rem out =>
            // Accept a trailing-whitespace-only remainder.
            String.trim rem == "" &&
            // `out`'s show must be non-empty (sanity: actually parsed something).
            String.length (show_term out) > 0,
        fail _ => false
    }

#[test]
def test_parse_tuple_two : Bool :=
    // (x, y)  ->  Pair.pair x y  ->  show "((Pair.pair x) y)"
    match expression empty_ctx "(x, y)" {
        success _ out => show_term out == "((Pair.pair x) y)",
        fail _ => false
    }

#[test]
def test_parse_tuple_three : Bool :=
    // (x, y, z)  ->  Pair.pair x (Pair.pair y z)  ->  "((Pair.pair x) ((Pair.pair y) z))"
    match expression empty_ctx "(x, y, z)" {
        success _ out => show_term out == "((Pair.pair x) ((Pair.pair y) z))",
        fail _ => false
    }

#[test]
def test_parse_tuple_single_trailing_comma : Bool :=
    // (x,)  ->  just x  (matches the reference's desugar_tuple_literal([x]))
    match expression empty_ctx "(x,)" {
        success _ out => show_term out == "x",
        fail _ => false
    }

#[test]
def test_parse_parens_no_comma : Bool :=
    // (x)  ->  just x  (unchanged single-element paren behaviour)
    match expression empty_ctx "(x)" {
        success _ out => show_term out == "x",
        fail _ => false
    }

#[test]
def test_parse_tuple_trailing_comma : Bool :=
    // (x, y,)  ->  Pair.pair x y  (trailing comma optional)
    match expression empty_ctx "(x, y,)" {
        success _ out => show_term out == "((Pair.pair x) y)",
        fail _ => false
    }

#[test]
def test_parse_tuple_consumed : Bool :=
    // The tuple literal is consumed in full (no leftover after the closing `)`).
    parse_full (expression empty_ctx "(1, 2, 3)") "(1, 2, 3)"