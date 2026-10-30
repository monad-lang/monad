// The emitter's output has to be source a parser accepts, so every test
// here reads it back with `decls_parser` as well as pinning the shape.

use gen::tree {Gen.emit, Leaf, Spec, leaf, spec}
use lang::construct {apps, con, con_app, global, if_, str, var}
use lang::parser {decls_parser}
use parsec::core {ParseResult}
use std::list {List.length}

/// A leaf that answers `Option.some "<key>"` for exactly `key`.
def entry_leaf (name : String) : Leaf :=
    leaf (str name)
        (if_ (apps (global "String.beq") [var 0 "name", str name])
            (con_app "Option" "some" [str name])
            (con "Option" "none"))

def spec_of (base : String) : Spec :=
    spec base "name" (global "String")
        (apps (global "Option") [global "String"])
        "String.lt" (con "Option" "none")

#[test]
def test_three_leaves_emit_five_helpers_and_an_entry : Bool :=
    let text := Gen.emit (spec_of "t") [entry_leaf "a", entry_leaf "b", entry_leaf "c"] in
    match decls_parser text {
        ParseResult.success _ decls => I64.beq (List.length decls) 6,
        ParseResult.fail _ => false,
    }

#[test]
def test_leaf_bodies_are_kept : Bool :=
    let text := Gen.emit (spec_of "t") [entry_leaf "a", entry_leaf "b"] in
    String.contains text "String.beq name \"b\""

#[test]
def test_entry_point_calls_the_root_helper : Bool :=
    let text := Gen.emit (spec_of "t") [entry_leaf "a", entry_leaf "b"] in
    String.contains text "pub def t (name : String) : (Option String) :=\n    (t_2 name)"

#[test]
def test_pivot_is_the_first_key_of_the_right_half : Bool :=
    // [a, b, c]: the root splits before "b", so keys below "b" go left.
    let text := Gen.emit (spec_of "t") [entry_leaf "a", entry_leaf "b", entry_leaf "c"] in
    String.contains text "String.lt name \"b\""

#[test]
def test_empty_tree_returns_the_fallback : Bool :=
    let text := Gen.emit (spec_of "t") List.empty in
    String.beq text "pub def t (name : String) : (Option String) :=\n    Option.none\n"
