/// Highlighting: spans round-trip their source and classify tokens.
use std::list {List.filter, List.intercalate}
use lib::highlight {HlClass, Span, Highlight.css_class, Highlight.spans}

def joined (src : String) : String :=
    String.concat_list (List.map (fn (s : Span) => s.text) (Highlight.spans src))

/// `class:text` for every non-whitespace span.
def classes (src : String) : String :=
    List.intercalate " " (List.map tagged (List.filter (fn (s : Span) => Bool.not (String.is_empty (String.trim s.text))) (Highlight.spans src)))

def tagged (s : Span) : String :=
    match s {
        { cls, text } => String.concat (Highlight.css_class cls) (String.concat ":" text),
    }

def sample : String :=
    "#[test]\npub def add (a : I64) (b : I64) : I64 :=\n\ta + b  // sum  \n\nlet s := \"hi\" in 42\n"

#[test]
def test_spans_round_trip_whitespace_and_tabs : Bool :=
    String.beq (joined sample) sample

#[test]
def test_round_trip_trailing_blank_after_line_comment : Bool :=
    String.beq (joined "x // c   \n  y") "x // c   \n  y"

#[test]
def test_classes : Bool :=
    String.beq (classes "#[test] pub def add (a : I64) := a + 1 // done")
        "attr:#[ attr:test attr:] kw:pub kw:def fn:add :( :a :: type:I64 :) ::= :a :+ num:1 comment:// done"

#[test]
def test_string_and_keyword : Bool :=
    String.beq (classes "match x { _ => \"s\" }") "kw:match :x :{ :_ :=> str:\"s\" :}"

#[test]
def test_unlexable_source_is_one_plain_span : Bool :=
    String.beq (classes "\"unterminated") ":\"unterminated"
