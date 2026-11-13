// Phase 5's `/` search gate: the wrap rule, the literal-match rule, and the
// selection a search leaves behind (code-editor.md Phase 5, third item).
//
// THE WRAP RULE IS THE WHOLE POINT OF A SEARCH MOTION. A forward search that
// refused to wrap would make `n` at the last match look broken; a backward one
// that wrapped to the wrong end would find the first match when the user
// asked for the last. Both ends are pinned here, on both directions.
//
// THE ORIGIN RULE IS THE OTHER HALF: `n` must find the NEXT match, not the
// one the caret is already on. `Search.next_match` is given the origin its
// caller computes (`commands.mo`'s `search_origin` passes the selection's end
// going forward and its start going backward), and the tests assert both
// halves of that contract.
//
// The fixtures are hand-derived from the rule, never from a run: each
// expected offset is a byte index into the fixture string, written out.

use lib::search {Search.find_from, Search.last_before, Search.next_match,
    Search.selection_at}
use lib::types {Selection, Selections}
use lib::selection {Selection.start, Selection.stop, Selections.primary_sel}
use init::shared {Shared}
use std::list {}

/// The fixture: "foo bar foo baz foo" -- three matches at 0, 8 and 16, and
/// enough non-matching text between them that an off-by-one origin shows.
def sr_text : String := "foo bar foo baz foo"

/// "foo" is 3 bytes; the three matches are at 0, 8, 16.
#[test]
def test_find_from_the_first : Bool :=
    match Search.find_from sr_text "foo" 0 {
        Option.some at => I64.beq at 0,
        Option.none => false
    }

/// From inside the first match's text, the NEXT one at or after the origin.
#[test]
def test_find_from_skips_past_the_origin : Bool :=
    match Search.find_from sr_text "foo" 1 {
        Option.some at => I64.beq at 8,
        Option.none => false
    }

/// From an origin past the last match there is none -- the wrap is the
/// CALLER's rule (`next_match`), not `find_from`'s.
#[test]
def test_find_from_past_the_end_is_none : Bool :=
    match Search.find_from sr_text "foo" 19 {
        Option.some _ => false,
        Option.none => true
    }

/// An empty query never matches -- the guard that keeps `/` + Enter from
/// selecting offset 0 forever.
#[test]
def test_empty_query_never_matches : Bool :=
    match Search.find_from sr_text "" 0 {
        Option.some _ => false,
        Option.none => true
    }

/// The last match strictly before `before`: from the end of the text, the
/// third one at 16.
#[test]
def test_last_before_the_end : Bool :=
    match Search.last_before sr_text "foo" 25 {
        Option.some at => I64.beq at 16,
        Option.none => false
    }

/// Strictly before 16 means the SECOND match at 8 -- a `<=` here would make
/// `N` find the span the caret is on.
#[test]
def test_last_before_is_strict : Bool :=
    match Search.last_before sr_text "foo" 16 {
        Option.some at => I64.beq at 8,
        Option.none => false
    }

/// Before the first match there is none.
#[test]
def test_last_before_the_first_is_none : Bool :=
    match Search.last_before sr_text "foo" 0 {
        Option.some _ => false,
        Option.none => true
    }

/// Forward from the last match WRAPS to the first.
#[test]
def test_forward_wraps_to_the_first : Bool :=
    match Search.next_match sr_text "foo" 19 true {
        Option.some at => I64.beq at 0,
        Option.none => false
    }

/// Backward from the first match WRAPS to the last.
#[test]
def test_backward_wraps_to_the_last : Bool :=
    match Search.next_match sr_text "foo" 0 false {
        Option.some at => I64.beq at 16,
        Option.none => false
    }

/// Forward in the middle finds the next one, no wrap involved.
#[test]
def test_forward_finds_the_next : Bool :=
    match Search.next_match sr_text "foo" 3 true {
        Option.some at => I64.beq at 8,
        Option.none => false
    }

/// Backward in the middle finds the previous one.
#[test]
def test_backward_finds_the_previous : Bool :=
    match Search.next_match sr_text "foo" 16 false {
        Option.some at => I64.beq at 8,
        Option.none => false
    }

/// A query with no match at all is `none` in both directions -- and does NOT
/// wrap onto some other match.
#[test]
def test_no_match_anywhere : Bool :=
    sr_misses (Search.next_match sr_text "zzz" 0 true)
        && sr_misses (Search.next_match sr_text "zzz" 25 false)

def sr_misses (r : Option I64) : Bool :=
    match r {
        Option.some _ => false,
        Option.none => true
    }

/// THE LITERAL RULE: `/a.b` finds the four characters "a.b", not "axb". This
/// is what makes a plain `.` mean a dot, and it is why `/` is not a regex.
#[test]
def test_a_dot_is_a_literal_dot : Bool :=
    let text : String := "axb a.b" in
    match Search.find_from text "a.b" 0 {
        Option.some at => I64.beq at 4,
        Option.none => false
    }

/// A multi-byte match is found and selected by its BYTE span: "é" is two
/// bytes, so the match at 1 has length 2.
#[test]
def test_multibyte_match_spans_its_bytes : Bool :=
    let text : String := "aéb" in
    match Search.find_from text "é" 0 {
        // `at` is read twice (the offset pin, then the span); `I64` is
        // `Copy`, and a named local states the duplicate the rule wants.
        Option.some at =>
            let hit : I64 := at in
            I64.beq hit 1 && I64.beq (sr_sel_len (Search.selection_at hit 2)) 2,
        Option.none => false
    }

/// A selection's length, from one handle (both accessors read it).
def sr_sel_len (sel : Selections) : I64 :=
    match Selections.primary_sel sel {
        Option.none => 0,
        Option.some one => sr_shared_len (Shared.of one)
    }

/// One shared selection's length, from a single handle.
def sr_shared_len (s : Shared Selection) : I64 :=
    Selection.stop (Shared.get s) - Selection.start (Shared.get s)

/// A search SELECTS: the span is `[start, start + len)`, anchor first, so `d`
/// deletes exactly the match.
#[test]
def test_selection_covers_the_match : Bool :=
    let sel : Selections := Search.selection_at 8 3 in
    match Selections.primary_sel sel {
        Option.none => false,
        // One `Shared` handle, because both accessors read the selection
        // (the affine rule's own remedy -- the same shape `sr_sel_len` uses).
        Option.some one => sr_span_is (Shared.of one) 8 11
    }

/// A shared selection's span equals `lo..hi`.
def sr_span_is (s : Shared Selection) (lo : I64) (hi : I64) : Bool :=
    I64.beq (Selection.start (Shared.get s)) lo
        && I64.beq (Selection.stop (Shared.get s)) hi

/// An empty text has no match even for a query in it -- the bound guards
/// `from` against a `String.drop` past the end.
#[test]
def test_empty_text_has_no_match : Bool :=
    sr_misses (Search.find_from "" "foo" 0)
        && sr_misses (Search.next_match "" "foo" 0 true)
