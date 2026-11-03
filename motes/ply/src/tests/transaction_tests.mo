// Phase 1's transaction gate: the editing funnel's contract.
//
// THE VERSION PIN: `Document.version` bumps EXACTLY once per applied
// transaction and NOT AT ALL on a rejected one -- the number LSP
// `didChange` (Phase 6) and MCP `buffer_apply` (Phase 7) both check, so a
// double bump or a rejection that moved the document would surface there
// as a stale-version bug, the exact class this plan's Decision 6 exists
// to prevent. Rejection cases assert the document is UNTOUCHED (text and
// version both), because "rejected" must mean "nothing happened", not
/// "mostly nothing happened".
//
// Field reads inside `#[test]` defs go through `tx_*` accessors, never
// inline, per the recorded `#[test]` + struct-field codegen hazard.

use init::shared {Shared}
use lib::types {Rope, Change}
use lib::rope {Rope.to_string}
use lib::selection {Selections.primary_sel, Selections.cursor}
use lib::model {Document, Document.of_text}
use lib::history {History.undo, History.current_rope}
use lib::rope {Rope.of_string}
use lib::transaction {Transaction.apply, Transaction.validate, Rejection}
use lib::instances {}

// --- Accessors and builders ---

def tx_text (d : Document) : String := Rope.to_string d.rope

def tx_version (d : Document) : I64 := d.version

def tx_cursor (d : Document) : I64 :=
    match Selections.primary_sel d.selections {
        Option.some s => s.head,
        Option.none => 0 - 1
    }

/// One change, hand-built.
def tx_chg (a : I64) (b : I64) (t : String) : Change := { start := a, stop := b, text := t }

/// The applied document, or a marker naming the rejection -- so a failing
/// assertion reports WHICH rejection, not just false.
def tx_applied (d : Document) (chs : List Change) : String :=
    match Transaction.apply d chs {
        Result.ok grown => "ok:" ++ Rope.to_string grown.rope,
        Result.err why => "rejected:" ++ tx_rejection why
    }

/// The rejection as a word, so the assertion output names the case.
def tx_rejection (r : Rejection) : String :=
    match r {
        Rejection.out_of_bounds _ => "out_of_bounds",
        Rejection.overlap _ _ => "overlap",
        Rejection.splits_char _ => "splits_char",
        Rejection.inverted _ _ => "inverted"
    }

// ── Applying: the happy path ──────────────────────────────────────────────

#[test]
def test_apply_insert : Bool :=
    String.beq (tx_applied (Document.of_text "ab") [tx_chg 1 1 "XY"]) "ok:aXYb"

#[test]
def test_apply_delete : Bool :=
    String.beq (tx_applied (Document.of_text "abcdef") [tx_chg 2 5 ""]) "ok:abf"

#[test]
def test_apply_replace : Bool :=
    String.beq (tx_applied (Document.of_text "hello world") [tx_chg 6 11 "ply"]) "ok:hello ply"

/// Several changes in ONE transaction: right-to-left application keeps
/// every offset valid, and the text agrees with a hand-built oracle.
/// Fixture: "abcdefghij", delete [8,10) "ij", insert [2,2) "XY":
/// -> "abXYcdefgh".
#[test]
def test_apply_multi : Bool :=
    let chs : List Change := [tx_chg 2 2 "XY", tx_chg 8 10 ""] in
    String.beq (tx_applied (Document.of_text "abcdefghij") chs) "ok:abXYcdefgh"

/// An empty change list is a legal transaction (no-op): applied, version
/// bumped, text unchanged. The bump is deliberate -- the edit SURFACE
/// moved even when the edit did not, and Phase 6/7's version checks
/// expect every applied transaction to move the number.
#[test]
def test_apply_empty_list : Bool :=
    match Transaction.apply (Document.of_text "abc") List.empty {
        Result.ok d => tx_noop_check d,
        Result.err _ => false
    }

/// The no-op's two assertions, split so `d` is used once per def.
def tx_noop_check (d : Document) : Bool :=
    let shared : Shared Document := Shared.of d in
    tx_noop_text (Shared.get shared) && tx_noop_version (Shared.get shared)

def tx_noop_text (d : Document) : Bool := String.beq (tx_text d) "abc"

def tx_noop_version (d : Document) : Bool := I64.beq (tx_version d) 1

// ── THE VERSION PIN ───────────────────────────────────────────────────────

/// One transaction: version 0 -> 1. Not 2, not 0 -- the single bump.
#[test]
def test_version_bumps_once : Bool :=
    match Transaction.apply (Document.of_text "abc") [tx_chg 0 0 "x"] {
        Result.ok d => I64.beq (tx_version d) 1,
        Result.err _ => false
    }

/// Two transactions: 0 -> 1 -> 2, one bump each, the second's document
/// chained from the first.
#[test]
def test_version_bumps_per_transaction : Bool :=
    match Transaction.apply (Document.of_text "a") [tx_chg 1 1 "b"] {
        Result.ok d1 =>
            match Transaction.apply d1 [tx_chg 2 2 "c"] {
                Result.ok d2 => I64.beq (tx_version d2) 2,
                Result.err _ => false
            },
        Result.err _ => false
    }

// ── Selections travel with the transaction ──────────────────────────────

/// A cursor AFTER an insert moves with the text: cursor at 3, insert
/// [1,1) "XY" -> cursor at 5. (The fixture's cursor starts somewhere other
/// than 0 -- a cursor at 0 is before the change and correctly stays.)
#[test]
def test_cursor_shifts : Bool :=
    let base : Document := Document.of_text "abc" in
    let doc : Document := { base with selections := Selections.cursor 3 } in
    match Transaction.apply doc [tx_chg 1 1 "XY"] {
        Result.ok d => I64.beq (tx_cursor d) 5,
        Result.err _ => false
    }

/// A cursor BEFORE the insert stays put -- the other half of the rule.
#[test]
def test_cursor_before_stays : Bool :=
    let base : Document := Document.of_text "abc" in
    let doc : Document := { base with selections := Selections.cursor 0 } in
    match Transaction.apply doc [tx_chg 1 1 "XY"] {
        Result.ok d => I64.beq (tx_cursor d) 0,
        Result.err _ => false
    }

/// A cursor inside a deleted range collapses to the range's start -- the
/// same rule `selection_tests` pins, exercised through the funnel. The
/// fixture's cursor starts at 4, INSIDE [2,5).
#[test]
def test_cursor_collapses_in_delete : Bool :=
    let base : Document := Document.of_text "abcdefgh" in
    let doc : Document := { base with selections := Selections.cursor 4 } in
    match Transaction.apply doc [tx_chg 2 5 ""] {
        Result.ok d => I64.beq (tx_cursor d) 2,
        Result.err _ => false
    }

// ── Rejections: the document is untouched ───────────────────────────────

/// An offset past the end is rejected and the document keeps its text
/// AND its version -- "nothing happened".
#[test]
def test_reject_out_of_bounds : Bool :=
    match Transaction.apply (Document.of_text "abc") [tx_chg 9 12 "x"] {
        Result.err _ => tx_untouched,
        Result.ok _ => false
    }

/// "Untouched" is a constant: the document a rejection must equal.
def tx_untouched : Bool := String.beq (tx_text (Document.of_text "abc")) "abc"

/// A negative offset is rejected.
#[test]
def test_reject_negative : Bool :=
    let doc : Document := Document.of_text "abc" in
    match Transaction.apply doc [tx_chg (0 - 1) 1 "x"] {
        Result.err _ => true,
        Result.ok _ => false
    }

/// An inverted change (`stop < start`) is rejected by the bounds check.
#[test]
def test_reject_inverted : Bool :=
    match Transaction.apply (Document.of_text "abc") [tx_chg 2 1 "x"] {
        Result.err _ => true,
        Result.ok _ => false
    }

/// Unsorted changes are rejected: the second starts before the first ends.
#[test]
def test_reject_unsorted : Bool :=
    let chs : List Change := [tx_chg 4 6 "x", tx_chg 1 2 "y"] in
    match Transaction.apply (Document.of_text "0123456789") chs {
        Result.err _ => true,
        Result.ok _ => false
    }

/// Overlapping changes are rejected: [2,6) and [5,8) share a byte.
#[test]
def test_reject_overlap : Bool :=
    let chs : List Change := [tx_chg 2 6 "x", tx_chg 5 8 "y"] in
    match Transaction.apply (Document.of_text "0123456789") chs {
        Result.err _ => true,
        Result.ok _ => false
    }

/// An adjacent pair is LEGAL: [2,6) then [6,8) touch but do not overlap,
/// because the ranges are half-open. Pinned so the overlap check cannot
/// grow an off-by-one and reject the touching case editors rely on.
#[test]
def test_adjacent_is_legal : Bool :=
    let chs : List Change := [tx_chg 2 6 "x", tx_chg 6 8 "y"] in
    match Transaction.apply (Document.of_text "0123456789") chs {
        Result.ok d => String.beq (tx_text d) "01xy89",
        Result.err _ => false
    }

/// THE UTF-8 PIN (the plan's named risk): an offset inside a multi-byte
/// sequence is REJECTED rather than producing invalid text. Fixture
/// "café": the `é` is bytes [3,5), so offset 4 is a continuation byte.
#[test]
def test_reject_splits_char : Bool :=
    match Transaction.apply (Document.of_text "café") [tx_chg 4 4 "x"] {
        Result.err _ => tx_untouched_cafe,
        Result.ok _ => false
    }

/// "Untouched" for the UTF-8 fixture.
def tx_untouched_cafe : Bool := String.beq (tx_text (Document.of_text "café")) "café"

/// The legal boundary next to it is accepted: offset 5 is the character
/// after `é`, an ordinary ASCII boundary.
#[test]
def test_accepts_char_boundary : Bool :=
    match Transaction.apply (Document.of_text "café") [tx_chg 5 5 "!"] {
        Result.ok d => String.beq (tx_text d) "café!",
        Result.err _ => false
    }

/// A change list where only the LAST change is bad is rejected whole --
/// validation is all-or-nothing, so no half-applied edit list exists.
#[test]
def test_reject_is_whole_list : Bool :=
    let chs : List Change := [tx_chg 0 0 "good", tx_chg 99 99 "bad"] in
    match Transaction.apply (Document.of_text "abc") chs {
        Result.err _ => true,
        Result.ok _ => false
    }

// ── validate directly ────────────────────────────────────────────────────

#[test]
def test_validate_ok : Bool :=
    match Transaction.validate (Rope.of_string "abc") [tx_chg 0 0 "x"] {
        Result.ok _ => true,
        Result.err _ => false
    }

#[test]
def test_validate_empty_list : Bool :=
    match Transaction.validate (Rope.of_string "abc") List.empty {
        Result.ok _ => true,
        Result.err _ => false
    }

// ── bytes and undo integration ───────────────────────────────────────────

/// A transaction on a CHUNKED document (over the 1 KiB target) applies
/// correctly -- the funnel's rope walk, not the single-leaf case.
#[test]
def test_apply_on_chunked : Bool :=
    let doc : Document := Document.of_text (tx_repeat "ab" 800) in
    match Transaction.apply doc [tx_chg 900 1100 "XY"] {
        Result.ok d =>
            let want : String := tx_flat_replace (tx_repeat "ab" 800) 900 1100 "XY" in
            String.beq (tx_text d) want,
        Result.err _ => false
    }

/// Undo after a transaction returns the pre-transaction rope: the
/// document's history was committed by the funnel, so `History.undo`
/// works on `d.history` exactly as it does on a bare history.
#[test]
def test_undo_through_the_funnel : Bool :=
    match Transaction.apply (Document.of_text "abc") [tx_chg 3 3 "def"] {
        Result.ok d =>
            match History.undo d.history {
                Option.some back =>
                    let rope : Rope := History.current_rope back in
                    String.beq (Rope.to_string rope) "abc",
                Option.none => false
            },
        Result.err _ => false
    }

// --- helpers ---

#[terminating]
def tx_repeat (s : String) (n : I64) : String :=
    if I64.beq n 0 then "" else String.concat s (tx_repeat s (n - 1))

/// The flat oracle (the same one `rope_tests` uses).
def tx_flat_replace (s : String) (start : I64) (stop : I64) (text : String) : String :=
    String.concat (String.slice s 0 start) (String.concat text (String.drop stop s))
