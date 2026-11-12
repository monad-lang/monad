// Phase 1's selection gate: mapping across insert/delete, the collapse
// rule, and the primary-selection accessor.
//
// EVERY EXPECTATION IS AN OFFSET COUNTED BY HAND over fixtures whose bytes
// are written beside them (the toolkit suite's discipline). The collapse
// rule is the one that reads as if it must be off by one somewhere, so its
// two boundary cases are pinned from both sides: a point exactly AT the
// deleted range's start, and one exactly AT its end.
//
// Field reads inside `#[test]` defs go through the `sel_*` accessors below,
// never inline, per the recorded `#[test]` + struct-field codegen hazard.

use lib::types {Selection, Selections, Change}
use lib::selection {Selection.span, Selection.start, Selection.stop, Selection.is_empty,
    Selection.map_through, Selection.map_through_changes, Selections.map_through_changes,
    Selections.cursor, Selections.primary_sel, Selections.collapse}
use init::shared {Shared}
// `List.length` lives in `init/src/list.mo` (ambient and pure) as of the
// upstream move, so this import pulls the module's INSTANCES into scope
// and names nothing -- the empty brace list is the documented form.
use std::list {}
use lib::instances {}

// --- Accessors: one read per binding, each used once ---

def sel_anchor (s : Selection) : I64 := s.anchor

def sel_head (s : Selection) : I64 := s.head

/// A selection's low end via the span.
def sel_start (s : Selection) : I64 := Selection.start s

/// A selection's high end via the span.
def sel_stop (s : Selection) : I64 := Selection.stop s

/// One change, hand-built.
def sel_chg (a : I64) (b : I64) (t : String) : Change := { start := a, stop := b, text := t }

/// A cursor (empty selection) at `off`.
def sel_at (off : I64) : Selection := { anchor := off, head := off }

// ── span: the backward-drag case ──────────────────────────────────────────

#[test]
def test_span_forward : Bool :=
    match Selection.span (sel_at 5) { Pair.pair lo hi => I64.beq lo 5 && I64.beq hi 5 }

/// A BACKWARD drag is `anchor > head`, and `span` orders it -- the one
/// place the backward case is handled, so nothing downstream can get it
/// wrong separately.
#[test]
def test_span_orders_a_backward_drag : Bool :=
    let s : Selection := { anchor := 8, head := 3 } in
    match Selection.span s { Pair.pair lo hi => I64.beq lo 3 && I64.beq hi 8 }

#[test]
def test_start_stop_of_backward_drag : Bool :=
    let s : Selection := { anchor := 8, head := 3 } in
    I64.beq (sel_start s) 3 && I64.beq (sel_stop s) 8

#[test]
def test_is_empty : Bool :=
    Selection.is_empty (sel_at 4) && Bool.not (Selection.is_empty { anchor := 3, head := 9 })

// ── Mapping through one change: the insert case ──────────────────────────

/// A cursor AFTER an insert shifts by the inserted length: 6 bytes of new
/// text before offset 10 moves a cursor at 10 to 16.
#[test]
def test_insert_shifts_after : Bool :=
    let after : Selection := Selection.map_through (sel_at 10) (sel_chg 4 4 "abcdef") in
    I64.beq (sel_head after) 16

/// A cursor AT the insert point stays: typing inserts AT the cursor, so
/// the cursor must not jump over what was just typed. This is the pin the
/// plan's gate names ("a selection after an insert shifts by the insert's
/// length" -- the at-the-point case is the exception the rule implies).
#[test]
def test_insert_at_point_stays : Bool :=
    let after : Selection := Selection.map_through (sel_at 4) (sel_chg 4 4 "abcdef") in
    I64.beq (sel_head after) 4

#[test]
def test_insert_before_leaves_unchanged : Bool :=
    let after : Selection := Selection.map_through (sel_at 2) (sel_chg 4 4 "abcdef") in
    I64.beq (sel_head after) 2

/// A selection SPANNING the insert point grows: anchor before, head after.
#[test]
def test_insert_grows_spanning_selection : Bool :=
    let s : Selection := { anchor := 2, head := 8 } in
    let after : Selection := Selection.map_through s (sel_chg 4 4 "abc") in
    I64.beq (sel_anchor after) 2 && I64.beq (sel_head after) 11

// ── Mapping through one change: the delete case ──────────────────────────

/// A cursor strictly inside the deleted range collapses to the range's
/// start: THE COLLAPSE RULE (the Phase 1 gate's named case).
#[test]
def test_delete_collapses_inside_to_start : Bool :=
    let after : Selection := Selection.map_through (sel_at 7) (sel_chg 4 10 "") in
    I64.beq (sel_head after) 4

/// A cursor exactly AT the range's start also answers the start: an
/// empty delete target at the same offset is the same point.
#[test]
def test_delete_at_start_answers_start : Bool :=
    let after : Selection := Selection.map_through (sel_at 4) (sel_chg 4 10 "") in
    I64.beq (sel_head after) 4

/// A cursor exactly AT the range's end is the first point that shifts:
/// it was strictly after every deleted byte, so it moves back by the
/// deleted length.
#[test]
def test_delete_at_end_shifts_back : Bool :=
    let after : Selection := Selection.map_through (sel_at 10) (sel_chg 4 10 "") in
    I64.beq (sel_head after) 4

/// A cursor past the range shifts back by the deleted length: 6 deleted
/// bytes before offset 14 move it to 8.
#[test]
def test_delete_after_shifts_back : Bool :=
    let after : Selection := Selection.map_through (sel_at 14) (sel_chg 4 10 "") in
    I64.beq (sel_head after) 8

#[test]
def test_delete_before_leaves_unchanged : Bool :=
    let after : Selection := Selection.map_through (sel_at 2) (sel_chg 4 10 "") in
    I64.beq (sel_head after) 2

/// A replace (delete + insert at once): the delta is `text - deleted`, and
/// a past-cursor moves by it. 6 deleted, 2 inserted = net -4: offset 14
/// -> 10.
#[test]
def test_replace_shifts_by_delta : Bool :=
    let after : Selection := Selection.map_through (sel_at 14) (sel_chg 4 10 "xy") in
    I64.beq (sel_head after) 10

// ── Mapping through a whole list ──────────────────────────────────────────

/// Two independent inserts, sorted: a cursor between them shifts by only
/// the first's length; a cursor after both by both.
#[test]
def test_two_inserts : Bool :=
    // Both cursors map through the same change list, so the list is shared
    // (`Shared` is the affine rule's own remedy for a two-read value).
    let shared : Shared (List Change) := Shared.of [sel_chg 2 2 "AAA", sel_chg 8 8 "BB"] in
    let mid : Selection := Selection.map_through_changes (sel_at 5) (Shared.get shared) in
    let after : Selection := Selection.map_through_changes (sel_at 12) (Shared.get shared) in
    I64.beq (sel_head mid) 8 && I64.beq (sel_head after) 17

/// The insert-then-delete interplay, sorted: an insert at 2 of 3 bytes and
/// a delete of [5,9). A cursor at 7 sits inside the delete in OLD
/// coordinates, so it collapses to the delete's start (5) -- and the
/// earlier insert's delta still applies on top, because that insert sits
/// before the collapsed point. 5 + 3 = 8: the fold clamps to the OLD
/// start and keeps the carried delta, which is what makes it agree with
/// the rope applying the same two changes.
#[test]
def test_insert_then_delete_uses_old_coordinates : Bool :=
    let chs : List Change := [sel_chg 2 2 "AAA", sel_chg 5 9 ""] in
    let after : Selection := Selection.map_through_changes (sel_at 7) chs in
    I64.beq (sel_head after) 8

/// Every selection maps, and the primary index survives. The mapped
/// record is read through the `sel_*` accessors rather than a record
/// pattern: a `{ .. }` in a match scrutinee inside a `#[test]` def is the
/// recorded two-host inference failure, and an accessor read through a
/// helper def is its remedy.
#[test]
def test_all_selections_map_and_primary_survives : Bool :=
    let chs : List Change := [sel_chg 4 4 "abcdef"] in
    let mapped : Selections := Selections.map_through_changes (sel_two_ranges) chs in
    // `mapped` feeds two assertions, so it is shared: `Shared A` is the
    // affine rule's own remedy for a two-read value, and a selections
    // record is not one of the value types with a Copy instance.
    let shared : Shared Selections := Shared.of mapped in
    I64.beq (sel_count (Shared.get shared)) 2
        && sel_primary_maps_to_itself (Shared.get shared)

/// The fixture: a cursor at 10 and a span [1,3), primary the span. The
/// span is a helper def, not a bare literal inside the list: a `{ .. }`
/// in argument position (inside the list literal) is the OTHER half of
/// the two-host inference gotcha, and a def with a declared return type
/// is its remedy.
def sel_two_ranges : Selections :=
    { ranges := [sel_at 10, sel_span_1_3], primary := 1 }

/// A backward-drag-shaped span [1,3): anchor 1, head 3.
def sel_span_1_3 : Selection := { anchor := 1, head := 3 }

/// How many ranges a selections value holds.
def sel_count (s : Selections) : I64 := List.length (sel_ranges s)

/// The ranges field, read once through a helper def.
def sel_ranges (s : Selections) : List Selection :=
    match s {
        { ranges, .. } => ranges
    }

/// The primary selection after mapping: [1,3) sits entirely before the
/// insert at 4, so it maps to itself.
def sel_primary_maps_to_itself (s : Selections) : Bool :=
    match Selections.primary_sel s {
        Option.some p => sel_spans_1_to_3 p,
        Option.none => false
    }

/// The mapped second selection's bounds, as a helper so the `Option.some`
/// pattern bind is used once (the pattern-bound variable the affine
/// analysis cannot type). [1,3) is entirely before the insert at 4, so it
/// maps to itself.
def sel_spans_1_to_3 (p : Selection) : Bool :=
    I64.beq (sel_start p) 1 && I64.beq (sel_stop p) 3

// ── collapse ─────────────────────────────────────────────────────────────

#[test]
def test_collapse_leaves_a_cursor : Bool :=
    match Selections.collapse (Selections.cursor 0) {
        { ranges, .. } =>
            match ranges {
                List.cons one _ => Selection.is_empty one,
                List.empty => false
            }
    }

/// A drag collapses to its head, wherever the anchor was. Same
/// accessor-shape rule as the mapping test above: no record pattern in a
/// `#[test]` def's match.
#[test]
def test_collapse_takes_the_head : Bool :=
    match sel_first (Selections.collapse (sel_backward_drag)) {
        Option.some one => sel_is_head_three (Shared.of one),
        Option.none => false
    }

/// A collapsed drag answers head 3 and anchor 3: the pattern bind is
/// shared for the same reason `test_all_selections_map_and_primary_survives`
/// shares its record.
def sel_is_head_three (one : Shared Selection) : Bool :=
    I64.beq (sel_anchor (Shared.get one)) 3
        && I64.beq (sel_head (Shared.get one)) 3

/// The fixture: one backward drag, anchor 8 head 3. Same nested-literal
/// rule as `sel_two_ranges` above.
def sel_backward_drag : Selections :=
    { ranges := [sel_drag_8_3], primary := 0 }

/// A backward drag: anchor 8, head 3.
def sel_drag_8_3 : Selection := { anchor := 8, head := 3 }

/// The first range, if any.
def sel_first (s : Selections) : Option Selection :=
    match sel_ranges s {
        List.cons one _ => Option.some one,
        List.empty => Option.none
    }

// ── primary_sel ───────────────────────────────────────────────────────────

#[test]
def test_primary_sel_picks_by_index : Bool :=
    let sel : Selections :=
        { ranges := [sel_at 1, sel_at 2, sel_at 3], primary := 2 } in
    match Selections.primary_sel sel {
        Option.some p => I64.beq (sel_head p) 3,
        Option.none => false
    }

#[test]
def test_primary_sel_out_of_range_is_none : Bool :=
    let sel : Selections := { ranges := [sel_at 1], primary := 5 } in
    match Selections.primary_sel sel {
        Option.some _ => false,
        Option.none => true
    }
