// Ply's selections: the anchor/head pairs a selection-first editor acts on.
//
// A SELECTION IS TWO POINTS, NOT A RANGE (the plan's Decision 2 and §1):
// `anchor` is where it started, `head` is where the cursor is, and either
// can be ahead of the other -- a backward drag is `anchor > head`. Anything
// that needs the left/right order goes through `Selection.span`, never
// through a field read, so the backward case is handled exactly once.
//
// MAPPING THROUGH A CHANGE IS THE ONE PLACE SELECTION-PRESERVATION LOGIC
// LIVES (the plan's §1 note). A `Change` replaces `[start, stop)` with
// `text`; a point around it moves accordingly:
//
//   * at or past `stop`             -> shift by the change's delta
//   * strictly inside [start, stop)  -> clamp to `start` (the collapse rule)
//   * at or before `start`          -> unchanged
//
// A point exactly at `start` is "at or before": an insert there leaves the
// cursor before the new text (typing inserts AT the cursor, so the cursor
// must not jump over what was just typed), and a delete starting there
// collapses the point to the very same offset. This is the rule the Phase 1
// gate pins ("one inside a deleted range collapses to its start").
//
// THE CHANGES COME SORTED AND NON-OVERLAPPING (a transaction's precondition,
// `transaction.mo`'s check), and every point is mapped through the whole
// list in one pass: later changes are already expressed in the OLD text's
// coordinates, so a single left-to-right fold carrying the running delta
// converts each point once.

use init::shared {Shared}
use lib::types {Selection, Selections, Change}
// Loads the Copy instances (a use with no names; the instances are global).
use lib::instances {}

/// The selection as `(lo, hi)`, independent of drag direction. Everything
/// that compares offsets uses this, so `anchor > head` costs one swap
/// rather than a second code path.
pub def Selection.span (s : Selection) : Pair I64 I64 :=
    if s.head < s.anchor
    then Pair.pair s.head s.anchor
    else Pair.pair s.anchor s.head

/// The leftmost byte the selection covers.
pub def Selection.start (s : Selection) : I64 :=
    match Selection.span s { Pair.pair lo _ => lo }

/// The byte one past the selection's rightmost byte: half-open, matching
/// `Change`'s `[start, stop)`.
pub def Selection.stop (s : Selection) : I64 :=
    match Selection.span s { Pair.pair _ hi => hi }

/// Whether the selection covers no bytes (a bare cursor).
pub def Selection.is_empty (s : Selection) : Bool :=
    I64.beq s.anchor s.head

/// The byte a user-facing cursor sits on: the head. (Kept for the view;
/// the mapping below never needs it.)
pub def Selection.cursor (s : Selection) : I64 := s.head

/// Map one point through a sorted, non-overlapping list of changes, in one
/// pass carrying the running delta. Each change is in OLD coordinates, so
/// the point is shifted by everything already passed before the next
/// comparison -- the same discipline a coalescing editor applies.
def selection_map_point (chs : List Change) (applied : I64) (pt : I64) : I64 :=
    match chs {
        List.cons ch rest =>
            let delta := (String.length ch.text) - (ch.stop - ch.start) in
            // The point stays in OLD coordinates the whole way: the fold
            // only accumulates each change's delta into `applied`, and the
            // final `pt + applied` lands in the new text. That is the
            // discipline that keeps the comparisons below honest -- a
            // change's own `[start, stop)` is old-coordinate, so the point
            // it is compared against must be too.
            if pt < ch.start
            // Strictly before the change: nothing moves.
            then selection_map_point rest applied pt
            else if pt < ch.stop
            // Inside the replaced range: collapse to the range's start.
            // That start is old-coordinate, and every later change begins
            // at or after this one's `stop`, so the recursion below adds
            // nothing more -- the collapsed point IS the answer's old side.
            then selection_map_point rest applied ch.start
            else if I64.beq pt ch.start
            // At an INSERT point (`start == stop == pt`): the cursor stays
            // before the inserted text, so nothing accumulates. This is
            // the typing rule -- a cursor must not jump over what was
            // just typed at it.
            then selection_map_point rest applied pt
            else
            // At or past the range's end: the change shifts the point.
            selection_map_point rest (applied + delta) pt,
        List.empty => pt + applied
    }

/// Map one selection through one change: both ends are points, and they
/// move independently -- a selection spanning a deleted range collapses to
/// that range's start, which is exactly "both points clamp".
pub def Selection.map_through (s : Selection) (ch : Change) : Selection :=
    Selection.map_through_changes s (List.cons ch List.empty)

/// Map one selection through a whole sorted, non-overlapping transaction.
///
/// The change list is read twice -- once per end -- so it is shared:
/// `Shared A` is `Copy` (`init/src/shared.mo`), the remedy the affine rule
/// itself names for a value used more than once. A `List` is deliberately
/// NOT `Copy` (`init/src/copy.mo`'s absent list), so the share is explicit
/// here rather than an instance away.
pub def Selection.map_through_changes (s : Selection) (chs : List Change) : Selection :=
    let shared : Shared (List Change) := Shared.of chs in
    { anchor := selection_map_point (Shared.get shared) 0 s.anchor,
      head := selection_map_point (Shared.get shared) 0 s.head }

/// Every selection, mapped. The primary index survives: the list keeps its
/// order, so the i-th selection out is the i-th in, whatever the changes
/// did to the offsets. The record is matched once, so each field is bound
/// once -- an affine parameter is read through a pattern, not by touching
/// the struct twice.
pub def Selections.map_through_changes (sel : Selections) (chs : List Change) : Selections :=
    match sel {
        { ranges, primary } => selection_map_ranges chs ranges primary
    }

/// The mapped rebuild, split out so the two fields are each used once.
def selection_map_ranges (chs : List Change) (rs : List Selection) (primary : I64) : Selections :=
    { ranges := List.map (fn s => Selection.map_through_changes s chs) rs,
      primary := primary }

/// A one-selection `Selections` spanning `[lo, hi)`, ordered regardless
/// of which end the caller names first -- the builder every view-side
/// caller of a KNOWN span wants (the status line's line/col, a test's
/// hand-set selection), and the one `commands.mo`'s private `sel_from`
/// duplicated. THE HEAD IS `hi`: a span built this way is forward, so
/// the caret sits at the span's right end.
pub def Selections.span (lo : I64) (hi : I64) : Selections :=
    let one : Selection := { anchor := lo, head := hi } in
    { ranges := List.cons one List.empty,
      primary := 0 }

/// A one-selection `Selections` with a bare cursor at `off`.
pub def Selections.cursor (off : I64) : Selections :=
    // The literal is bound to an annotated local first: a bare struct
    // literal inside `List.cons` argument position checks clean on the
    // self-hosted host and fails to infer on the Rust one (the recorded
    // two-host gotcha -- AGENTS.md's "bind to an annotated local first").
    let sel : Selection := { anchor := off, head := off } in
    { ranges := List.cons sel List.empty,
      primary := 0 }

/// The primary selection, for the callers (status line, goto) that only
/// want the one the user is driving. A `Selections` always has at least one
/// range -- an editor with none is a view concern, and `primary` names an
/// index into `ranges`, so there is no empty case to defend here.
///
/// Named `primary_sel` because `primary` is the FIELD it reads: a def and
/// a struct field cannot share one whole-program bare name.
pub def Selections.primary_sel (sel : Selections) : Option Selection :=
    match sel {
        { ranges, primary } => selection_nth ranges primary
    }

#[terminating]
def selection_nth (rs : List Selection) (i : I64) : Option Selection :=
    match rs {
        List.empty => Option.none,
        List.cons one rest =>
            if I64.beq i 0 then Option.some one else selection_nth rest (i - 1)
    }

/// Collapse every selection to its head: the `;` command. A bare cursor
/// stays where it is; a drag becomes the cursor it ended on.
pub def Selections.collapse (sel : Selections) : Selections :=
    match sel {
        { ranges, primary } => selection_collapse_ranges ranges primary
    }

def selection_collapse_ranges (rs : List Selection) (primary : I64) : Selections :=
    { ranges := List.map selection_collapse_one rs,
      primary := primary }

/// One selection, collapsed to its head. A def of its own so the literal
/// sits in a declared-return position the Rust host can type -- the same
/// gotcha `Selections.cursor`'s local works around.
def selection_collapse_one (s : Selection) : Selection :=
    { anchor := s.head, head := s.head }
