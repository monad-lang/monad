// Phase 1's history gate: commit, undo, redo, and the reachable branch.
//
// UNDO IS SNAPSHOT MOVEMENT, so the assertions compare WHOLE ROPES (via
// `to_string`), not offset deltas -- an undo that restored "almost" the
// same text would pass a delta assertion and fail these.
//
// THE BRANCH CASE (the plan's gate names it): undo, then a NEW edit, then
// `goto` the abandoned child and its text is still there. A stack-based
// history cannot pass this; that is the point of pinning it.
//
// Field reads inside `#[test]` defs go through `hist_*` accessors, never
// inline, per the recorded `#[test]` + struct-field codegen hazard.

use init::shared {Shared}
use lib::types {Selections, History}
use lib::rope {Rope.of_string, Rope.to_string}
use lib::selection {Selections.cursor, Selections.primary_sel}
use lib::history {History.empty, History.commit, History.undo, History.redo,
    History.goto, History.mark_saved, History.current_rope, History.current_selections,
    History.current_revision}
use lib::instances {}

// --- Accessors and builders ---

def hist_text (h : History) : String := Rope.to_string (History.current_rope h)

/// A cursor's head offset, the thing undo restores along with the rope.
def hist_cursor (h : History) : I64 :=
    let sel : Selections := History.current_selections h in
    match Selections.primary_sel sel {
        Option.some s => s.head,
        Option.none => 0 - 1
    }

/// One commit, text-only: a rope over `text`, a cursor at 0, no changes.
/// Returns the grown history and the new revision's id.
def hist_commit_text (h : History) (text : String) : Pair History I64 :=
    History.commit h (Rope.of_string text) (Selections.cursor 0) List.empty 0

/// One commit with a cursor position, so the undo tests can pin that the
/// SELECTIONS come back too (the gate asks for "rope and selections").
def hist_commit_at (h : History) (text : String) (off : I64) : History :=
    match History.commit h (Rope.of_string text) (Selections.cursor off) List.empty 0 {
        Pair.pair grown _ => grown
    }

// ── commit ────────────────────────────────────────────────────────────────

/// The first commit creates revision 0 and moves `current` to it.
#[test]
def test_first_commit_is_zero : Bool :=
    match hist_commit_text History.empty "one" {
        Pair.pair h id => I64.beq id 0 && String.beq (hist_text h) "one"
    }

#[test]
def test_empty_history_has_no_current : Bool :=
    match History.current_revision History.empty {
        Option.some _ => false,
        Option.none => true
    }

#[test]
def test_empty_history_answers_empty_rope : Bool :=
    String.beq (hist_text History.empty) ""

/// Commits grow the id space: 0, 1, 2 -- the numbers LSP `didChange` and
/// MCP `buffer_apply` will check (Phase 6/7) are these.
#[test]
def test_ids_grow : Bool :=
    match hist_commit_text History.empty "a" {
        Pair.pair h1 _ =>
            match hist_commit_text h1 "ab" {
                Pair.pair h2 id2 =>
                    match hist_commit_text h2 "abc" {
                        Pair.pair h3 id3 => I64.beq id2 1 && I64.beq id3 2 && String.beq (hist_text h3) "abc"
                    }
            }
    }

// ── undo ─────────────────────────────────────────────────────────────────

/// THE SNAPSHOT PIN: undo after two commits restores the FIRST revision's
/// exact rope AND its cursor (the selections travel with the revision, not
/// with the edit).
#[test]
def test_undo_restores_rope_and_selections : Bool :=
    let h0 : History := hist_commit_at History.empty "first" 3 in
    match hist_commit_text h0 "second" {
        Pair.pair h1 _ =>
            match History.undo h1 {
                Option.some back => hist_back_matches back,
                Option.none => false
            }
    }

/// Undo at the root is `none` -- a value to report, not an error.
/// The undone revision is exactly the first one: rope AND cursor. A
/// helper so the `Option.some` bind is used once.
def hist_back_matches (back : History) : Bool :=
    let shared : Shared History := Shared.of back in
    hist_back_text (Shared.get shared) && hist_back_cursor (Shared.get shared)

/// The text half, split so `back` is used once per def.
def hist_back_text (back : History) : Bool :=
    String.beq (hist_text back) "first"

/// The cursor half of the match.
def hist_back_cursor (back : History) : Bool :=
    I64.beq (hist_cursor back) 3

#[test]
def test_undo_at_root_is_none : Bool :=
    let h : History := hist_commit_at History.empty "only" 0 in
    match History.undo h {
        Option.some _ => false,
        Option.none => true
    }

#[test]
def test_undo_empty_history_is_none : Bool :=
    match History.undo History.empty {
        Option.some _ => false,
        Option.none => true
    }

/// Two undos walk two revisions back, in order.
#[test]
def test_undo_twice : Bool :=
    match hist_commit_text History.empty "a" {
        Pair.pair h1 _ =>
            match hist_commit_text h1 "ab" {
                Pair.pair h2 _ =>
                    match hist_commit_text h2 "abc" {
                        Pair.pair h3 _ =>
                            match History.undo h3 {
                                Option.some back2 =>
                                    match History.undo back2 {
                                        Option.some back1 => String.beq (hist_text back1) "a",
                                        Option.none => false
                                    },
                                Option.none => false
                            }
                    }
            }
    }

// ── redo ──────────────────────────────────────────────────────────────────

/// Redo after an undo returns to the undone revision's text.
#[test]
def test_redo_returns_to_undone_text : Bool :=
    match hist_commit_text History.empty "a" {
        Pair.pair h1 _ =>
            match hist_commit_text h1 "ab" {
                Pair.pair h2 _ =>
                    match History.undo h2 {
                        Option.some back =>
                            match History.redo back {
                                Option.some fwd => String.beq (hist_text fwd) "ab",
                                Option.none => false
                            },
                        Option.none => false
                    }
            }
    }

/// Redo at a leaf (nothing was undone) is `none`.
#[test]
def test_redo_at_leaf_is_none : Bool :=
    let h : History := hist_commit_at History.empty "only" 0 in
    match History.redo h {
        Option.some _ => false,
        Option.none => true
    }

// ── THE BRANCH: undo, new edit, goto ─────────────────────────────────────

/// The forked-tip fixture: commit "a", commit "ab" (id returned), undo,
/// then commit "xyz" -- the fork that a stack would flatten. Returns the
/// forked history and the ABANDONED "ab" revision's id. `none` when any
/// step did the wrong thing, so each test below names which.
def hist_forked : Option (Pair History I64) :=
    match hist_commit_text History.empty "a" {
        Pair.pair h1 _ =>
            match hist_commit_text h1 "ab" {
                Pair.pair h2 id_ab =>
                    match History.undo h2 {
                        Option.some back =>
                            match hist_commit_text back "xyz" {
                                Pair.pair forked _ => Option.some (Pair.pair forked id_ab)
                            },
                        Option.none => Option.none
                    }
            }
    }

/// THE BRANCH PIN (the plan's gate): undo to "a", commit "xyz" (a fork),
/// and the abandoned "ab" revision is STILL REACHABLE -- `goto` walks to
/// it and its rope is intact. A history that dropped the undone branch
/// fails here.
#[test]
def test_branch_stays_reachable : Bool :=
    match hist_forked {
        Option.some fork => hist_branch_back fork,
        Option.none => false
    }

/// The branch check on a bound pair: goto the abandoned id.
def hist_branch_back (fork : Pair History I64) : Bool :=
    match fork {
        Pair.pair forked id_ab =>
            match History.goto forked id_ab {
                Option.some revived => String.beq (hist_text revived) "ab",
                Option.none => false
            }
    }

/// The fork does not lose the ROOT either: from the forked tip, `goto 0`
/// reaches the first revision.
#[test]
def test_branch_keeps_the_root : Bool :=
    match hist_forked {
        Option.some fork => hist_root_back fork,
        Option.none => false
    }

/// The root check on a bound pair.
def hist_root_back (fork : Pair History I64) : Bool :=
    match fork {
        Pair.pair forked _ =>
            match History.goto forked 0 {
                Option.some root => String.beq (hist_text root) "a",
                Option.none => false
            }
    }

/// `goto` to an id the map does not hold is `none`: editor-facing input,
/// total, no crash.
#[test]
def test_goto_unknown_is_none : Bool :=
    let h : History := hist_commit_at History.empty "a" 0 in
    match History.goto h 99 {
        Option.some _ => false,
        Option.none => true
    }

// ── saved mark ────────────────────────────────────────────────────────────

/// The dirty flag is `current != saved` (Phase 4's `Space w`/`:q` logic).
/// A fresh history is clean-by-absence (its `saved` is the sentinel), and
/// `mark_saved` makes the CURRENT revision the saved one.
#[test]
def test_mark_saved_moves_the_mark : Bool :=
    match hist_commit_text History.empty "a" {
        Pair.pair h1 _ =>
            match hist_commit_text h1 "ab" {
                Pair.pair h2 _ =>
                    // unsaved: current is 1, saved is the sentinel
                    let saved_at : History := History.mark_saved h2 in
                    match saved_at {
                        { current, saved, .. } => I64.beq current saved
                    }
            }
    }
