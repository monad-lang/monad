// Phase 2's command gate: a scripted keystroke list drives the pure
// `update` from an initial state to an expected rope, selection list and
// mode (the plan's Phase 2 gate), with no terminal anywhere -- the
// update is pure, so the drive is a fold.
//
// COVERAGE, per the gate: `w d`, `x x d`, `mi( c`, `i ... Esc`, `u`, `U`.
// Each scenario's fixture bytes are written beside it (the toolkit
// suite's discipline), and the expected text is derived by hand from the
// rule the command states -- never by re-running the command.
//
// No record patterns or bare nested struct literals inside `#[test]`
// defs: the state goes through the `cx_*` accessors, per the recorded
// two-host inference hazard this mote's Phase 1 selection tests learned.

use lib::types {Rope, Mode, Selection, Selections}
use lib::model {Document, Document.of_text, EditorState, EditorMsg, EditorState.init,
    EditorState.mode_of, EditorState.pending_of, EditorState.active_doc,
    EditorState.hscroll_of}
use lib::rope {Rope.to_string}
use lib::selection {Selections.primary_sel, Selection.start, Selection.stop}
use lib::commands {update}
use tui::types {Key}
// `List.length` lives in `init/src/list.mo` (ambient and pure) as of the
// upstream move, so this import pulls the module's INSTANCES into scope
// and names nothing -- the empty brace list is the documented form.
use std::list {}
use init::shared {Shared}
use lib::instances {}

// --- Builders ---

/// The state's stored horizontal window, read once -- what a scroll
/// command moved (the VIEW's clamp is `View.left_col`'s job and is pinned
/// in `view_tests.mo`; these tests pin the command's own arithmetic).
def cx_hscroll (st : EditorState) : I64 := EditorState.hscroll_of st

/// An `Alt`-modified character key, built in its own def so the `Key.alt`
/// constructor is never spelled inside a test body.
def cx_alt (c : String) : Key := Key.alt c

/// `n` `l` keys, for placing the head at a chosen column.
#[terminating]
def cx_ls (n : I64) : List Key :=
    if Bool.not (0 < n)
    then List.empty
    else List.cons (cx_key "l") (cx_ls (n - 1))

/// A character key.
def cx_key (c : String) : Key := Key.char c

/// One `update` step over a key. The message is bound with its type
/// spelled out: `EditorMsg.key` in argument position is not a "use" the
/// Rust host's unused-import analysis can see, and the annotation is the
/// one form both hosts count.
def cx_press (st : EditorState) (k : Key) : EditorState :=
    let msg : EditorMsg := EditorMsg.key k in
    match update st msg {
        Pair.pair after _ => after
    }

/// A whole keystroke script, folded through `update`.
#[terminating]
def cx_type (st : EditorState) (keys : List Key) : EditorState :=
    match keys {
        List.empty => st,
        List.cons k rest => cx_type (cx_press st k) rest
    }

/// The state's active document's text.
def cx_text (st : EditorState) : String :=
    match EditorState.active_doc st {
        Option.some doc => Rope.to_string (cx_doc_rope doc),
        Option.none => "<no doc>"
    }

def cx_doc_rope (doc : Document) : Rope :=
    match doc { { rope, .. } => rope }

/// The state's mode.
def cx_mode (st : EditorState) : Mode := EditorState.mode_of st

/// The primary selection's span, as `lo..hi`, or `<none>`.
def cx_span (st : EditorState) : String :=
    match EditorState.active_doc st {
        Option.some doc =>
            match Selections.primary_sel (cx_doc_sel doc) {
                Option.some s => cx_span_ends (Shared.of s),
                Option.none => "<none>"
            },
        Option.none => "<none>"
    }

def cx_doc_sel (doc : Document) : Selections :=
    match doc { { selections, .. } => selections }

/// One selection's ends as a display string, shared because both ends
/// read the same bind.
def cx_span_ends (s : Shared Selection) : String :=
    cx_two_ends (Selection.start (Shared.get s)) (Selection.stop (Shared.get s))

/// The span as a display string.
def cx_two_ends (lo : I64) (hi : I64) : String :=
    I64.to_string lo ++ ".." ++ I64.to_string hi

/// The pending prefix's length (a chord's waiting state).
def cx_pending_len (st : EditorState) : I64 := List.length (EditorState.pending_of st)

/// A fresh state over `text`.
def cx_state (text : String) : EditorState :=
    EditorState.init (Document.of_text text) 24 80

// ── The gate's scripted scenarios ────────────────────────────────────────

/// `w d`: select the next word, then delete the selection.
///
/// Derived by hand from the motion's rule, not by running it: `w` from
/// the cursor at 0 skips the run "alpha" (5 bytes), then the gap " " (1
/// byte), stopping at 6 -- the `b`. The selection is anchor 0 head 6,
/// so `d` deletes [0,6) and "beta" is what is left. THE MOTION SELECTS
/// (selection-first): it does not just move the cursor.
#[test]
def test_w_then_d : Bool :=
    let after : EditorState :=
        cx_type (cx_state "alpha beta") [cx_key "w", cx_key "d"] in
    String.beq (cx_text after) "beta"

/// The motion's own span, on its own: the pin the delete test derives
/// from.
#[test]
def test_w_selects_from_cursor : Bool :=
    let after : EditorState := cx_type (cx_state "alpha beta") [cx_key "w"] in
    String.beq (cx_span after) "0..6"

/// `x x d`: extend line twice, then delete. Fixture "ab\ncd\nef":
/// `x` selects line 0 [0,2); the second `x` extends to [0,5) (line 1's
/// end); `d` deletes [0,5) leaving "\nef".
#[test]
def test_x_x_d : Bool :=
    let after : EditorState :=
        cx_type (cx_state "ab\ncd\nef") [cx_key "x", cx_key "x", cx_key "d"] in
    String.beq (cx_text after) "\nef"

/// `mi( c`: match-inside selects the head's line (Phase 2 scope), then
/// `c` deletes it and enters insert mode. Fixture "foo\nbar":
/// `mi(` selects line 0 [0,3); `c` deletes and switches to insert.
#[test]
def test_mi_then_c : Bool :=
    let after : EditorState :=
        cx_type (cx_state "foo\nbar") [cx_key "m", cx_key "i", cx_key "(", cx_key "c"] in
    String.beq (cx_text after) "\nbar" && cx_is_insert (cx_mode after)

/// The mode check, as a helper so the `Mode.insert` constructor is
/// compared in one place.
def cx_is_insert (m : Mode) : Bool :=
    match m {
        Mode.insert => true,
        _ => false
    }

/// `i ... Esc`: insert mode types at the head, and Esc returns to normal.
/// Inserting "hi" at 0 in "there" gives "hithere"; the mode ends normal.
#[test]
def test_i_type_esc : Bool :=
    let after : EditorState :=
        cx_type (cx_state "there") [cx_key "i", cx_key "h", cx_key "i", Key.escape] in
    String.beq (cx_text after) "hithere" && Bool.not (cx_is_insert (cx_mode after))

/// `u`: undo restores the previous revision through the funnel -- the
/// Phase 1 history gate's case, exercised from a keystroke.
#[test]
def test_u_undoes : Bool :=
    let after : EditorState :=
        cx_type (cx_state "ab") [cx_key "i", cx_key "x", Key.escape, cx_key "u"] in
    String.beq (cx_text after) "ab"

/// `U` after `u`: redo returns to the later revision.
#[test]
def test_U_redoes : Bool :=
    let after : EditorState :=
        cx_type (cx_state "ab") [cx_key "i", cx_key "x", Key.escape, cx_key "u", cx_key "U"] in
    String.beq (cx_text after) "xab"

/// Insert mode's Enter and Backspace: a newline at the head, then a
/// delete back. Fixture "ab": Enter at 0 -> "\nab"; Backspace deletes
/// the newline -> "ab".
#[test]
def test_enter_backspace : Bool :=
    let after : EditorState :=
        cx_type (cx_state "ab") [cx_key "i", Key.enter, Key.backspace, Key.escape] in
    String.beq (cx_text after) "ab"

// ── The three answers, through the update ───────────────────────────────

/// A chord's first key KEEPS pending (the update's `prefix` arm).
#[test]
def test_prefix_keeps_pending : Bool :=
    let after : EditorState := cx_type (cx_state "x") [cx_key "g"] in
    I64.beq (cx_pending_len after) 1

/// The chord completes and pending CLEARS (`matched`'s arm).
#[test]
def test_matched_clears_pending : Bool :=
    let after : EditorState := cx_type (cx_state "x") [cx_key "g", cx_key "g"] in
    I64.beq (cx_pending_len after) 0

/// `unbound` clears pending and reports (the gate's third case).
#[test]
def test_unbound_clears_pending : Bool :=
    let after : EditorState := cx_type (cx_state "x") [cx_key "g", cx_key "z"] in
    I64.beq (cx_pending_len after) 0

/// `Space w` resolves through the whole update: a prefix, then a match.
/// A SCRATCH state has no path, so Phase 4's write refuses in the pure
/// half and says why -- this pins the CHORD, and `save_tests.mo` pins the
/// write itself.
#[test]
def test_space_w_resolves : Bool :=
    let after : EditorState := cx_type (cx_state "x") [cx_key " ", cx_key "w"] in
    I64.beq (cx_pending_len after) 0 && String.beq (cx_status after) "no path to write"

def cx_status (st : EditorState) : String :=
    match st { { status, .. } => status }

/// `:` enters command mode; Esc returns to normal.
#[test]
def test_colon_command_mode : Bool :=
    let after : EditorState := cx_type (cx_state "x") [cx_key ":"] in
    let back : EditorState := cx_type after [Key.escape] in
    cx_is_command (cx_mode after) && Bool.not (cx_is_command (cx_mode back))

def cx_is_command (m : Mode) : Bool :=
    match m {
        Mode.command _ => true,
        _ => false
    }

/// `y` then `p`: yank the word, paste it after the head. Fixture "ab cd":
/// `w` selects [0,3); `y` yanks "ab "; `;` collapses to the head at 3;
/// `p` pastes "ab " at 3 -> "ab ab cd".
#[test]
def test_yank_paste : Bool :=
    let after : EditorState :=
        cx_type (cx_state "ab cd") [cx_key "w", cx_key "y", cx_key ";", cx_key "p"] in
    String.beq (cx_text after) "ab ab cd"

/// `%` selects the whole buffer; `d` deletes everything.
#[test]
def test_percent_select_all_d : Bool :=
    let after : EditorState := cx_type (cx_state "hello") [cx_key "%", cx_key "d"] in
    String.beq (cx_text after) ""

/// `gg` puts the head at the start; on a fresh state it already is, so
/// the pin is the span after `gg` from a moved head.
#[test]
def test_gg_goto_start : Bool :=
    let after : EditorState :=
        cx_type (cx_state "abc") [cx_key "l", cx_key "l", cx_key "g", cx_key "g"] in
    String.beq (cx_span after) "0..0"

/// `ge` puts the head at the buffer's end.
#[test]
def test_ge_goto_end : Bool :=
    let after : EditorState := cx_type (cx_state "abc") [cx_key "g", cx_key "e"] in
    String.beq (cx_span after) "3..3"

// ── horizontal scrolling ──────────────────────────────────────────────────
//
// The COMMANDS move the stored window by half a text area (75 cells at 80
// columns -> 37). What the view does with it -- following the caret -- is
// `View.left_col`'s clamp, pinned in view_tests.mo. These two pin that the
// keys reach the commands at all, which the clamp alone would hide: a
// broken binding would leave `hscroll` at 0 and every clamp test would
// still pass.

/// `Alt-l` scrolls right by half the text area. `cx_state` is 24x80, so
/// the text area is 75 cells (80 minus the 5-cell gutter) and half of it
/// is 37 -- the half-page step, derived by hand from that arithmetic.
#[test]
def test_alt_l_scrolls_right : Bool :=
    let after : EditorState := cx_type (cx_state "abc") [cx_alt "l"] in
    I64.beq (cx_hscroll after) 37

/// `Alt-h` scrolls left, and STOPS AT ZERO: two presses from a fresh state
/// stay at 0 rather than going negative.
#[test]
def test_alt_h_scrolls_left_and_stops_at_zero : Bool :=
    let right : EditorState := cx_type (cx_state "abc") [cx_alt "l"] in
    let back : EditorState := cx_type right [cx_alt "h"] in
    let past : EditorState := cx_type back [cx_alt "h", cx_alt "h"] in
    I64.beq (cx_hscroll back) 0 && I64.beq (cx_hscroll past) 0

/// A scroll DRAGS A CARET that falls outside the new window, and leaves
/// one that is inside it alone.
///
/// The drag is not cosmetic: `View.left_col` clamps the window so the
/// caret is always visible, so a window set while the caret sits outside
/// it would be undone on the next frame and the command would move
/// nothing. Fixture "abcdef": `l l` puts the head at 2, `Alt-l` moves the
/// window to 37, which leaves the head outside -- so it is pulled to the
/// window's left edge, column 37.
#[test]
def test_scrolling_drags_a_caret_outside_the_window : Bool :=
    let before : EditorState := cx_type (cx_state (String.repeat "x" 80)) [cx_key "l", cx_key "l"] in
    let after : EditorState := cx_type before [cx_alt "l"] in
    I64.beq (cx_hscroll after) 37 && String.beq (cx_span after) "37..37"

/// A CARET INSIDE THE NEW WINDOW IS LEFT ALONE: scrolling LEFT from a
/// window of 74 with the head at column 100 lands on window 37, which
/// still contains the head -- so the head does not move. Looking around
/// never disturbs a caret you can already see.
#[test]
def test_scrolling_leaves_a_visible_caret_alone : Bool :=
    let at : EditorState := cx_type (cx_state (String.repeat "x" 200)) (cx_ls 100) in
    let right : EditorState := EditorState.with_hscroll at 74 in
    let after : EditorState := cx_type right [cx_alt "h"] in
    I64.beq (cx_hscroll after) 37 && String.beq (cx_span after) "100..100"
