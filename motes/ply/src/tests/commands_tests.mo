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
use lib::commands {update, parse_command}
use lib::model {Document.with_path, EditorState.status_of}
use tui::types {Key}
use tui::tui {Cmd}
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

// ── The command line (Phase 5) ───────────────────────────────────────────
//
// `:` ENTERS COMMAND MODE AND THE KEYS TYPE INTO ITS LINE. Until Phase 5 the
// mode was entered and nothing else: no key appended to the line, so `:w` was
// unreachable from a keyboard and `:q!` was a spelling nobody could type. The
// line lives in `Mode.command`'s payload, so these pins read it back through
// `EditorState.cmd_line_of` after a scripted keystroke list.
//
// THE TWO HALVES ARE PINNED SEPARATELY, on purpose: typing is one thing (a
// `:` and then characters make a line), and RUNNING the line is another (the
// parsed name reaches the SAME registry row a key would). A test that only
// asserted `:w` wrote a file would pass on a `:`-only reimplementation of the
// save, which is exactly what the plan forbids.

/// The state's command line, `""` off a command line.
def cx_line (st : EditorState) : String := EditorState.cmd_line_of st

/// `:` then the characters of `text`, folded through `update`.
#[terminating]
def cx_colon (st : EditorState) (text : String) : EditorState :=
    cx_type (cx_press st (cx_key ":")) (cx_chars text)

/// The characters of `text` as character keys.
#[terminating]
def cx_chars (s : String) : List Key :=
    cx_chars_go (String.to_list s)

#[terminating]
def cx_chars_go (bs : List U8) : List Key :=
    match bs {
        List.empty => List.empty,
        List.cons b rest =>
            List.cons (cx_key (String.from_list (List.cons b List.empty))) (cx_chars_go rest)
    }

/// TYPING BUILDS THE LINE: `:` then `w` `q` leaves `wq` in the command line.
/// This is the assertion the whole phase was blocked on -- before it, the
/// line was permanently `""` and every `:` command was unreachable.
#[test]
def test_typing_builds_the_command_line : Bool :=
    let after : EditorState := cx_colon (cx_state "x") "wq" in
    String.beq (cx_line after) "wq"

/// BACKSPACE REMOVES THE LAST CHARACTER, and pressing it on an empty line
/// stays empty rather than going negative or eating the `:`.
#[test]
def test_backspace_edits_the_command_line : Bool :=
    let typed : EditorState := cx_colon (cx_state "x") "wq" in
    let cut : EditorState := cx_type typed [Key.backspace] in
    let cut2 : EditorState := cx_type cut [Key.backspace] in
    let cut3 : EditorState := cx_type cut2 [Key.backspace] in
    String.beq (cx_line cut) "w" && String.beq (cx_line cut2) ""
        && String.beq (cx_line cut3) ""

/// A TYPED CHARACTER IS NOT INSERTED INTO THE BUFFER: command mode is the
/// line, not the text. (The same fixture would read "xwq" if the key path
/// fell through to insert mode's rule.)
#[test]
def test_command_typing_does_not_touch_the_buffer : Bool :=
    let after : EditorState := cx_colon (cx_state "x") "wq" in
    String.beq (cx_text after) "x"

/// ENTER RUNS THE LINE AND LEAVES THE MODE: `:q` on a clean buffer answers
/// `Cmd.quit` and the mode is normal again -- the command is the SAME
/// `quit` row `Space q` runs, so a clean buffer quits here too.
#[test]
def test_colon_q_quits : Bool :=
    let pair : Pair EditorState (Cmd EditorMsg) :=
        cx_type_pair (cx_state "x") [cx_key ":", cx_key "q", Key.enter] in
    // THE PAIR IS READ ONCE, into its two halves: an affine value may be used
    // once, and a `Pair` is not `Copy` (so two accessor calls on the same
    // binder would be rejected rather than duplicated).
    match pair {
        Pair.pair after cmd => cx_is_quit_cmd cmd && Bool.not (cx_is_command (cx_mode after))
    }

/// The script's folded pair -- the state AND the command, for the tests that
/// need the command (a quit, a write). The script's answer is its LAST key's
/// command: every earlier key in a command line answers `Cmd.none` (the `:` is
/// a mode switch and each character edits the line), so only `Enter` can
/// issue one.
#[terminating]
def cx_type_pair_go (st : EditorState) (keys : List Key) (last : Cmd EditorMsg)
    : Pair EditorState (Cmd EditorMsg) :=
    match keys {
        List.empty => Pair.pair st last,
        List.cons k rest => cx_type_pair_step st k rest last
    }

#[terminating]
def cx_type_pair_step (st : EditorState) (k : Key) (rest : List Key) (last : Cmd EditorMsg)
    : Pair EditorState (Cmd EditorMsg) :=
    match update st (cx_msg k) {
        Pair.pair after cmd => cx_type_pair_go after rest cmd
    }

def cx_type_pair (st : EditorState) (keys : List Key)
    : Pair EditorState (Cmd EditorMsg) :=
    cx_type_pair_go st keys Cmd.none

/// The message constructor, spelled in one place.
def cx_msg (k : Key) : EditorMsg := EditorMsg.key k

def cx_pair_state (pair : Pair EditorState (Cmd EditorMsg)) : EditorState :=
    match pair {
        Pair.pair st _ => st
    }

def cx_pair_cmd (pair : Pair EditorState (Cmd EditorMsg)) : Cmd EditorMsg :=
    match pair {
        Pair.pair _ cmd => cmd
    }

def cx_is_quit_cmd (cmd : Cmd EditorMsg) : Bool :=
    match cmd {
        Cmd.quit => true,
        _ => false
    }

/// `:q` ON A DIRTY BUFFER REFUSES, exactly as `Space q` does: `:` is the same
/// command, so it must be the same rule -- the status names the way out and no
/// quit is issued.
#[test]
def test_colon_q_refuses_when_dirty : Bool :=
    let dirty : EditorState := cx_type (cx_state "x") [cx_key "i", cx_key "y", Key.escape] in
    let pair : Pair EditorState (Cmd EditorMsg) :=
        cx_type_pair dirty [cx_key ":", cx_key "q", Key.enter] in
    match pair {
        Pair.pair after cmd =>
            Bool.not (cx_is_quit_cmd cmd)
                && String.beq (EditorState.status_of after)
                    "unsaved changes; Space Q quits without saving"
    }

/// `:q!` QUITS A DIRTY BUFFER -- the spelling the plan named and the keymap
/// could not reach before the line existed.
#[test]
def test_colon_q_bang_quits_when_dirty : Bool :=
    let dirty : EditorState := cx_type (cx_state "x") [cx_key "i", cx_key "y", Key.escape] in
    let pair : Pair EditorState (Cmd EditorMsg) :=
        cx_type_pair dirty [cx_key ":", cx_key "q", cx_key "!", Key.enter] in
    match pair {
        Pair.pair _ cmd => cx_is_quit_cmd cmd
    }

/// `:w` ON A SCRATCH BUFFER REFUSES IN THE PURE HALF, the same answer
/// `Space w` gives: no path, no write, and the status says why.
#[test]
def test_colon_w_refuses_without_a_path : Bool :=
    let pair : Pair EditorState (Cmd EditorMsg) :=
        cx_type_pair (cx_state "x") [cx_key ":", cx_key "w", Key.enter] in
    match pair {
        Pair.pair after cmd =>
            Bool.not (cx_is_perform_cmd cmd)
                && String.beq (EditorState.status_of after) "no path to write"
    }

def cx_is_perform_cmd (cmd : Cmd EditorMsg) : Bool :=
    match cmd {
        Cmd.perform _ => true,
        _ => false
    }

/// `:w` ON A BUFFER WITH A PATH ISSUES THE WRITE, and the state it leaves is
/// the one `Space w` leaves: "writing..." in the status, a `Cmd.perform`
/// carrying the action. The file itself is `save_tests.mo`'s gate; this pins
/// that the LINE reaches the same command.
#[test]
def test_colon_w_issues_the_write : Bool :=
    let with_path : EditorState :=
        EditorState.init (Document.with_path (Document.of_text "x") "/tmp/ply_cmdline_probe") 24 80 in
    let pair : Pair EditorState (Cmd EditorMsg) :=
        cx_type_pair with_path [cx_key ":", cx_key "w", Key.enter] in
    match pair {
        Pair.pair after cmd =>
            cx_is_perform_cmd cmd && String.beq (EditorState.status_of after) "writing..."
    }

/// AN UNKNOWN LINE IS REPORTED, NOT IGNORED, and the mode is left: a silent
/// no-op would read as "the command ran".
#[test]
def test_unknown_command_is_reported : Bool :=
    let pair : Pair EditorState (Cmd EditorMsg) :=
        cx_type_pair (cx_state "x") [cx_key ":", cx_key "q", cx_key "w", Key.enter] in
    match pair {
        Pair.pair after cmd =>
            // The state is read three times (status, mode), so one `Shared`
            // handle serves them -- `after` has no `Copy` instance either.
            let shared : Shared EditorState := Shared.of after in
            Bool.not (cx_is_quit_cmd cmd)
                && String.beq (EditorState.status_of (Shared.get shared)) "no such command: qw"
                && Bool.not (cx_is_command (cx_mode (Shared.get shared)))
    }

/// AN EMPTY LINE IS THE WAY OUT: `:` then Enter is Escape -- normal mode, no
/// command, no report.
#[test]
def test_empty_command_line_cancels : Bool :=
    let pair : Pair EditorState (Cmd EditorMsg) :=
        cx_type_pair (cx_state "x") [cx_key ":", Key.enter] in
    match pair {
        Pair.pair after cmd => Bool.not (cx_is_command (cx_mode after)) && cx_is_no_cmd cmd
    }

def cx_is_no_cmd (cmd : Cmd EditorMsg) : Bool :=
    match cmd {
        Cmd.none => true,
        _ => false
    }

/// ESCAPE LEAVES THE LINE WITHOUT RUNNING IT: the buffer is untouched, the
/// status is quiet, and the mode is normal.
#[test]
def test_escape_cancels_the_command_line : Bool :=
    let typed : EditorState := cx_colon (cx_state "x") "q!" in
    let out : EditorState := cx_type typed [Key.escape] in
    Bool.not (cx_is_command (cx_mode out))
        && String.beq (cx_text out) "x" && String.beq (cx_line out) ""

/// THE PARSER'S TABLE, pinned directly: each spelling names the registry row
/// the key bindings already use, so `ply.toml` and the `:` line agree.
/// `:x` is `:wq` (the vim alias every editor keeps).
#[test]
def test_parse_command_table : Bool :=
    cx_parses "w" "write" && cx_parses "write" "write"
        && cx_parses "q" "quit" && cx_parses "quit" "quit"
        && cx_parses "q!" "quit!" && cx_parses "quit!" "quit!"
        && cx_parses "wq" "write_quit" && cx_parses "x" "write_quit"

/// Nothing else parses -- a typo, an empty line, a command from a later phase.
#[test]
def test_parse_command_rejects_unknown : Bool :=
    cx_parses_nothing "" && cx_parses_nothing "qw" && cx_parses_nothing "nohlsearch"
        && cx_parses_nothing "bn"

def cx_parses (line : String) (name : String) : Bool :=
    match parse_command line {
        Option.some got => String.beq got name,
        Option.none => false
    }

def cx_parses_nothing (line : String) : Bool :=
    match parse_command line {
        Option.some _ => false,
        Option.none => true
    }

/// LEADING AND TRAILING SPACE IS IGNORED when the line runs: `: w ` is `:w`.
/// Typing a space before a command is what a user does after a miss, and
/// refusing it would be the editor's mistake, not theirs.
#[test]
def test_command_line_ignores_surrounding_space : Bool :=
    let pair : Pair EditorState (Cmd EditorMsg) :=
        cx_type_pair (cx_state "x") [cx_key ":", cx_key " ", cx_key "q", cx_key " ", Key.enter] in
    match pair {
        Pair.pair _ cmd => cx_is_quit_cmd cmd
    }

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
