// Ply's command registry and the pure update (code-editor.md §4 and
// Phase 2).
//
// COMMANDS ARE NAMED, AND THE BINDINGS POINT AT THE NAMES (Decision 4):
// the keymap resolves a sequence to a string, and the registry pairs
// strings with steps. That indirection is what makes `ply.toml`
// rebinding a data merge rather than a code change.
//
// THE UPDATE IS PURE (the Elm step `tui::App` folds):
// `EditorState -> EditorMsg -> Pair EditorState (Cmd EditorMsg)`. Every
// edit goes through `transaction.mo` -- the one editing funnel -- so
// keystrokes, LSP edits and MCP applies all share one invariant-holding
// path.
//
// NO LOCAL IS NAMED `insert`/`select`/`prefix`/`tick` in this file:
// those are whole-program constructor names (`Mode.insert`,
// `KeyResult.prefix`, `EditorMsg.tick`) that shadow same-named locals on
// older toolchains -- the plan's named risk, followed literally. The
// insert-mode commands are therefore spelled `cmd_insert_*`, and the
// word "selection" is always fully written.
//
// EVERY MULTI-READ RECORD GOES THROUGH AN ACCESSOR OR A `Shared` SHARE:
// the affine rule reads a record twice only through one of those two,
// and an `EditorState` this update rebuilds per keystroke is the shape
// the rule was written for.

use init::shared {Shared}
use lib::types {Rope, Selection, Selections, Change, History, Mode}
use lib::types {Rope}
use lib::rope {Rope.line_start, Rope.line_of, Rope.line_content_end,
    Rope.byte_at, Rope.end_offset, Rope.slice, Rope.to_string}
use lib::selection {Selection.start, Selection.stop,
    Selections.cursor, Selections.collapse, Selections.primary_sel}
use lib::history {History.undo, History.redo, History.current_rope, History.current_selections}
use lib::model {Document, EditorState, EditorMsg, Command,
    EditorState.active_doc, EditorState.with_active_doc, EditorState.with_mode,
    EditorState.with_status, EditorState.mode_of, EditorState.pending_of,
    EditorState.with_pending, EditorState.bindings_of, EditorState.registers_of,
    EditorState.with_registers, EditorState.writing_status,
    EditorState.no_path_status, EditorState.dirty_quit_status,
    EditorState.hscroll_of, EditorState.with_hscroll, EditorState.cols_of,
    Document.mark_saved, Document.dirty}
use std::path {Path}
use std::stream {StreamError}
use lib::keymap {KeyResult.as_pair, Keymap.resolve, Keymap.mode_table}
use lib::transaction {Transaction.apply, Rejection}
use tui::types {Key}
use tui::text {Text.col_of_byte, Text.byte_at_col}
use tui::tui {Cmd}

// ── The registry ──────────────────────────────────────────────────────────

/// Look a command up by name. A linear scan over a few dozen rows: the
/// registry is small, rebuilt never, and a map would pay the hashmap's
/// per-call allocation for nothing.
#[terminating]
pub def Registry.lookup (cmds : List Command) (name : String) : Option Command :=
    match cmds {
        List.empty => Option.none,
        List.cons c rest =>
            match c {
                Command.command n _ _ =>
                    if String.beq n name then Option.some c else Registry.lookup rest name
            }
    }

/// The whole registry: the plan's §4, one `Command` per row, in the
/// table's order. Phase 6's LSP-backed commands are stubs that report,
/// and so is Phase 5's `file_picker` -- the NAME and the BINDING are
/// stable from today, the body catches up. `write` and `quit` are real
/// as of Phase 4 (see the bodies at the file's end).
pub def Registry.default : List Command :=
    [cmd_of "move_char_left" "collapse to the head, one byte left" cmd_move_char_left,
        cmd_of "move_char_down" "collapse to the head, one line down" cmd_move_char_down,
        cmd_of "move_char_up" "collapse to the head, one line up" cmd_move_char_up,
        cmd_of "move_char_right" "collapse to the head, one byte right" cmd_move_char_right,
        cmd_of "select_next_word" "select to the start of the next word" cmd_select_next_word,
        cmd_of "select_prev_word" "select to the start of the previous word" cmd_select_prev_word,
        cmd_of "select_word_end" "select to the end of the word" cmd_select_word_end,
        cmd_of "extend_line" "select the line; repeat extends" cmd_extend_line,
        cmd_of "select_all" "select the whole buffer" cmd_select_all,
        cmd_of "select_regex" "split the buffer into substring matches" cmd_select_regex,
        cmd_of "collapse_selection" "collapse every selection to its head" cmd_collapse_selection,
        cmd_of "keep_primary_selection" "drop every selection but the primary" cmd_keep_primary_selection,
        cmd_of "delete" "delete every selection" cmd_delete,
        cmd_of "change" "delete every selection and enter insert mode" cmd_change,
        cmd_of "yank" "copy every selection into the registers" cmd_yank,
        cmd_of "paste" "paste the register after each head" cmd_paste,
        cmd_of "insert_before" "enter insert mode at each head" cmd_insert_before,
        cmd_of "insert_after" "enter insert mode after each head" cmd_insert_after,
        cmd_of "open_below" "open a line below and enter insert mode" cmd_open_below,
        cmd_of "open_above" "open a line above and enter insert mode" cmd_open_above,
        cmd_of "scroll_left" "move the view left, without moving the caret" cmd_scroll_left,
        cmd_of "scroll_right" "move the view right, without moving the caret" cmd_scroll_right,
        cmd_of "undo" "move back one revision" cmd_undo,
        cmd_of "redo" "move forward one revision" cmd_redo,
        cmd_of "match_inside" "select inside the surrounding parens" cmd_match_inside,
        cmd_of "match_around" "select around the surrounding parens" cmd_match_around,
        cmd_of "goto_start" "put the head at the buffer's start" cmd_goto_start,
        cmd_of "goto_end" "put the head at the buffer's end" cmd_goto_end,
        cmd_of "goto_definition" "jump to the definition (needs LSP, Phase 6)" cmd_goto_definition,
        cmd_of "goto_references" "list the references (needs LSP, Phase 6)" cmd_goto_references,
        cmd_of "hover" "show the type at the head (needs LSP, Phase 6)" cmd_hover,
        cmd_of "file_picker" "pick a file (Phase 5)" cmd_file_picker,
        cmd_of "write" "write the buffer to its file" cmd_write,
        cmd_of "quit" "exit the editor (refused while unsaved changes exist)" cmd_quit,
        cmd_of "quit!" "exit the editor, discarding unsaved changes" cmd_quit_forced,
        cmd_of "command_mode" "enter command mode" cmd_command_mode,
        cmd_of "search_mode" "enter search mode" cmd_search_mode,
        cmd_of "normal_mode" "return to normal mode" cmd_normal_mode,
        cmd_of "insert_char" "insert a typed character" cmd_insert_char_row,
        cmd_of "insert_newline" "insert a newline" cmd_insert_newline_row,
        cmd_of "insert_backspace" "delete back one byte" cmd_insert_backspace_row]

/// One registry row.
def cmd_of (name : String) (doc : String) (run : EditorState -> Pair EditorState (Cmd EditorMsg)) : Command :=
    Command.command name doc run

// ── The pure update ──────────────────────────────────────────────────────

/// The Elm step: fold one message into the next state and a command.
///
/// THE KEY PATH (Decision 4's contract):
///   * insert mode takes a character/Enter/Backspace key BEFORE the
///     table is consulted -- typing is the default case, not a row per
///     character; `escape` still resolves through the table;
///   * every other key is appended to `pending` and the whole sequence
///     resolves against the mode's table;
///   * `matched` runs the named command and CLEARS `pending`;
///   * `prefix` keeps `pending` (waiting for the rest of the chord);
///   * `unbound` clears `pending` and says so in the status line.
pub def update (st : EditorState) (msg : EditorMsg) : Pair EditorState (Cmd EditorMsg) :=
    match msg {
        EditorMsg.key k => update_key st k,
        EditorMsg.resize r c => Pair.pair (update_resize st r c) Cmd.none,
        EditorMsg.tick => Pair.pair st Cmd.none,
        EditorMsg.save_result ok msg => Pair.pair (fold_save_result st ok msg) Cmd.none,
        EditorMsg.lsp_frame _ =>
            Pair.pair (EditorState.with_status st "lsp frame (client lands in Phase 6)") Cmd.none
    }

/// The key half, split out so `st` is read once per def.
def update_key (st : EditorState) (k : Key) : Pair EditorState (Cmd EditorMsg) :=
    let shared : Shared Key := Shared.of k in
    match insert_default st (Shared.get shared) {
        Option.some step => step,
        Option.none => update_resolve st (Shared.get shared)
    }

/// Insert mode's default case: a character key inserts, Enter inserts a
/// newline, Backspace deletes back -- and only in insert mode. Everything
/// else (escape included) falls through to the table.
///
/// The answer is the ALREADY-RUN command rather than a name to run
/// later: the typed character is part of the command's meaning (it is
/// what `insert_char` inserts), so it cannot travel through the registry
/// by name. The registry row for `insert_char` exists for documentation
/// and for a config that binds it explicitly; the update's fast path is
/// here.
def insert_default (st : EditorState) (k : Key) : Option (Pair EditorState (Cmd EditorMsg)) :=
    let shared : Shared Key := Shared.of k in
    // The mode is bound with its type spelled out: a match pattern alone
    // is not a "use" the Rust host's unused-import analysis can see, and
    // the self-hosted host needs the type imported for the constructors
    // -- the annotation is the one form both count.
    let m : Mode := EditorState.mode_of st in
    match m {
        Mode.insert =>
            match Shared.get shared {
                Key.char _ => Option.some (cmd_insert_char st (Shared.get shared)),
                Key.enter => Option.some (cmd_insert_newline st (Shared.get shared)),
                Key.backspace => Option.some (cmd_insert_backspace st (Shared.get shared)),
                _ => Option.none
            },
        _ => Option.none
    }

// ── the resolution path ───────────────────────────────────────────────────

/// The resolution half: append, resolve, dispatch on the answer. The
/// three answers are exactly the keymap's three.
def update_resolve (st : EditorState) (k : Key) : Pair EditorState (Cmd EditorMsg) :=
    match Keymap.mode_table (EditorState.mode_of st) {
        Option.some table => resolve_in_table st table k,
        Option.none => Pair.pair (EditorState.with_status st "no key table for this mode") Cmd.none
    }

/// Resolve inside a known table. The state is shared: `pending` is read
/// for the sequence and the state is rebuilt per answer.
def resolve_in_table (st : EditorState) (table : String) (k : Key) : Pair EditorState (Cmd EditorMsg) :=
    let shared : Shared EditorState := Shared.of st in
    let seq : List Key := List.append (EditorState.pending_of (Shared.get shared)) (List.cons k List.empty) in
    let shared_seq : Shared (List Key) := Shared.of seq in
    resolve_answer (Shared.get shared) (Shared.get shared_seq)
        (KeyResult.as_pair (Keymap.resolve (EditorState.bindings_of (Shared.get shared)) table (Shared.get shared_seq)))

/// The three answers' dispatch, split so the pair's components are
/// bound by a match the Rust host can parse (a nested constructor
/// pattern inside a pair pattern is a two-host parse divergence).
def resolve_answer (st : EditorState) (seq : List Key) (answer : Pair (Option String) Bool) : Pair EditorState (Cmd EditorMsg) :=
    match answer {
        Pair.pair cmd is_wait =>
            match cmd {
                Option.some name =>
                    // Matched: run the named command with the pending
                    // prefix CLEARED first -- the command's state must
                    // not carry the chord that invoked it.
                    run_command (EditorState.with_pending st List.empty) name,
                Option.none =>
                    if is_wait
                    then Pair.pair (EditorState.with_pending st seq) Cmd.none
                    else Pair.pair (EditorState.with_status (EditorState.with_pending st List.empty) "unbound") Cmd.none
            }
    }

/// Run a command by name against the state, reporting an unknown name in
/// the status line rather than failing -- the registry and the keymap
/// are both data, and data can drift.
def run_command (st : EditorState) (name : String) : Pair EditorState (Cmd EditorMsg) :=
    match Registry.lookup Registry.default name {
        Option.some c =>
            match c {
                Command.command _ _ run => run st
            },
        Option.none => Pair.pair (EditorState.with_status st ("no command: " ++ name)) Cmd.none
    }

// ── the command bodies: motions are selection-first ───────────────────────
//
// A MOTION SELECTS (the plan's §4 note: "the motion *selects*"). A bare
// cursor moves; an existing selection extends. The collapse-to-head
// variants (`h j k l`) are the exception the table names, and they go
// through `Selections.collapse` first.

/// The active document's byte bound, clamped for a head position.
def head_bound (doc : Document) (head : I64) : I64 :=
    let end_off : I64 := Rope.end_offset (doc_rope doc) in
    if head < 0 then 0 else if head > end_off then end_off else head

/// The document's rope, read once.
def doc_rope (doc : Document) : Rope :=
    match doc { { rope, .. } => rope }

/// The document's selections, read once.
def doc_selections (doc : Document) : Selections :=
    match doc { { selections, .. } => selections }

/// One selection at `off`.
def sel_at (off : I64) : Selection := { anchor := off, head := off }

/// Replace the active doc's selections and return the state.
def with_selections (st : EditorState) (sel : Selections) : EditorState :=
    match EditorState.active_doc st {
        Option.some doc =>
            EditorState.with_active_doc st (doc_with_selections doc sel),
        Option.none => st
    }

/// The document with new selections.
def doc_with_selections (doc : Document) (sel : Selections) : Document :=
    Document.with_selections doc sel

/// Replace the active doc's rope, selections and history in one step
/// (the undo path: all three move together).
def with_revision (st : EditorState) (rope : Rope) (sel : Selections) (history : History) : EditorState :=
    match EditorState.active_doc st {
        Option.some doc =>
            EditorState.with_active_doc st (doc_with_revision doc rope sel history),
        Option.none => st
    }

def doc_with_revision (doc : Document) (rope : Rope) (sel : Selections) (history : History) : Document :=
    { doc with rope := rope, selections := sel, history := history }

/// Apply a transaction to the active document and fold the result back
/// into the state. A rejection reports itself in the status line and
/// leaves the state otherwise untouched -- the funnel's own contract.
def apply_changes (st : EditorState) (chs : List Change) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            match Transaction.apply doc chs {
                Result.ok grown => Pair.pair (EditorState.with_active_doc st grown) Cmd.none,
                Result.err why => Pair.pair (EditorState.with_status st (rejection_word why)) Cmd.none
            },
        Option.none => Pair.pair st Cmd.none
    }

/// A rejection as a status-line word, naming the class so the user can
/// tell a bad offset from a bad boundary.
def rejection_word (r : Rejection) : String :=
    match r {
        Rejection.out_of_bounds _ => "edit rejected: offset outside the buffer",
        Rejection.inverted _ _ => "edit rejected: stop before start",
        Rejection.overlap _ _ => "edit rejected: changes overlap",
        Rejection.splits_char _ => "edit rejected: offset splits a character"
    }

// ── motions ───────────────────────────────────────────────────────────────

/// The primary head, or 0 when there is none.
def primary_head (st : EditorState) : I64 :=
    match EditorState.active_doc st {
        Option.some doc =>
            match Selections.primary_sel (doc_selections doc) {
                Option.some s => s.head,
                Option.none => 0
            },
        Option.none => 0
    }

/// One byte left, collapsing to the head first (the §4 `h` rule).
def cmd_move_char_left (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (move_head st (primary_head st - 1)) Cmd.none

def cmd_move_char_right (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (move_head st (primary_head st + 1)) Cmd.none

def cmd_move_char_down (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (move_head st (line_step st 1)) Cmd.none

def cmd_move_char_up (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (move_head st (line_step st (0 - 1))) Cmd.none

/// Move the primary head to `head`, collapsed: the bare-cursor motion.
def move_head (st : EditorState) (head : I64) : EditorState :=
    match EditorState.active_doc st {
        Option.some doc =>
            let bound : I64 := head_bound doc head in
            with_selections st (Selections.cursor bound),
        Option.none => st
    }

/// One line's start offset, plus `delta` lines, from the head's line.
def line_step (st : EditorState) (delta : I64) : I64 :=
    match EditorState.active_doc st {
        Option.some doc =>
            let rope : Rope := doc_rope doc in
            let head : I64 := primary_head st in
            let line : I64 := Rope.line_of rope head in
            Rope.line_start rope (line + delta),
        Option.none => 0
    }

// ── word motions (selection-first) ─────────────────────────────────────────

/// Whether a byte is a word byte (not whitespace, not punctuation).
def is_word_byte (b : Option U8) : Bool :=
    match b {
        Option.none => false,
        Option.some c =>
            // ASCII letters, digits and underscore; a multi-byte
            // character's lead byte is above 0x7f and reads as a word
            // byte, which is the right call for an identifier-bearing
            // language and harmless for prose. The byte is shared: the
            // range tests read it five times.
            let shared : Shared U8 := Shared.of c in
            word_digit (Shared.get shared)
                || word_upper (Shared.get shared)
                || word_lower (Shared.get shared)
                || word_underscore (Shared.get shared)
                || U8.gt (Shared.get shared) 127u8
    }

/// A digit: `0x30..=0x39`.
def word_digit (c : U8) : Bool := U8.gt c 47u8 && Bool.not (U8.gt c 57u8)

/// An uppercase letter: `0x41..=0x5a`.
def word_upper (c : U8) : Bool := U8.gt c 64u8 && Bool.not (U8.gt c 90u8)

/// A lowercase letter: `0x61..=0x7a`.
def word_lower (c : U8) : Bool := U8.gt c 96u8 && Bool.not (U8.gt c 122u8)

/// The underscore byte.
def word_underscore (c : U8) : Bool := U8.beq c 95u8

/// The next word's start after `from`: skip the current run, then the
/// whitespace, and stop at the first word byte of the next run.
#[terminating]
def next_word_start (rope : Rope) (off : I64) : I64 :=
    let end_off : I64 := Rope.end_offset rope in
    if off > end_off - 1 then end_off
    else if is_word_byte (Rope.byte_at rope off)
    then skip_run rope off end_off
    else skip_gap rope off end_off

#[terminating]
def skip_run (rope : Rope) (off : I64) (end_off : I64) : I64 :=
    if off > end_off - 1 then end_off
    else if is_word_byte (Rope.byte_at rope off)
    then skip_run rope (off + 1) end_off
    else skip_gap rope off end_off

#[terminating]
def skip_gap (rope : Rope) (off : I64) (end_off : I64) : I64 :=
    if off > end_off - 1 then end_off
    else if is_word_byte (Rope.byte_at rope off)
    then off
    else skip_gap rope (off + 1) end_off

/// `w`: select from the head to the next word's start.
def cmd_select_next_word (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let head : I64 := primary_head st in
            let target : I64 := next_word_start (doc_rope doc) head in
            Pair.pair (with_selections st (sel_from head target)) Cmd.none,
        Option.none => Pair.pair st Cmd.none
    }

/// One selection spanning `[a, b)`, ordered regardless of direction.
def sel_from (a : I64) (b : I64) : Selections :=
    let one : Selection := { anchor := a, head := b } in
    { ranges := List.cons one List.empty, primary := 0 }

/// `b`: select back to the previous word's start.
def cmd_select_prev_word (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let head : I64 := primary_head st in
            let target : I64 := prev_word_start (doc_rope doc) head in
            Pair.pair (with_selections st (sel_from head target)) Cmd.none,
        Option.none => Pair.pair st Cmd.none
    }

/// The previous word's start before `from`: back over the gap, back
/// over the run, and stop where that run began.
#[terminating]
def prev_word_start (rope : Rope) (off : I64) : I64 :=
    if off < 1 then 0
    else if is_word_byte (Rope.byte_at rope (off - 1))
    then back_run rope off
    else back_gap rope off

#[terminating]
def back_run (rope : Rope) (off : I64) : I64 :=
    if off < 1 then 0
    else if is_word_byte (Rope.byte_at rope (off - 1))
    then back_run rope (off - 1)
    else off

#[terminating]
def back_gap (rope : Rope) (off : I64) : I64 :=
    if off < 1 then 0
    else if Bool.not (is_word_byte (Rope.byte_at rope (off - 1)))
    then back_gap rope (off - 1)
    else back_run rope off

/// `e`: select to the end of the current word.
def cmd_select_word_end (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let head : I64 := primary_head st in
            let target : I64 := word_end (doc_rope doc) head in
            Pair.pair (with_selections st (sel_from head target)) Cmd.none,
        Option.none => Pair.pair st Cmd.none
    }

#[terminating]
def word_end (rope : Rope) (off : I64) : I64 :=
    let end_off : I64 := Rope.end_offset rope in
    if off > end_off - 1 then end_off
    else if is_word_byte (Rope.byte_at rope off)
    then word_end_go rope (off + 1) end_off
    else next_word_start rope off

#[terminating]
def word_end_go (rope : Rope) (off : I64) (end_off : I64) : I64 :=
    if off > end_off - 1 then end_off
    else if is_word_byte (Rope.byte_at rope off)
    then word_end_go rope (off + 1) end_off
    else off

// ── line and buffer selections ────────────────────────────────────────────

/// `x`: select the head's line, without its terminator. A repeat EXTENDS
/// by a line (the §4 note): the selection's start stays where it was and
/// its stop moves to the NEXT line's end, so `x x` selects two lines.
def cmd_extend_line (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let shared_doc : Shared Document := Shared.of doc in
            let rope : Rope := doc_rope (Shared.get shared_doc) in
            let sel : Selections := doc_selections (Shared.get shared_doc) in
            let head : I64 := primary_head st in
            Pair.pair (with_selections st (extend_line_sel rope sel head)) Cmd.none,
        Option.none => Pair.pair st Cmd.none
    }

/// The extended selection: from the EXISTING span's start (so a repeat
/// extends rather than re-selects) to one line past the span's last
/// line's end. A bare cursor (empty span) selects its own line.
def extend_line_sel (rope : Rope) (sel : Selections) (head : I64) : Selections :=
    match Selections.primary_sel sel {
        Option.some one =>
            let shared_sel : Shared Selection := Shared.of one in
            let lo : I64 := Selection.start (Shared.get shared_sel) in
            let hi : I64 := Selection.stop (Shared.get shared_sel) in
            let first_line : I64 := Rope.line_of rope lo in
            // THE FIRST PRESS selects the head's line; A REPEAT
            // extends by one: an empty span covers its own line and
            // stops there, a non-empty span covers ONE PAST its last
            // covered line. (`hi - 1` underflows on an empty span, so
            // the guard reads the span's start instead.)
            let last_covered : I64 :=
                if I64.beq lo hi
                then Rope.line_of rope lo
                else Rope.line_of rope (hi - 1) + 1 in
            let span_lo : I64 := Rope.line_start rope first_line in
            let span_hi : I64 := Rope.line_content_end rope last_covered in
            sel_from span_lo span_hi,
        Option.none => sel_from head head
    }

/// `%`: select the whole buffer.
def cmd_select_all (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let end_off : I64 := Rope.end_offset (doc_rope doc) in
            Pair.pair (with_selections st (sel_from 0 end_off)) Cmd.none,
        Option.none => Pair.pair st Cmd.none
    }

/// `s`: the substring splitter. A regex mote does not exist (the plan's
/// Known Limitation), so Phase 2's `s` selects the WHOLE buffer -- the
/// command runs, the mode's contract holds, and the status line says
/// what is missing.
def cmd_select_regex (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match cmd_select_all st {
        Pair.pair extended cmd =>
            Pair.pair
                (EditorState.with_status extended "select_regex needs a regex mote; the whole buffer is selected")
                cmd
    }

/// `;`: collapse every selection to its head -- the plan's §4 row, and
/// exactly `Selections.collapse`.
def cmd_collapse_selection (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            Pair.pair (with_selections st (Selections.collapse (doc_selections doc))) Cmd.none,
        Option.none => Pair.pair st Cmd.none
    }

/// `,`: keep only the primary selection.
def cmd_keep_primary_selection (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            match Selections.primary_sel (doc_selections doc) {
                Option.some one =>
                    let kept : Selections :=
                        { ranges := List.cons one List.empty, primary := 0 } in
                    Pair.pair (with_selections st kept) Cmd.none,
                Option.none => Pair.pair st Cmd.none
            },
        Option.none => Pair.pair st Cmd.none
    }

// ── the operators: delete, change, yank, paste ─────────────────────────────

/// `d`: delete every selection, one change per selection, one
/// transaction. The changes are sorted by construction (the selections
/// are rebuilt in buffer order by the motions that made them) and
/// non-overlapping by the same argument.
def cmd_delete (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let chs : List Change := changes_of_selections (doc_selections doc) in
            apply_changes st chs,
        Option.none => Pair.pair st Cmd.none
    }

/// One `Change` per selection: the span's bytes become nothing.
#[terminating]
def changes_of_selections (sel : Selections) : List Change :=
    changes_of_ranges (sel_ranges sel)

def sel_ranges (sel : Selections) : List Selection :=
    match sel { { ranges, .. } => ranges }

#[terminating]
def changes_of_ranges (rs : List Selection) : List Change :=
    match rs {
        List.empty => List.empty,
        List.cons one rest =>
            List.cons (change_of_sel one) (changes_of_ranges rest)
    }

def change_of_sel (s : Selection) : Change :=
    { start := Selection.start s, stop := Selection.stop s, text := "" }

/// `c`: delete, then enter insert mode at each head.
def cmd_change (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match cmd_delete st {
        Pair.pair after_del cmd =>
            Pair.pair (EditorState.with_mode after_del Mode.insert) cmd
    }

/// `y`: copy every selection's text into the registers, newest first.
def cmd_yank (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let shared_doc : Shared Document := Shared.of doc in
            let rope : Rope := doc_rope (Shared.get shared_doc) in
            let texts : List String :=
                texts_of_selections rope (doc_selections (Shared.get shared_doc)) in
            let regs : List String := List.append texts (EditorState.registers_of st) in
            Pair.pair (EditorState.with_registers st regs) Cmd.none,
        Option.none => Pair.pair st Cmd.none
    }

/// Each selection's text, in selection order.
#[terminating]
def texts_of_selections (rope : Rope) (sel : Selections) : List String :=
    texts_of_ranges rope (sel_ranges sel)

#[terminating]
def texts_of_ranges (rope : Rope) (rs : List Selection) : List String :=
    match rs {
        List.empty => List.empty,
        List.cons one rest =>
            let lo : I64 := Selection.start one in
            let hi : I64 := Selection.stop one in
            List.cons (text_span rope lo hi) (texts_of_ranges rope rest)
    }

/// A span's text, sliced once. The length is `hi - lo`, the half-open
/// span's own arithmetic.
def text_span (rope : Rope) (lo : I64) (hi : I64) : String :=
    Rope.slice rope lo (hi - lo)

/// `p`: paste the newest register after the primary head.
def cmd_paste (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.registers_of st {
        List.cons newest _ =>
            match EditorState.active_doc st {
                Option.some doc =>
                    let head : I64 := primary_head st in
                    apply_changes st (List.cons (paste_change head newest) List.empty),
                Option.none => Pair.pair st Cmd.none
            },
        List.empty => Pair.pair (EditorState.with_status st "no register to paste") Cmd.none
    }

/// The insert-at-head change.
def paste_change (head : I64) (text : String) : Change :=
    { start := head, stop := head, text := text }

// ── insert mode ────────────────────────────────────────────────────────────

/// A typed character, inserted at the head through the funnel, and the
/// head then advances past it -- the typing rule. The transaction keeps
/// a cursor AT the insert point put (the selection-mapping rule), which
/// is right for an edit arriving from outside and wrong for typing, so
/// the command moves the head itself.
def cmd_insert_char (st : EditorState) (k : Key) : Pair EditorState (Cmd EditorMsg) :=
    match k {
        Key.char c =>
            match EditorState.active_doc st {
                Option.some doc =>
                    let head : I64 := primary_head st in
                    insert_at st head c,
                Option.none => Pair.pair st Cmd.none
            },
        _ => Pair.pair st Cmd.none
    }

/// One insert followed by the head's advance to `head + len c`.
def insert_at (st : EditorState) (head : I64) (c : String) : Pair EditorState (Cmd EditorMsg) :=
    match apply_changes st (List.cons (paste_change head c) List.empty) {
        Pair.pair after cmd => Pair.pair (move_head after (head + String.length c)) cmd
    }

/// Enter: a newline at the head, head advanced past it.
def cmd_insert_newline (st : EditorState) (k : Key) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let head : I64 := primary_head st in
            insert_at st head "\n",
        Option.none => Pair.pair st Cmd.none
    }

/// Backspace: delete one byte back, through the funnel (so the boundary
/// rule and the version discipline both hold).
def cmd_insert_backspace (st : EditorState) (k : Key) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let head : I64 := primary_head st in
            if head < 1
            then Pair.pair st Cmd.none
            else apply_changes st (List.cons (backspace_change head) List.empty),
        Option.none => Pair.pair st Cmd.none
    }

/// The delete-back change: `[head-1, head)` becomes empty. The byte
/// before an insert-mode head is always a character boundary (the head
/// only ever moved onto one), so the funnel's boundary check holds.
def backspace_change (head : I64) : Change :=
    { start := head - 1, stop := head, text := "" }

/// The registry's `insert_char` row: the fast path in `insert_default`
/// runs the real body with the key in hand; this row exists so the name
/// is documented and bindable. Same for the two rows below.
def cmd_insert_char_row (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_status st "insert_char runs from the key itself") Cmd.none

def cmd_insert_newline_row (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_status st "insert_newline runs from the Enter key") Cmd.none

def cmd_insert_backspace_row (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_status st "insert_backspace runs from the Backspace key") Cmd.none

// ── mode switches ──────────────────────────────────────────────────────────

def cmd_insert_before (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_mode st Mode.insert) Cmd.none

def cmd_insert_after (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let head : I64 := primary_head st in
            let after : I64 := skip_char_forward (doc_rope doc) head in
            Pair.pair (EditorState.with_mode (move_head st after) Mode.insert) Cmd.none,
        Option.none => Pair.pair (EditorState.with_mode st Mode.insert) Cmd.none
    }

/// One character forward: past a lead byte's continuation bytes.
def skip_char_forward (rope : Rope) (off : I64) : I64 :=
    match Rope.byte_at rope off {
        Option.none => off,
        Option.some b =>
            let shared : Shared U8 := Shared.of b in
            if U8.gt (Shared.get shared) 239u8 then off + 4
            else if U8.gt (Shared.get shared) 223u8 then off + 3
            else if U8.gt (Shared.get shared) 191u8 then off + 2
            else off + 1
    }

/// `o`: open a line below the head's line and enter insert mode there.
def cmd_open_below (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let rope : Rope := doc_rope doc in
            let head : I64 := primary_head st in
            let line : I64 := Rope.line_of rope head in
            let at : I64 := Rope.line_content_end rope line in
            let step : Pair EditorState (Cmd EditorMsg) :=
                apply_changes st (List.cons (paste_change at "\n") List.empty) in
            match step {
                Pair.pair after cmd =>
                    Pair.pair (EditorState.with_mode (move_head after (at + 1)) Mode.insert) cmd
            },
        Option.none => Pair.pair (EditorState.with_mode st Mode.insert) Cmd.none
    }

/// `O`: open a line above the head's line.
def cmd_open_above (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            let rope : Rope := doc_rope doc in
            let head : I64 := primary_head st in
            let line : I64 := Rope.line_of rope head in
            let at : I64 := Rope.line_start rope line in
            let step : Pair EditorState (Cmd EditorMsg) :=
                apply_changes st (List.cons (paste_change at "\n") List.empty) in
            match step {
                Pair.pair after cmd =>
                    Pair.pair (EditorState.with_mode (move_head after at) Mode.insert) cmd
            },
        Option.none => Pair.pair (EditorState.with_mode st Mode.insert) Cmd.none
    }

/// Esc: back to normal mode, selections kept (the §4 rule).
def cmd_normal_mode (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_mode st Mode.normal) Cmd.none

def cmd_command_mode (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_mode st (Mode.command "")) Cmd.none

def cmd_search_mode (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_mode st (Mode.search "")) Cmd.none

// ── undo and redo ──────────────────────────────────────────────────────────

/// `u`: move back one revision, restoring its rope AND selections -- the
/// snapshot contract (`history.mo`), folded into the active document.
def cmd_undo (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            match History.undo (doc_history doc) {
                Option.some back =>
                    let shared : Shared History := Shared.of back in
                    Pair.pair
                        (with_revision st (History.current_rope (Shared.get shared))
                            (History.current_selections (Shared.get shared))
                            (Shared.get shared))
                        Cmd.none,
                Option.none => Pair.pair (EditorState.with_status st "nothing to undo") Cmd.none
            },
        Option.none => Pair.pair st Cmd.none
    }

/// `U`: move forward one revision.
def cmd_redo (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            match History.redo (doc_history doc) {
                Option.some fwd =>
                    let shared : Shared History := Shared.of fwd in
                    Pair.pair
                        (with_revision st (History.current_rope (Shared.get shared))
                            (History.current_selections (Shared.get shared))
                            (Shared.get shared))
                        Cmd.none,
                Option.none => Pair.pair (EditorState.with_status st "nothing to redo") Cmd.none
            },
        Option.none => Pair.pair st Cmd.none
    }

def doc_history (doc : Document) : History :=
    match doc { { history, .. } => history }

// ── match commands and gotos ────────────────────────────────────────────────

/// `mi(`: select inside the parens surrounding the head -- the head's
/// line, for Phase 2 (the full surrounding-scan is a later refinement;
/// the command name and binding are stable today). The extend-line STATE
/// is what runs; the status rides on top of it.
def cmd_match_inside (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match cmd_extend_line st {
        Pair.pair extended cmd =>
            Pair.pair
                (EditorState.with_status extended "match_inside: the head's line (Phase 2 scope)")
                cmd
    }

/// `ma(`: select around the parens (the head's line, Phase 2 scope).
def cmd_match_around (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match cmd_extend_line st {
        Pair.pair extended cmd =>
            Pair.pair
                (EditorState.with_status extended "match_around: the head's line (Phase 2 scope)")
                cmd
    }

/// `gg`: the head to the buffer's start.
def cmd_goto_start (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (move_head st 0) Cmd.none

/// `ge`: the head to the buffer's end.
def cmd_goto_end (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc =>
            Pair.pair (move_head st (Rope.end_offset (doc_rope doc))) Cmd.none,
        Option.none => Pair.pair st Cmd.none
    }

// ── Phase 4/5/6 stubs: the names are bound, the bodies report ───────────────

def cmd_goto_definition (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_status st "goto_definition needs the LSP client (Phase 6)") Cmd.none

def cmd_goto_references (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_status st "goto_references needs the LSP client (Phase 6)") Cmd.none

def cmd_hover (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_status st "hover needs the LSP client (Phase 6)") Cmd.none

def cmd_file_picker (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_status st "file_picker lands with config (Phase 5)") Cmd.none

// ── writing and quitting (Phase 4) ─────────────────────────────────────────
//
// THE UPDATE STAYS PURE. `Cmd.perform`'s action is `Unit -> IO EditorMsg`:
// it cannot see the state and cannot change it, so the write's OUTCOME
// travels back as an `EditorMsg.save_result` message and the fold above
// applies it. That is the same split Phase 6's `lsp_frame` uses, and it is
// why a save is two defs (one to issue, one to fold) rather than one.
//
// THE WHOLE-BUFFER STRING IS BUILT INSIDE THE ACTION, never at keystroke
// time: `Rope.to_string` is O(n) over the leaves, which is the right price
// once per save and the wrong one per keypress on a 10k-line file. The
// closure therefore captures the ROPE (a pointer to persistent structure),
// not the text.

/// `Space w`: write the active buffer to its file.
///
/// A SCRATCH BUFFER REFUSES IN THE PURE HALF -- there is no path, so
/// there is nothing to open and no reason to pay for an action; the
/// status line says why. A path means the write is issued as
/// `Cmd.perform`, so the terminal is restored correctly even when the
/// write is the last thing that happens (the loop's EOF path folds a
/// final `perform`, `motes/tui/src/tui.mo`'s `final_frame`).
def cmd_write (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.active_doc st {
        Option.some doc => split_write st doc,
        Option.none => Pair.pair (EditorState.with_status st ply_no_doc_status) Cmd.none
    }

/// The document split into the two things a write needs, in ONE match: a
/// `Document` is not `Copy` (its history holds a `BTreeMap`), so two
/// accessor calls would spend the affine budget twice on one binder.
def split_write (st : EditorState) (doc : Document) : Pair EditorState (Cmd EditorMsg) :=
    match doc {
        { path, rope, .. } => begin_write st path rope
    }

/// The pure half's two answers: no path refuses, a path issues the write.
def begin_write (st : EditorState) (path : Option String) (rope : Rope) : Pair EditorState (Cmd EditorMsg) :=
    match path {
        Option.none => Pair.pair (EditorState.with_status st EditorState.no_path_status) Cmd.none,
        Option.some p =>
            Pair.pair (EditorState.with_status st EditorState.writing_status)
                (Cmd.perform (fn (_ : Unit) => ply_write_rope p rope))
    }

/// The write itself, run inside the frame (or the loop's final frame).
/// The text is materialized HERE, once.
def ply_write_rope (p : String) (rope : Rope) : IO EditorMsg := do {
    let r <- IO.write_file (Path.path p) (Rope.to_string rope);
    return (save_outcome p r)
}

/// The write's result as the message the pure half folds in: the path it
/// wrote to, or the OS message that refused. `StreamError.message` always
/// carries the OS text (`std/src/stream.mo`).
def save_outcome (p : String) (r : Result StreamError Unit) : EditorMsg :=
    match r {
        Result.ok _ => EditorMsg.save_result true (String.concat "wrote " p),
        Result.err e =>
            EditorMsg.save_result false (String.concat "write failed: " e.message)
    }

/// The one-line report for a state with no buffer at all. The editor
/// always holds one (`EditorState.init`), so this is the accessor's
/// totality showing, not a reachable editing state.
def ply_no_doc_status : String := "no buffer to write"

/// Fold a finished write: report it either way, and on success mark the
/// current revision as the saved one, so the view's `[+]` turns off and
/// `Space q` stops refusing.
def fold_save_result (st : EditorState) (ok : Bool) (msg : String) : EditorState :=
    let noted : EditorState := EditorState.with_status st msg in
    if ok then mark_active_saved noted else noted

/// The active document's current revision marked saved.
def mark_active_saved (st : EditorState) : EditorState :=
    match EditorState.active_doc st {
        Option.some doc => EditorState.with_active_doc st (Document.mark_saved doc),
        Option.none => st
    }

/// `Space q`: quit, unless the buffer has unsaved changes. The refusal
/// names the way out (`quit!`), because a status line that only says "no"
/// leaves the user stuck with no idea which key says otherwise.
///
/// WHY `quit!` AND NOT `:q!`: `:` enters command mode, but no key
/// currently appends to the command line (that is Phase 5's command
/// line), so a `:q!` spelling would be unreachable from a keystroke. The
/// rule is the plan's; the key is one that already exists.
def cmd_quit (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    if active_dirty st
    then Pair.pair (EditorState.with_status st EditorState.dirty_quit_status) Cmd.none
    else Pair.pair st Cmd.quit

/// `Space Q`: quit regardless of unsaved changes -- the discard.
def cmd_quit_forced (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair st Cmd.quit

/// Whether the active buffer has unsaved changes.
def active_dirty (st : EditorState) : Bool :=
    match EditorState.active_doc st {
        Option.some doc => Document.dirty doc,
        Option.none => false
    }

// ── horizontal scrolling ───────────────────────────────────────────────────
//
// The view already follows the caret horizontally (`View.left_col` clamps
// the window around the head's column), so a caret past the right margin
// is always visible without these two commands. What they add is the
// ability to LOOK AROUND -- to read text the caret is not on -- which
// automatic follow by itself never gives you.
//
// They move only the stored `hscroll`; the view's clamp still wins when
// the caret would otherwise leave the window, so scrolling away from the
// caret and then moving it snaps back rather than leaving a blind caret.

/// How far one scroll press moves the window: half a text area, the
/// half-page convention `Ctrl-d`-style scrolling uses everywhere.
def scroll_step (st : EditorState) : I64 :=
    let width : I64 := text_width_of st in
    let half : I64 := width / 2 in
    if half < 1 then 1 else half

/// The text area's width for this state -- the same arithmetic
/// `View.text_width` states, kept here so `commands.mo` does not import
/// the view (the update stays independent of how the editor is drawn).
def text_width_of (st : EditorState) : I64 :=
    let cols : I64 := EditorState.cols_of st in
    if cols < 6 then 0 else cols - 5

/// `scroll_left`: move the window left by half a page, stopping at column 0.
def cmd_scroll_left (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    let target : I64 := EditorState.hscroll_of st - scroll_step st in
    scroll_to st (if target < 0 then 0 else target)

/// `scroll_right`: move the window right by half a page. There is no upper
/// bound worth computing -- the caret's own drag (below) and the view's
/// clamp between them keep the window on the text.
def cmd_scroll_right (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    scroll_to st (EditorState.hscroll_of st + scroll_step st)

/// Move the window to `left`, DRAGGING THE CARET along when the new window
/// would leave it off-screen.
///
/// THE DRAG IS NOT A CONVENIENCE, IT IS WHAT MAKES THE COMMAND EXIST.
/// `View.left_col` clamps the window so the caret is always visible, so a
/// window set while the caret is outside it would be undone on the very
/// next frame -- `Alt-l` would move nothing at all. Dragging the caret to
/// the near edge keeps both guarantees at once: the caret is visible, and
/// the window really moved. A caret already inside the new window is left
/// exactly where it was, which is the "look around without editing" case.
def scroll_to (st : EditorState) (left : I64) : Pair EditorState (Cmd EditorMsg) :=
    let moved : EditorState := EditorState.with_hscroll st left in
    Pair.pair (drag_caret_into_window moved left) Cmd.none

/// The caret pulled to the nearest edge of the window `[left, left + width)`.
/// A caret inside the window, or a state with no buffer, is unchanged.
def drag_caret_into_window (st : EditorState) (left : I64) : EditorState :=
    let width : I64 := text_width_of st in
    match EditorState.active_doc st {
        Option.none => st,
        Option.some doc => drag_in_doc st doc left width
    }

def drag_in_doc (st : EditorState) (doc : Document) (left : I64) (width : I64) : EditorState :=
    let shared : Shared Document := Shared.of doc in
    let rope : Rope := doc_rope (Shared.get shared) in
    let head : I64 := primary_head st in
    let line : I64 := Rope.line_of rope head in
    let ls : I64 := Rope.line_start rope line in
    let text : String := Rope.slice rope ls (Rope.line_content_end rope line - ls) in
    let col : I64 := Text.col_of_byte text (head - ls) in
    let right : I64 := left + width in
    if col < left
    then move_head st (ls + Text.byte_at_col text left)
    else if Bool.not (col < right)
    then move_head st (ls + Text.byte_at_col text (if width < 1 then left else right - 1))
    else st

/// The resize half: geometry in step.
def update_resize (st : EditorState) (r : I64) (c : I64) : EditorState :=
    { st with rows := r, cols := c }
