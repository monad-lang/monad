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
    EditorState.cmd_line_of, EditorState.search_line_of, EditorState.picker_query_of,
    EditorState.picker_selected_of, EditorState.picker_files_of,
    EditorState.picker_dir_of, EditorState.with_picker_files,
    EditorState.search_query_of, EditorState.search_forward_of, EditorState.with_search,
    EditorState.doc_count, EditorState.with_active, EditorState.with_doc_added,
    EditorState.index_of_path, EditorState.rows_of,
    Document.mark_saved, Document.dirty, Document.of_file, Document.text_of,
    Document.path_of}
use lib::search {Search.find_from, Search.last_before, Search.next_match,
    Search.selection_at, Search.line_number_of, Search.text_of}
use lib::picker {Picker.rank, Picker.clamp_selected, Picker.nth, Picker.resolve}
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
        cmd_of "search_next" "repeat the last search" cmd_search_next,
        cmd_of "search_prev" "repeat the last search, backwards" cmd_search_prev,
        cmd_of "file_picker" "pick a file from the current directory" cmd_file_picker,
        cmd_of "picker_next" "highlight the next candidate" cmd_picker_next,
        cmd_of "picker_prev" "highlight the previous candidate" cmd_picker_prev,
        cmd_of "picker_page_down" "highlight a page of candidates on" cmd_picker_page_down,
        cmd_of "picker_page_up" "highlight a page of candidates back" cmd_picker_page_up,
        cmd_of "picker_accept" "open the highlighted candidate" cmd_picker_accept,
        cmd_of "buffer_next" "focus the next buffer, wrapping" cmd_buffer_next,
        cmd_of "buffer_prev" "focus the previous buffer, wrapping" cmd_buffer_prev,
        cmd_of "clear_status" "clear the status line" cmd_clear_status,
        cmd_of "write" "write the buffer to its file" cmd_write,
        cmd_of "write_quit" "write the buffer, then quit if the write succeeded" cmd_write_quit,
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
        // THE QUIT MESSAGE: the one path an IO-side decision has to stop the
        // editor, because a `Cmd.perform`'s action can only answer a message.
        // `:wq` uses it to quit after a successful write and stay open on a
        // failed one. The status line is not read again -- the terminal is
        // already restored by the time the loop sees `Cmd.quit`.
        EditorMsg.quit => Pair.pair st Cmd.quit,
        // THE LISTING'S FOLD: the IO half could not touch the state, so the
        // candidates arrive as a message (the same split as `save_result`).
        EditorMsg.picker_files dir files => Pair.pair (fold_picker_files st dir files) Cmd.none,
        // The open's fold, likewise.
        EditorMsg.file_opened path text => Pair.pair (fold_file_opened st path text) Cmd.none,
        EditorMsg.lsp_frame _ =>
            Pair.pair (EditorState.with_status st "lsp frame (client lands in Phase 6)") Cmd.none
    }

/// The key half, split out so `st` is read once per def.
///
/// THE TWO TEXT MODES HANDLE THEIR OWN KEYS FIRST: insert mode types into the
/// buffer and command mode types into the command LINE, and in both cases the
/// typed character is part of the command's meaning, so it cannot travel
/// through the registry by name. Everything else -- Escape above all, which is
/// the only binding either mode's table carries -- falls through to the table.
def update_key (st : EditorState) (k : Key) : Pair EditorState (Cmd EditorMsg) :=
    let shared : Shared Key := Shared.of k in
    match typed_default st (Shared.get shared) {
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
def typed_default (st : EditorState) (k : Key) : Option (Pair EditorState (Cmd EditorMsg)) :=
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
        // The command line and the `/` line are the SAME EDIT with different
        // destinations -- `typed_default` is the shared body, and which mode
        // reads it decides where a typed character lands.
        Mode.command line =>
            line_edit_default st line (Shared.get shared),
        Mode.search query =>
            line_edit_default st query (Shared.get shared),
        // The picker types its FILTER, and its keys (arrows, Enter, Escape)
        // are real bindings in its own table -- so only a character is a
        // default case here. Escape and Enter fall through to `resolve`.
        Mode.picker query sel =>
            picker_default st query sel (Shared.get shared),
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

// ── the command line (`:` commands) ────────────────────────────────────────
//
// A `:` COMMAND AND A KEY BINDING ARE THE SAME STEP (the plan's own rule):
// `:w` is not a second implementation of the save, it is the save. So a typed
// line is parsed into a command NAME and handed to `run_command`, the very def
// a matched key already goes through -- there is no registry of `:` forms
// beside the registry of commands.
//
// THE LINE LIVES IN `Mode.command`'s PAYLOAD (see `EditorState.cmd_line_of`),
// so entering the mode and typing the line are one value's history, and
// leaving the mode throws the line away with no cleanup pass.
//
// UNKNOWN NAMES ARE REPORTED, NOT SWALLOWED: a mistyped `:qw` says so in the
// status line and leaves the mode. Silence would read as "the command ran".

/// The keys a LINE-TYPING mode types with: a character appends, Enter runs
/// the line, Backspace deletes the last character. Anything else -- Escape
/// first among them -- answers `none` here and resolves through the mode's
/// table, which is where `normal_mode` lives.
///
/// THE COMMAND LINE AND THE `/` LINE SHARE THIS BODY, because they are the
/// same edit with different destinations: which mode is in the state decides
/// where the line goes back. Two copies would be two chances for the
/// backspace rule to drift (and the command line's UTF-8 rule is exactly the
/// kind of thing that drifts).
def line_edit_default (st : EditorState) (line : String) (k : Key)
    : Option (Pair EditorState (Cmd EditorMsg)) :=
    match k {
        Key.char c => Option.some (Pair.pair (cmd_line_append st line c) Cmd.none),
        Key.enter => Option.some (cmd_line_run st line),
        Key.backspace => Option.some (Pair.pair (cmd_line_backspace st line) Cmd.none),
        _ => Option.none
    }

/// The line with one character appended -- what typing does on a command or
/// search line. The character is already the text to show (there is no
/// cursor movement inside the line yet), so the append is the whole edit.
///
/// THE DESTINATION IS THE CURRENT MODE, read from the state rather than
/// passed in: a `Mode.command` state gets a `Mode.command` back and a
/// `Mode.search` state a `Mode.search`, so the one body serves both and
/// cannot write a line into the wrong payload.
def cmd_line_append (st : EditorState) (line : String) (c : String) : EditorState :=
    line_replacing st (String.concat line c)

/// The line with its last CHARACTER removed. BYTES, NOT CELLS: the payload is
/// a byte string, and a multi-byte character's trailing continuation bytes
/// must come off with it or the line stops being valid UTF-8 -- so the drop
/// point walks back over the continuation bytes (`0x80..=0xbf`) first.
def cmd_line_backspace (st : EditorState) (line : String) : EditorState :=
    let kept : I64 := line_drop_point line (String.length line - 1) in
    line_replacing st (String.slice line 0 kept)

/// `text` as the current typing mode's line. A mode that is not a line mode
/// (nothing reaches this) is left alone rather than guessed at.
def line_replacing (st : EditorState) (text : String) : EditorState :=
    match EditorState.mode_of st {
        Mode.command _ => EditorState.with_mode st (Mode.command text),
        Mode.search _ => EditorState.with_mode st (Mode.search text),
        _ => st
    }

/// The largest character boundary at or below `at`, for a byte string whose
/// `at` may land inside a multi-byte character. `String.get` is O(1) here (the
/// line is a few bytes), and an out-of-range index answers 0 like a line that
/// is already empty.
#[terminating]
def line_drop_point (line : String) (at : I64) : I64 :=
    if Bool.not (0 < at)
    then 0
    else match String.get line at {
        Option.none => 0,
        Option.some b => if is_continuation_byte b then line_drop_point line (at - 1) else at
    }

/// A UTF-8 continuation byte: `0x80..=0xbf`.
def is_continuation_byte (b : U8) : Bool :=
    U8.gt b 127u8 && Bool.not (U8.gt b 191u8)

/// Enter on a typing line, dispatched by WHICH line it is: the command line
/// runs its text as a command, the `/` line runs it as a search. The mode is
/// left BEFORE the command runs, so a command that sets a mode of its own
/// (`:e` opens a file, `:` leaves) is not overwritten afterwards.
def cmd_line_run (st : EditorState) (line : String) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.mode_of st {
        Mode.search _ => run_search_line st line,
        _ => run_command_line st line
    }

/// Enter on the command line: parse the text and RUN it, leaving the mode
/// first. An empty (or blank) line is the plain way out -- `:` then Enter is
/// Escape -- and a name outside the whitelist is reported rather than run.
def run_command_line (st : EditorState) (line : String) : Pair EditorState (Cmd EditorMsg) :=
    let trimmed : String := String.trim line in
    let left : EditorState := EditorState.with_mode st Mode.normal in
    if String.is_empty trimmed
    then Pair.pair left Cmd.none
    else run_parsed left trimmed

// ── `/` search ────────────────────────────────────────────────────────────
//
// THE `/` LINE IS THE COMMAND LINE'S TWIN. It types into `Mode.search`'s
// payload, Enter runs it, Escape leaves -- the same three keys, dispatched by
// the state's mode (`cmd_line_run`). What it does with the line is the whole
// of this section.
//
// AN EMPTY SEARCH LINE REPEATS THE LAST SEARCH. `/` then Enter is how every
// modal editor says "again", and it is why `search_query` lives on the state
// and not in the mode: the query has to outlive the line that typed it.
//
// A QUERY WITH NO MATCH IS REPORTED AND DOES NOT MOVE THE CARET. Moving it
// somewhere arbitrary (to 0, say) would be the editor inventing an answer;
// saying "no match" leaves the selection exactly where the user left it.

/// Enter on the `/` line: run `line` as a search, or repeat the last one when
/// the line is blank. The mode always returns to normal -- a search is a
/// motion, and a motion does not leave you in a typing mode.
def run_search_line (st : EditorState) (line : String) : Pair EditorState (Cmd EditorMsg) :=
    let trimmed : String := String.trim line in
    let left : EditorState := EditorState.with_mode st Mode.normal in
    if String.is_empty trimmed
    then Pair.pair (search_repeat left true) Cmd.none
    else Pair.pair (search_from_origin left trimmed true) Cmd.none

/// Run `query` as a fresh search from the primary head's offset, going
/// `forward` -- and remember it, so `n`/`N` can repeat it.
def search_from_origin (st : EditorState) (query : String) (forward : Bool) : EditorState :=
    let remembered : EditorState := EditorState.with_search st query forward in
    search_at remembered query (primary_head st) forward

/// Repeat the committed search: `forward` says whether this is `n` (same
/// direction as last time) or `N` (the opposite).
def search_repeat (st : EditorState) (forward : Bool) : EditorState :=
    let query : String := EditorState.search_query_of st in
    if String.is_empty query
    then EditorState.with_status st "no previous search"
    else
        let dir : Bool := if forward then EditorState.search_forward_of st else go_back (EditorState.search_forward_of st) in
        search_next_from st query dir

/// Run the committed search again, from the current match -- the `n`/`N` path.
///
/// THE ORIGIN IS THE SELECTION'S START GOING BACKWARD AND ITS END GOING
/// FORWARD, which is what makes `n` find the NEXT match rather than the same
/// one: the caret sits on a match, and a search starting at the caret would
/// find that match again. Forward from the end and backward from the start
/// step off the span in the direction of travel.
def search_next_from (st : EditorState) (query : String) (forward : Bool) : EditorState :=
    let origin : I64 := search_origin st forward in
    search_at st query origin forward

/// Where the next search starts: the primary selection's end going forward,
/// its start going backward.
def search_origin (st : EditorState) (forward : Bool) : I64 :=
    match EditorState.active_doc st {
        Option.none => 0,
        Option.some doc =>
            match Selections.primary_sel (doc_selections doc) {
                Option.none => 0,
                Option.some one =>
                    if forward then Selection.stop one else Selection.start one
            }
    }

/// Flip a direction.
def go_back (forward : Bool) : Bool := Bool.not forward

/// Run `query` from `origin` in direction `forward`, select the match, and
/// report the line it landed on. A miss reports and leaves the buffer alone.
///
/// THE WHOLE BUFFER IS MATERIALIZED ONCE, HERE. `String` scans need a string,
/// and the rope is the editing structure -- so a search pays one O(n) pass,
/// not one per candidate. That is the same trade `cmd_write` makes, and it is
/// the right one for a motion a human triggers by hand.
def search_at (st : EditorState) (query : String) (origin : I64) (forward : Bool)
    : EditorState :=
    match EditorState.active_doc st {
        Option.none => st,
        Option.some doc =>
            let shared : Shared Document := Shared.of doc in
            let rope : Rope := doc_rope (Shared.get shared) in
            let text : String := Search.text_of (Shared.of rope) in
            match Search.next_match text query origin forward {
                Option.none => search_miss st query,
                Option.some at =>
                    // `at` is read twice (the selection and the report), and
                    // `I64` is `Copy`, so a named local is the duplicate the
                    // rule wants -- the share is the value, not the binder.
                    let hit : I64 := at in
                    let selected : EditorState :=
                        EditorState.with_active_doc st
                            (Document.with_selections (Shared.get shared)
                                (Search.selection_at hit (String.length query))) in
                    EditorState.with_status selected
                        ("/" ++ query ++ " at line " ++ I64.to_string (Search.line_number_of rope hit))
            }
    }

/// The no-match report. It names the query, because the row a user reads is
/// one line in a status bar and "no match" alone does not say for what.
def search_miss (st : EditorState) (query : String) : EditorState :=
    EditorState.with_status st ("no match: " ++ query)

/// `n`: repeat the last search the way it ran.
def cmd_search_next (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (search_repeat st true) Cmd.none

/// `N`: repeat the last search the other way.
def cmd_search_prev (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (search_repeat st false) Cmd.none

// ── the file picker ───────────────────────────────────────────────────────
//
// `Space f` IS TWO HALVES: a `Cmd.perform` that lists the directory (the IO
// side, which cannot touch the state) and a fold of `EditorMsg.picker_files`
// onto it (the pure side). Opening the picker needs BOTH -- the mode so the
// user can type, and the listing so there is something to type at -- so the
// command issues the listing as a command and switches the mode right away.
// The frame after shows the picker empty and then filled, which is
// indistinguishable from fast on any real directory.

/// The status while a listing is in flight -- only visible on a slow disk.
pub def ply_listing_status : String := "listing files..."

/// `Space f`: enter the picker and ask for a listing of the current
/// directory.
///
/// THE MODE IS SET BEFORE THE LISTING ARRIVES, so a keystroke typed while the
/// listing runs lands in the filter rather than in the buffer. `picker_dir`
/// stays `""` -- the process's own cwd -- which is also what `Picker.resolve`
/// answers for a candidate unchanged.
def cmd_file_picker (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    let entered : EditorState :=
        EditorState.with_mode (EditorState.with_status st ply_listing_status)
            (Mode.picker "" 0) in
    Pair.pair entered (Cmd.perform (fn (_ : Unit) => ply_list_dir ""))

/// The listing, run inside the frame: one level of `dir`, its entries as the
/// relative paths the filter ranks. `dir` of `""` is the process's cwd.
///
/// A DIRECTORY'S OWN ENTRIES ARE ALL CANDIDATES, files and directories alike:
/// the picker has no notion of a file type, and hiding directories would hide
/// the `..` a user needs to walk out. `IO.list_dir` already sorts.
def ply_list_dir (dir : String) : IO EditorMsg := do {
    let path : Path := if String.is_empty dir then Path.path "." else Path.path dir;
    let entries <- IO.list_dir path;
    return (picker_files_msg dir (paths_of_entries dir entries))
}

/// The entries as display paths: the bare name when `dir` is the cwd (so the
/// listing reads like `ls`), the `dir`-joined spelling otherwise. A
/// `Path.file_name` round-trip keeps the `dir` out of the filter's view for
/// the common case, which is what makes typing `ma` find `main.mo`.
#[terminating]
def paths_of_entries (dir : String) (entries : List Path) : List String :=
    match entries {
        List.empty => List.empty,
        List.cons one rest =>
            List.cons (entry_name dir one) (paths_of_entries dir rest)
    }

/// One entry's display path.
def entry_name (dir : String) (p : Path) : String :=
    if String.is_empty dir then Path.file_name p else Path.to_string p

/// The `picker_files` message, built in its own def so the constructor is
/// never spelled inline in an `IO` body (the constructor-shadowing risk).
def picker_files_msg (dir : String) (files : List String) : EditorMsg :=
    EditorMsg.picker_files dir files

/// Fold a finished listing onto the state: the candidates, and the directory
/// they are relative to. The mode is untouched -- a listing that arrives
/// after the user pressed Escape must not re-open the picker.
def fold_picker_files (st : EditorState) (dir : String) (files : List String) : EditorState :=
    EditorState.with_picker_files st dir files

/// A character typed in the picker: it filters. The selection RESETS to the
/// top, because the list under it just changed -- keeping row 7 selected
/// while the list shrinks would highlight a different file than the one the
/// user was looking at.
def picker_default (st : EditorState) (query : String) (sel : I64) (k : Key)
    : Option (Pair EditorState (Cmd EditorMsg)) :=
    match k {
        Key.char c =>
            Option.some (Pair.pair
                (EditorState.with_mode st (Mode.picker (String.concat query c) 0)) Cmd.none),
        Key.backspace =>
            Option.some (Pair.pair
                (EditorState.with_mode st
                    (Mode.picker (String.slice query 0 (line_drop_point query (String.length query - 1))) 0))
                Cmd.none),
        _ => Option.none
    }

/// The ranked candidates for the state's filter -- what the view lists and
/// what `picker_accept` opens, so the two cannot disagree.
pub def picker_ranked (st : EditorState) : List String :=
    Picker.rank (EditorState.picker_files_of st) (EditorState.picker_query_of st)

/// The row `move` past the current one, in the RANKED list. The bounds come
/// from the list itself, so a filter that shrank the list cannot leave the
/// selection out of range.
def picker_move (st : EditorState) (delta : I64) : EditorState :=
    let count : I64 := List.length (picker_ranked st) in
    let from : I64 := EditorState.picker_selected_of st in
    let target : I64 := Picker.clamp_selected (from + delta) count in
    editor_with_picker_selection st target

/// The state with the picker's highlighted row set, leaving the filter as it
/// is. The mode's payload carries both halves, so both are rebuilt here.
def editor_with_picker_selection (st : EditorState) (sel : I64) : EditorState :=
    EditorState.with_mode st (Mode.picker (EditorState.picker_query_of st) sel)

/// `picker_next` / `picker_prev` / the page keys: move the highlight.
def cmd_picker_next (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (picker_move st 1) Cmd.none

def cmd_picker_prev (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (picker_move st (-1)) Cmd.none

/// A page is the text area's height, less the picker's own header row -- the
/// same arithmetic the view lays out with.
def picker_page (st : EditorState) : I64 :=
    let rows : I64 := EditorState.rows_of st in
    if rows < 3 then 1 else rows - 2

def cmd_picker_page_down (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (picker_move st (picker_page st)) Cmd.none

def cmd_picker_page_up (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (picker_move st (0 - picker_page st)) Cmd.none

/// `picker_accept` (Enter): open the highlighted candidate and leave the
/// picker. On an empty list it reports and stays -- Escape is the way out of
/// a filter that matched nothing, and reporting beats closing on a keystroke
/// the user meant as "open what I found".
def cmd_picker_accept (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    // The ranked list is read twice (its length, then the nth row), and a
    // `List` is deliberately not `Copy`, so one `Shared` handle serves both
    // -- the affine rule's own remedy.
    let ranked : Shared (List String) := Shared.of (picker_ranked st) in
    let sel : I64 :=
        Picker.clamp_selected (EditorState.picker_selected_of st)
            (List.length (Shared.get ranked)) in
    match Picker.nth sel (Shared.get ranked) {
        Option.none =>
            Pair.pair (EditorState.with_status st "no file to open") Cmd.none,
        Option.some rel =>
            let path : String := Picker.resolve (EditorState.picker_dir_of st) rel in
            open_path_in_picker st path
    }

/// Accepting a candidate opens it: the mode returns to normal, then the open
/// proceeds exactly as `:e <path>` does -- one open path, so the picker and
/// the command line cannot build different documents for one file.
def open_path_in_picker (st : EditorState) (path : String) : Pair EditorState (Cmd EditorMsg) :=
    let left : EditorState := EditorState.with_mode st Mode.normal in
    open_in_editor left path

/// `:e <path>` and the picker's accept: read `path` and either FOCUS an open
/// buffer that already holds it or ADD a new one focused. The read is a
/// `Cmd.perform`, so the terminal is restored correctly even when the open is
/// the last thing that happens.
///
/// A PATH ALREADY OPEN IS NOT RE-READ: two buffers over one file would save
/// over each other, and the second save would silently discard the first
/// buffer's edits. `index_of_path` is the one test for that.
def open_in_editor (st : EditorState) (path : String) : Pair EditorState (Cmd EditorMsg) :=
    match EditorState.index_of_path st path {
        Option.some i => Pair.pair (focus_buffer st i path) Cmd.none,
        Option.none =>
            Pair.pair (EditorState.with_status st ("opening " ++ path))
                (Cmd.perform (fn (_ : Unit) => ply_read_file path))
    }

/// Focus the buffer at index `i`, reporting which one it is.
def focus_buffer (st : EditorState) (i : I64) (path : String) : EditorState :=
    EditorState.with_status (EditorState.with_active st i) ("focused " ++ path)

/// The read behind an open, run inside the frame. A failure answers a status
/// line rather than exiting: the editor is already running, so an unreadable
/// path is a report and not the end of the program (`main.mo`'s argv path is
/// the one that exits, before any loop exists).
def ply_read_file (path : String) : IO EditorMsg := do {
    let r <- IO.read_file (Path.path path);
    return (open_outcome path r)
}

/// The read's result as the message the pure half folds in.
def open_outcome (path : String) (r : Result StreamError String) : EditorMsg :=
    match r {
        Result.ok text => EditorMsg.file_opened path text,
        Result.err e => EditorMsg.save_result false ("open failed: " ++ path ++ ": " ++ e.message)
    }

/// Fold a finished open: add the buffer, focus it, and report it.
def fold_file_opened (st : EditorState) (path : String) (text : String) : EditorState :=
    let doc : Document := Document.of_file path text in
    let grown : EditorState := EditorState.with_doc_added st doc in
    EditorState.with_status (EditorState.with_active grown (EditorState.doc_count grown - 1))
        ("opened " ++ path)

// ── the buffer list (`:bn` / `:bp`) ───────────────────────────────────────

/// `:bn` -- focus the next buffer, wrapping. One buffer is a no-op that says
/// so, which is honest: the key was pressed and nothing changed.
def cmd_buffer_next (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (buffer_step st 1) Cmd.none

/// `:bp` -- focus the previous buffer, wrapping.
def cmd_buffer_prev (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (buffer_step st (-1)) Cmd.none

/// Move the focus `delta` buffers, WRAPPING: past the last buffer is the
/// first, which is the `:bn` every editor keeps (a "next" that stopped at the
/// end would make the key look broken on the buffer it refused to leave).
def buffer_step (st : EditorState) (delta : I64) : EditorState :=
    let count : I64 := EditorState.doc_count st in
    if count < 2
    then EditorState.with_status st ("only one buffer: " ++ buffer_name st)
    else
        let raw : I64 := EditorState.active_of st + delta in
        EditorState.with_status (EditorState.with_active st (buffer_wrap raw count))
            ("buffer " ++ I64.to_string (EditorState.active_of (EditorState.with_active st (buffer_wrap raw count)) + 1))

/// `i` wrapped into `[0, count)`.
def buffer_wrap (i : I64) (count : I64) : I64 :=
    if count < 1 then 0 else if i < 0 then count - 1 else if Bool.not (i < count) then 0 else i

/// The active buffer's display name: its path, or `[scratch]`.
def buffer_name (st : EditorState) : String :=
    match EditorState.active_doc st {
        Option.none => "[none]",
        Option.some doc =>
            match Document.path_of doc {
                Option.some p => p,
                Option.none => "[scratch]"
            }
    }

/// Run a parsed command line: an `:e <path>` first (its argument is a value,
/// not a registry name), then the no-argument names, then the unknown report.
///
/// THE ORDER IS THE PRECEDENCE, and `:e` has to come first because `parse_open`
/// is the only parser that looks at more than the whole line.
def run_parsed (st : EditorState) (line : String) : Pair EditorState (Cmd EditorMsg) :=
    match parse_open line {
        Option.some path => open_in_editor st path,
        Option.none => run_parsed_name st line
    }

/// The no-argument half of `run_parsed`.
def run_parsed_name (st : EditorState) (line : String) : Pair EditorState (Cmd EditorMsg) :=
    match parse_command line {
        Option.some cmd => run_command st cmd,
        Option.none =>
            Pair.pair (EditorState.with_status st (String.concat "no such command: " line)) Cmd.none
    }

/// THE `:`-COMMAND PARSER: the line as the name of a command in the registry.
///
/// A WHITELIST, not a pass-through, for two reasons: a typo becomes a report
/// instead of a registry miss, and the accepted spellings are readable in one
/// place. Every answer is a name `Registry.default` already carries -- `:q!`
/// is the `quit!` row, the same one `Space Q` runs, and `:w` is the same
/// `write` the `Space w` chord runs.
///
/// THE LINE IS `name` OR `name argument`, AND ONLY `:e` TAKES ONE. A command
/// that took an argument and ignored it would look like it worked, which is
/// the one failure mode a command line must not have -- so `:w extra` is
/// reported as unknown rather than run as `:w`.
///
/// `parse_command` answers the registry NAME for the no-argument forms, which
/// is what `run_parsed` hands to `run_command`. The one form with an argument
/// (`:e <path>`, and `:edit`) is answered by `parse_open`, because its
/// argument is a VALUE and not a name -- see `run_parsed`.
pub def parse_command (line : String) : Option String :=
    if String.beq line "w" then Option.some "write"
    else if String.beq line "write" then Option.some "write"
    else if String.beq line "q" then Option.some "quit"
    else if String.beq line "q!" then Option.some "quit!"
    else if String.beq line "quit" then Option.some "quit"
    else if String.beq line "quit!" then Option.some "quit!"
    else if String.beq line "wq" then Option.some "write_quit"
    else if String.beq line "x" then Option.some "write_quit"
    else if String.beq line "bn" then Option.some "buffer_next"
    else if String.beq line "bnext" then Option.some "buffer_next"
    else if String.beq line "bp" then Option.some "buffer_prev"
    else if String.beq line "bprevious" then Option.some "buffer_prev"
    else if String.beq line "noh" then Option.some "clear_status"
    else Option.none

/// The path `:e <path>` / `:edit <path>` names, or `none` when the line is
/// not that form. A bare `:e` (no path) is `none` too: "edit what?" has no
/// answer, and reporting it beats re-reading the buffer that is already open.
///
/// THE FIRST WORD IS THE COMMAND, THE REST IS THE PATH, so a path with a
/// space in it works -- which is exactly why this splits at the first space
/// rather than on every space.
pub def parse_open (line : String) : Option String :=
    match first_word line {
        Option.none => Option.none,
        Option.some word =>
            // The first word is compared twice and then dropped from the
            // line, so it is shared: `String` is `Copy`, but a `Shared` here
            // states the multi-read in one place and costs a pointer.
            let shared : Shared String := Shared.of word in
            if Bool.not (String.beq (Shared.get shared) "e")
                && Bool.not (String.beq (Shared.get shared) "edit")
            then Option.none
            else ply_open_arg line (Shared.get shared)
    }

/// The argument after the command word, trimmed. An empty remainder is
/// `none` (a bare `:e`), which is the case `parse_open`'s doc states.
def ply_open_arg (line : String) (word : String) : Option String :=
    let rest : String := String.trim (String.drop (String.length word) line) in
    if String.is_empty rest then Option.none else Option.some rest

/// The first whitespace-delimited word of a line, or `none` when the line
/// starts with space (which the caller has already trimmed) or is empty.
#[terminating]
def first_word_go (line : String) (at : I64) : Option String :=
    match String.get line at {
        Option.none => Option.some line,
        Option.some b =>
            if is_space_byte b
            then Option.some (String.slice line 0 at)
            else first_word_go line (at + 1)
    }

/// The line's first word, or `none` when there is none.
def first_word (line : String) : Option String :=
    if String.is_empty line then Option.none else first_word_go line 0

/// A space or a tab -- the two bytes that separate a command from its
/// argument.
def is_space_byte (b : U8) : Bool := U8.beq b 32u8 || U8.beq b 9u8

/// `:noh` clears the status line, which is the one thing a stale report
/// needs: the row is otherwise the last command's answer forever.
def cmd_clear_status (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    Pair.pair (EditorState.with_status st "") Cmd.none

/// `:wq` (and `:x`): save, and quit only when the save SUCCEEDED.
///
/// A failed write must not close the editor -- the user would lose exactly the
/// text the save was meant to keep -- so the two halves run in order through
/// the IO side: the save's action answers, and a successful answer is replaced
/// by `EditorMsg.quit`, which `update` turns into `Cmd.quit`. That indirection
/// exists because `Cmd.perform`'s action returns a MESSAGE, so an action can
/// never itself hand back a `Cmd`.
///
/// THE SCRATCH BUFFER CASE FALLS THROUGH: `cmd_write` refuses in the pure half
/// with no command at all, and `quit_on_save` leaves a non-`perform` command
/// alone, so `:wq` on a buffer with no path reports and stays open.
def cmd_write_quit (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    match cmd_write st {
        Pair.pair after cmd => Pair.pair after (quit_on_save cmd)
    }

/// A command that quits after a successful save. Only a `perform` can be
/// wrapped (that is the shape a write issues); anything else -- `Cmd.none` for
/// the no-path refusal -- passes through untouched.
def quit_on_save (cmd : Cmd EditorMsg) : Cmd EditorMsg :=
    // The command is read twice (the arm's test, then the untouched answer),
    // so it goes through one `Shared` handle -- the affine rule's own remedy
    // for a value with no `Copy` instance.
    let shared : Shared (Cmd EditorMsg) := Shared.of cmd in
    match Shared.get shared {
        Cmd.perform action => Cmd.perform (fn (_ : Unit) => write_then_quit action),
        Cmd.none => Shared.get shared,
        Cmd.quit => Shared.get shared,
        Cmd.dispatch _ => Shared.get shared,
        Cmd.inspect _ => Shared.get shared,
        Cmd.perform_async _ _ => Shared.get shared
    }

/// Run the save and decide: success answers `EditorMsg.quit` (carrying the
/// write's report nowhere -- the terminal is restored before the message is
/// folded, so the status line is not read again), failure answers the write's
/// own report so the status line explains itself.
def write_then_quit (action : Unit -> IO EditorMsg) : IO EditorMsg := do {
    let msg <- action unit;
    return (quit_msg_or msg)
}

/// The save's answer as the message to fold: the quit on success, the report
/// on failure.
def quit_msg_or (msg : EditorMsg) : EditorMsg :=
    // The message is read twice in the failure arm (the test, then the
    // answer), so one `Shared` handle serves both.
    let shared : Shared EditorMsg := Shared.of msg in
    match Shared.get shared {
        EditorMsg.save_result ok _ =>
            if ok then ply_quit_msg else Shared.get shared,
        EditorMsg.key _ => Shared.get shared,
        EditorMsg.resize _ _ => Shared.get shared,
        EditorMsg.tick => Shared.get shared,
        EditorMsg.quit => Shared.get shared,
        EditorMsg.lsp_frame _ => Shared.get shared,
        EditorMsg.picker_files _ _ => Shared.get shared,
        EditorMsg.file_opened _ _ => Shared.get shared
    }

/// The quit message, built in its own def so the constructor is never
/// spelled inline in a match arm (the constructor-shadowing risk).
def ply_quit_msg : EditorMsg := EditorMsg.quit

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

/// Esc: back to normal mode, selections kept (the §4 rule). It is also the
/// way OFF the command line, and it is bound in every mode's table, so the
/// command line needs no cancel command of its own.
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
