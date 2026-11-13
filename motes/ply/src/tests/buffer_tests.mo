// Phase 5's buffer-list gate: `:e <path>` opens and focuses, `:bn`/`:bp`
// move the focus and wrap, and a path already open is FOCUSED rather than
// re-read (code-editor.md Phase 5, fourth item).
//
// THE FOCUS RATHER THAN RE-READ RULE IS THE ONE THAT MATTERS: two buffers over
// one file would save over each other, so the second save would silently
// discard the first buffer's edits. `test_reopen_focuses_instead_of_copying`
// is that assertion, and it is a test rather than a comment because the
// failure mode is silent data loss.
//
// THE IO HALF IS NOT DRIVEN HERE. `:e` issues a `Cmd.perform` that reads the
// file and answers `EditorMsg.file_opened`; these tests fold that message
// directly, which is the same fold the real loop runs (see `save_tests.mo`'s
// note on the same split, and `tests/e2e_tests.mo` for the end-to-end gate).

use lib::model {Document, Document.of_text, EditorState, EditorState.init,
    EditorState.active_doc, EditorState.active_of, EditorState.doc_count,
    EditorState.mode_of, EditorState.status_of, EditorMsg,
    EditorState.with_active, EditorState.with_bindings, EditorState.with_docs,
    EditorState.with_picker_files}
use lib::commands {update, parse_command, parse_open}
use lib::keymap {Binding, Keymap.default_bindings}
use lib::rope {Rope.to_string}
use lib::types {Mode, Rope}
use tui::types {Key}
use tui::tui {Cmd}
// `List.length` lives in `init/src/list.mo`; the empty brace list is the
// documented form for pulling its INSTANCES into scope.
use init::shared {Shared}
use std::list {}
// `Copy EditorState` and `Copy Mode` live in `lib::instances`; without them
// a test's `after` binder is affine and the two-read assertions are errors.
use lib::instances {}

// ── Accessors, one read each ─────────────────────────────────────────────

/// A fresh one-buffer state over `text`.
def bl_state (text : String) : EditorState :=
    EditorState.init (Document.of_text text) 24 80

/// One `update` step's state.
def bl_press (st : EditorState) (k : Key) : EditorState :=
    let msg : EditorMsg := EditorMsg.key k in
    match update st msg {
        Pair.pair after _ => after
    }

/// A whole keystroke script.
#[terminating]
def bl_type (st : EditorState) (keys : List Key) : EditorState :=
    match bl_keys_pair st keys {
        Pair.pair after _ => after
    }

/// The same fold, KEEPING the last key's pair -- so a test can see the `Cmd`
/// the final keystroke issued (`:e`'s read, `Space f`'s listing) as well as
/// the state it left. An empty script issues nothing.
#[terminating]
def bl_keys_pair (st : EditorState) (keys : List Key) : Pair EditorState (Cmd EditorMsg) :=
    match keys {
        List.empty => Pair.pair st Cmd.none,
        List.cons k rest =>
            match update st (EditorMsg.key k) {
                // THE LAST KEY'S COMMAND IS KEPT, not discarded: a command can
                // be issued by any key of a chord (`Space f` issues its
                // listing on `f`, not on the prefix), so dropping every
                // intermediate answer loses the only command there was. The
                // recursion therefore threads the pair forward and only the
                // FINAL step's command is the answer.
                Pair.pair after cmd => bl_keys_pair_keep (bl_keys_pair after rest) cmd
            }
    }

/// The pair from the rest of the script, unless that part issued nothing -- in
/// which case the command from the key just pressed is the answer.
///
/// BOTH ARMS ARE REBUILT from their own binders, and neither binder is read
/// twice: a `Pair` is not `Copy`, so `Pair.pair after c` built from two
/// match-bound components is the only shape the affine rule accepts here.
def bl_keys_pair_keep (tail : Pair EditorState (Cmd EditorMsg)) (cmd : Cmd EditorMsg)
    : Pair EditorState (Cmd EditorMsg) :=
    match tail {
        Pair.pair after tail_cmd =>
            match tail_cmd {
                Cmd.none => Pair.pair after cmd,
                Cmd.quit => Pair.pair after Cmd.quit,
                Cmd.dispatch m => Pair.pair after (Cmd.dispatch m),
                Cmd.perform f => Pair.pair after (Cmd.perform f),
                Cmd.inspect f => Pair.pair after (Cmd.inspect f),
                Cmd.perform_async f g => Pair.pair after (Cmd.perform_async f g)
            }
    }

/// Fold a finished open, as the loop does. The state keeps its scratch buffer,
/// so the opened file ADDS one -- what the buffer-list tests below assert.
def bl_opened (st : EditorState) (path : String) (text : String) : EditorState :=
    let msg : EditorMsg := EditorMsg.file_opened path text in
    match update st msg {
        Pair.pair after _ => after
    }

/// The state a session whose FIRST act is opening a file reaches: the file's
/// buffer is the only one. `main.mo`'s argv path builds exactly this (it opens
/// the document, it does not append to a scratch buffer), which is why the
/// reopen pins start here.
def bl_opened_fresh (st : EditorState) (path : String) (text : String) : EditorState :=
    let msg : EditorMsg := EditorMsg.file_opened path text in
    match update (bl_without_buffers st) msg {
        Pair.pair after _ => after
    }

/// The state with its buffer list emptied and no buffer focused.
def bl_without_buffers (st : EditorState) : EditorState :=
    EditorState.with_docs (EditorState.with_active st 0) List.empty

/// A character key.
def bl_key (c : String) : Key := Key.char c

/// The active buffer's text.
def bl_text (st : EditorState) : String :=
    match EditorState.active_doc st {
        Option.some doc => Rope.to_string (bl_doc_rope doc),
        Option.none => "<no doc>"
    }

def bl_doc_rope (doc : Document) : Rope :=
    match doc { { rope, .. } => rope }

/// The active buffer's path, or `<scratch>`.
def bl_path (st : EditorState) : String :=
    match EditorState.active_doc st {
        Option.some doc =>
            match Document.path_of doc {
                Option.some p => p,
                Option.none => "<scratch>"
            },
        Option.none => "<none>"
    }

/// Type a whole command line (`:` then the characters then Enter).
def bl_colon (st : EditorState) (text : String) : EditorState :=
    bl_type st (List.append (List.cons (bl_key ":") List.empty)
        (List.append (bl_chars text) (List.cons Key.enter List.empty)))

/// `text` as character keys, one per byte -- the fixtures are ASCII.
#[terminating]
def bl_chars (text : String) : List Key :=
    match String.get text 0 {
        Option.none => List.empty,
        Option.some _ =>
            List.cons (bl_key (String.slice text 0 1)) (bl_chars (String.drop 1 text))
    }

// ── `:e <path>` parsing ──────────────────────────────────────────────────

/// `:e main.mo` names `main.mo`; `:edit` is the long spelling.
#[test]
def test_parse_open_table : Bool :=
    bl_parses "e main.mo" "main.mo"
        && bl_parses "edit motes/ply/src/main.mo" "motes/ply/src/main.mo"

/// A path with a SPACE survives: the first word is the command, the REST is
/// the path -- splitting on every space would truncate it.
#[test]
def test_parse_open_keeps_spaces_in_the_path : Bool :=
    bl_parses "e my notes.mo" "my notes.mo"

/// A bare `:e` has no path, so it is not an open -- "edit what?" has no
/// answer, and re-reading the open buffer would be a guess.
#[test]
def test_parse_open_needs_a_path : Bool :=
    bl_open_none "e" && bl_open_none "edit" && bl_open_none "e   "

/// Another command's line is not an open, even with an argument.
#[test]
def test_parse_open_rejects_other_commands : Bool :=
    bl_open_none "w main.mo" && bl_open_none "bn" && bl_open_none "wq"

def bl_parses (line : String) (want : String) : Bool :=
    match parse_open line {
        Option.some got => String.beq got want,
        Option.none => false
    }

def bl_open_none (line : String) : Bool :=
    match parse_open line {
        Option.some _ => false,
        Option.none => true
    }

// ── The buffer-list commands' names ──────────────────────────────────────

/// `:bn`/`:bp` and their long spellings name the registry rows.
#[test]
def test_parse_buffer_commands : Bool :=
    bl_names "bn" "buffer_next" && bl_names "bnext" "buffer_next"
        && bl_names "bp" "buffer_prev" && bl_names "bprevious" "buffer_prev"
        && bl_names "noh" "clear_status"

def bl_names (line : String) (want : String) : Bool :=
    match parse_command line {
        Option.some got => String.beq got want,
        Option.none => false
    }

/// `:e` is NOT a registry name -- it carries an argument, so it is answered by
/// `parse_open` and must not also answer `parse_command`.
#[test]
def test_parse_command_does_not_answer_e : Bool :=
    match parse_command "e" {
        Option.some _ => false,
        Option.none => true
    }

// ── Opening ──────────────────────────────────────────────────────────────

/// An open adds a SECOND buffer and focuses it: the original text is still
/// there behind the new one.
#[test]
def test_open_adds_and_focuses_a_buffer : Bool :=
    let st : EditorState := bl_opened (bl_state "alpha") "b.mo" "beta" in
    I64.beq (EditorState.doc_count st) 2
        && I64.beq (EditorState.active_of st) 1
        && String.beq (bl_text st) "beta"
        && String.beq (bl_path st) "b.mo"

/// The buffer that was open is still open, unchanged.
#[test]
def test_open_keeps_the_first_buffer : Bool :=
    let st : EditorState := bl_opened (bl_state "alpha") "b.mo" "beta" in
    I64.beq (bl_buffer_text_at st 0) 0
        && String.beq (bl_text_at st 0) "alpha"

/// The count of buffers, then the text of one of them.
def bl_buffer_text_at (st : EditorState) (i : I64) : I64 :=
    if String.beq (bl_text_at st i) "alpha" then 0 else 1

/// The text of buffer `i`, or `<none>`.
def bl_text_at (st : EditorState) (i : I64) : String :=
    match bl_doc_at (EditorState.docs_of st) i {
        Option.some doc => Rope.to_string (bl_doc_rope doc),
        Option.none => "<none>"
    }

#[terminating]
def bl_doc_at (docs : List Document) (i : I64) : Option Document :=
    match docs {
        List.empty => Option.none,
        List.cons one rest => if i < 1 then Option.some one else bl_doc_at rest (i - 1)
    }

/// THE SILENT-DATA-LOSS PIN. Opening a path that is ALREADY open focuses it
/// and adds no buffer -- so an edit in the first buffer cannot be overwritten
/// by a second buffer's save of the same file.
#[test]
def test_reopen_focuses_instead_of_copying : Bool :=
    let st : EditorState := bl_opened_fresh (bl_state "alpha") "a.mo" "alpha" in
    let st2 : EditorState := bl_second_open st in
    I64.beq (EditorState.doc_count st2) 1
        && I64.beq (EditorState.active_of st2) 0
        && String.beq (bl_text st2) "alpha"

/// A second open folded by hand: the same path, different text. The state
/// keeps ONE buffer, which is the assertion -- the text is the focused
/// document's, so re-reading would show "changed" here.
def bl_second_open (st : EditorState) : EditorState :=
    bl_focus_path st "a.mo"

/// The state `:e a.mo` reaches, driven through the real command line: the
/// path is already open, so the pure half focuses it with no IO at all.
def bl_focus_path (st : EditorState) (path : String) : EditorState :=
    bl_colon st (String.concat "e " path)

/// `:e <path>` on an ALREADY-open path focuses it through the real command
/// line, with no read issued.
#[test]
def test_colon_e_on_an_open_path_focuses : Bool :=
    let st : EditorState := bl_opened_fresh (bl_state "alpha") "a.mo" "alpha" in
    let pair : Pair EditorState (Cmd EditorMsg) :=
        bl_colon_pair st "e a.mo" in
    match pair {
        Pair.pair after cmd => I64.beq (EditorState.doc_count after) 1 && bl_is_none cmd
    }

/// A command with no IO work is `Cmd.none`.
def bl_is_none (cmd : Cmd EditorMsg) : Bool :=
    match cmd {
        Cmd.none => true,
        Cmd.quit => false,
        Cmd.dispatch _ => false,
        Cmd.perform _ => false,
        Cmd.inspect _ => false,
        Cmd.perform_async _ _ => false
    }

/// A whole `:` line typed, with the command it produced.
def bl_colon_pair (st : EditorState) (text : String) : Pair EditorState (Cmd EditorMsg) :=
    bl_keys_pair st (List.append (List.cons (bl_key ":") List.empty)
        (List.append (bl_chars text) (List.cons Key.enter List.empty)))

/// A NOT-OPEN path on the command line issues the read: the mode returns to
/// normal, the status says it is opening, and the command is a `perform`.
#[test]
def test_colon_e_on_a_new_path_issues_the_read : Bool :=
    match bl_open_pair (bl_state "alpha") "e b.mo" {
        // The state is bound to a TYPED local before it is read twice: a
        // match binder's type is not settled when the affine check runs, so
        // `Copy EditorState` would not be consulted and the second read
        // would be a double use.
        Pair.pair after cmd => bl_open_ok (bl_typed after) (bl_is_none cmd)
    }

/// The state as a typed local -- the annotation is the point.
def bl_typed (st : EditorState) : EditorState := st

/// The `:e` assertions over one typed state.
def bl_open_ok (st : EditorState) (cmd_is_none : Bool) : Bool :=
    Bool.not cmd_is_none
        && String.contains (EditorState.status_of st) "opening"
        && Bool.not (bl_is_mode_command (EditorState.mode_of st))

/// The pair a `:e <path>` line produces, captured at the Enter key.
def bl_open_pair (st : EditorState) (text : String) : Pair EditorState (Cmd EditorMsg) :=
    bl_pair_key (bl_type st (List.append (List.cons (bl_key ":") List.empty) (bl_chars text)))
        Key.enter

/// One step, keeping the pair.
def bl_pair_key (st : EditorState) (k : Key) : Pair EditorState (Cmd EditorMsg) :=
    let msg : EditorMsg := EditorMsg.key k in
    update st msg

/// Is the mode the command line? (`:` leaves it before the command runs.)
def bl_is_mode_command (m : Mode) : Bool :=
    match m {
        Mode.command _ => true,
        _ => false
    }

// ── `:bn` / `:bp` ────────────────────────────────────────────────────────

/// A two-buffer state: "alpha" focused.
def bl_two : EditorState :=
    let st : EditorState := bl_opened (bl_state "alpha") "b.mo" "beta" in
    EditorState.with_active st 0

/// `:bn` focuses the next buffer.
#[test]
def test_buffer_next : Bool :=
    let st : EditorState := bl_colon bl_two "bn" in
    I64.beq (EditorState.active_of st) 1 && String.beq (bl_text st) "beta"

/// `:bp` focuses the previous one.
#[test]
def test_buffer_prev : Bool :=
    let st : EditorState := bl_colon bl_two "bp" in
    I64.beq (EditorState.active_of st) 1

/// `:bn` from the LAST buffer WRAPS to the first -- a next that stopped would
/// make the key look broken on the buffer it refused to leave.
#[test]
def test_buffer_next_wraps : Bool :=
    let st : EditorState := bl_colon (EditorState.with_active bl_two 1) "bn" in
    I64.beq (EditorState.active_of st) 0

/// `:bp` from the FIRST buffer wraps to the last.
#[test]
def test_buffer_prev_wraps : Bool :=
    let st : EditorState := bl_colon bl_two "bp" in
    I64.beq (EditorState.active_of st) 1

/// One buffer is a no-op that SAYS so, rather than a silent nothing.
#[test]
def test_buffer_next_with_one_buffer_reports : Bool :=
    let st : EditorState := bl_colon (bl_state "alpha") "bn" in
    I64.beq (EditorState.active_of st) 0
        && String.contains (EditorState.status_of st) "only one buffer"

// ── The picker's listing fold ────────────────────────────────────────────

/// The fold puts the candidates and their directory on the state, and does
/// NOT open the picker: a listing that arrives after Escape must not.
#[test]
def test_picker_files_fold_sets_the_listing : Bool :=
    let msg : EditorMsg :=
        EditorMsg.picker_files "" (List.cons "main.mo" List.empty) in
    match update (bl_state "x") msg {
        Pair.pair after _ => bl_listing_ok (bl_typed after)
    }

/// The listing assertions over one typed state (three reads of it).
def bl_listing_ok (st : EditorState) : Bool :=
    I64.beq (List.length (EditorState.picker_files_of st)) 1
        && String.beq (EditorState.picker_dir_of st) ""
        && Bool.not (bl_is_mode_picker (EditorState.mode_of st))

/// Is the mode the picker?
def bl_is_mode_picker (m : Mode) : Bool :=
    match m {
        Mode.picker _ _ => true,
        _ => false
    }

/// `Space f` enters the picker and asks for a listing -- the mode is set
/// BEFORE the listing arrives, so a key typed meanwhile lands in the filter.
#[test]
def test_file_picker_enters_and_lists : Bool :=
    match bl_picker_pair (bl_state "x") {
        Pair.pair after cmd =>
            bl_is_mode_picker (EditorState.mode_of after) && Bool.not (bl_is_none cmd)
    }

/// The pair a `Space f` chord produces.
def bl_picker_pair (st : EditorState) : Pair EditorState (Cmd EditorMsg) :=
    bl_keys_pair st
        (List.cons (Key.char " ") (List.cons (Key.char "f") List.empty))

// ── A rebinding still reaches the new commands ───────────────────────────

/// The config gate's mechanism, applied to a Phase 5 command: a `ply.toml`
/// row rebinding `n` to `buffer_next` really runs it, because the registry
/// name is all a binding carries. This is the check that the new rows are in
/// the same registry the keymap addresses.
#[test]
def test_config_can_bind_a_buffer_command : Bool :=
    let base : EditorState := bl_two in
    let st : EditorState :=
        EditorState.with_bindings base
            (List.append Keymap.default_bindings (List.cons (bl_binding "buffer_next") List.empty)) in
    let after : EditorState := bl_press st (bl_key "n") in
    I64.beq (EditorState.active_of after) 1

/// A one-key normal-mode binding for `buffer_next`.
def bl_binding (command : String) : Binding :=
    { mode := "normal", keys := List.cons (bl_key "n") List.empty, command := command }
