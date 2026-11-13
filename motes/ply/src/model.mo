// Ply's document and, later, the editor model.
//
// Phase 1 needs `Document` -- the thing a transaction transforms -- and
// nothing else from the plan's §3 block. `EditorState`/`EditorMsg`/`Command`
// arrive with the keymap (Phase 2) and pull in `tui`'s types, so they stay
// out until then: a Phase 1 mote that does not import `tui` keeps its pure
// core checkable without the widget tree's scope.
//
// `Document.version` BUMPS EXACTLY ONCE PER APPLIED TRANSACTION (the plan's
// §3 note, and the Phase 1 gate's last case). It is the number LSP
// `didChange` (Phase 6) and MCP `buffer_apply` (Phase 7) both check, so the
// bump lives in `transaction.mo`'s apply, not in any caller -- a caller
// that could forget it is a caller that would.

use init::shared {Shared}
use init::copy {Copy}
use lib::types {Rope, Selections, History, Mode}
use lib::rope {Rope.of_string, Rope.to_string}
use lib::history {History.empty, History.commit, History.mark_saved}
use lib::selection {Selections.cursor}
use lib::keymap {Binding, Keymap.default_bindings}
use tui::types {Key, Event}
use tui::tui {Cmd}

/// One open buffer: its text as a rope, the selections a view has on it,
/// the undo tree, and the version a transaction bumps.
pub struct Document {
    /// The file it came from, or `none` for a scratch buffer. A path is
    /// data, not an open handle (Phase 4 reads and writes through `IO`,
    /// on open and on save).
    path : Option String,
    /// The whole text. Persistent: every revision points at a rope it
    /// shares with the revisions around it.
    rope : Rope,
    /// Every selection in this view, plus the primary one.
    selections : Selections,
    /// The undo tree. `History.current` names the revision `rope` IS --
    /// a document is a history position plus its text.
    history : History,
    /// The edit language, for the highlighter's table (Phase 3) and the
    /// LSP client's languageId (Phase 6). `"text"` is the no-highlight
    /// default.
    language : String,
    /// Bumped once per applied transaction by `transaction.mo`, never by
    /// a caller, never by undo/redo (those move `History.current`, and the
    /// buffer's on-disk identity did not change).
    version : I64
}

/// A document over `text` with a bare cursor at 0: the state Phase 4
/// opens a file into, and the one every test builds.
///
/// THE HISTORY IS SEEDED, NOT EMPTY: the opened text is revision 0, so
/// the first edit commits revision 1 and an undo walks back to the file
/// as it was opened -- not to nothing. A document whose history started
/// empty would have nothing to undo after its first edit, and `:q`'s
/// dirty check would read the wrong baseline.
///
/// THE SEEDED REVISION IS ALSO THE SAVED ONE: the text a document is
/// created over is the baseline it came from (a file's bytes on open, a
/// scratch buffer's empty start), so the dirty flag -- `current !=
/// saved`, Phase 4's `Space w`/`:q` rule -- reads FALSE on every fresh
/// document. Without the mark the seeded revision would read dirty
/// forever, and `:q` would refuse to quit a buffer nobody touched.
///
/// One constructor for every `Document` in the program (the plan's
/// two-host struct-literal risk names why: a struct literal that omits a
/// field checks clean on both hosts and reads garbage at runtime, so the
/// field list lives in exactly one place).
pub def Document.of_text (text : String) : Document :=
    let rope : Rope := Rope.of_string text in
    // THE ROPE IS BUILT ONCE, and the seeded revision 0 shares the tree the
    // document holds (`History.commit` takes the rope, not the text) -- so
    // opening a file pays `Rope.of_string` once, and undo's baseline is the
    // very same persistent structure rather than an equal copy.
    match History.commit History.empty rope (Selections.cursor 0) List.empty 0 {
        Pair.pair seeded _ =>
            { path := Option.none,
                rope := rope,
                selections := Selections.cursor 0,
                history := History.mark_saved seeded,
                language := "text",
                version := 0 }
    }

/// The document with its edit language set: the highlighter's table
/// choice (Phase 3) and the LSP client's `languageId` (Phase 6). Phase
/// 4's open derives it from the file's extension; a test sets it
/// directly, and nothing else does -- the language is open-time data,
/// not a per-keystroke field.
pub def Document.with_language (doc : Document) (lang : String) : Document :=
    { doc with language := lang }

/// The document with its file path set: Phase 4's open, and nothing else
/// (a scratch buffer keeps `Option.none`, and `Space w` refuses it --
/// there is no file to write).
///
/// A PATH IS DATA, NOT A HANDLE: the file was read before this builder
/// ran, and `cmd_write`'s action writes it after, so no descriptor rides
/// in the document.
pub def Document.with_path (doc : Document) (p : String) : Document :=
    { doc with path := Option.some p }

/// The document with its history replaced -- the builder a save uses to
/// move `saved` onto the current revision. The history travels as an
/// ARGUMENT rather than being read from the document here: a `Document`
/// is not `Copy` (its history holds a `BTreeMap`), so a def that both
/// reads a field and updates the record would trip the affine rule at
/// its own binder. `commands.mo`'s `doc_history` is the read.
pub def Document.with_history (doc : Document) (h : History) : Document :=
    { doc with history := h }

/// The document's whole text, for the writer. O(n) over the leaves --
/// the right price at save time and the wrong one per keystroke, so
/// nothing in the editing loop calls it.
pub def Document.text_of (doc : Document) : String :=
    match doc { { rope, .. } => Rope.to_string rope }

/// The language name a path's extension names: `monad` for `.mo`, `text` (the
/// no-highlight default) for everything else. Phase 3's `Highlight.config_for`
/// takes the same names, and "text" is its fallback too -- an editor must open
/// any file, not only the ones it can color.
///
/// IT LIVES HERE, not in `main.mo`, because `:e <path>` (`commands.mo`) opens
/// files too: the binary and the command line must derive the same language
/// or the same file would highlight differently depending on how it was
/// opened. `main.mo`'s own tests point at this def.
///
/// Matched case-sensitively: `.MO` is not `.mo` anywhere else in this corpus,
/// and guessing would only make the highlighter's table wrong in a way nothing
/// reports.
///
/// ARGUMENT ORDER: `String.ends_with` takes the STRING first and the suffix
/// second (`std`'s other user, `acorn::passes`, reads `ends_with path ".md"`).
/// That is the opposite of `String.starts_with`, which takes the prefix first
/// -- the pair is an easy one to write backwards, and backwards here is
/// silently always-false.
pub def Document.language_for_path (path : String) : String :=
    if String.ends_with path ".mo" then "monad" else "text"

/// A document opened from a file: its text, its path, and the language its
/// extension names. The ONE open constructor, so `main.mo`'s argv path and
/// Phase 5's `:e <path>` cannot build different documents for one file.
///
/// Built through THREE annotated locals rather than one expression: a
/// struct-update expression in argument position is the two-host inference
/// hazard, and `Document.of_text` is the one constructor for a `Document`'s
/// field list.
pub def Document.of_file (path : String) (text : String) : Document :=
    let base : Document := Document.of_text text in
    let named : Document := Document.with_path base path in
    Document.with_language named (Document.language_for_path path)

/// Whether this document came from `path` -- how `:e` decides between
/// focusing an open buffer and adding a second one.
pub def Document.has_path (doc : Document) (path : String) : Bool :=
    match Document.path_of doc {
        Option.some p => String.beq p path,
        Option.none => false
    }

/// The document's path, or `none` for a scratch buffer.
pub def Document.path_of (doc : Document) : Option String :=
    match doc { { path, .. } => path }

/// The document's history, read once (see `with_history` on why the
/// save's two halves are separate defs).
pub def Document.history_of (doc : Document) : History :=
    match doc { { history, .. } => history }

/// Whether the buffer has unsaved changes: the current revision is not
/// the saved one. The one place the rule is spelled, so the status
/// line's `[+]` and the `Space q` refusal cannot disagree (`view.mo`
/// delegates here).
pub def Document.dirty (doc : Document) : Bool :=
    match doc { { history, .. } => ply_history_dirty history }

/// The history's own dirty bit: `current != saved`.
def ply_history_dirty (h : History) : Bool :=
    match h {
        { current, saved, .. } => Bool.not (I64.beq current saved)
    }

/// The document with the current revision marked saved: what a
/// successful write does, so `Document.dirty` turns off. A SAVE DOES NOT
/// COMMIT A REVISION -- the text did not change, only which revision is
/// on disk -- so `saved` moves and nothing else does.
///
/// The two reads go through a `Shared` handle: a `Document` is not
/// `Copy` (its history holds a `BTreeMap`), so a def that reads a field
/// AND updates the record would use its binder twice.
pub def Document.mark_saved (doc : Document) : Document :=
    let shared : Shared Document := Shared.of doc in
    Document.with_history (Shared.get shared)
        (History.mark_saved (Document.history_of (Shared.get shared)))

/// Everything a write needs -- the path (`none` for a scratch buffer) and
/// the whole text -- read in ONE match. Two accessors would read the
/// `Document` binder twice, which the affine rule refuses for a
/// non-`Copy` record; one match is one read.
pub def Document.save_target (doc : Document) : Pair (Option String) String :=
    match doc {
        { path, rope, .. } => Pair.pair path (Rope.to_string rope)
    }

// ── The status-line lines the file commands print ────────────────────────
//
// Three fixed strings, each named once so the message a user sees and the
// message a test asserts cannot drift apart. They hang off `EditorState`
// because that is the record whose `status` field carries them.

/// The status while a write is in flight. It is replaced in the same
/// frame by the `save_result` fold, so it is only ever visible on a
/// pathologically slow disk -- but it is the honest thing to say.
pub def EditorState.writing_status : String := "writing..."

/// A write with no path: a scratch buffer has no file to open.
pub def EditorState.no_path_status : String := "no path to write"

/// The `Space q` refusal. It NAMES THE WAY OUT: a bare "no" would leave
/// the user with an unsaved buffer and no idea which key discards it.
pub def EditorState.dirty_quit_status : String := "unsaved changes; Space Q quits without saving"

// ── The editor model (the plan's §3 remainder) ──────────────────────────
//
// `EditorState` is the Elm model `update` folds. Modes are RUNTIME DATA,
// not an indexed monad (Decision 3): the mode is chosen by the next
// keystroke, which a compile-time index cannot follow, so wrong-mode
// commands are ruled out by the keymap's mode tables and not by types.
//
// The registers field is an ADDITION to the plan's §3 record: `y`/`p`
// (§4's yank/paste) need somewhere to put the text, and the plan's field
// list has no slot. It is the internal-register Known Limitation (the
// plan's own wording: "Clipboard is internal registers only"), so the
// list IS the whole clipboard story for now.

/// The loop's message type: a key, a resize, a tick, or one LSP frame
/// body (Phase 6 -- `lsp_frame` folds as a no-op until the client lands,
/// so the message the wire will send is already in place).
///
/// NO `#[derive BEq]` here: this file holds function bodies, and a
/// derive-bearing file must hold none (`motes/tui/src/types.mo`'s rule).
pub type EditorMsg {
    key (k : Key),
    resize (rows : I64) (cols : I64),
    tick,
    lsp_frame (body : String),
    /// A write finished: `ok` says the file was written, `msg` is the
    /// status line's report (the path on success, the OS message on
    /// failure). THE IO CANNOT TOUCH THE STATE -- `Cmd.perform`'s action
    /// sees only `Unit` -- so the result comes back as a message and the
    /// pure `update` folds it in. Phase 6's `lsp_frame` is the same shape
    /// for the same reason.
    save_result (ok : Bool) (msg : String),
    /// Stop the editor. A MESSAGE RATHER THAN A COMMAND, so a decision made
    /// on the IO side can still end the program: `Cmd.perform`'s action
    /// returns a message, and nothing it returns can BE a `Cmd`. `:wq` needs
    /// exactly that -- write, and only quit if the write succeeded -- so the
    /// successful action answers with this and `update` turns it into
    /// `Cmd.quit`.
    quit,
    /// The file picker's candidates arrived. THE SAME SPLIT AS
    /// `save_result`, FOR THE SAME REASON: `Cmd.perform`'s action cannot see
    /// or touch the state, so `IO.list_dir`'s answer travels back as a
    /// message and the pure `update` folds it in.
    ///
    /// `dir` rides along, and the paths are RELATIVE to it. Re-deriving the
    /// directory at fold time would read the process's cwd a second time,
    /// and the two readings are not the same question -- a listing taken in
    /// `..` is not a listing of `.`.
    picker_files (dir : String) (files : List String),
    /// A file finished reading for `:e <path>` / `picker_accept`. Same split,
    /// same reason: the read is a `Cmd.perform` action, so its answer comes
    /// back as a message and the pure `update` adds the buffer.
    file_opened (path : String) (text : String)
}

/// `tui::App`'s `on_event : Event -> EditorMsg` (the plan's §3): keys and
/// resizes lift into the editor's own messages; everything else is a tick,
/// which the pure update ignores. A bare `EditorMsg.tick` in the default
/// arm would shadow same-named locals in older toolchains -- the plan's
/// constructor-name risk -- so the arm binds the event instead.
pub def on_event (e : Event) : EditorMsg :=
    match e {
        Event.key k => EditorMsg.key k,
        Event.resize r c => EditorMsg.resize r c,
        _ => ply_tick_msg
    }

/// The tick message, built in its own def so `on_event`'s default arm
/// never spells the constructor inline.
def ply_tick_msg : EditorMsg := EditorMsg.tick

/// A named command: its name (what a `Binding` points at), a doc line,
/// and the Elm-style step. A single-constructor `type`, not a `struct`,
/// because its field holds a closure over the model (the plan's §3 note).
pub type Command {
    command (name : String) (doc : String) (run : EditorState -> Pair EditorState (Cmd EditorMsg))
}

/// The editor's whole model: the open buffers, the active one, the mode,
/// the pending key prefix, the binding tables, the status line, the
/// scroll, and the terminal size the view needs.
pub struct EditorState {
    /// Every open buffer. The active one is `active`'s index.
    docs : List Document,
    /// Which doc is focused.
    active : I64,
    /// The mode (runtime data -- Decision 3).
    mode : Mode,
    /// The key sequence so far, waiting for the rest of a chord.
    pending : List Key,
    /// The binding tables, data (Decision 4): the defaults, with
    /// `ply.toml`'s rows merged over them in Phase 5.
    bindings : List Binding,
    /// The one-line status message (what `:` commands print to).
    status : String,
    /// The first visible row (the view scrolls it).
    scroll : I64,
    /// The first visible COLUMN of the text area -- horizontal scroll. The
    /// view clamps it around the primary head's column exactly as `scroll`
    /// is clamped around its line, so a caret past the text area's right
    /// margin is shown by moving the window rather than by painting the
    /// caret nowhere.
    hscroll : I64,
    /// Terminal geometry, kept in step by `EditorMsg.resize`.
    rows : I64,
    cols : I64,
    /// The yank/paste registers (the internal-register Known Limitation).
    /// The head is the most recent yank; `p` pastes it.
    registers : List String,
    /// The file picker's candidates, RELATIVE to `picker_dir`: what the last
    /// `IO.list_dir` answered, and what `Space f` filters. It lives on the
    /// state rather than in `Mode.picker` because it outlives the mode (a
    /// picker re-opened in the same directory starts from the same listing)
    /// and because the mode is rebuilt per keystroke.
    ///
    /// AN ABSOLUTE PATH IS NOT A REJECTION: `Path.is_absolute` decides, and
    /// a listing of `/` really is `/a`, `/b`.
    picker_files : List String,
    /// The directory `picker_files` names paths in. `""` means the process's
    /// own cwd, which is what the editor starts in.
    picker_dir : String,
    /// The last COMMITTED search -- the query `n`/`N` repeat. On the state
    /// rather than in `Mode.search` because it outlives the mode: `/foo`,
    /// Enter, Escape, and `n` still means "the next foo".
    search_query : String,
    /// Which way the last search ran, so `n` repeats it and `N` reverses it.
    /// `true` is forward (towards the buffer's end), the default a fresh `/`
    /// sets -- the same `n`/`N` rule every modal editor keeps.
    search_forward : Bool
}

/// The one `EditorState` constructor (the plan's two-host struct-literal
/// risk: a literal that omits a field checks clean and reads garbage at
/// runtime, so the field list lives in exactly one place). One document,
/// normal mode, a bare cursor, the default bindings.
pub def EditorState.init (doc : Document) (rows : I64) (cols : I64) : EditorState :=
    let docs : List Document := List.cons doc List.empty in
    { docs := docs,
        active := 0,
        mode := Mode.normal,
        pending := List.empty,
        bindings := Keymap.default_bindings,
        status := "",
        scroll := 0,
        hscroll := 0,
        rows := rows,
        cols := cols,
        registers := List.empty,
        picker_files := List.empty,
        picker_dir := "",
        search_query := "",
        search_forward := true }

/// The active document, or none when the state holds no buffer (the
/// editor always has one; the `Option` keeps the accessor total).
pub def EditorState.active_doc (st : EditorState) : Option Document :=
    match st {
        { docs, active, .. } => ply_nth_doc docs active
    }

#[terminating]
def ply_nth_doc (docs : List Document) (i : I64) : Option Document :=
    match docs {
        List.empty => Option.none,
        List.cons one rest =>
            if I64.beq i 0 then Option.some one else ply_nth_doc rest (i - 1)
    }

/// The state with its active document replaced, for the update's edit
/// path. The one place a doc swap happens, so the docs list is rebuilt
/// here and nowhere else.
pub def EditorState.with_active_doc (st : EditorState) (doc : Document) : EditorState :=
    // Field reads go through the accessors, not a record pattern: a
    // `{ field, .. }` pattern on this struct is a self-hosted checker
    // failure (the same class the toolkit tests record for `#[test]`
    // defs), and the accessors exist anyway.
    let shared : Shared EditorState := Shared.of st in
    let docs : List Document := EditorState.docs_of (Shared.get shared) in
    let active : I64 := EditorState.active_of (Shared.get shared) in
    ply_state_with_docs (Shared.get shared) (ply_replace_doc docs active doc)

/// The update-base bind: the record update's base is a local here, not a
/// call expression.
def ply_state_with_docs (st : EditorState) (docs : List Document) : EditorState :=
    { st with docs := docs }

/// The docs field, read once.
pub def EditorState.docs_of (st : EditorState) : List Document :=
    match st { { docs, .. } => docs }

/// The active field, read once.
pub def EditorState.active_of (st : EditorState) : I64 :=
    match st { { active, .. } => active }

#[terminating]
def ply_replace_doc (docs : List Document) (i : I64) (doc : Document) : List Document :=
    match docs {
        List.empty => List.cons doc List.empty,
        List.cons one rest =>
            if I64.beq i 0
            then List.cons doc rest
            else List.cons one (ply_replace_doc rest (i - 1) doc)
    }

/// How many buffers are open. The buffer list's arithmetic
/// (`:bn`/`:bp`) wraps with this.
#[terminating]
pub def EditorState.doc_count (st : EditorState) : I64 :=
    ply_doc_count_go (EditorState.docs_of st)

#[terminating]
def ply_doc_count_go (docs : List Document) : I64 :=
    match docs {
        List.empty => 0,
        List.cons _ rest => 1 + ply_doc_count_go rest
    }

/// The state focused on buffer `i`, clamped into `[0, doc_count)`. The one
/// place `active` moves, so `:bn`/`:bp`/`:e` cannot disagree about which
/// buffer is focused.
pub def EditorState.with_active (st : EditorState) (i : I64) : EditorState :=
    let count : I64 := EditorState.doc_count st in
    let bounded : I64 := if i < 0 then 0 else if Bool.not (i < count) then count - 1 else i in
    { st with active := bounded }

/// The index of the buffer whose path is `path`, or `none` when no open
/// buffer came from there. `:e` uses it to FOCUS rather than re-read: opening
/// the same file twice would give two buffers whose saves overwrite each
/// other, which is the one thing a multi-buffer editor must not do.
#[terminating]
pub def EditorState.index_of_path (st : EditorState) (path : String) : Option I64 :=
    ply_index_of_path (EditorState.docs_of st) path 0

#[terminating]
def ply_index_of_path (docs : List Document) (path : String) (i : I64) : Option I64 :=
    match docs {
        List.empty => Option.none,
        List.cons one rest =>
            if Document.has_path one path
            then Option.some i
            else ply_index_of_path rest path (i + 1)
    }

/// The state with a buffer appended at the end. The new buffer is NOT
/// focused -- the caller decides, because `:e` focuses and a future split
/// view would not.
pub def EditorState.with_doc_added (st : EditorState) (doc : Document) : EditorState :=
    let shared : Shared EditorState := Shared.of st in
    ply_state_with_docs (Shared.get shared)
        (List.append (EditorState.docs_of (Shared.get shared)) (List.cons doc List.empty))

/// The state with its whole buffer list replaced -- the one swap, for a
/// consumer that builds the list itself (a session restore).
pub def EditorState.with_docs (st : EditorState) (docs : List Document) : EditorState :=
    { st with docs := docs }

/// The state with the mode set and the pending prefix cleared -- the
/// common end of every mode-switching command.
pub def EditorState.with_mode (st : EditorState) (m : Mode) : EditorState :=
    { st with mode := m, pending := List.empty }

/// The state with a status line, for the commands that report.
pub def EditorState.with_status (st : EditorState) (msg : String) : EditorState :=
    { st with status := msg }

/// The mode field, read once.
pub def EditorState.mode_of (st : EditorState) : Mode :=
    match st { { mode, .. } => mode }

/// The command line `Mode.command` carries: the text between the `:` and the
/// cursor. `""` in every other mode, so a caller need not match the mode to
/// ask the question -- the same totality `EditorState.scroll_of` has.
///
/// THE LINE LIVES IN THE MODE, not in a field of its own. `Mode.command` was
/// declared with a `line` payload in Phase 1 for exactly this: a second field
/// would be a second truth about whether the editor is on a command line, and
/// `Mode`'s payload already answers that. `EditorState.with_mode` clears the
/// pending chord, which command mode has none of anyway.
pub def EditorState.cmd_line_of (st : EditorState) : String :=
    match EditorState.mode_of st {
        Mode.command line => line,
        _ => ""
    }

/// The search line `Mode.search` carries: the query as typed. `""` in every
/// other mode -- the total reading `cmd_line_of` states. NOTE the difference
/// from `search_query_of`: this is the line being typed, that is the query
/// `n`/`N` repeat.
pub def EditorState.search_line_of (st : EditorState) : String :=
    match EditorState.mode_of st {
        Mode.search query => query,
        _ => ""
    }

/// The picker's filter as typed -- `""` in every other mode.
pub def EditorState.picker_query_of (st : EditorState) : String :=
    match EditorState.mode_of st {
        Mode.picker query _ => query,
        _ => ""
    }

/// The picker's highlighted row -- `0` in every other mode.
pub def EditorState.picker_selected_of (st : EditorState) : I64 :=
    match EditorState.mode_of st {
        Mode.picker _ sel => sel,
        _ => 0
    }

/// The picker's candidates, relative to `picker_dir`.
pub def EditorState.picker_files_of (st : EditorState) : List String :=
    match st { { picker_files, .. } => picker_files }

/// The directory the picker's candidates are relative to (`""` is the cwd).
pub def EditorState.picker_dir_of (st : EditorState) : String :=
    match st { { picker_dir, .. } => picker_dir }

/// The state with the picker's listing set: the fold of
/// `EditorMsg.picker_files`. Both halves move in one def so a listing and the
/// directory it names cannot come from different reads.
pub def EditorState.with_picker_files (st : EditorState) (dir : String) (files : List String)
    : EditorState :=
    { st with picker_files := files, picker_dir := dir }

/// The last committed search, read once.
pub def EditorState.search_query_of (st : EditorState) : String :=
    match st { { search_query, .. } => search_query }

/// The last search's direction: `true` forward.
pub def EditorState.search_forward_of (st : EditorState) : Bool :=
    match st { { search_forward, .. } => search_forward }

/// The state with the committed search -- what Enter on the `/` line does.
/// The query and its direction move together: a search that ran one way and
/// remembered another would make `n` repeat the wrong search.
pub def EditorState.with_search (st : EditorState) (query : String) (forward : Bool)
    : EditorState :=
    { st with search_query := query, search_forward := forward }

/// The pending key prefix, read once.
pub def EditorState.pending_of (st : EditorState) : List Key :=
    match st { { pending, .. } => pending }

/// The state with the pending prefix set.
pub def EditorState.with_pending (st : EditorState) (keys : List Key) : EditorState :=
    { st with pending := keys }

/// The binding tables, read once.
pub def EditorState.bindings_of (st : EditorState) : List Binding :=
    match st { { bindings, .. } => bindings }

/// The state with a binding table -- what a `ply.toml` layer produces, and the
/// one place a table swap happens, so `bindings` is rebuilt here and nowhere
/// else (the same rule `with_active_doc` states for `docs`).
///
/// THE TABLE IS THE WHOLE TABLE, not a delta: the caller composes the layers
/// (`Config.bindings_of_all` with the defaults first), because the keymap's
/// LAST-match rule is what makes a later row win and this module has no
/// business re-deciding it.
pub def EditorState.with_bindings (st : EditorState) (bs : List Binding) : EditorState :=
    { st with bindings := bs }

/// The yank registers, read once.
pub def EditorState.registers_of (st : EditorState) : List String :=
    match st { { registers, .. } => registers }

/// The state with the registers set.
pub def EditorState.with_registers (st : EditorState) (regs : List String) : EditorState :=
    { st with registers := regs }

/// The document with its selections replaced -- the builder a view-side
/// caller (a test's hand-set selection, a future mouse drag) wants, and
/// the one `commands.mo`'s private `doc_with_selections` duplicated. An
/// edit still goes through `transaction.mo`'s apply (which commits a
/// revision); this is the selection-only swap, so no history moves.
pub def Document.with_selections (doc : Document) (sel : Selections) : Document :=
    { doc with selections := sel }

/// The state with the scroll set. The view CLAMPS it around the primary
/// head's line (`View.first_visible`), so a caller can hand it anything
/// -- the stored value is the baseline, the clamp is the guarantee.
pub def EditorState.with_scroll (st : EditorState) (line : I64) : EditorState :=
    { st with scroll := line }

/// The scroll field, read once. The view CLAMPS it (a cursor below the
/// window pulls it down, one above pulls it up) rather than trusting the
/// stored value: a resize or a jump can leave `scroll` naming a window
/// the cursor is not in, and the view is where the geometry lives.
pub def EditorState.scroll_of (st : EditorState) : I64 :=
    match st { { scroll, .. } => scroll }

/// The state with the horizontal scroll set. Like `with_scroll`, the view
/// CLAMPS it around the primary head's column (`View.left_col`), so the
/// stored value is a baseline and the clamp is the guarantee -- a horizontal
/// scroll command can hand it anything, and the caret stays on screen.
pub def EditorState.with_hscroll (st : EditorState) (col : I64) : EditorState :=
    { st with hscroll := col }

/// The horizontal scroll field, read once. A negative stored value is
/// clamped to 0 by the reader: there is no text left of column 0.
pub def EditorState.hscroll_of (st : EditorState) : I64 :=
    match st { { hscroll, .. } => hscroll }

/// The rows field, read once.
pub def EditorState.rows_of (st : EditorState) : I64 :=
    match st { { rows, .. } => rows }

/// The cols field, read once.
pub def EditorState.cols_of (st : EditorState) : I64 :=
    match st { { cols, .. } => cols }

/// The status field, read once.
pub def EditorState.status_of (st : EditorState) : String :=
    match st { { status, .. } => status }

/// `EditorState` is a pure data record over persistent structures, so a
/// duplicate of the VALUE is the correct duplicate -- the same reading
/// `Copy Rope` records (`rope.mo`), and the same reason `Selection`/
/// `Change` carry instances (`instances.mo`). The list fields are rebuilt
/// rather than shared: `init/src/copy.mo`'s absent list is about the
/// cells a mutation could alias, and nothing here mutates, but the
/// honest duplicate still walks them.
///
/// The update reads the state several times per keystroke (mode, pending,
/// bindings, the doc itself), which the affine rule would otherwise make
/// a `Shared` share at every read site; the instance licenses the reads
/// instead, which is what it is for.
pub instance Copy EditorState {
    def copy (st : EditorState) : Pair EditorState EditorState :=
        match st {
            { docs, active, mode, pending, bindings, status, scroll, hscroll, rows, cols, registers,
                picker_files, picker_dir, search_query, search_forward } =>
                let one : EditorState :=
                    { docs := copy_list docs, active := active, mode := mode,
                        pending := copy_list pending, bindings := copy_list bindings,
                        status := status, scroll := scroll, hscroll := hscroll, rows := rows, cols := cols,
                        registers := copy_list registers, picker_files := copy_list picker_files,
                        picker_dir := picker_dir, search_query := search_query,
                        search_forward := search_forward } in
                let two : EditorState :=
                    { docs := copy_list docs, active := active, mode := mode,
                        pending := copy_list pending, bindings := copy_list bindings,
                        status := status, scroll := scroll, hscroll := hscroll, rows := rows, cols := cols,
                        registers := copy_list registers, picker_files := copy_list picker_files,
                        picker_dir := picker_dir, search_query := search_query,
                        search_forward := search_forward } in
                Pair.pair one two
        }
}

/// Field-wise list copy, so a duplicated state owns its own list cells.
#[terminating]
def copy_list {A : Type} (xs : List A) : List A :=
    match xs {
        List.empty => List.empty,
        List.cons one rest => List.cons one (copy_list rest)
    }
