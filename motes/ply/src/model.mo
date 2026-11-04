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
use lib::rope {Rope.of_string}
use lib::history {History.empty, History.commit}
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
/// One constructor for every `Document` in the program (the plan's
/// two-host struct-literal risk names why: a struct literal that omits a
/// field checks clean on both hosts and reads garbage at runtime, so the
/// field list lives in exactly one place).
pub def Document.of_text (text : String) : Document :=
    let rope : Rope := Rope.of_string text in
    match History.commit History.empty rope (Selections.cursor 0) List.empty 0 {
        Pair.pair seeded _ =>
            { path := Option.none,
              rope := rope,
              selections := Selections.cursor 0,
              history := seeded,
              language := "text",
              version := 0 }
    }

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
    lsp_frame (body : String)
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
    /// Terminal geometry, kept in step by `EditorMsg.resize`.
    rows : I64,
    cols : I64,
    /// The yank/paste registers (the internal-register Known Limitation).
    /// The head is the most recent yank; `p` pastes it.
    registers : List String
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
      rows := rows,
      cols := cols,
      registers := List.empty }

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

/// The pending key prefix, read once.
pub def EditorState.pending_of (st : EditorState) : List Key :=
    match st { { pending, .. } => pending }

/// The state with the pending prefix set.
pub def EditorState.with_pending (st : EditorState) (keys : List Key) : EditorState :=
    { st with pending := keys }

/// The binding tables, read once.
pub def EditorState.bindings_of (st : EditorState) : List Binding :=
    match st { { bindings, .. } => bindings }

/// The yank registers, read once.
pub def EditorState.registers_of (st : EditorState) : List String :=
    match st { { registers, .. } => registers }

/// The state with the registers set.
pub def EditorState.with_registers (st : EditorState) (regs : List String) : EditorState :=
    { st with registers := regs }

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
            { docs, active, mode, pending, bindings, status, scroll, rows, cols, registers } =>
                let one : EditorState :=
                    { docs := copy_list docs, active := active, mode := mode,
                      pending := copy_list pending, bindings := copy_list bindings,
                      status := status, scroll := scroll, rows := rows, cols := cols,
                      registers := copy_list registers } in
                let two : EditorState :=
                    { docs := copy_list docs, active := active, mode := mode,
                      pending := copy_list pending, bindings := copy_list bindings,
                      status := status, scroll := scroll, rows := rows, cols := cols,
                      registers := copy_list registers } in
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
