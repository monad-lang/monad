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

use lib::types {Rope, Selections, History}
use lib::rope {Rope.of_string}
use lib::history {History.empty, History.commit}
use lib::selection {Selections.cursor}

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
