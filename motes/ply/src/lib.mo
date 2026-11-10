// The ply mote's library root -- bare `use ply` resolves here.
//
// The pure core is complete as of Phase 1: the value types (types.mo), the
// rope (rope.mo), selections (selection.mo), the undo history (history.mo),
// a document (model.mo) and the transaction that edits one
// (transaction.mo). Later phases add the modules that drive these -- the
// keymap, commands, view, LSP client and MCP server -- and re-export them
// here the same way, so a consumer (Weaver's approval diff, a future
// `monad-shell` line editor) gets the whole reusable core through this one
// import.
//
// No `{*}` globs -- the `motes/json/src/lib.mo` doctrine.

pub use lib::types {Rope, Selection, Selections, Change, Revision, History, Mode}
pub use lib::rope {Rope.of_string}
pub use lib::selection {Selections.cursor}
pub use lib::model {Document, Document.of_text, EditorState, EditorMsg, Command, on_event}
pub use lib::keymap {KeyResult, Binding, Keymap.resolve, Keymap.default_bindings}
pub use lib::commands {update, Registry.default}
pub use lib::highlight {LanguageConfig, Token, TokenKind, Highlight.lex,
    Highlight.style, Highlight.segments, Highlight.config_for}
pub use lib::view {RowView, View.view, View.rows, View.row_segments,
    View.status_segments, View.first_visible}
