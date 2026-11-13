// The ply mote's library root -- bare `use ply` resolves here.
//
// The pure core is complete as of Phase 1: the value types (types.mo), the
// rope (rope.mo), selections (selection.mo), the undo history (history.mo),
// a document (model.mo) and the transaction that edits one
// (transaction.mo). Later phases add the modules that drive these -- the
// keymap, commands, view, the `ply.toml` config, `/` search, the file picker,
// the LSP client and the MCP server -- and re-export them here the same way,
// so a consumer (Weaver's approval diff, a future `monad-shell` line editor)
// gets the whole reusable core through this one import.
//
// No `{*}` globs -- the `motes/json/src/lib.mo` doctrine.

pub use lib::types {Rope, Selection, Selections, Change, Revision, History, Mode}
pub use lib::rope {Rope.of_string, Rope.to_string}
pub use lib::selection {Selections.cursor}
pub use lib::model {Document, Document.of_text, Document.with_language,
    Document.with_path, Document.of_file, Document.language_for_path,
    Document.text_of, Document.path_of, Document.dirty, Document.mark_saved,
    EditorState, EditorState.init, EditorState.hscroll_of,
    EditorState.with_hscroll, EditorState.cmd_line_of, EditorState.search_line_of,
    EditorState.picker_query_of, EditorState.picker_files_of,
    EditorState.search_query_of, EditorState.search_forward_of,
    EditorState.doc_count, EditorState.with_active, EditorState.with_bindings,
    EditorMsg, Command, on_event}
pub use lib::keymap {KeyResult, Binding, Keymap.resolve, Keymap.default_bindings}
pub use lib::commands {update, parse_command, parse_open, Registry.default,
    Registry.lookup}
pub use lib::config {Config, Config.empty, Config.parse, Config.merge,
    Config.bindings_of_all, Config.problems_of_all, Config.parse_key_spec}
pub use lib::search {Search.find_from, Search.last_before, Search.next_match,
    Search.selection_at, Search.line_number_of}
pub use lib::picker {Picker.rank, Picker.score, Picker.tier_name_prefix,
    Picker.tier_path_prefix, Picker.tier_contains, Picker.tier_subsequence,
    Picker.window_offset, Picker.clamp_selected, Picker.take_from, Picker.nth,
    Picker.resolve}
pub use lib::highlight {LanguageConfig, Token, TokenKind, Highlight.lex,
    Highlight.style, Highlight.segments, Highlight.config_for}
pub use lib::view {RowView, View.view, View.rows, View.row_segments, View.left_col,
    View.status_segments, View.first_visible}
