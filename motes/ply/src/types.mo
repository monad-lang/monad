// Ply's core value types -- declarations only.
//
// This file holds no function bodies on purpose. Expanding a `#[derive]`
// re-checks the whole derive-bearing file (plus its use-closure) in the
// Rust host's meta-capture path, and that path loses def-signature expected
// types: a file mixing derives with ordinary defs fails it on every struct
// literal and dot access (`cannot infer the type of { .. }`). Keeping the
// derives alone here is load-bearing. See `motes/tui/src/types.mo`, which
// records the same rule, and the `types.mo`/`rope.mo` split the plan calls
// for.
//
// Everything below is the plan's Design §1 verbatim, plus the one import
// the derive backend needs.

use std::map {BTreeMap}
// The derive backend. The compiler's unused-import analysis does not see
// macro-name dispatch as a reference, so this reads as unused -- it is not;
// removing it makes `#[derive BEq]` below fail with
// "macro `derive_beq` not found".
use std::derive {derive_beq}

/// A persistent rope over UTF-8 text. Every offset is a BYTE offset.
pub type Rope {
    leaf (text : String),
    node (left : Rope) (right : Rope) (bytes : I64) (newlines : I64) (depth : I64)
}

/// One selection: `anchor` is where it started, `head` is where the
/// cursor is. A bare cursor is `anchor == head`.
#[derive BEq]
pub struct Selection {
    anchor : I64,
    head : I64
}

/// Every selection in a view, plus which one is primary.
pub struct Selections {
    ranges : List Selection,
    primary : I64
}

/// One replacement: bytes `[start, stop)` of the OLD text become `text`.
#[derive BEq]
pub struct Change {
    start : I64,
    stop : I64,
    text : String
}

/// One node of the undo tree. `rope` is the full text AFTER `changes`.
pub struct Revision {
    parent : I64,
    rope : Rope,
    selections : Selections,
    changes : List Change,
    time_ms : I64
}

pub struct History {
    revisions : BTreeMap I64 Revision,
    current : I64,
    next_id : I64,
    saved : I64
}

#[derive BEq]
pub type Mode {
    normal,
    insert,
    select,
    /// `:` command line. The payload is the text typed so far -- and it is
    /// the WHOLE truth about the line, so leaving the mode throws it away
    /// with no cleanup pass (`EditorState.cmd_line_of` reads it).
    command (line : String),
    /// `/` search. The payload is the QUERY typed so far, by exactly the
    /// rule `command` follows. The COMMITTED query (what `n`/`N` repeat) is
    /// NOT here: it lives on the state, because it outlives the mode -- you
    /// leave search mode and `n` still repeats the last search.
    search (query : String),
    /// The `Space f` file picker. The payload is the FILTER typed so far
    /// plus the highlighted row. The candidate LIST is deliberately NOT
    /// here: it arrives from `IO.list_dir` as a message
    /// (`EditorMsg.picker_files`) and lives on the state, because a mode is
    /// a value the update rebuilds per keystroke and a few thousand path
    /// strings do not belong in one. The scroll OFFSET is not here either --
    /// the view derives it from `selected` and the window height, the way
    /// `View.first_visible` derives the text area's.
    picker (query : String) (selected : I64)
}
