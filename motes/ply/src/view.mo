// Ply's view: `EditorState -> Widget`, composed from tui's components
// (code-editor.md Phase 3).
//
// THE VIEW BUILDS NO NEW RENDERING MACHINERY. Every visual is an existing
// tui piece: `Widget.column` + `sized` split the screen into the text
// area and the status line, `Widget.row` splits each visible row into
// the gutter and the text, `label` paints the gutter, the `spans` leaf
// paints the styled text, and `Text.slice_spans` cuts a row's segments
// around a highlighted span. The view's own work is GEOMETRY (which
// lines are visible, where each selection lands on each row) and
// COMPOSITION (which style merges onto which segment) -- the same
// split `motes/weaver`'s rows/pane components draw.
//
// SELECTIONS ARE BACKGROUNDS, NOT REVERSE VIDEO: a selection merges a
// `bg` color into the covered cells' styles, so a selected keyword
// stays bold blue ON TOP of the selection background -- the two layers
// compose instead of one erasing the other. Only the PRIMARY HEAD is
// reverse video (the caret's unmissable block, the same visual tui's
// `text_input` cursor uses), and it merges the same way, onto whatever
// style the cell already carries.
//
// BYTE OFFSETS BECOME CELLS AT THIS EDGE AND NOWHERE ELSE (the plan's
// Decision 2): the document and its selections speak bytes, the screen
// speaks cells, and `Text.col_of_byte` is the one bridge. A selection
// covering half a multi-byte glyph snaps to the glyph's start cell --
// a selection never splits a character, the same rule `Text.snap_span`
// states for weaver's mouse selections.
//
// NO LOCAL IS NAMED `insert`/`select`/`prefix`/`tick`: whole-program
// constructor names that shadow same-named locals are the plan's named
// risk. The selections are therefore always spelled in full.
//
// NO `#[derive]` HERE: this file holds function bodies, and a
// derive-bearing file must hold none (`motes/tui/src/types.mo`'s rule).

use init::shared {Shared}
use lib::types {Rope, Selection, Selections, Mode}
use lib::rope {Rope.line_start, Rope.line_of, Rope.line_content_end,
    Rope.end_offset, Rope.newlines, Rope.slice}
use lib::selection {Selection.start, Selection.stop, Selections.primary_sel}
use lib::model {Document, EditorState,
    EditorState.active_doc, EditorState.scroll_of, EditorState.rows_of,
    EditorState.cols_of, EditorState.status_of, EditorState.mode_of,
    EditorState.pending_of, EditorState.hscroll_of, EditorState.picker_files_of,
    EditorState.picker_query_of, EditorState.picker_selected_of}
use lib::picker {Picker.rank, Picker.window_offset, Picker.clamp_selected,
    Picker.take_from}
use lib::keymap {Keymap.mode_table}
use lib::highlight {Highlight.config_for, Highlight.lex, Highlight.segments}
use tui::types {LayoutSize, TextStyle, TextSegment, Key}
use tui::core {style_default, style_merge, mk_text_segment, clamp}
use tui::widget {Widget, SizedWidget, label, spans, sized, with_style}
use tui::text {Text.width, Text.col_of_byte, Text.slice_spans, Text.width_spans,
    Text.snap_span}
use std::ansi {Color}

// ── Geometry ───────────────────────────────────────────────────────────────

/// The status line's height: one row, always.
pub def View.status_height : I64 := 1

/// The gutter's width in cells: line numbers right-aligned in four
/// cells plus one separating space. Five admits files to 9999 lines
/// without the gutter growing mid-session; a larger file keeps the
/// last four digits, which is what every terminal editor does past
/// the fixed field anyway.
pub def View.gutter_width : I64 := 5

/// The text area's height: the terminal's rows less the status line.
/// A terminal too short for both answers 0, and the view paints no
/// rows -- `layout_column`'s clamping makes that safe rather than
/// something to defend against here.
pub def View.text_height (rows : I64) : I64 :=
    if rows < View.status_height + 1 then 0 else rows - View.status_height

/// The text area's width: the terminal's columns less the gutter.
pub def View.text_width (cols : I64) : I64 :=
    if cols < View.gutter_width + 1 then 0 else cols - View.gutter_width

/// The first visible line, from the stored scroll CLAMPED to keep the
/// primary head's line on screen: a head below the window pulls the
/// window down to it, a head above pulls it up. The stored value is
/// the baseline (a future scroll command sets it); the clamp is the
/// guarantee that the caret is never off-screen, which is the whole
/// reason the view computes this rather than trusting `scroll`.
pub def View.first_visible (st : EditorState) : I64 :=
    match EditorState.active_doc st {
        Option.some doc => ply_first_visible st doc,
        Option.none => EditorState.scroll_of st
    }

/// The clamped first line for a known document. The head's line is
/// the anchor; the stored scroll is only a starting point.
def ply_first_visible (st : EditorState) (doc : Document) : I64 :=
    let height : I64 := View.text_height (EditorState.rows_of st) in
    if height < 1
    then 0
    else
        let shared : Shared Document := Shared.of doc in
        let rope : Rope := ply_doc_rope (Shared.get shared) in
        let head_line : I64 := Rope.line_of rope (ply_primary_head (Shared.get shared)) in
        let stored : I64 := EditorState.scroll_of st in
        if head_line < stored
        then head_line
        else if stored + height < head_line + 1
        then head_line - height + 1
        else stored

/// The first visible COLUMN of the text area -- the horizontal half of
/// `View.first_visible`, and the same shape: `hscroll` is the baseline and
/// the clamp is the guarantee that the caret is never painted past the
/// right margin.
///
/// THIS IS THE WHOLE OF HORIZONTAL SCROLLING. A line is not wrapped (that
/// is a later change, and it reflows rows besides), so a line longer than
/// the text area is CLIPPED at the margin. Without a window the caret
/// simply stops being painted once its column passes `text_width` -- the
/// head is real and the status line counts it, but the terminal shows no
/// caret at all. Moving the window instead is the fix.
///
/// The two clamps mirror the vertical pair exactly (a head left of the
/// window pulls it left, one right of it pulls it right, otherwise the
/// stored value holds), so the behaviour a reader already knows from
/// scrolling lines applies unchanged to columns.
///
/// A text area of width 0 has no cell to show, so the answer is the stored
/// value clamped at 0 -- never a negative column.
pub def View.left_col (st : EditorState) : I64 :=
    match EditorState.active_doc st {
        Option.some doc => ply_left_col st doc,
        Option.none => ply_non_negative (EditorState.hscroll_of st)
    }

/// The clamped first column for a known document.
def ply_left_col (st : EditorState) (doc : Document) : I64 :=
    let width : I64 := View.text_width (EditorState.cols_of st) in
    let stored : I64 := ply_non_negative (EditorState.hscroll_of st) in
    if width < 1
    then stored
    else
        let shared : Shared Document := Shared.of doc in
        let caret : I64 := ply_caret_col (Shared.get shared) in
        if caret < stored
        then caret
        else if Bool.not (caret < stored + width)
        then caret - width + 1
        else stored

/// The primary head's display COLUMN on its own line -- the coordinate the
/// horizontal clamp is stated in. Bytes become cells here, the same
/// `Text.col_of_byte` bridge every other geometry in this file uses.
def ply_caret_col (doc : Document) : I64 :=
    let shared : Shared Document := Shared.of doc in
    let rope : Rope := ply_doc_rope (Shared.get shared) in
    let head : I64 := ply_primary_head (Shared.get shared) in
    let line : I64 := Rope.line_of rope head in
    let ls : I64 := Rope.line_start rope line in
    let text : String := Rope.slice rope ls (Rope.line_content_end rope line - ls) in
    Text.col_of_byte text (head - ls)

/// A column never goes below 0: a stored `hscroll` of -5 and a head at 0
/// both mean "the window starts at the first cell".
def ply_non_negative (n : I64) : I64 := if n < 0 then 0 else n

/// The horizontal window for a row's segments: `(lo, hi)` in cells. `lo` is
/// floored to a character boundary so a wide glyph straddling the left edge
/// is shown whole rather than cut in half (the rule `Text.drop_cols`
/// states); `hi` is one text area past it.
def ply_window (text : String) (left : I64) (width : I64) : Pair I64 I64 :=
    let lo : I64 := ply_snap_left text left in
    let hi : I64 := left + width in
    Pair.pair lo (if lo < hi then hi else lo)

/// The left edge floored to the glyph start it lands in: `Text.snap_span`
/// floors a column to a glyph start, which is exactly the question here.
def ply_snap_left (text : String) (left : I64) : I64 :=
    if left < 1
    then 0
    else
        match Text.snap_span text left left {
            Pair.pair lo _ => ply_non_negative lo
        }

/// The document's rope, read once.
def ply_doc_rope (doc : Document) : Rope :=
    match doc { { rope, .. } => rope }

/// The document's selections, read once.
def ply_doc_sel (doc : Document) : Selections :=
    match doc { { selections, .. } => selections }

/// The document's language name, read once.
def ply_doc_lang (doc : Document) : String :=
    match doc { { language, .. } => language }

/// The primary head offset, or 0 when there is no primary selection
/// (the editor always has one; the 0 keeps the geometry total).
def ply_primary_head (doc : Document) : I64 :=
    match Selections.primary_sel (ply_doc_sel doc) {
        Option.some s => s.head,
        Option.none => 0
    }

// ── Rows: the text area's content ──────────────────────────────────────────

/// One visible row's worth of data: the line's number, its content
/// (no terminator), and the document-relative byte offsets the content
/// spans. The view computes this once per row and both the gutter and
/// the text paint from it.
pub struct RowView {
    /// The line's index (0-based), for the gutter.
    line : I64,
    /// The line's content, terminator excluded.
    text : String,
    /// The content's first byte, document-relative.
    start : I64,
    /// One past the content's last byte, document-relative.
    stop : I64
}

/// `RowView` is a small immutable record of `I64`s and a `String`, read
/// several times per row (the selection cut reads `start` and `text`,
/// the caret cut reads them again) -- the same shape and the same
/// reasoning as `Copy Rope` (`rope.mo`) and `Copy EditorState`
/// (`model.mo`): a duplicate of the VALUE is the correct duplicate, and
/// the instance licenses the reads instead of a `Shared` share at each
/// one.
pub instance Copy RowView {
    def copy (r : RowView) : Pair RowView RowView :=
        match r {
            { line, text, start, stop } =>
                let one : RowView := { line := line, text := text, start := start, stop := stop } in
                let two : RowView := { line := line, text := text, start := start, stop := stop } in
                Pair.pair one two
        }
}

/// The row's line index, read once -- the accessor shape `model.mo`'s
/// `*_of` defs set, so a consumer never needs a record pattern.
pub def RowView.line_of (r : RowView) : I64 :=
    match r { { line, .. } => line }

/// The row's text, read once.
pub def RowView.text_of (r : RowView) : String :=
    match r { { text, .. } => text }

/// The row's first byte, read once.
pub def RowView.start_of (r : RowView) : I64 :=
    match r { { start, .. } => start }

/// One past the row's last byte, read once.
pub def RowView.stop_of (r : RowView) : I64 :=
    match r { { stop, .. } => stop }

/// The rows `height` tall starting at `first`: the visible window of
/// the document. A window reaching past the last line answers fewer
/// rows, and the renderer paints the unused area rows as background --
/// an `empty_screen` starts blank.
#[partial]
pub def View.rows (doc : Document) (first : I64) (height : I64) : List RowView :=
    ply_rows_go doc first height List.empty

#[partial]
def ply_rows_go (doc : Document) (line : I64) (left : I64) (acc : List RowView)
    : List RowView :=
    if left < 1
    then List.reverse acc
    else
        // The document is read twice per row (existence, then the row
        // itself) and holds a `History` (deliberately not `Copy`), so
        // the loop shares one handle -- the affine rule's own remedy.
        let shared : Shared Document := Shared.of doc in
        if Bool.not (ply_line_exists (Shared.get shared) line)
        then List.reverse acc
        else
            let row : RowView := ply_row_of (Shared.get shared) line in
            ply_rows_go (Shared.get shared) (line + 1) (left - 1) (List.cons row acc)

/// Does line `line` exist? A rope with N newlines has lines `0..N`
/// (the newline COUNT is the line index of the last line), so the test
/// is one comparison against the cached total -- no walk.
def ply_line_exists (doc : Document) (line : I64) : Bool :=
    Bool.and (Bool.not (line < 0)) (line < Rope.newlines (ply_doc_rope doc) + 1)

/// One row's data for an existing line.
def ply_row_of (doc : Document) (line : I64) : RowView :=
    let rope : Rope := ply_doc_rope doc in
    let start : I64 := Rope.line_start rope line in
    let stop : I64 := Rope.line_content_end rope line in
    { line := line,
        text := Rope.slice rope start (stop - start),
        start := start,
        stop := stop }

// ── The styled text of one row ─────────────────────────────────────────────

/// The row's segments: the highlighter's base layer, with every
/// selection's background merged onto the covered cells and the
/// primary head's cell reversed.
///
/// THE ORDER IS THE LAYERING: highlight first (the palette), selection
/// backgrounds second (they merge INTO the palette, so a selected
/// keyword keeps its blue foreground under the selection bg), the
/// primary head last (it merges onto whatever the cell already
/// carries, palette or palette+selection).
pub def View.row_segments (doc : Document) (row : RowView) : List TextSegment :=
    let shared : Shared Document := Shared.of doc in
    let base : List TextSegment :=
        Highlight.segments
            (Highlight.lex (Highlight.config_for (ply_doc_lang (Shared.get shared))) row.text) in
    let selected : List TextSegment :=
        ply_merge_selections (ply_doc_sel (Shared.get shared)) row base in
    ply_reverse_primary_head (ply_doc_sel (Shared.get shared)) row selected

/// Merge every selection's background onto the row's segments. A
/// selection may cover any part of any row; the ones that touch THIS
/// row contribute a bg-styled span, the others contribute nothing.
#[partial]
def ply_merge_selections (sel : Selections) (row : RowView) (segs : List TextSegment)
    : List TextSegment :=
    match sel {
        { ranges, .. } => ply_merge_ranges ranges row segs
    }

/// Fold the ranges over the segments: each range that intersects the
/// row re-styles the covered cells, in range order. Later ranges see
/// the earlier ranges' work, which is correct -- two selections on
/// one row are disjoint by construction (the transaction's overlap
/// check), so at most one range styles any cell.
#[partial]
def ply_merge_ranges (ranges : List Selection) (row : RowView) (segs : List TextSegment)
    : List TextSegment :=
    match ranges {
        List.empty => segs,
        List.cons one rest =>
            ply_merge_ranges rest row (ply_merge_one one row segs)
    }

/// One selection's contribution to one row. The selection's byte span
/// `[lo, hi)` intersects the row's `[start, stop)` -- or it does not,
/// and the row keeps its styles. A BARE CURSOR (`lo == hi`) never
/// intersects: its whole visual is the caret, painted later.
def ply_merge_one (sel : Selection) (row : RowView) (segs : List TextSegment)
    : List TextSegment :=
    let lo : I64 := Selection.start sel in
    let hi : I64 := Selection.stop sel in
    if Bool.not (lo < row.stop)
    then segs
    else if Bool.not (row.start < hi)
    then segs
    else ply_merge_hit lo hi row segs

/// The intersecting case: the covered CELL span, then the merge. The
/// cut is byte-to-cell (`Text.col_of_byte`), clamped to the row -- a
/// selection beginning before the row covers from cell 0, one ending
/// past it covers through the last cell.
def ply_merge_hit (lo : I64) (hi : I64) (row : RowView) (segs : List TextSegment)
    : List TextSegment :=
    let total : I64 := Text.width row.text in
    let c0 : I64 := clamp (Text.col_of_byte row.text (lo - row.start)) 0 total in
    let c1 : I64 := clamp (Text.col_of_byte row.text (hi - row.start)) 0 total in
    if Bool.not (c0 < c1)
    then segs
    else
        // The segment list is cut three times (head, mid, tail), so it
        // is shared -- a `List` is deliberately not `Copy`
        // (`init/src/copy.mo`'s absent list), and the share is the
        // explicit remedy.
        let shared : Shared (List TextSegment) := Shared.of segs in
        let head : List TextSegment := Text.slice_spans (Shared.get shared) 0 c0 in
        let mid : List TextSegment :=
            ply_map_bg (Text.slice_spans (Shared.get shared) c0 c1) in
        let tail : List TextSegment :=
            Text.slice_spans (Shared.get shared) c1 (Text.width_spans (Shared.get shared)) in
        ply_join3 head mid tail

/// The selection background's style: a blue that keeps a black
/// foreground legible and reads on both light and dark terminals.
pub def View.selection_style : TextStyle :=
    { style_default with bg := Option.some Color.blue }

/// Merge the selection background onto a covered segment.
#[partial]
def ply_map_bg (segs : List TextSegment) : List TextSegment :=
    match segs {
        List.empty => List.empty,
        List.cons one rest =>
            List.cons (mk_text_segment one.text (style_merge one.style View.selection_style))
                (ply_map_bg rest)
    }

/// Concatenate three segment lists.
#[partial]
def ply_join3 (a : List TextSegment) (b : List TextSegment) (c : List TextSegment)
    : List TextSegment :=
    List.append a (List.append b c)

// ── The primary head ───────────────────────────────────────────────────────

/// Reverse the primary head's cell on the row: the caret's block. The
/// head is a BYTE offset; its cell is `Text.col_of_byte` of the row's
/// text. A head past the content (end-of-line, the common case) pads
/// the row with one space so the caret still paints -- the same rule
/// tui's `text_input` leaf states for a cursor past the value's end.
///
/// The guard is the row membership test: the caret paints on the row
/// whose `[start, stop]` contains the head. A head at the START of the
/// next line belongs to that line, not to this one's trailing pad.
def ply_reverse_primary_head (sel : Selections) (row : RowView) (segs : List TextSegment)
    : List TextSegment :=
    match Selections.primary_sel sel {
        Option.none => segs,
        Option.some one => ply_reverse_if_on_row one row segs
    }

/// The head's row-membership guard and its reversal, split so the
/// selection is matched into its fields exactly once (the same
/// read-once discipline `selection.mo` states).
def ply_reverse_if_on_row (one : Selection) (row : RowView) (segs : List TextSegment)
    : List TextSegment :=
    match one {
        { head, .. } =>
            if Bool.or (Bool.not (row.start < head + 1)) (Bool.not (head < row.stop + 1))
            then segs
            else ply_reverse_head_cell head row segs
    }

/// The head cell's reversal, for a head inside `[start, stop]`.
def ply_reverse_head_cell (head : I64) (row : RowView) (segs : List TextSegment)
    : List TextSegment :=
    let col : I64 := Text.col_of_byte row.text (head - row.start) in
    if col < Text.width row.text
    then ply_reverse_at col segs
    else ply_append_caret segs

/// Reverse the cell at `col` within the segments: cut head / one cell
/// / tail, merge reverse onto the middle, join. A `col` of 0 gives an
/// empty head -- `slice_spans` answers the empty list and the join is
/// the identity, so there is no case of its own.
def ply_reverse_at (col : I64) (segs : List TextSegment) : List TextSegment :=
    let shared : Shared (List TextSegment) := Shared.of segs in
    let head : List TextSegment := Text.slice_spans (Shared.get shared) 0 col in
    let mid : List TextSegment :=
        ply_map_rev (Text.slice_spans (Shared.get shared) col (col + 1)) in
    let tail : List TextSegment :=
        Text.slice_spans (Shared.get shared) (col + 1) (Text.width_spans (Shared.get shared)) in
    ply_join3 head mid tail

/// The caret past the content: pad the row with one space segment,
/// reversed, so the caret paints in the first cell past the text.
def ply_append_caret (segs : List TextSegment) : List TextSegment :=
    List.append segs (List.cons (mk_text_segment " " View.caret_style) List.empty)

/// Merge reverse video onto a covered segment.
#[partial]
def ply_map_rev (segs : List TextSegment) : List TextSegment :=
    match segs {
        List.empty => List.empty,
        List.cons one rest =>
            List.cons (mk_text_segment one.text (style_merge one.style View.caret_style))
                (ply_map_rev rest)
    }

/// The caret's style: reverse video, the same visual tui's
/// `text_input` cursor uses (`underline_at`'s recorded finding: an
/// underline alone reads as "no caret" on real screens).
pub def View.caret_style : TextStyle :=
    { style_default with reverse := true }

// ── The gutter ─────────────────────────────────────────────────────────────

/// The gutter's label for a row: the line number right-aligned in
/// `View.gutter_width - 1` cells, then one space. `(line + 1)` because
/// editors number from 1 while the rope numbers from 0.
pub def View.gutter_label (line : I64) : String :=
    let digits : String := I64.to_string (line + 1) in
    let pad : I64 := (View.gutter_width - 1) - Text.width digits in
    String.concat (ply_spaces (if pad < 1 then 0 else pad)) (String.concat digits " ")

/// `n` spaces.
#[partial]
def ply_spaces (n : I64) : String :=
    if n < 1 then "" else String.concat " " (ply_spaces (n - 1))

/// The gutter's style: dim, so the numbers never compete with the text.
pub def View.gutter_style : TextStyle :=
    { style_default with dim := true }

// ── The status line ────────────────────────────────────────────────────────

/// The status line's segments: mode, path, `line:col`, dirty flag and
/// the pending chord -- each its own segment so the styles compose
/// (the mode is bold, the rest plain).
///
/// THE COMMAND LINE WINS OVER EVERYTHING: while the editor is on a `:`
/// line, that row IS the line -- `:` plus what has been typed plus the
/// caret, the way every modal editor shows it. Without this the typed text
/// lives only in `Mode.command`'s payload and the user types blind, which is
/// indistinguishable from a dead key.
///
/// THE CARET IS AN APPENDED BLOCK, not a hardware cursor: the row is built
/// as segments, so a reversed space at the end is the caret -- the same
/// "reverse video is the caret" rule the text area's own rows follow (there
/// is no cell to reverse on an empty line, so a space is added).
///
/// THE STATUS MESSAGE IS SECOND -- when a command printed one (`:`
/// commands, rejections, a save's path), it is the whole status line: a
/// report and the position would fight for one row, and the report is what
/// the user just asked for.
pub def View.status_segments (st : EditorState) : List TextSegment :=
    match EditorState.mode_of st {
        Mode.command line => ply_command_line ":" line,
        Mode.search query => ply_command_line "/" query,
        Mode.picker query _ => ply_picker_line st query,
        _ => ply_status_or_message st
    }

/// The status row when the editor is not on a command line: the message if
/// one was printed, the position otherwise.
def ply_status_or_message (st : EditorState) : List TextSegment :=
    let msg : String := EditorState.status_of st in
    if Bool.not (String.is_empty msg)
    then List.cons (mk_text_segment msg style_default) List.empty
    else ply_status_full st

/// A typing line as two segments: its `prompt` (`:` or `/`) plus the text
/// typed so far, then the caret's reversed space. Both styles are the
/// default; the line is not a report, so nothing about it is emphasised.
///
/// THE PROMPT IS A PARAMETER, not a `:`. The `/` line is the same row with a
/// different sigil, and a second def would be a second place for the caret
/// rule to drift -- a user typing blind on one of them is the bug the whole
/// row exists to prevent.
def ply_command_line (prompt : String) (line : String) : List TextSegment :=
    let typed : TextSegment := mk_text_segment (String.concat prompt line) style_default in
    let caret : TextSegment := mk_text_segment " " View.caret_style in
    List.cons typed (List.cons caret List.empty)

/// The picker's filter row: the prompt, the filter and the count of what it
/// matched (`3/17`), so a filter that hides everything says so on the row the
/// user is typing on rather than by an empty list they have to interpret.
def ply_picker_line (st : EditorState) (query : String) : List TextSegment :=
    let matched : I64 := List.length (Picker.rank (EditorState.picker_files_of st) query) in
    let total : I64 := List.length (EditorState.picker_files_of st) in
    let count : String :=
        String.concat (I64.to_string matched) (String.concat "/" (I64.to_string total)) in
    let typed : TextSegment :=
        mk_text_segment (String.concat "> " (String.concat query (String.concat "   " count)))
            style_default in
    let caret : TextSegment := mk_text_segment " " View.caret_style in
    List.cons typed (List.cons caret List.empty)

/// The full status line, for the quiet case.
def ply_status_full (st : EditorState) : List TextSegment :=
    match EditorState.active_doc st {
        Option.none => List.cons (mk_text_segment "[no buffer]" style_default) List.empty,
        Option.some doc => ply_status_doc st doc
    }

/// The document-bearing status line. The document is read four times
/// (rope, head, path, dirty) and is not `Copy` (its history holds a
/// `BTreeMap`), so the reads share one handle.
def ply_status_doc (st : EditorState) (doc : Document) : List TextSegment :=
    let shared : Shared Document := Shared.of doc in
    let rope : Rope := ply_doc_rope (Shared.get shared) in
    let head : I64 := ply_primary_head (Shared.get shared) in
    let line : I64 := Rope.line_of rope head in
    let ls : I64 := Rope.line_start rope line in
    let line_text : String := Rope.slice rope ls (Rope.line_content_end rope line - ls) in
    let col : I64 := Text.col_of_byte line_text (head - ls) + 1 in
    let mode : String := ply_mode_name (EditorState.mode_of st) in
    let path : String := ply_path (Shared.get shared) in
    let dirty : String := if ply_doc_dirty (Shared.get shared) then " [+]" else "" in
    let pending : String := ply_pending_name (EditorState.pending_of st) in
    ply_status_join mode path (I64.to_string (line + 1)) (I64.to_string col) dirty pending

/// The status line's segments from its parts: mode bold, the rest
/// plain, the dirty flag riding the position segment. The right half
/// opens with ONE SPACE so the position never crowds the path --
/// without it the row reads "normal [scratch]1:1", the two halves
/// run together.
def ply_status_join (mode : String) (path : String) (line : String) (col : String)
    (dirty : String) (pending : String) : List TextSegment :=
    let bold : TextStyle := { style_default with bold := true } in
    let left : TextSegment :=
        mk_text_segment (String.concat mode (String.concat " " path)) bold in
    let right : TextSegment :=
        mk_text_segment
            (String.concat " "
                (String.concat (String.concat line (String.concat ":" col))
                    (String.concat dirty (String.concat " " pending))))
            style_default in
    List.cons left (List.cons right List.empty)

/// The mode's display name, from the mode-table name the keymap
/// already owns -- one mapping, not two.
def ply_mode_name (m : Mode) : String :=
    match Keymap.mode_table m {
        Option.some t => t,
        Option.none => "?"
    }

/// The path, or `[scratch]` for a pathless document.
def ply_path (doc : Document) : String :=
    match doc {
        { path, .. } =>
            match path {
                Option.some p => p,
                Option.none => "[scratch]"
            }
    }

/// The dirty flag: the current revision is not the saved one. The rule
/// lives in `model.mo`'s `Document.dirty` -- one definition, so the
/// status line's `[+]` and the `Space q` refusal cannot disagree.
def ply_doc_dirty (doc : Document) : Bool := Document.dirty doc

/// The pending chord's display: the keys typed so far, or "" when
/// none. One character per key; a non-character key contributes its
/// name in brackets.
#[partial]
def ply_pending_name (keys : List Key) : String :=
    match keys {
        List.empty => "",
        List.cons one rest =>
            String.concat (ply_key_name one) (ply_pending_name rest)
    }

/// One key's display name.
def ply_key_name (k : Key) : String :=
    match k {
        Key.char c => c,
        Key.escape => "<esc>",
        Key.enter => "<enter>",
        Key.tab => "<tab>",
        Key.backspace => "<bs>",
        Key.up => "<up>",
        Key.down => "<down>",
        Key.left => "<left>",
        Key.right => "<right>",
        Key.home => "<home>",
        Key.end => "<end>",
        Key.page_up => "<pgup>",
        Key.page_down => "<pgdn>",
        Key.delete => "<del>",
        Key.insert => "<ins>",
        Key.function_key n => "<F" ++ I64.to_string n ++ ">",
        Key.ctrl c => "<C-" ++ c ++ ">",
        Key.alt c => "<A-" ++ c ++ ">"
    }

// ── The view ────────────────────────────────────────────────────────────────

/// The editor's whole view: the text area (gutter + styled rows) above
/// the status line. `tui::App`'s `view` field -- `render` walks this
/// tree into the `Screen` the loop diffs.
pub def View.view (st : EditorState) : Widget :=
    Widget.column (ply_view_children st)

/// The column's children: the text area fills, the status line is one
/// row. Built as a def so the list literal is never in an argument
/// position (the two-host inference gotcha).
def ply_view_children (st : EditorState) : List SizedWidget :=
    // THE PICKER TAKES THE AREA: while it is open the body is its list, not
    // the buffer. A modal overlay would be the richer design, but `tui` has
    // no overlay leaf and a picker you can see the buffer around does not
    // open any file the list did not name.
    match EditorState.mode_of st {
        Mode.picker _ _ =>
            List.cons (ply_picker_area st) (List.cons (ply_status_row st) List.empty),
        _ => ply_buffer_children st
    }

/// The buffer's area and the status line -- the ordinary frame.
def ply_buffer_children (st : EditorState) : List SizedWidget :=
    match EditorState.active_doc st {
        Option.none =>
            List.cons (ply_status_row st) List.empty,
        Option.some doc =>
            // The document is read three times (the window, the rows,
            // the row widgets) and holds a history, so one handle
            // serves all three.
            let shared : Shared Document := Shared.of doc in
            let height : I64 := View.text_height (EditorState.rows_of st) in
            let width : I64 := View.text_width (EditorState.cols_of st) in
            let first : I64 := ply_first_visible st (Shared.get shared) in
            let left : I64 := ply_left_col st (Shared.get shared) in
            let rows : List RowView := View.rows (Shared.get shared) first height in
            let text_area : SizedWidget :=
                sized (LayoutSize.fill 1)
                    (Widget.column (ply_row_widgets (Shared.get shared) rows left width)) in
            List.cons text_area (List.cons (ply_status_row st) List.empty)
    }

/// The picker's body: a header row naming the directory, then the ranked
/// candidates with the highlighted one reversed, filling the text area.
///
/// THE WINDOW IS DERIVED, NOT STORED: `Picker.window_offset` computes the
/// first visible row from the highlight and the height, so a resize or a
/// filter that shrank the list cannot strand the highlight off-screen (the
/// same rule `View.first_visible` applies to the caret's line).
def ply_picker_area (st : EditorState) : SizedWidget :=
    let height : I64 := View.text_height (EditorState.rows_of st) in
    // The list gets the height less its one header row, and never less than
    // one row: a one-row terminal still shows a candidate.
    let list_height : I64 := if height < 2 then 1 else height - 1 in
    // The ranked list is read three times (its length, the window, the
    // rows), and a `List` is deliberately not `Copy`, so one `Shared` handle
    // serves all three.
    let ranked : Shared (List String) :=
        Shared.of (Picker.rank (EditorState.picker_files_of st) (EditorState.picker_query_of st)) in
    let count : I64 := List.length (Shared.get ranked) in
    let selected : I64 := Picker.clamp_selected (EditorState.picker_selected_of st) count in
    let first : I64 := Picker.window_offset selected list_height count in
    let rows : List String := Picker.take_from first list_height (Shared.get ranked) in
    let header : SizedWidget :=
        sized (LayoutSize.fixed 1) (with_style View.gutter_style (label (ply_picker_header st count))) in
    sized (LayoutSize.fill 1)
        (Widget.column (List.cons header (ply_picker_rows rows first selected List.empty)))

/// The picker's header row: its title and the row counter, so a long listing
/// says where in it the user is.
def ply_picker_header (st : EditorState) (count : I64) : String :=
    let dir : String := EditorState.picker_dir_of st in
    let where_ : String := if String.is_empty dir then "." else dir in
    String.concat "pick a file in " (String.concat where_
        (String.concat "   " (String.concat (I64.to_string count) " matches")))

/// The candidate rows, one `Widget.row` each with the highlighted one
/// reversed.
///
/// `at` CARRIES THE ABSOLUTE ROW INDEX, because the window starts at `first`
/// and the highlight names a position in the WHOLE ranked list -- comparing
/// the window-relative index would reverse the wrong row whenever the window
/// has scrolled. Each step consumes one row, so `at` advances with it.
#[partial]
def ply_picker_rows (rows : List String) (at : I64) (selected : I64)
    (acc : List SizedWidget) : List SizedWidget :=
    match rows {
        List.empty => List.reverse acc,
        List.cons one rest =>
            ply_picker_rows rest (at + 1) selected
                (List.cons (ply_picker_row one at selected) acc)
    }

/// One candidate row: a marker for the highlighted one, then the path.
def ply_picker_row (path : String) (index : I64) (selected : I64) : SizedWidget :=
    let here : Bool := I64.beq index selected in
    let marker : String := if here then "> " else "  " in
    let style : TextStyle := if here then View.caret_style else style_default in
    sized (LayoutSize.fixed 1) (with_style style (label (String.concat marker path)))

/// The status line's row widget: one row, the whole width, the status
/// segments.
def ply_status_row (st : EditorState) : SizedWidget :=
    sized (LayoutSize.fixed 1) (spans (View.status_segments st))

/// The rows' widgets: one `Widget.row` per visible line, gutter fixed
/// and text filling. `layout_row` gives the text every column past the
/// gutter, and `render_spans` clips whatever runs past it -- a line
/// wider than the viewport is the renderer's case, not the view's.
#[partial]
def ply_row_widgets (doc : Document) (rows : List RowView) (left : I64) (width : I64)
    : List SizedWidget :=
    ply_row_widgets_go (Shared.of doc) rows left width

def ply_row_widgets_go (doc : Shared Document) (rows : List RowView) (left : I64) (width : I64)
    : List SizedWidget :=
    match rows {
        List.empty => List.empty,
        List.cons one rest =>
            List.cons (ply_row_widget (Shared.get doc) one left width)
                (ply_row_widgets_go doc rest left width)
    }

/// One row's widget: the gutter label and the styled text side by side.
///
/// THE TEXT IS PAINTED THROUGH THE HORIZONTAL WINDOW (`left` .. `left +
/// width`): the segments are built at their ABSOLUTE columns -- highlight,
/// selection backgrounds and the caret's reversed cell all land where the
/// byte offsets say -- and then cut to the visible slice. Cutting after
/// styling is what keeps the caret correct for free: no hardware cursor
/// has to be moved, because the caret is a reversed cell inside this grid.
def ply_row_widget (doc : Document) (row : RowView) (left : I64) (width : I64) : SizedWidget :=
    let gutter : SizedWidget :=
        sized (LayoutSize.fixed View.gutter_width)
            (with_style View.gutter_style (label (View.gutter_label row.line))) in
    let text : SizedWidget :=
        sized (LayoutSize.fill 1) (spans (ply_windowed_segments doc row left width)) in
    sized (LayoutSize.fixed 1) (Widget.row (List.cons gutter (List.cons text List.empty)))

/// The row's segments cut to the horizontal window. A `left` of 0 with a
/// line that fits is the identity: `Text.slice_spans` answers the same
/// segments, so the common case pays one walk and nothing else.
def ply_windowed_segments (doc : Document) (row : RowView) (left : I64) (width : I64)
    : List TextSegment :=
    let segs : List TextSegment := View.row_segments doc row in
    if left < 1
    then Text.slice_spans segs 0 width
    else match ply_window row.text left width {
        Pair.pair lo hi => Text.slice_spans segs lo hi
    }
