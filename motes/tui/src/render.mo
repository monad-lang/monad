// Terminal UI Library - Rendering, diff, ANSI emission (Phase 3)
//
// Walks a `Widget` tree (widget.mo) into a `Screen` (core.mo), using the
// layout primitives (layout.mo) to place children. A `TextStyle` is threaded
// through the walk so the `styled` decorator composes: `render_with` carries
// an `active` style, and `styled` merges onto it before recursing. `diff`
// compares two same-sized screens cell-by-cell and `apply_deltas` folds the
// deltas into one ANSI escape string — the whole pipeline is pure, needs no
// terminal, and is exercised by the tests below.
//
// `String.slice`/`String.length` (init/string) and `List.map` (init/prelude)
// are auto-available. Per-character extraction is `String.slice text i 1`;
// v1 is ASCII-only (a UTF-8 code point may be multi-byte, so a single
// `String.slice` unit can split a code point — documented, not silently
// assumed).

use lib::types {
    Rect, Screen, Cell, TextStyle, CellDelta, LayoutSize
}
use lib::core {
    mk_screen, screen_get_cell, screen_set_cell,
    style_default, style_merge, style_to_ansi, mk_rect, clamp
}
use lib::layout { layout_row, layout_column, pad_rect }
use lib::text {Glyph, Text.col_of_byte, Text.drop_cols, Text.glyphs, Text.take_width, Text.wrap}
// The Phase 5 stateful widgets' states -- matched on in the new
// `LeafWidget` arms below.
use lib::widgets::input {
    InputState, input_lines, input_line_window, cursor_line, nth_lines, InputLine,
    InputState.selection_cols, InputState.press, InputState.drag,
}
use lib::widgets::list { ListState }
// `LeafWidget`/`DecoratorKind` are matched on, never named in a term, so the
// unused-import analysis reports them as unused -- the same blind spot
// `docs/src/macros.md` records for macro-name dispatch. Removing them makes
// the `use`-completeness rule fail the load on the bare `spacer`/`styled`
// patterns.
use lib::widget {
    Widget, BorderStyle, SizedWidget, LeafWidget, DecoratorKind,
    label, sized, border, padding, with_style, blank, text_input, list
}

// ==================== Cells ====================

/// A `Cell` with all fields explicit (Cell has no default fields, so a
/// literal omitting `style` would panic the checker).
def mk_styled_cell (char : String) (style : TextStyle) : Cell :=
    { char := char, style := style }

/// Write one styled char at `(row, col)`. Out-of-range writes are no-ops
/// (`screen_set_cell` guards the bounds), so border/label code can call this
/// freely without re-checking the rectangle.
def write_char (screen : Screen) (row : I64) (col : I64) (ch : String) (active : TextStyle) : Screen :=
    screen_set_cell screen row col (mk_styled_cell ch active)

// ==================== Label ====================

/// Paint `text` left-to-right into row `area.y` starting at `area.x`, up to
/// `area.width` CELLS. No-op when `area.height < 1`.
def render_label (text : String) (area : Rect) (screen : Screen) (active : TextStyle) : Screen :=
    if area.height < 1 then screen
    else screen_write_text screen area.y area.x text area.width active

/// Copy the remaining cells unchanged (they were not painted by the glyph
/// run). `acc` is the reverse-ordered prefix already built.
#[partial]
def copy_cells (cells : List Cell) (acc : List Cell) : List Cell :=
    match cells {
        List.empty => List.reverse acc,
        List.cons c rest => copy_cells rest (List.cons c acc),
    }

/// Paint whole glyphs into the row starting at cell `col`, stopping before a
/// glyph that would not fit the cell budget. A width-2 glyph writes its text
/// into cell `i` and a `""` continuation into cell `i+1`; the emitter knows
/// the continuation is covered by the glyph.
#[partial]
def write_cells (cells : List Cell) (i : I64) (col : I64) (glyphs : List Glyph) (budget : I64) (style : TextStyle) (used : I64) (acc : List Cell) : List Cell :=
    match cells {
        List.empty => List.reverse acc,
        List.cons c rest =>
            if i < col
            then write_cells rest (i + 1) col glyphs budget style used (List.cons c acc)
            else match glyphs {
                List.empty => copy_cells (List.cons c rest) acc,
                List.cons g grest =>
                    if budget < used + g.width
                    then copy_cells (List.cons c rest) acc
                    else if g.width == 2
                    then match rest {
                        List.empty => copy_cells (List.cons c rest) acc,
                        List.cons c2 rest2 =>
                            write_cells rest2 (i + 2) col grest budget style (used + 2)
                                (List.cons (mk_styled_cell "" style) (List.cons (mk_styled_cell g.text style) acc)),
                    }
                    else write_cells rest (i + 1) col grest budget style (used + 1) (List.cons (mk_styled_cell g.text style) acc),
            },
    }

#[partial]
def write_rows (rows : List (List Cell)) (i : I64) (row : I64) (col : I64) (glyphs : List Glyph) (budget : I64) (style : TextStyle) (acc : List (List Cell)) : List (List Cell) :=
    match rows {
        List.empty => List.reverse acc,
        List.cons r rest =>
            if i == row
            then write_rows rest (i + 1) row col glyphs budget style (List.cons (write_cells r 0 col glyphs budget style 0 List.empty) acc)
            else write_rows rest (i + 1) row col glyphs budget style (List.cons r acc),
    }

pub def screen_write_text (screen : Screen) (row : I64) (col : I64) (text : String) (stop : I64) (style : TextStyle) : Screen :=
    let nrows : I64 := screen.rows in
    let ncols : I64 := screen.cols in
    if Bool.or (row < 0) (Bool.or (Bool.not (row < nrows)) (Bool.or (col < 0) (Bool.not (col < ncols)))) then screen
    else
        let glyphs : List Glyph := Text.glyphs text in
        let cells : List (List Cell) := screen.row_cells in
        let cells2 : List (List Cell) := write_rows cells 0 row col glyphs stop style List.empty in
        let s : Screen := { screen with row_cells := cells2 } in
        s

// ==================== Wrapping ====================

/// Split `line` into rows of at most `width` CELLS: word-wrap at the last
/// space that fits, hard-break a word longer than the width. Widths below 1
/// clamp to 1 (a zero width would never advance). The cell-aware
/// implementation lives in `text.mo`; this name stays for callers.
pub def wrap_text (width : I64) (line : String) : List String :=
    Text.wrap width line

#[test]
def test_wrap_exact_fit : Bool := wrap_text 5 "abcde" == ["abcde"]

#[test]
def test_wrap_hard_break : Bool := wrap_text 3 "abcdefg" == ["abc", "def", "g"]

#[test]
def test_wrap_word_boundary : Bool := wrap_text 6 "hello world" == ["hello", "world"]

#[test]
def test_wrap_width_one : Bool := wrap_text 1 "abc" == ["a", "b", "c"]

#[test]
def test_wrap_empty : Bool := wrap_text 4 "" == [""]

#[test]
def test_wrap_zero_width_advances : Bool := wrap_text 0 "ab" == ["a", "b"]

#[test]
def test_wrap_trailing_space_adds_no_row : Bool := wrap_text 3 "abc " == ["abc"]

// ==================== Borders ====================

/// The six box-drawing glyphs a `BorderStyle` resolves to.
pub struct BorderChars {
    tl : String, tr : String, bl : String, br : String, h : String, v : String
}

/// Resolve glyphs for a `BorderStyle`. Unicode escapes give the rounded,
/// double, and thick box characters.
def border_chars (bs : BorderStyle) : BorderChars :=
    match bs {
        plain =>
            { tl := "+", tr := "+", bl := "+", br := "+", h := "-", v := "|" },
        rounded =>
            { tl := "\u{256d}", tr := "\u{256e}", bl := "\u{2570}", br := "\u{256f}", h := "\u{2500}", v := "\u{2502}" },
        double_box =>
            { tl := "\u{2554}", tr := "\u{2557}", bl := "\u{255a}", br := "\u{255d}", h := "\u{2550}", v := "\u{2551}" },
        thick =>
            { tl := "\u{250f}", tr := "\u{2513}", bl := "\u{2517}", br := "\u{251b}", h := "\u{2501}", v := "\u{2503}" }
    }

/// Fill the horizontal run between the two corners with `fill`, exclusive of
/// the right corner column `end_col`.
#[terminating]
def draw_h_fill (screen : Screen) (y : I64) (col : I64) (end_col : I64) (fill : String) (active : TextStyle) : Screen :=
    if col < end_col then
        draw_h_fill (write_char screen y col fill active) y (col + 1) end_col fill active
    else screen

/// One horizontal edge: `left` corner, `fill` run, `right` corner.
def draw_h_edge (area : Rect) (y : I64) (left : String) (fill : String) (right : String) (screen : Screen) (active : TextStyle) : Screen :=
    let s0 := write_char screen y area.x left active in
    let s1 := draw_h_fill s0 y (area.x + 1) (area.x + area.width - 1) fill active in
    write_char s1 y (area.x + area.width - 1) right active

/// The two vertical edges, between the top and bottom rows.
#[terminating]
def draw_v_edges (area : Rect) (y : I64) (end_y : I64) (v : String) (screen : Screen) (active : TextStyle) : Screen :=
    if y < end_y then
        let s0 := write_char screen y area.x v active in
        let s1 := write_char s0 y (area.x + area.width - 1) v active in
        draw_v_edges area (y + 1) end_y v s1 active
    else screen

/// Draw a full box around `area`. Caller must ensure `area.width >= 2` and
/// `area.height >= 2` (the top/bottom rows and the two verticals overlap the
/// corner cells, which is why the edges are drawn in this order: top, then
/// bottom, then the verticals between them).
def draw_border (area : Rect) (bs : BorderStyle) (screen : Screen) (active : TextStyle) : Screen :=
    let bc := border_chars bs in
    let top := draw_h_edge area area.y bc.tl bc.h bc.tr screen active in
    let bottom := draw_h_edge area (area.y + area.height - 1) bc.bl bc.h bc.br top active in
    draw_v_edges area (area.y + 1) (area.y + area.height - 1) bc.v bottom active

// ==================== Text input & list (Phase 5) ====================

/// Re-style the cell at `(row, col)` as the text field's cursor: merge
/// `underline := true` and `reverse := true` into the cell's own style,
/// whatever it is. The cursor's visual is a style, not a glyph, so it
/// composes with any character under it. `run_app` HIDES the terminal
/// cursor, and an underline alone reads as "no caret" on real screens
/// (the recorded UI-repair finding) -- reverse gives an unmissable
/// block cursor.
def underline_at (screen : Screen) (row : I64) (col : I64) : Screen :=
    match screen_get_cell screen row col {
        some c =>
            let u : TextStyle := { style_default with underline := true, reverse := true } in
            let s1 : Screen := screen_set_cell screen row col { c with style := style_merge c.style u } in
            // A width-2 glyph occupies the next cell too (`""`): style it so
            // the cursor block covers the whole glyph.
            match screen_get_cell s1 row (col + 1) {
                some c2 =>
                    if String.is_empty c2.char
                    then screen_set_cell s1 row (col + 1) { c2 with style := style_merge c2.style u }
                    else s1,
                none => s1,
            },
        none => screen
    }

/// Merge `reverse := true` into cells `[c0, c1)` on `row` -- the mouse
/// selection's highlight. Continuation cells of wide glyphs are included;
/// `apply_one` skips their empty char.
#[terminating]
def reverse_span_go (screen : Screen) (row : I64) (col : I64) (stop : I64) : Screen :=
    if Bool.not (col < stop)
    then screen
    else match screen_get_cell screen row col {
        none => screen,
        some c =>
            let u : TextStyle := { style_default with reverse := true } in
            let s1 : Screen := screen_set_cell screen row col { c with style := style_merge c.style u } in
            reverse_span_go s1 row (col + 1) stop,
    }

def reverse_span (screen : Screen) (row : I64) (c0 : I64) (c1 : I64) : Screen :=
    if Bool.not (c0 < c1) then screen else reverse_span_go screen row c0 c1

/// One text field. The value scrolls horizontally to keep the cursor
/// inside the field (the visible window starts at the cursor minus the
/// last column), the cursor cell is a reverse block (see `underline_at`;
/// a space reversed when the cursor sits past the value's end), and an
/// empty value shows the placeholder dimmed UNDER the cursor block: the
/// field is focused from the first frame, so the caret is visible before
/// the user types anything.
///
/// MULTILINE (Phase 11b, the input pass): a value containing newlines
/// renders one row per line, the window showing the
/// cursor-anchored LAST rows of the line list, each row keeping the
/// single-line horizontal-window rule; the cursor cell sits on its
/// line's row at the cursor's column. A single-line value takes the
/// original one-row path, byte-identical to before.
def render_text_input (st : InputState) (area : Rect) (screen : Screen) (active : TextStyle) : Screen :=
    if area.height < 1
    then screen
    else
        let len := String.length st.value in
        let cur := clamp st.cursor 0 len in
        if len == 0 && Bool.not (st.placeholder == "")
        then
            // The `: TextStyle` annotation is load-bearing on struct-update
            // literals flowing into style_merge (see the note on
            // test_style_to_ansi_bold_red_combines_one_sequence in core.mo).
            let dim : TextStyle := { style_default with dim := true } in
            let drawn : Screen := render_label st.placeholder area screen (style_merge active dim) in
            underline_at drawn area.y (area.x + Text.col_of_byte st.value (clamp st.cursor 0 len))
        else
            let multi : Bool := contains_newline st.value 0 in
            if Bool.not multi
            then render_text_input_row st st.value cur area.y 0 area screen active
            else render_text_input_multi st cur area screen active

#[terminating]
def contains_newline (s : String) (i : I64) : Bool :=
    if Bool.not (i < String.length s)
    then false
    else if String.slice s i 1 == "\n"
    then true
    else contains_newline s (i + 1)

/// The dropped display columns for a line's window (the same rule the
/// hit-test uses).
def window_dropped (text : String) (caret_byte : I64) (width : I64) : I64 :=
    match input_line_window text caret_byte width {
        Pair.pair _ d => d,
    }

/// One input line: its horizontal window, the selection's reverse span
/// mapped into the window, no caret. Both the single-line and multiline
/// renderers use it.
#[partial]
def render_input_line (st : InputState) (line_idx : I64) (text : String) (caret_byte : I64)
        (row : I64) (area : Rect) (screen : Screen) (active : TextStyle) : Screen :=
    match input_line_window text caret_byte area.width {
        Pair.pair visible dropped =>
            let row_area : Rect := { area with y := row, height := 1 } in
            let drawn : Screen := render_label visible row_area screen active in
            match InputState.selection_cols st line_idx text {
                Option.none => drawn,
                Option.some pr => match pr {
                    Pair.pair a b =>
                        let c0 : I64 := clamp (a - dropped) 0 area.width in
                        let c1 : I64 := clamp (b - dropped) 0 area.width in
                        reverse_span drawn row (area.x + c0) (area.x + c1),
                },
            },
    }

/// The single-line body of `render_text_input`, factored for both the
/// one-row and the multiline path: value `text` with the cursor at
/// byte `cur`, rendered on row `row`.
#[partial]
def render_text_input_row (st : InputState) (text : String) (cur : I64) (row : I64) (line_idx : I64)
        (area : Rect) (screen : Screen) (active : TextStyle) : Screen :=
    let drawn : Screen := render_input_line st line_idx text cur row area screen active in
    let dropped : I64 := window_dropped text cur area.width in
    underline_at drawn row (area.x + (Text.col_of_byte text cur - dropped))

/// The multiline body: the value's lines, the CURSOR-anchored window
/// (down-shifted so the cursor's line is the last visible row), each
/// rendered on its row; the cursor cell lands on its line's row, at
/// its (windowed) column.
#[partial]
def render_text_input_multi (st : InputState) (cur : I64) (area : Rect) (screen : Screen) (active : TextStyle) : Screen :=
    let lines : List InputLine := input_lines st.value 0 in
    match cursor_line lines 0 cur {
        Option.none => screen,
        Option.some found =>
            match found {
                Pair.pair row_idx cl =>
                    // Shift the line window so the cursor's line is the
                    // LAST row: the first visible line's index.
                    let first : I64 := row_idx - (area.height - 1) in
                    let shifted : List InputLine := nth_lines (input_lines st.value 0) (if first < 0 then 0 else first) in
                    render_input_lines st shifted
                        (if first < 0 then 0 else first)
                        (st.value) (cur) (row_idx - (if first < 0 then 0 else first))
                        0 area screen active,
            },
    }

/// Walk the shifted line window painting its rows; `display_row` is the
/// first row's display offset, `cursor_row` tracks the cursor's line.
/// The cursor line is horizontally windowed to the caret; other lines
/// render from column 0 (and the hit-test maps them with dropped=0).
#[terminating]
def render_input_lines (st : InputState) (lines : List InputLine) (line_idx : I64) (value : String) (cur : I64) (cursor_row : I64) (display_row : I64) (area : Rect) (screen : Screen) (active : TextStyle) : Screen :=
    if Bool.not (display_row < area.height)
    then screen
    else
        match lines {
            List.empty => screen,
            List.cons l rest =>
                let text : String := String.slice value l.start l.len in
                let caret : I64 := clamp (cur - l.start) 0 l.len in
                let caret_byte : I64 := if display_row == cursor_row then caret else 0 in
                let drawn : Screen := render_input_line st line_idx text caret_byte (area.y + display_row) area screen active in
                let screen2 : Screen :=
                    if display_row == cursor_row
                    then
                        let dropped : I64 := window_dropped text caret area.width in
                        underline_at drawn (area.y + display_row) (area.x + (Text.col_of_byte text caret - dropped))
                    else drawn in
                render_input_lines st rest (line_idx + 1) value cur cursor_row (display_row + 1) area screen2 active,
        }

/// One list row per line of `area`, starting at `st.offset`: the selected
/// row gets the `"> "` marker and a bold style, other rows a two-space
/// indent and the ambient style. Rows stop at the shorter of the item
/// list and the area's height.
#[terminating]
def render_list_rows (items : List String) (selected : I64) (index : I64) (area : Rect) (row : I64) (screen : Screen) (active : TextStyle) : Screen :=
    match items {
        empty => screen,
        cons item rest =>
            if Bool.not (row < area.y + area.height)
            then screen
            else
                let sel := index == selected in
                let line := (if sel then "> " else "  ") ++ item in
                let row_style :=
                    if sel
                    then
                        let bold : TextStyle := { style_default with bold := true } in
                        style_merge active bold
                    else active in
                let drawn := render_label line (mk_rect area.x row area.width 1) screen row_style in
                render_list_rows rest selected (index + 1) area (row + 1) drawn active
    }

/// The visible window of a list's state, starting at `st.offset`. The
/// stdlib has no `List.drop`, so the skip is a local walk: `render_list_rows`
/// labels the list head with `index`, so it must be handed the sublist that
/// starts at `st.offset`, not the full `items`.
#[terminating]
def drop_strings (n : I64) (xs : List String) : List String :=
    if n < 1
    then xs
    else match xs { empty => xs, cons _ rest => drop_strings (n - 1) rest }

def render_list (st : ListState) (area : Rect) (screen : Screen) (active : TextStyle) : Screen :=
    render_list_rows (drop_strings st.offset st.items) st.selected st.offset area area.y screen active

// ==================== Renderer ====================

/// Render `w` into `area` of `screen` with the default style.
pub def render (w : Widget) (area : Rect) (screen : Screen) : Screen :=
    render_with w area screen style_default

/// Render `w` carrying `active`, the composed style for this subtree.
///
/// `#[terminating]`: the decorator cases recurse on the structurally-smaller
/// `child`, but the `column`/`row` cases hand `List.map`-built widget lists to
/// `render_children` (which re-enters `render_with` on each element). That
/// mutual recursion is well-founded — every step descends the finite widget
/// tree — but the mapped list is not a structural subterm of `w`, so the
/// checker cannot see it.
#[terminating]
pub def render_with (w : Widget) (area : Rect) (screen : Screen) (active : TextStyle) : Screen :=
    match w {
        Widget.leaf kind =>
            match kind {
                LeafWidget.label text => render_label text area screen active,
                LeafWidget.spacer _ => screen,
                LeafWidget.text_input st => render_text_input st area screen active,
                LeafWidget.list st => render_list st area screen active,
                LeafWidget.blank => screen
            },
        Widget.decorator kind child =>
            match kind {
                DecoratorKind.border bs =>
                    // Skip the box (but still render the child inset by 1) when
                    // there is no room for a 2x2 frame.
                    let boxed := if area.width < 2 || area.height < 2 then screen else draw_border area bs screen active in
                    render_with child (pad_rect area 1 1 1 1) boxed active,
                DecoratorKind.padding l t r b =>
                    render_with child (pad_rect area l t r b) screen active,
                DecoratorKind.styled s =>
                    render_with child area screen (style_merge active s)
            },
        Widget.column children =>
            render_children (List.map widget_of children) (layout_column area (List.map size_of children)) screen active,
        Widget.row children =>
            render_children (List.map widget_of children) (layout_row area (List.map size_of children)) screen active,
        Widget.stack children =>
            render_stack children area screen active
    }

/// `List.map` needs a function, and a bare field projection is not one, so the
/// two halves of a `SizedWidget` get named lambdas here rather than the
/// accessor defs they used to have in `widget.mo`.
def widget_of (sw : SizedWidget) : Widget := sw.widget
def size_of (sw : SizedWidget) : LayoutSize := sw.size

/// Render each widget into its own (widget, rect) pair in lockstep, threading
/// the screen forward. Stops at the shorter list.
#[terminating]
def render_children (ws : List Widget) (rects : List Rect) (screen : Screen) (active : TextStyle) : Screen :=
    match ws {
        empty => screen,
        cons w rest =>
            match rects {
                empty => screen,
                cons r rrest => render_children rest rrest (render_with w r screen active) active
            }
    }

/// Stack: render each child over the same `area` in order, so a later child
/// paints over an earlier one.
#[terminating]
def render_stack (children : List Widget) (area : Rect) (screen : Screen) (active : TextStyle) : Screen :=
    match children {
        empty => screen,
        cons w rest => render_stack rest area (render_with w area screen active) active
    }

// ==================== Diff ====================

/// Walk two rows of cells in lockstep, emitting `CellDelta.set row col <new>`
/// for each cell that differs (carrying the NEW cell, since a delta is the
/// change to apply from old to new).
#[terminating]
def diff_row (old_cells : List Cell) (new_cells : List Cell) (row : I64) (col : I64) : List CellDelta :=
    match old_cells {
        empty => List.empty,
        cons o or =>
            match new_cells {
                empty => List.empty,
                cons n nr =>
                    let rest := diff_row or nr row (col + 1) in
                    if Bool.not (o == n) then List.cons (CellDelta.set row col n) rest else rest
            }
    }

/// Walk two lists of rows in lockstep, concatenating each row's deltas.
#[terminating]
def diff_rows (old_rows : List (List Cell)) (new_rows : List (List Cell)) (row : I64) : List CellDelta :=
    match old_rows {
        empty => List.empty,
        cons or orr =>
            match new_rows {
                empty => List.empty,
                cons nr nrr => List.append (diff_row or nr row 0) (diff_rows orr nrr (row + 1))
            }
    }

/// Deltas to go from `old` to `new`. Only same-sized screens are diffed (a
/// resize is an empty delta list in v1 — the design doc leaves resize as
/// `…`; noted here, not silently assumed).
pub def diff (old : Screen) (new : Screen) : List CellDelta :=
    if old.rows == new.rows && old.cols == new.cols
    then diff_rows old.row_cells new.row_cells 0
    else List.empty

// ==================== ANSI emission ====================

/// The CSI cursor-position code for 1-indexed `(row, col)`.
def cursor_code (r : I64) (c : I64) : String :=
    "\u{1b}[" ++ I64.to_string (r + 1) ++ ";" ++ I64.to_string (c + 1) ++ "H"

/// One delta as an ANSI fragment: move, reset, then (for `set`) the cell's
/// style + char, or (for `clear`) a space.
///
/// The `\u{1b}[0m` is load-bearing and cannot be replaced by
/// `style_to_ansi style_default`, which is `""` -- a style renderer has
/// nothing to say about the default style, and that is correct for
/// `render_with`'s composition but wrong here. Without the reset a cell
/// INHERITS whatever SGR state the previous fragment left: a default-styled
/// cell written after a bold red one comes out bold red, and `clear` emits a
/// bare space that keeps the old background.
///
/// Resetting per delta rather than tracking the emitted style across the fold
/// keeps every fragment self-contained, so `apply_deltas` stays a `List.map`
/// and the deltas stay independent of each other's order. A style-tracking
/// emitter would spend fewer bytes per frame; it belongs with the terminal
/// backend that has a real cursor to track as well.
def apply_one (d : CellDelta) : String :=
    match d {
        CellDelta.set r c cell =>
            // `""` is a wide glyph's continuation cell: its left neighbour's
            // delta already paints both terminal columns.
            if String.is_empty cell.char
            then ""
            else cursor_code r c ++ "\u{1b}[0m" ++ style_to_ansi cell.style ++ cell.char,
        CellDelta.clear r c =>
            cursor_code r c ++ "\u{1b}[0m" ++ " "
    }

/// Fold a delta list into one ANSI string in ONE allocation:
/// `String.concat_all` is the quadratic fold (it recopies the
/// accumulated tail at every step), and a full repaint is thousands of
/// deltas.
pub def apply_deltas (deltas : List CellDelta) : String :=
    // The trailing reset leaves the terminal in the default style: the
    // last painted cell may be styled (plan mode's green status bar), and
    // anything written after the frame -- a raw fragment, the next clear,
    // the shell after exit -- would otherwise inherit it.
    String.concat (String.concat_list (List.map apply_one deltas)) "\u{1b}[0m"

// ==================== Tests ====================

/// Extract a cell's char from a screen, defaulting to "?" when out of range.
def cell_char (screen : Screen) (row : I64) (col : I64) : String :=
    match screen_get_cell screen row col {
        some c => c.char,
        none => "?"
    }

/// The char at `(row,col)` equals `ch`.
def cell_is (screen : Screen) (row : I64) (col : I64) (ch : String) : Bool :=
    cell_char screen row col == ch

/// The cell at `(row,col)` has `bold` set to the given Bool.
def cell_bold_is (screen : Screen) (row : I64) (col : I64) (want : Bool) : Bool :=
    match screen_get_cell screen row col {
        some c => c.style.bold == want,
        none => false
    }

#[test]
def test_render_label_writes_chars : Bool :=
    let s := render (label "Hi") (mk_rect 0 0 5 1) (mk_screen 1 5) in
    cell_is s 0 0 "H" && cell_is s 0 1 "i" && cell_is s 0 2 " "

#[test]
def test_render_label_clips_to_width : Bool :=
    // width 3 admits only "Hel" of "Hello"; col 3 stays a space.
    let s := render (label "Hello") (mk_rect 0 0 3 1) (mk_screen 1 3) in
    cell_is s 0 0 "H" && cell_is s 0 1 "e" && cell_is s 0 2 "l"

#[test]
def test_render_label_no_height_is_noop : Bool :=
    let empty := mk_screen 1 5 in
    let s := render (label "Hi") (mk_rect 0 0 5 0) empty in
    cell_is s 0 0 " " && cell_is s 0 1 " "

#[test]
def test_render_label_utf8_chars : Bool :=
    let s := render (label "æøå") (mk_rect 0 0 5 1) (mk_screen 1 5) in
    cell_is s 0 0 "æ" && cell_is s 0 1 "ø" && cell_is s 0 2 "å" && cell_is s 0 3 " "

#[test]
def test_render_label_wide_uses_two_cells : Bool :=
    let s := render (label "日本") (mk_rect 0 0 5 1) (mk_screen 1 5) in
    cell_is s 0 0 "日" && cell_is s 0 1 "" && cell_is s 0 2 "本" && cell_is s 0 3 ""

#[test]
def test_render_label_wide_clipped_at_the_edge : Bool :=
    let s := render (label "日") (mk_rect 0 0 1 1) (mk_screen 1 1) in
    cell_is s 0 0 " "

#[test]
def test_apply_deltas_skips_a_wide_continuation : Bool :=
    let d1 := CellDelta.set 0 0 (mk_styled_cell "日" style_default) in
    let d2 := CellDelta.set 0 1 (mk_styled_cell "" style_default) in
    apply_deltas [d1, d2] == "\u{1b}[1;1H\u{1b}[0m日\u{1b}[0m"

#[test]
def test_render_border_plain : Bool :=
    let s := render (border BorderStyle.plain (label "x")) (mk_rect 0 0 3 3) (mk_screen 3 3) in
    cell_is s 0 0 "+" && cell_is s 0 2 "+"
    && cell_is s 2 0 "+" && cell_is s 2 2 "+"
    && cell_is s 0 1 "-" && cell_is s 2 1 "-"
    && cell_is s 1 0 "|" && cell_is s 1 2 "|"
    && cell_is s 1 1 "x"

#[test]
def test_render_border_rounded_glyphs : Bool :=
    let s := render (border BorderStyle.rounded blank) (mk_rect 0 0 3 3) (mk_screen 3 3) in
    cell_is s 0 0 "\u{256d}" && cell_is s 0 2 "\u{256e}"
    && cell_is s 2 0 "\u{2570}" && cell_is s 2 2 "\u{256f}"

#[test]
def test_render_border_too_small_skips_box : Bool :=
    // 1x1 area: no room for a 2x2 frame; child still renders inset (to a
    // zero-size rect), so the single cell stays a space.
    let s := render (border BorderStyle.plain (label "x")) (mk_rect 0 0 1 1) (mk_screen 1 1) in
    cell_is s 0 0 " "

#[test]
def test_render_column_splits_vertically : Bool :=
    let w := Widget.column [sized (LayoutSize.fill 1) (label "a"), sized (LayoutSize.fill 1) (label "b")] in
    let s := render w (mk_rect 0 0 1 2) (mk_screen 2 1) in
    cell_is s 0 0 "a" && cell_is s 1 0 "b"

#[test]
def test_render_row_splits_horizontally : Bool :=
    let w := Widget.row [sized (LayoutSize.fixed 1) (label "a"), sized (LayoutSize.fixed 1) (label "b")] in
    let s := render w (mk_rect 0 0 2 1) (mk_screen 1 2) in
    cell_is s 0 0 "a" && cell_is s 0 1 "b"

#[test]
def test_render_padding_insets_child : Bool :=
    // padding 1 0 1 0 over a 3x1 area leaves a 1x1 inner rect at col 1.
    let s := render (padding 1 0 1 0 (label "x")) (mk_rect 0 0 3 1) (mk_screen 1 3) in
    cell_is s 0 0 " " && cell_is s 0 1 "x" && cell_is s 0 2 " "

#[test]
def test_render_styled_sets_cell_style : Bool :=
    let bold_style : TextStyle := { style_default with bold := true } in
    let s := render (with_style bold_style (label "z")) (mk_rect 0 0 1 1) (mk_screen 1 1) in
    cell_bold_is s 0 0 true

#[test]
def test_render_stack_overlays : Bool :=
    // "b" paints over "a" at the same cell.
    let s := render (Widget.stack [label "a", label "b"]) (mk_rect 0 0 1 1) (mk_screen 1 1) in
    cell_is s 0 0 "b"

#[test]
def test_render_border_then_styled_compose : Bool :=
    let bold_style : TextStyle := { style_default with bold := true } in
    let s := render (border BorderStyle.plain (with_style bold_style (label "x"))) (mk_rect 0 0 3 3) (mk_screen 3 3) in
    // border corners are NOT bold (drawn before the styled child); the inner
    // "x" IS bold.
    cell_bold_is s 0 0 false && cell_bold_is s 1 1 true

/// The cell at `(row,col)` has `underline` set to the given Bool.
def cell_underline_is (screen : Screen) (row : I64) (col : I64) (want : Bool) : Bool :=
    match screen_get_cell screen row col {
        some c => c.style.underline == want,
        none => false
    }

def cell_reverse_is (screen : Screen) (row : I64) (col : I64) (want : Bool) : Bool :=
    match screen_get_cell screen row col {
        some c => c.style.reverse == want,
        none => false
    }

#[test]
def test_render_text_input_writes_value_and_underlines_cursor : Bool :=
    let st : InputState := { value := "ab", cursor := 1, placeholder := "", sel := Option.none } in
    let s := render (text_input st) (mk_rect 0 0 3 1) (mk_screen 1 3) in
    cell_is s 0 0 "a" && cell_is s 0 1 "b"
    && cell_underline_is s 0 0 false
    && cell_underline_is s 0 1 true
    && cell_underline_is s 0 2 false

#[test]
def test_render_text_input_cursor_after_multibyte : Bool :=
    let st : InputState := { value := "æø", cursor := 2, placeholder := "", sel := Option.none } in
    let s := render (text_input st) (mk_rect 0 0 4 1) (mk_screen 1 4) in
    cell_is s 0 0 "æ" && cell_is s 0 1 "ø" && cell_underline_is s 0 1 true

#[test]
def test_render_text_input_cursor_at_end_underlines_trailing_space : Bool :=
    let st : InputState := { value := "ab", cursor := 2, placeholder := "", sel := Option.none } in
    let s := render (text_input st) (mk_rect 0 0 3 1) (mk_screen 1 3) in
    cell_is s 0 2 " " && cell_underline_is s 0 2 true

#[test]
def test_render_text_input_scrolls_long_value_to_cursor : Bool :=
    // 10 chars, cursor at 9, width 3: window starts at 7, showing "hij"
    // with the cursor on the last column.
    let st : InputState := { value := "abcdefghij", cursor := 9, placeholder := "", sel := Option.none } in
    let s := render (text_input st) (mk_rect 0 0 3 1) (mk_screen 1 3) in
    cell_is s 0 0 "h" && cell_is s 0 1 "i" && cell_is s 0 2 "j"
    && cell_underline_is s 0 2 true

#[test]
def test_render_text_input_empty_shows_dim_placeholder : Bool :=
    let st : InputState := { value := "", cursor := 0, placeholder := "Search", sel := Option.none } in
    let s := render (text_input st) (mk_rect 0 0 6 1) (mk_screen 1 6) in
    cell_is s 0 0 "S"
    && (match screen_get_cell s 0 0 { some c => c.style.dim, none => false })

/// The field is focused from the first frame: the empty placeholder carries
/// the reverse-block caret on its first cell.
#[test]
def test_render_text_input_empty_placeholder_shows_caret : Bool :=
    let st : InputState := { value := "", cursor := 0, placeholder := "Search", sel := Option.none } in
    let s := render (text_input st) (mk_rect 0 0 6 1) (mk_screen 1 6) in
    cell_is s 0 0 "S"
    && cell_underline_is s 0 0 true
    && cell_reverse_is s 0 0 true
    && Bool.not (cell_reverse_is s 0 1 true)

#[test]
def test_render_text_input_selection_is_reverse : Bool :=
    let st0 : InputState := { value := "hello", cursor := 5, placeholder := "", sel := Option.none } in
    let st1 : InputState := InputState.press st0 10 1 0 1 in
    let st2 : InputState := InputState.drag st1 10 1 0 2 in
    let s := render (text_input st2) (mk_rect 0 0 10 1) (mk_screen 1 10) in
    cell_is s 0 1 "e" && cell_is s 0 2 "l"
    && cell_reverse_is s 0 1 true && cell_reverse_is s 0 2 true
    && Bool.not (cell_reverse_is s 0 0 true)
    && Bool.not (cell_reverse_is s 0 3 true)

#[test]
def test_render_text_input_selection_covers_a_wide_glyph : Bool :=
    let st0 : InputState := { value := "日本", cursor := 6, placeholder := "", sel := Option.none } in
    let st1 : InputState := InputState.press st0 4 1 0 0 in
    let st2 : InputState := InputState.drag st1 4 1 0 1 in
    let s := render (text_input st2) (mk_rect 0 0 4 1) (mk_screen 1 4) in
    cell_reverse_is s 0 0 true && cell_reverse_is s 0 1 true

#[test]
def test_render_text_input_multiline_selection : Bool :=
    let st0 : InputState := { value := "ab\ncd", cursor := 5, placeholder := "", sel := Option.none } in
    let st1 : InputState := InputState.press st0 6 2 0 1 in
    let st2 : InputState := InputState.drag st1 6 2 1 2 in
    let s := render (text_input st2) (mk_rect 0 0 6 2) (mk_screen 2 6) in
    cell_reverse_is s 0 1 true
    && cell_reverse_is s 1 0 true
    && cell_reverse_is s 1 1 true

#[test]
def test_render_list_marks_and_bolds_selected_row : Bool :=
    let st : ListState := { items := ["a", "b", "c"], selected := 1, offset := 0 } in
    let s := render (list st) (mk_rect 0 0 4 3) (mk_screen 3 4) in
    cell_is s 0 0 " " && cell_is s 0 1 " " && cell_is s 0 2 "a"
    && cell_is s 1 0 ">" && cell_is s 1 1 " " && cell_is s 1 2 "b"
    && cell_bold_is s 0 2 false && cell_bold_is s 1 2 true && cell_bold_is s 2 2 false

#[test]
def test_render_list_starts_at_offset : Bool :=
    // offset 1: rows show items "b" and "c"; the "> " marker follows the
    // selection, not the window.
    let st : ListState := { items := ["a", "b", "c"], selected := 2, offset := 1 } in
    let s := render (list st) (mk_rect 0 0 4 2) (mk_screen 2 4) in
    cell_is s 0 2 "b" && cell_is s 1 0 ">" && cell_is s 1 2 "c"

#[test]
def test_render_list_clips_to_area_height : Bool :=
    // 3 items, 1-row area: only the first item paints.
    let st : ListState := { items := ["a", "b", "c"], selected := 0, offset := 0 } in
    let s := render (list st) (mk_rect 0 0 4 1) (mk_screen 1 4) in
    cell_is s 0 2 "a" && cell_is s 0 3 " "

#[test]
def test_diff_one_changed_cell : Bool :=
    let old := mk_screen 1 2 in
    let new := screen_set_cell old 0 1 (mk_styled_cell "x" style_default) in
    let deltas := diff old new in
    // exactly one delta, at (0,1), carrying the new cell "x".
    match List.get 0 deltas {
        some d =>
            (match List.get 1 deltas { some _ => false, none => true })
            && (match d { CellDelta.set r c cell => r == 0 && c == 1 && cell.char == "x", _ => false }),
        none => false
    }

#[test]
def test_diff_identical_is_empty : Bool :=
    let s := mk_screen 2 2 in
    match diff s s { empty => true, _ => false }

#[test]
def test_diff_different_size_is_empty : Bool :=
    match diff (mk_screen 1 2) (mk_screen 2 1) { empty => true, _ => false }

#[test]
def test_apply_deltas_set_cell : Bool :=
    let d := CellDelta.set 0 1 (mk_styled_cell "x" style_default) in
    let out := apply_deltas [d] in
    // the cursor code for 1-indexed (1,2), the reset, the char "x", and
    // the frame's trailing reset.
    out == "\u{1b}[1;2H\u{1b}[0mx\u{1b}[0m"

#[test]
def test_apply_deltas_clear_cell_writes_space : Bool :=
    let out := apply_deltas [CellDelta.clear 0 0] in
    out == "\u{1b}[1;1H\u{1b}[0m \u{1b}[0m"

#[test]
def test_apply_deltas_default_cell_does_not_inherit_style : Bool :=
    // A bold cell, then a default one. Without the per-delta reset the second
    // fragment carries no escape at all, so its "b" renders bold too.
    let bold : TextStyle := { style_default with bold := true } in
    let out := apply_deltas [
        CellDelta.set 0 0 (mk_styled_cell "a" bold),
        CellDelta.set 0 1 (mk_styled_cell "b" style_default)
    ] in
    out == "\u{1b}[1;1H\u{1b}[0m\u{1b}[1ma\u{1b}[1;2H\u{1b}[0mb\u{1b}[0m"
