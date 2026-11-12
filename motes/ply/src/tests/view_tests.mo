// Phase 3's view gate: the view's geometry and its rendering, pinned by
// rendering a fixed `EditorState` through `tui::render {render}` into a
// `mk_screen` and comparing CELLS -- the plan's Phase 3 gate, the same
// golden-Screen discipline `motes/weaver`'s `ui_tests.mo` records.
//
// THE LAYERING IS THE PIN: a cell inside a selected keyword carries fg
// blue + bold (the palette) AND the selection's blue bg -- the two layers
// COMPOSE, so a selection never erases the highlighting it covers, and
// the primary head's cell is reverse video on top of whatever it already
// carries. Neighbors carry the palette with no bg and no reverse.
//
// EVERY FIXTURE'S BYTES ARE WRITTEN BESIDE IT (the toolkit suite's
// discipline), and every expected cell is derived by hand from the
// geometry the view states -- never by re-running the view.
//
// THE SCREEN IS SHARED, NOT COPIED: a `Screen` is deliberately not
// `Copy`, and every test reads it several times, so each holds one
// `Shared Screen` -- the affine rule's own remedy, the same shape
// `selection.mo`'s multi-read records take.
//
// No record patterns or bare nested struct literals inside `#[test]`
// defs: `vw_*` accessor defs hold the reads, per the recorded two-host
// inference hazard (`AGENTS.md`'s "bind to an annotated local first").
// No local is named `insert`/`select`/`prefix`/`tick` (the
// constructor-shadowing risk).

use lib::model {Document, Document.of_text, Document.with_language,
    Document.with_selections, EditorState, EditorMsg,
    EditorState.init, EditorState.active_doc, EditorState.with_status,
    EditorState.with_scroll, EditorState.rows_of, EditorState.cols_of}
use lib::selection {Selections.span}
use lib::view {View.view, View.rows, View.row_segments, View.first_visible,
    View.text_height, View.gutter_label, View.selection_style,
    RowView, RowView.line_of, RowView.text_of, RowView.start_of, RowView.stop_of}
use lib::highlight {TokenKind, Highlight.style}
use lib::commands {update}
use tui::types {Screen, Cell, TextStyle, TextSegment, Key}
use tui::core {mk_screen, mk_rect, screen_get_cell, style_default}
use tui::render {render}
use std::ansi {Color}
// `List.length` lives in `init/src/list.mo` (ambient and pure) as of the
// upstream move, so this import pulls the module's INSTANCES into scope
// and names nothing -- the empty brace list is the documented form.
use std::list {}
use init::shared {Shared}

// --- Builders ---

/// A character key, built in its own def so the `Key.char` constructor is
/// never spelled inside a test body (the constructor-shadowing risk).
def vw_key (c : String) : Key := Key.char c

/// One `update` step over a key, with the message bound to its type
/// (the same discipline `commands_tests.mo`'s `cx_press` states).
def vw_press (st : EditorState) (k : Key) : EditorState :=
    let msg : EditorMsg := EditorMsg.key k in
    match update st msg {
        Pair.pair after _ => after
    }

/// A keystroke script, folded through `update`.
#[terminating]
def vw_type (st : EditorState) (keys : List Key) : EditorState :=
    match keys {
        List.empty => st,
        List.cons k rest => vw_type (vw_press st k) rest
    }

/// A fresh 10x40 state over `text`: ten rows so the window arithmetic
/// is visible, forty columns so the gutter's five leave thirty-five
/// for text. THE LANGUAGE IS "monad" -- the tests pin the highlighter's
/// painting, and `Document.of_text` answers "text" (the fallback).
def vw_state (text : String) : EditorState :=
    vw_lang_state text "monad"

/// A fresh state over `text` with the language set -- the two dials a
/// fixture needs.
def vw_lang_state (text : String) (lang : String) : EditorState :=
    let doc : Document := Document.with_language (Document.of_text text) lang in
    EditorState.init doc 10 40

/// A fresh "text"-language state -- for the fallback-table pin.
def vw_text_state (text : String) : EditorState := vw_lang_state text "text"

/// A fresh "monad"-language state whose primary selection is the
/// hand-set span `[lo, hi)` -- the fixture for the byte-to-cell bridge's
/// snap rules, where a motion's own span would not land on the exact
/// bytes under test.
def vw_sel_state (text : String) (lo : I64) (hi : I64) : EditorState :=
    let doc : Document :=
        Document.with_selections
            (Document.with_language (Document.of_text text) "monad")
            (Selections.span lo hi) in
    EditorState.init doc 10 40

/// The state's active document, or a clean one for the no-doc case.
def vw_doc (st : EditorState) : Document :=
    match EditorState.active_doc st {
        Option.some d => d,
        Option.none => Document.of_text ""
    }

/// The screen the state renders to, as a shared handle -- every test
/// reads it several times and a `Screen` is not `Copy`. Built by the
/// three steps `run_app`'s loop performs: the view widget, the full
/// rect, a fresh `mk_screen`.
def vw_screen (st : EditorState) : Shared Screen :=
    Shared.of (render (View.view st) (mk_rect 0 0 (EditorState.cols_of st) (EditorState.rows_of st)) (mk_screen (EditorState.rows_of st) (EditorState.cols_of st)))

/// The cell at `(row, col)`, or a default cell when out of range.
def vw_cell (sh : Shared Screen) (row : I64) (col : I64) : Cell :=
    match screen_get_cell (Shared.get sh) row col {
        Option.some c => c,
        Option.none => vw_blank_cell
    }

def vw_blank_cell : Cell := { char := " ", style := style_default }

/// The rendered char at `(row, col)`, through one bound cell (the
/// recorded `(f x).field` projection hazard).
def vw_char (sh : Shared Screen) (row : I64) (col : I64) : String :=
    let c : Cell := vw_cell sh row col in
    c.char

/// The rendered style at `(row, col)`, through one bound cell.
def vw_style (sh : Shared Screen) (row : I64) (col : I64) : TextStyle :=
    let c : Cell := vw_cell sh row col in
    c.style

/// The cell's char is `ch`.
def vw_is (sh : Shared Screen) (row : I64) (col : I64) (ch : String) : Bool :=
    String.beq (vw_char sh row col) ch

/// The cell carries fg `c`.
def vw_fg_is (sh : Shared Screen) (row : I64) (col : I64) (c : Color) : Bool :=
    let st : TextStyle := vw_style sh row col in
    match st.fg {
        Option.some got => got == c,
        Option.none => false
    }

/// The cell's bg is exactly the selection's blue background. The
/// selection style is bound to an annotated local before the field
/// read: a projection directly off a cross-module def reference
/// (`View.selection_style.bg`) mis-lowers on the self-hosted host (the
/// `(f x).field` hazard this file's header records) -- the bound local
/// is the recorded remedy.
def vw_bg_is_selection (sh : Shared Screen) (row : I64) (col : I64) : Bool :=
    let st : TextStyle := vw_style sh row col in
    let sel : TextStyle := View.selection_style in
    st.bg == sel.bg

/// The cell carries no bg (a neighbor outside every selection).
def vw_bg_is_none (sh : Shared Screen) (row : I64) (col : I64) : Bool :=
    let st : TextStyle := vw_style sh row col in
    st.bg == style_default.bg

/// The cell is reverse video (the caret's block).
def vw_reverse (sh : Shared Screen) (row : I64) (col : I64) : Bool :=
    let st : TextStyle := vw_style sh row col in
    st.reverse

/// The cell is bold.
def vw_bold (sh : Shared Screen) (row : I64) (col : I64) : Bool :=
    let st : TextStyle := vw_style sh row col in
    st.bold

/// The cell is dim (the gutter's numbers).
def vw_dim (sh : Shared Screen) (row : I64) (col : I64) : Bool :=
    let st : TextStyle := vw_style sh row col in
    st.dim

/// The whole rendered status row as one string, for `String.contains`
/// assertions cell-wise pins cannot state. The state is 40 columns and
/// the status is row 9.
#[terminating]
def vw_status_text (sh : Shared Screen) : String :=
    vw_row_text sh 9 0 ""

/// One row's chars, folded into a string.
#[terminating]
def vw_row_text (sh : Shared Screen) (row : I64) (col : I64) (acc : String) : String :=
    if Bool.not (col < 40)
    then acc
    else vw_row_text sh row (col + 1) (String.concat acc (vw_char sh row col))

/// No cell in row `row` carries the selection bg -- the fold behind
/// the "selection past the clip paints nothing" pin.
#[terminating]
def vw_no_selection_bg (sh : Shared Screen) (row : I64) (col : I64) : Bool :=
    if Bool.not (col < 40)
    then true
    else Bool.not (vw_bg_is_selection sh row col) && vw_no_selection_bg sh row (col + 1)

/// No cell in row `row` is reverse video.
#[terminating]
def vw_no_reverse_in_row (sh : Shared Screen) (row : I64) (col : I64) : Bool :=
    if Bool.not (col < 40)
    then true
    else Bool.not (vw_reverse sh row col) && vw_no_reverse_in_row sh row (col + 1)

/// `n` fixture lines "l0".."l(n-1)", one per line, trailing newline
/// included -- the scroll tests' document.
#[terminating]
def vw_lines (n : I64) : String :=
    vw_lines_go 0 n ""

/// The recursive half of the fixture builder.
#[terminating]
def vw_lines_go (i : I64) (n : I64) (acc : String) : String :=
    if Bool.not (i < n)
    then acc
    else vw_lines_go (i + 1) n
        (String.concat acc (String.concat "l" (String.concat (I64.to_string i) "\n")))

/// `n` `j` keys, for driving the head down.
#[terminating]
def vw_js (n : I64) : List Key :=
    if Bool.not (0 < n)
    then List.empty
    else List.cons (vw_key "j") (vw_js (n - 1))

// ── The gutter and the text area's split ──────────────────────────────────

/// THE SPLIT: the gutter occupies the first five columns of every text
/// row, dim, and the text starts at column 5. Fixture "let x = 1"
/// (9 bytes): row 0's gutter is "   1" (right-aligned in four cells)
/// plus one space, and "l" paints at column 5, undimmed.
#[test]
def test_gutter_and_text_split : Bool :=
    let sh : Shared Screen := vw_screen (vw_state "let x = 1") in
    vw_is sh 0 0 " " && vw_is sh 0 1 " " && vw_is sh 0 2 " " && vw_is sh 0 3 "1" && vw_is sh 0 4 " "
        && vw_is sh 0 5 "l" && vw_is sh 0 6 "e" && vw_is sh 0 7 "t"
        && vw_dim sh 0 3 && Bool.not (vw_dim sh 0 5)

/// The gutter's label: 1-based line numbers, right-aligned in four
/// cells plus one space. Line 9999's number is five digits: the label
/// overflows the fixed field by one (the trailing space clips at the
/// gutter's edge), which is what every terminal editor does past the
/// fixed width.
#[test]
def test_gutter_label : Bool :=
    String.beq (View.gutter_label 0) "   1 "
        && String.beq (View.gutter_label 9) "  10 "
        && String.beq (View.gutter_label 9999) "10000 "

/// THE STATUS LINE IS THE BOTTOM ROW: "normal [scratch] 1:1" -- the
/// mode and path bold on the left ("normal" cols 0-5, space 6,
/// "[scratch]" 7-15), the position plain on the right with one space
/// between the halves. Fixture: a fresh state over "ab", cursor at 0,
/// normal mode, no path -> "[scratch]", line 1 col 1, no dirty flag,
/// no pending chord.
#[test]
def test_status_line_position : Bool :=
    let sh : Shared Screen := vw_screen (vw_state "ab") in
    vw_is sh 9 0 "n" && vw_is sh 9 1 "o" && vw_is sh 9 2 "r" && vw_is sh 9 3 "m"
        && vw_is sh 9 7 "[" && vw_is sh 9 8 "s"
        && vw_is sh 9 16 " " && vw_is sh 9 17 "1" && vw_is sh 9 18 ":" && vw_is sh 9 19 "1"
        && vw_bold sh 9 0 && Bool.not (vw_bold sh 9 17)

/// THE STATUS MESSAGE WINS the whole row: a command's report is the
/// whole status line, not a segment of it.
#[test]
def test_status_message_wins : Bool :=
    let sh : Shared Screen := vw_screen (EditorState.with_status (vw_state "ab") "wrote!") in
    vw_is sh 9 0 "w" && vw_is sh 9 1 "r" && vw_is sh 9 2 "o" && vw_is sh 9 3 "t" && vw_is sh 9 4 "e"
        && vw_is sh 9 5 "!" && Bool.not (vw_bold sh 9 0)

/// THE DIRTY FLAG: an edit (which commits a revision through the
/// funnel) shows " [+] " in the status row; a fresh state does not.
/// Script: `i` "z" Esc inserts one byte at 0 -> "zab", the head at 1,
/// the current revision past the saved one.
#[test]
def test_dirty_flag_after_an_edit : Bool :=
    let after : EditorState :=
        vw_type (vw_state "ab") [vw_key "i", vw_key "z", Key.escape] in
    let sh : Shared Screen := vw_screen after in
    String.contains (vw_status_text sh) "[+]"
        && vw_is sh 0 5 "z" && vw_is sh 0 6 "a" && vw_is sh 0 7 "b"

/// THE PENDING CHORD: after `g` (the first half of `gg`), the status
/// row shows " g" -- the chord's first key waiting for the rest.
#[test]
def test_pending_chord_shows : Bool :=
    let sh : Shared Screen := vw_screen (vw_type (vw_state "ab") [vw_key "g"]) in
    String.contains (vw_status_text sh) " g"

/// THE MODE NAME: command mode shows "command", not "normal" -- the
/// status line reads the mode table, not a hard-coded word.
#[test]
def test_command_mode_status_name : Bool :=
    let sh : Shared Screen := vw_screen (vw_type (vw_state "ab") [vw_key ":"]) in
    vw_is sh 9 0 "c" && vw_is sh 9 1 "o" && vw_is sh 9 2 "m" && vw_is sh 9 3 "m"
        && vw_is sh 9 4 "a" && vw_is sh 9 5 "n" && vw_is sh 9 6 "d"

// ── Highlighting: the palette on the screen ──────────────────────────────

/// THE PALETTE COMPOSES WITH THE SELECTION: a cell inside a selected
/// keyword carries fg blue + bold (the palette) AND the selection's
/// blue bg. Fixture "let x = 1" (9 bytes, language "monad"), `w` from
/// head 0: the selection covers [0,4) -- "let " -- so cells (0,5),
/// (0,6), (0,7) (the "let") are fg blue, bold, bg blue, and cell
/// (0,8) (the trailing space of the word run) carries the bg with no
/// palette. Cell (0,9) (the "x") carries nothing but the caret's
/// reverse -- the head is at byte 4.
#[test]
def test_selection_over_a_keyword_composes : Bool :=
    let sh : Shared Screen := vw_screen (vw_type (vw_state "let x = 1") [vw_key "w"]) in
    vw_fg_is sh 0 5 Color.blue && vw_bold sh 0 5 && vw_bg_is_selection sh 0 5
        && vw_fg_is sh 0 6 Color.blue && vw_bold sh 0 6 && vw_bg_is_selection sh 0 6
        && vw_fg_is sh 0 7 Color.blue && vw_bold sh 0 7 && vw_bg_is_selection sh 0 7
        && vw_bg_is_selection sh 0 8
        && vw_bg_is_none sh 0 9 && vw_reverse sh 0 9
        && Bool.not (vw_reverse sh 0 5)

/// THE CARET COMPOSES WITH THE PALETTE: a caret on a keyword is bold
/// blue REVERSED, not a plain block. Fixture: "let x = 1", head at
/// byte 1 (the "e") via `l` -- cell (0,6) is fg blue, bold, reverse,
/// and the "l" beside it is not.
#[test]
def test_caret_on_a_keyword_is_reversed : Bool :=
    let sh : Shared Screen := vw_screen (vw_type (vw_state "let x = 1") [vw_key "l"]) in
    vw_reverse sh 0 6 && vw_fg_is sh 0 6 Color.blue && vw_bold sh 0 6
        && Bool.not (vw_reverse sh 0 5)

/// A caret past the content (end-of-line, the common case) pads the
/// row with one space and reverses it -- the caret paints in the
/// first cell past the text. Fixture "ab": `l l` puts the head at 2,
/// past the content, so cell (0,7) is a reversed space.
#[test]
def test_caret_past_the_content_pads_one_space : Bool :=
    let sh : Shared Screen := vw_screen (vw_type (vw_state "ab") [vw_key "l", vw_key "l"]) in
    vw_reverse sh 0 7 && vw_is sh 0 7 " "
        && Bool.not (vw_reverse sh 0 6) && Bool.not (vw_reverse sh 0 8)

/// THE KEYWORD PALETTE ON ITS OWN: "let" is fg blue + bold at cells
/// 5-7; the number "1" is fg magenta at cell 13; the rest is default.
/// The caret (head 0) rides cell 5 as reverse, on top of the palette.
#[test]
def test_keyword_and_number_palette : Bool :=
    let sh : Shared Screen := vw_screen (vw_state "let x = 1") in
    vw_fg_is sh 0 5 Color.blue && vw_bold sh 0 5
        && vw_fg_is sh 0 7 Color.blue && vw_bold sh 0 7
        && vw_fg_is sh 0 13 Color.magenta
        && vw_bg_is_none sh 0 8 && Bool.not (vw_reverse sh 0 8)

/// A comment paints fg bright_black (grey) to the end of the line.
/// Fixture "x // hi" (7 bytes): the comment starts at byte 2 (col 7)
/// and runs to the end (col 11).
#[test]
def test_comment_palette_on_the_screen : Bool :=
    let sh : Shared Screen := vw_screen (vw_state "x // hi") in
    vw_fg_is sh 0 7 Color.bright_black
        && vw_fg_is sh 0 11 Color.bright_black
        && Bool.not (vw_fg_is sh 0 5 Color.bright_black)

/// A string paints fg green. Fixture "\"hi\"" (4 bytes): cells 5-8.
#[test]
def test_string_palette_on_the_screen : Bool :=
    let sh : Shared Screen := vw_screen (vw_state "\"hi\"") in
    vw_fg_is sh 0 5 Color.green && vw_fg_is sh 0 6 Color.green
        && vw_fg_is sh 0 8 Color.green

/// THE FALLBACK TABLE: a "text"-language document paints no keyword
/// -- "let" stays default, the highlighter's fallback is the view's
/// default and Phase 4's open sets the real language.
#[test]
def test_text_fallback_no_keyword_painting : Bool :=
    let sh : Shared Screen := vw_screen (vw_text_state "let x = 1") in
    Bool.not (vw_fg_is sh 0 5 Color.blue) && Bool.not (vw_bold sh 0 5)

/// THE LANGUAGE DIAL: the same bytes under language "monad" paint
/// "let" as a keyword -- the two fixtures differ only in the language
/// field, so the pin names the dial the view reads.
#[test]
def test_monad_language_paints_keywords : Bool :=
    let sh : Shared Screen := vw_screen (vw_state "let x = 1") in
    vw_fg_is sh 0 5 Color.blue && vw_bold sh 0 5

// ── The byte-to-cell bridge: a selection never splits a character ────────

/// A MULTI-BYTE GLYPH never splits: "café" (5 bytes: c,a,f + the
/// 2-byte é) is four cells, and a selection covering [0,4) -- the
/// é's LEAD byte included -- covers "caf" only, because the cut's
/// byte-to-cell conversion snaps the span's end to the glyph's START
/// cell. The caret (head 4) reverses é's cell.
#[test]
def test_multibyte_selection_snaps_to_the_glyph_start : Bool :=
    let sh : Shared Screen := vw_screen (vw_sel_state "café" 0 4) in
    vw_is sh 0 5 "c" && vw_is sh 0 6 "a" && vw_is sh 0 7 "f" && vw_is sh 0 8 "é"
        && vw_bg_is_selection sh 0 5 && vw_bg_is_selection sh 0 6
        && vw_bg_is_selection sh 0 7
        && Bool.not (vw_bg_is_selection sh 0 8)
        && vw_reverse sh 0 8

/// A WIDE (2-cell) glyph: "日本" (6 bytes) paints 日 at cells 5-6
/// (the second cell the continuation "") and 本 at 7-8. A selection
/// covering [0,3) -- exactly 日's three bytes -- covers BOTH of its
/// cells; 本 is untouched. The caret (head 3) reverses 本's first
/// cell.
#[test]
def test_wide_glyph_selection_covers_both_cells : Bool :=
    let sh : Shared Screen := vw_screen (vw_sel_state "日本" 0 3) in
    vw_is sh 0 5 "日" && vw_is sh 0 6 "" && vw_is sh 0 7 "本" && vw_is sh 0 8 ""
        && vw_bg_is_selection sh 0 5 && vw_bg_is_selection sh 0 6
        && Bool.not (vw_bg_is_selection sh 0 7)
        && vw_reverse sh 0 7

// ── Clipping: a line wider than the viewport ─────────────────────────────

/// A line wider than the text area fills it exactly: 50 "a"s in the
/// 35-cell text area paint columns 5-39, the last visible cell an
/// "a". (The clip's own edge case -- a wide glyph that does not fit
/// whole -- is the next test.)
#[test]
def test_wide_line_fills_the_text_area : Bool :=
    let sh : Shared Screen := vw_screen (vw_state (String.repeat "a" 50)) in
    vw_is sh 0 34 "a" && vw_is sh 0 39 "a"

/// THE CLIP NEVER SPLITS A WIDE GLYPH: 18 日 (36 cells) in the
/// 35-cell text area paint seventeen of them (cells 5-38, the last
/// the 17th's continuation ""), and the 18th -- which would need
/// column 40 -- is left out, so column 39 stays a space.
#[test]
def test_clip_leaves_a_wide_glyph_whole : Bool :=
    let sh : Shared Screen := vw_screen (vw_state (String.repeat "日" 18)) in
    vw_is sh 0 5 "日" && vw_is sh 0 6 ""
        && vw_is sh 0 37 "日" && vw_is sh 0 38 ""
        && vw_is sh 0 39 " "

/// A SELECTION PAST THE CLIP PAINTS NOTHING: 50 "a"s with the
/// selection [45,50) -- entirely past the 35-cell text area -- paint
/// no bg anywhere in the row, and the caret (head 50, a cell past the
/// clip) paints no reverse anywhere either.
#[test]
def test_selection_past_the_clip_paints_nothing : Bool :=
    let sh : Shared Screen := vw_screen (vw_sel_state (String.repeat "a" 50) 45 50) in
    vw_no_selection_bg sh 0 0 && vw_no_reverse_in_row sh 0 0

/// A selection REACHING past the clip paints every visible cell it
/// covers: [0,50) over the 50 "a"s paints columns 5-39, and the caret
/// (head 50, past the clip) still paints nothing.
#[test]
def test_selection_reaching_past_the_clip_paints_the_window : Bool :=
    let sh : Shared Screen := vw_screen (vw_sel_state (String.repeat "a" 50) 0 50) in
    vw_bg_is_selection sh 0 5 && vw_bg_is_selection sh 0 39
        && vw_no_reverse_in_row sh 0 0

// ── Scrolling: the window keeps the caret visible ────────────────────────

/// FIRST_VISIBLE CLAMPS DOWN: a stored scroll below the head's line
/// pulls the window up to it. Fixture: 30 lines, head on line 0,
/// stored scroll 10 -> the window starts at 0.
#[test]
def test_scroll_clamps_down_to_the_head : Bool :=
    let st : EditorState := vw_type (vw_state (vw_lines 30)) [vw_key "g", vw_key "g"] in
    let clamped : EditorState := EditorState.with_scroll st 10 in
    I64.beq (View.first_visible clamped) 0

/// FIRST_VISIBLE CLAMPS UP: a head below the window pulls the window
/// down so the head's line is the LAST visible line. Fixture: 30
/// lines, head at line 25 (25 `j`s from the start), stored scroll 0,
/// height 9 -> the window starts at 17 (25 - 9 + 1), row 0 shows
/// "l17" and row 8 shows "l25" with the caret on its first cell.
#[test]
def test_scroll_clamps_up_to_the_head : Bool :=
    let st : EditorState := vw_type (vw_state (vw_lines 30)) (vw_js 25) in
    let sh : Shared Screen := vw_screen st in
    I64.beq (View.first_visible st) 17
        && vw_is sh 0 5 "l" && vw_is sh 8 5 "l"
        && vw_reverse sh 8 5

/// THE STORED SCROLL HOLDS when the head is inside the window: a
/// stored scroll of 3 with the head on line 5 keeps the window at 3.
#[test]
def test_scroll_holds_a_head_inside_the_window : Bool :=
    let st : EditorState := vw_type (vw_state (vw_lines 30)) (vw_js 5) in
    let scrolled : EditorState := EditorState.with_scroll st 3 in
    I64.beq (View.first_visible scrolled) 3

/// A terminal too short for text + status paints no rows: 1 row ->
/// `text_height` is 0, `first_visible` is 0, and the screen is the
/// status line alone (row 0).
#[test]
def test_tiny_terminal_paints_the_status_line_only : Bool :=
    let doc : Document := Document.with_language (Document.of_text "ab") "monad" in
    let st : EditorState := EditorState.init doc 1 40 in
    let sh : Shared Screen := vw_screen st in
    I64.beq (View.text_height 1) 0
        && vw_is sh 0 0 "n" && vw_is sh 0 1 "o"
        && vw_is sh 0 16 " " && vw_is sh 0 17 "1" && vw_is sh 0 18 ":" && vw_is sh 0 19 "1"

// ── The empty document ─────────────────────────────────────────────────────

/// AN EMPTY DOCUMENT paints its gutter ("   1"), an empty text row,
/// and the caret in the first text cell -- the editor's blank slate.
#[test]
def test_empty_document_paints_the_caret : Bool :=
    let sh : Shared Screen := vw_screen (vw_state "") in
    vw_is sh 0 3 "1" && vw_is sh 0 5 " "
        && vw_reverse sh 0 5
        && vw_is sh 9 17 "1" && vw_is sh 9 18 ":" && vw_is sh 9 19 "1"

// ── The rows API (the view's own geometry, unpainted) ─────────────────────

/// `View.rows` answers the visible window's `RowView`s: a 2-line
/// document in a 9-row window answers 2 rows, the first with its
/// line's number, content and byte span.
#[test]
def test_rows_window : Bool :=
    let doc : Document := vw_doc (vw_state "ab\ncd") in
    // The row list is read twice (the length, the first row), so it is
    // shared -- a `List` is deliberately not `Copy`.
    let rows : Shared (List RowView) := Shared.of (View.rows doc 0 9) in
    I64.beq (List.length (Shared.get rows)) 2
        && vw_row0_is_ab (Shared.get rows)

/// The first row's fields, through accessor defs (the record-pattern
/// hazard): line 0, text "ab", span [0,2).
def vw_row0_is_ab (rows : List RowView) : Bool :=
    match rows {
        List.cons one _ =>
            I64.beq (RowView.line_of one) 0
                && String.beq (RowView.text_of one) "ab"
                && I64.beq (RowView.start_of one) 0
                && I64.beq (RowView.stop_of one) 2,
        List.empty => false
    }

/// A window starting mid-document answers the lines from `first`:
/// line 1 ("cd") alone, for a 2-line document.
#[test]
def test_rows_start_mid_document : Bool :=
    let doc : Document := vw_doc (vw_state "ab\ncd") in
    let rows : Shared (List RowView) := Shared.of (View.rows doc 1 9) in
    I64.beq (List.length (Shared.get rows)) 1
        && vw_row0_is_cd (Shared.get rows)

/// The mid-document row's fields: line 1, text "cd", span [3,5).
def vw_row0_is_cd (rows : List RowView) : Bool :=
    match rows {
        List.cons one _ =>
            I64.beq (RowView.line_of one) 1
                && String.beq (RowView.text_of one) "cd"
                && I64.beq (RowView.start_of one) 3
                && I64.beq (RowView.stop_of one) 5,
        List.empty => false
    }

/// `View.row_segments` is the view's own painting pipeline, unpainted
/// screen: the caret (head 0) splits the keyword's first cell off as
/// its own segment, so the segments join back to the row's text and
/// the first segment is the keyword's palette reversed.
#[test]
def test_row_segments_pipeline : Bool :=
    let doc : Document := vw_doc (vw_state "let x = 1") in
    let shared : Shared Document := Shared.of doc in
    match View.rows (Shared.get shared) 0 9 {
        List.cons one _ =>
            let segs : Shared (List TextSegment) :=
                Shared.of (View.row_segments (Shared.get shared) one) in
            String.beq (vw_seg_join (Shared.get segs)) "let x = 1"
                && vw_first_seg_is_caret_keyword (Shared.get segs),
        List.empty => false
    }

/// The segments' texts, concatenated -- the round-trip witness that
/// the pipeline loses no bytes.
#[terminating]
def vw_seg_join (segs : List TextSegment) : String :=
    match segs {
        List.empty => "",
        List.cons one rest => String.concat one.text (vw_seg_join rest)
    }

/// The first segment is the caret-split keyword cell: text "l",
/// keyword fg, bold, reverse -- the caret's merge onto the palette.
def vw_first_seg_is_caret_keyword (segs : List TextSegment) : Bool :=
    match segs {
        List.cons first _ => vw_seg_is_caret_keyword first,
        List.empty => false
    }

/// One segment's fields, matched once each (the record-pattern
/// discipline).
def vw_seg_is_caret_keyword (seg : TextSegment) : Bool :=
    match seg {
        { text, style, .. } =>
            String.beq text "l" && vw_style_is_caret_keyword style
    }

/// The caret-split cell's style: the keyword palette's fg, bold, and
/// the caret's reverse -- all three merged.
def vw_style_is_caret_keyword (st : TextStyle) : Bool :=
    match st {
        { fg, bold, reverse, .. } =>
            vw_fg_is_keyword fg && bold && reverse
    }

/// The keyword palette's foreground, read once.
def vw_fg_is_keyword (fg : Option Color) : Bool :=
    let kw : TextStyle := Highlight.style TokenKind.keyword in
    match kw.fg {
        Option.some want => fg == Option.some want,
        Option.none => false
    }
