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
    EditorState.with_scroll, EditorState.with_mode,
    EditorState.with_picker_files, EditorState.rows_of, EditorState.cols_of}
use lib::selection {Selections.span, Selections.cursor}
use lib::types {Mode, Rope}
use lib::rope {Rope.bytes}
use lib::view {View.view, View.rows, View.row_segments, View.first_visible,
    View.left_col,
    View.text_height, View.gutter_label, View.selection_style,
    RowView, RowView.line_of, RowView.text_of, RowView.start_of, RowView.stop_of}
use lib::highlight {TokenKind, Highlight.style}
use lib::commands {update}
use tui::types {Screen, Cell, TextStyle, TextSegment, Key}
use tui::core {mk_screen, mk_rect, screen_get_cell, style_default}
use tui::render {render}
use tui::widget {Widget}
use std::ansi {Color}
use std::io {IO.current_time}
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
///
/// THE DEFAULT STYLE IS BOUND TO A LOCAL FIRST, exactly as `vw_bg_is_selection`
/// above binds `View.selection_style`: a projection straight off a cross-module
/// def reference (`style_default.bg`) is the recorded `(f x).field` hazard, and
/// the Rust host reads it as the qualified name `style_default.bg` and reports
/// `unbound variable`. The self-hosted host lowers it, which is why only the
/// Rust corpus check catches this shape -- the bound local is the remedy both
/// hosts accept.
def vw_bg_is_none (sh : Shared Screen) (row : I64) (col : I64) : Bool :=
    let st : TextStyle := vw_style sh row col in
    let base : TextStyle := style_default in
    st.bg == base.bg

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

/// SOME cell in row `row` is reverse video -- the existential the caret
/// tests assert: "the caret is painted somewhere on this row". A caret
/// past the text area's right margin paints NO cell at all, and only a
/// positive probe can tell that apart from "painted at the wrong place".
#[terminating]
def vw_any_reverse (sh : Shared Screen) (row : I64) (col : I64) : Bool :=
    if Bool.not (col < 40)
    then false
    else Bool.or (vw_reverse sh row col) (vw_any_reverse sh row (col + 1))

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

/// `n` lines of about 25 bytes each, "l5 = foo bar baz qux", one per line
/// with its terminator. THE LINE LENGTH IS THE POINT: the chunker targets
/// 1 KiB, so ~25-byte lines put about forty lines in the FIRST leaf and the
/// rest past it -- which is the arrangement a real source file has, and the
/// only one in which "a row past the first chunk" is a case that can be
/// reached at all. A 4-byte-line fixture would keep a hundred lines inside
/// leaf 0 and quietly assert nothing.
#[terminating]
def vw_lines_x (n : I64) : String :=
    vw_lines_x_go 0 n ""

/// The recursive half of the chunked fixture builder: "l" ++ the number ++
/// the fixed tail, so every line is at least 22 bytes.
#[terminating]
def vw_lines_x_go (i : I64) (n : I64) (acc : String) : String :=
    if Bool.not (i < n)
    then acc
    else vw_lines_x_go (i + 1) n
        (String.concat acc
            (String.concat "l"
                (String.concat (I64.to_string i)
                    (String.concat " = foo bar baz qux" "\n"))))

/// `n` `j` keys, for driving the head down.
#[terminating]
def vw_js (n : I64) : List Key :=
    if Bool.not (0 < n)
    then List.empty
    else List.cons (vw_key "j") (vw_js (n - 1))

/// `n` `l` keys, for driving the head right -- the horizontal-scroll
/// tests' dial.
#[terminating]
def vw_ls (n : I64) : List Key :=
    if Bool.not (0 < n)
    then List.empty
    else List.cons (vw_key "l") (vw_ls (n - 1))

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

/// COMMAND MODE'S ROW IS THE LINE, NOT THE MODE NAME. This used to assert
/// "command" at the row's start -- what the status line prints when it reads
/// the mode table. Phase 5 replaced it: while the editor is on a `:` line,
/// the row shows the line being typed (the section below), because a user
/// typing a command needs to see the command, and the row has no space for
/// both. Reaching command mode is still a distinct state, so the pin stays:
/// the row is no longer "normal" either.
#[test]
def test_command_mode_status_name : Bool :=
    let sh : Shared Screen := vw_screen (vw_type (vw_state "ab") [vw_key ":"]) in
    vw_is sh 9 0 ":" && Bool.not (vw_is sh 9 0 "n")

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

/// A SELECTION PAST THE RIGHT MARGIN PULLS THE WINDOW: 50 "a"s with the
/// selection [45,50) -- entirely past the 35-cell text area -- is shown
/// by SCROLLING to it, not by painting nothing.
///
/// This replaces a test that pinned the old truncation ("a selection past
/// the clip paints nothing"). Truncation made a real, selected range
/// invisible, which is indistinguishable from "the selection was lost" --
/// the same class of defect as the caret that painted no cell. The window
/// now follows the caret (head 50 -> columns 15..50), so the covered cells
/// paint inside it and the caret on the last one is reverse video.
#[test]
def test_selection_past_the_margin_scrolls_into_view : Bool :=
    let st : EditorState := vw_sel_state (String.repeat "a" 50) 45 50 in
    let sh : Shared Screen := vw_screen st in
    // head col 50, text width 35 -> left = 50 - 35 + 1 = 16.
    // head col 50, text width 35 -> left = 50 - 35 + 1 = 16, so the
    // window shows document columns 16..50 at screen columns 5..39.
    // The selection [45,50) therefore lands at screen 34..38, and the
    // caret (head 50, appended past the text) sits on screen 39.
    I64.beq (View.left_col st) 16
        && vw_bg_is_selection sh 0 34 && vw_bg_is_selection sh 0 38
        && Bool.not (vw_bg_is_selection sh 0 5)
        && vw_reverse sh 0 39

/// A selection STARTING before the window still paints its visible part:
/// [0,50) over the 50 "a"s, window at 0, paints columns 5-39 -- and the
/// caret (head 50) pulls the window only far enough to show itself.
#[test]
def test_selection_reaching_past_the_margin_paints_the_window : Bool :=
    let st : EditorState := vw_sel_state (String.repeat "a" 50) 0 50 in
    let sh : Shared Screen := vw_screen st in
    // The same window (head 50 -> left 16), but the selection covers the
    // whole line, so screen columns 5..38 are all covered and the caret
    // is on 39.
    I64.beq (View.left_col st) 16
        && vw_bg_is_selection sh 0 5 && vw_bg_is_selection sh 0 38
        && vw_reverse sh 0 39

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

// ── Horizontal scrolling: the caret is never painted past the margin ─────

/// THE BUG THIS SECTION EXISTS FOR: the text area is 35 cells (40 minus
/// the 5-cell gutter), so a caret whose column is 35 or more lands in no
/// painted cell and the terminal shows no caret at all -- the head is
/// real (`l` moved it, the status line counts it) but invisible.
///
/// Fixture: 60 "C"s, head at column 50 (50 `l` presses). The caret must
/// paint SOMEWHERE on row 0, and the status line must agree it is at
/// 1:51 -- so this cannot pass by the head failing to move.
#[test]
def test_caret_visible_past_the_margin : Bool :=
    let sh : Shared Screen := vw_screen (vw_type (vw_state (String.repeat "C" 60)) (vw_ls 50)) in
    vw_any_reverse sh 0 0
        && String.contains (vw_status_text sh) "1:51"

/// LEFT_COL CLAMPS LEFT: a caret left of the stored window pulls it left,
/// to the caret's own column. Fixture: a 60-char line, head at column 20
/// (20 `l`), stored hscroll 40 -> the window starts at the caret's column
/// rather than leaving the caret off the left edge.
#[test]
def test_left_col_clamps_left_to_the_caret : Bool :=
    let st : EditorState := vw_type (vw_state (String.repeat "C" 60)) (vw_ls 20) in
    let shifted : EditorState := EditorState.with_hscroll st 40 in
    I64.beq (View.left_col shifted) 20

/// LEFT_COL HOLDS when the caret is inside the window: a stored window of
/// 10 with the head at column 30 (30 - 10 = 20, inside 35 cells) keeps 10.
#[test]
def test_left_col_holds_a_caret_inside_the_window : Bool :=
    let st : EditorState := vw_type (vw_state (String.repeat "C" 60)) (vw_ls 30) in
    let shifted : EditorState := EditorState.with_hscroll st 10 in
    I64.beq (View.left_col shifted) 10

/// A SHORT LINE NEVER SCROLLS: with the head at column 0 on a line that
/// fits, the window is 0 -- and a stored hscroll left over from a longer
/// line is pulled back to 0 by the caret's own clamp.
#[test]
def test_left_col_is_zero_when_the_line_fits : Bool :=
    let st : EditorState := vw_state "short" in
    let shifted : EditorState := EditorState.with_hscroll st 40 in
    I64.beq (View.left_col st) 0 && I64.beq (View.left_col shifted) 0

/// THE CARET IS ON THE LEFT EDGE when it is exactly one text-area past
/// the window's right edge: caret col 35 in a 35-cell area -> the window
/// moves to 1, so the caret sits on the last cell rather than one past it.
#[test]
def test_left_col_puts_a_caret_at_the_right_edge_last : Bool :=
    let st : EditorState := vw_type (vw_state (String.repeat "C" 60)) (vw_ls 35) in
    I64.beq (View.left_col st) 1

// ── The command line ─────────────────────────────────────────────────────
//
// A `:` LINE IS PAINTED, not just stored: the mode's payload holds the typed
// text, and without this the user types blind -- which is indistinguishable
// from a dead keyboard. The row is `:` plus the text plus a reversed caret,
// and it TAKES PRECEDENCE over the status message (the position, a report)
// because the user is in the middle of typing one.

/// `:` PAINTS AS A LINE WITH A CARET: after `:` the status row starts with
/// the colon and has a reversed cell right after it -- the empty line's
/// caret. The mode name ("command") must NOT be there, which is what
/// separates "a line is being edited" from "the status line names the mode".
#[test]
def test_command_line_paints_a_colon_and_caret : Bool :=
    let st : EditorState := vw_type (vw_state "ab") [vw_key ":"] in
    let sh : Shared Screen := vw_screen st in
    vw_is sh 9 0 ":" && vw_reverse sh 9 1 && Bool.not (vw_is sh 9 2 "c")

/// THE TYPED TEXT IS SHOWN: `:w` paints ":w" at columns 0-1 with the caret
/// on column 2. This is the assertion that makes `:` usable -- the line the
/// user typed is the line the screen shows.
#[test]
def test_command_line_paints_the_typed_text : Bool :=
    let st : EditorState := vw_type (vw_state "ab") [vw_key ":", vw_key "w", vw_key "q"] in
    let sh : Shared Screen := vw_screen st in
    vw_is sh 9 0 ":" && vw_is sh 9 1 "w" && vw_is sh 9 2 "q"
        && vw_reverse sh 9 3

/// A MESSAGE DOES NOT DISPLACE THE LINE: the status report from an earlier
/// command is still in the state, but while the editor is on a `:` line the
/// row is the line. (The other order would hide what the user is typing.)
#[test]
def test_command_line_wins_over_a_status_message : Bool :=
    let typed : EditorState := EditorState.with_status (vw_state "ab") "wrote /tmp/x" in
    let st : EditorState := vw_type typed [vw_key ":", vw_key "w"] in
    let sh : Shared Screen := vw_screen st in
    vw_is sh 9 0 ":" && vw_is sh 9 1 "w" && Bool.not (vw_is sh 9 0 "w")

/// ESCAPE PUTS THE STATUS LINE BACK: after cancelling, the row is the mode
/// and position again -- `normal`, not a stranded `:`.
#[test]
def test_cancelling_the_command_line_restores_the_status : Bool :=
    let st : EditorState :=
        vw_type (vw_state "ab") [vw_key ":", vw_key "w", Key.escape] in
    let sh : Shared Screen := vw_screen st in
    vw_is sh 9 0 "n" && vw_is sh 9 1 "o" && vw_is sh 9 2 "r" && vw_is sh 9 3 "m"

// ── A document past the first chunk ──────────────────────────────────────
//
// THE BUG THIS SECTION EXISTS FOR: `Rope.line_start` answered LEAF-RELATIVE
// offsets for every line past the first 1 KiB chunk, so the view's rows past
// that point showed the wrong text -- and one of them was handed the REST OF
// THE DOCUMENT as its "line" (measured: 636 781 bytes of a 638 KB file),
// which the view then styled on every frame at 2.4 s per frame.
//
// The fixture is 500 lines of ~25 bytes (`vw_lines_x`), so the first 1 KiB
// leaf holds only about forty of them and the window below -- which starts
// at line 92 -- is entirely past the first chunk. Every assertion is a
// rendered CELL, so a wrong span shows up as a wrong glyph rather than an
// offset a reader has to check by hand.
//
// The gutter is five cells: four right-aligned digits then a space, so the
// text always starts at column 5. Line 100's label is " 101 " (columns 0-3
// carry "101", column 4 the space) and every line's text is
// "l<number> = foo bar baz qux".

/// LINE 100 PAINTS AS ITSELF in a chunked document. The caret is on line 100
/// (100 `j` presses), the 9-row text area clamps the window to start at line
/// 92, so line 100 is row 8: gutter " 101" and text "l100 = foo bar...".
#[test]
def test_row_past_the_first_chunk_paints_its_own_line : Bool :=
    let st : EditorState := vw_type (vw_state (vw_lines_x 500)) (vw_js 100) in
    let sh : Shared Screen := vw_screen st in
    I64.beq (View.first_visible st) 92
        && vw_is sh 8 1 "1" && vw_is sh 8 2 "0" && vw_is sh 8 3 "1"
        && vw_is sh 8 5 "l" && vw_is sh 8 6 "1" && vw_is sh 8 7 "0" && vw_is sh 8 8 "0"
        && vw_is sh 8 9 " " && vw_is sh 8 10 "="
        && vw_reverse sh 8 5

/// THE FIRST ROW OF A SCROLLED WINDOW IS THE LINE THE WINDOW NAMES, too: row
/// 0 shows line 92 -- gutter "  93" (the label is 1-based) and text "l92" --
/// rather than the start of the document.
#[test]
def test_scrolled_window_first_row_is_the_window_line : Bool :=
    let st : EditorState := vw_type (vw_state (vw_lines_x 500)) (vw_js 100) in
    let sh : Shared Screen := vw_screen st in
    vw_is sh 0 2 "9" && vw_is sh 0 3 "3"
        && vw_is sh 0 5 "l" && vw_is sh 0 6 "9" && vw_is sh 0 7 "2"
        && vw_is sh 0 8 " " && vw_is sh 0 9 "="

/// THE LAST WINDOW ROW SHOWS THE NEXT LINE, not the last one: row 8 is line
/// 100 and row 7 is line 99 ("l99"), so the rows are distinct lines in
/// order. Under the leaf-relative index every row past the first chunk
/// carried a slice of the wrong bytes, which made neighbouring rows repeat
/// each other's text.
#[test]
def test_neighbouring_rows_show_neighbouring_lines : Bool :=
    let st : EditorState := vw_type (vw_state (vw_lines_x 500)) (vw_js 100) in
    let sh : Shared Screen := vw_screen st in
    vw_is sh 7 5 "l" && vw_is sh 7 6 "9" && vw_is sh 7 7 "9"
        && vw_is sh 7 8 " "

/// A ROW'S TEXT IS ITS OWN LINE'S BYTES: the trailing line of a chunked
/// document (line 500, after the final `\n`) is empty, with an empty span.
/// Under the old line index the rows past the first chunk carried the rest
/// of the buffer, so `stop - start` was the file size rather than zero.
#[test]
def test_rows_in_a_chunked_document_are_their_lines : Bool :=
    let doc : Document := vw_doc (vw_state (vw_lines_x 500)) in
    let rows : Shared (List RowView) := Shared.of (View.rows doc 500 3) in
    I64.beq (List.length (Shared.get rows)) 1
        && vw_row_is_trailing_line (Shared.get rows)

/// The chunked fixture's trailing row: line 500, text "", span empty.
def vw_row_is_trailing_line (rows : List RowView) : Bool :=
    match rows {
        List.cons one _ =>
            I64.beq (RowView.line_of one) 500
                && String.beq (RowView.text_of one) ""
                && I64.beq (RowView.stop_of one) (RowView.start_of one),
        List.empty => false
    }

// ── The frame is viewport-bounded, not document-bounded ──────────────────
//
// THE 2.4 s FRAME. `View.view` on a 20 000-line document used to take 2.4 s
// against 5 ms on a 1 000-line one -- it was not the viewport that was slow,
// it was that `Rope.line_start` handed one row the REST OF THE DOCUMENT to
// style (see the section above). With that fixed the frame is ~6 ms on both,
// and these tests hold it there.
//
// A RATIO, not a wall-clock bound: an absolute millisecond threshold is
// flaky on a loaded machine, while "forty times the document must not cost
// forty times the frame" is exactly the property that broke. The bound is 8
// with the two sizes 40x apart, so a genuinely viewport-bounded frame (~1x)
// passes with room to spare and a document-proportional one (~40x) fails.

/// The frame cost is INDEPENDENT of the document's size: building the view
/// of a 20 000-line document must cost about what a 500-line one costs.
#[test]
def test_view_is_viewport_bounded : IO Bool := do {
    let small : EditorState := vw_state (vw_lines_x 500);
    let large : EditorState := vw_state (vw_lines_x 20000);
    let _ <- vw_warm small;
    let t1 <- IO.current_time;
    let _ <- vw_frame small;
    let t2 <- IO.current_time;
    let _ <- vw_frame large;
    let t3 <- IO.current_time;
    let bounded : Bool := vw_ratio_enough (vw_elapsed t1 t2) (vw_elapsed t2 t3);
    return bounded
}

/// A SECOND DIMENSION: the frame cost with the caret at the END of a large
/// document must not exceed the cost with it at the top.
///
/// This is the dimension the leaf-relative line index broke hardest: every
/// line past the first 1 KiB chunk was mis-indexed, so the DEEPER the caret
/// sat the more of the document a row swallowed. The caret is placed by byte
/// offset (`Selections.cursor` at the buffer's end) rather than by pressing
/// `j` 19 990 times, so the fixture costs one rope build instead of twenty
/// thousand update steps.
#[test]
def test_view_cost_does_not_grow_with_the_caret_depth : IO Bool := do {
    let top : EditorState := vw_state (vw_lines_x 20000);
    let deep : EditorState := vw_state_at_end (vw_lines_x 20000);
    let _ <- vw_warm top;
    let t1 <- IO.current_time;
    let _ <- vw_frame top;
    let t2 <- IO.current_time;
    let _ <- vw_frame deep;
    let t3 <- IO.current_time;
    let bounded : Bool := vw_ratio_enough (vw_elapsed t1 t2) (vw_elapsed t2 t3);
    return bounded
}

/// A state over `text` with the cursor at the buffer's END -- the fixture
/// the depth test needs, built without a keystroke per line.
def vw_state_at_end (text : String) : EditorState :=
    // The document is read twice (the rope, then the selection swap) and is
    // not `Copy` (its history holds a `BTreeMap`), so one handle serves both
    // -- the affine rule's own remedy.
    let base : Shared Document :=
        Shared.of (Document.with_language (Document.of_text text) "monad") in
    let rope : Rope := ply_rope_of (Shared.get base) in
    let doc : Document :=
        Document.with_selections (Shared.get base) (Selections.cursor (Rope.bytes rope)) in
    EditorState.init doc 10 40

/// The document's rope, read once (the accessor `view.mo` also has, private
/// there -- a test needs its own).
def ply_rope_of (doc : Document) : Rope :=
    match doc { { rope, .. } => rope }

/// One warm-up frame, so neither timed run pays for whatever the first call
/// allocates lazily.
def vw_warm (st : EditorState) : IO Unit := do {
    let _w : Widget := View.view st;
    return unit
}

/// Build the view and render it -- one whole frame, which is what the cost
/// under test actually is.
def vw_frame (st : EditorState) : IO Unit := do {
    let sh : Shared Screen := vw_screen st;
    let _n : I64 := vw_char_count sh 0 0 0;
    return unit
}

/// A cheap read of the rendered screen, so the frame's result is not
/// discarded before it is used (a dead binding could be optimised away).
#[terminating]
def vw_char_count (sh : Shared Screen) (row : I64) (col : I64) (acc : I64) : I64 :=
    if Bool.not (row < 10)
    then acc
    else if Bool.not (col < 40)
    then vw_char_count sh (row + 1) 0 acc
    else vw_char_count sh row (col + 1) (acc + String.length (vw_char sh row col))

/// The elapsed milliseconds between two readings, floored at 1 so the ratio
/// stays meaningful for a sub-millisecond measurement (a floor can only make
/// the assertion stricter).
def vw_elapsed (a : I64) (b : I64) : I64 :=
    let d : I64 := b - a in
    if d < 1 then 1 else d

/// Is `big` under 8x `small`? The two documents are 40x apart, so a
/// viewport-bounded frame (~1x) passes and a document-proportional one
/// (~40x) fails, with room for noise either way.
def vw_ratio_enough (small_ms : I64) (big_ms : I64) : Bool :=
    big_ms < small_ms * 8

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

// ── The `/` search line ──────────────────────────────────────────────────
//
// THE `/` LINE IS THE `:` LINE WITH ANOTHER SIGIL, and it is pinned the same
// way: the prompt, the typed query, and the caret's reversed cell. What it
// is NOT allowed to be is the status row -- a query you cannot see is a
// query you cannot correct.

/// The `/` line shows its own prompt and the query typed so far, and the
/// status message underneath is not what paints the row.
#[test]
def test_search_line_renders_prompt_and_query : Bool :=
    String.contains (vw_status_text (vw_screen (vw_search_st "foo"))) "/foo"

/// An EMPTY search line still shows the prompt -- the row is the line, not a
/// message, so `/` then nothing is a visible `/` and a caret to type at.
#[test]
def test_empty_search_line_shows_the_prompt : Bool :=
    String.contains (vw_status_text (vw_screen (vw_search_st ""))) "/"

/// The search line paints a caret -- the reversed cell after the query, in
/// the same column rule the `:` line follows (`prompt ++ query`, then the
/// caret), so typing blind is not possible on either.
#[test]
def test_search_line_paints_a_caret : Bool :=
    let sh : Shared Screen := vw_screen (vw_search_st "ab") in
    vw_reverse sh 9 3 && Bool.not (vw_reverse sh 9 2)

/// A state on the `/` line with `query` typed. The mode is set through the
/// state's own builder, so the fixture does not depend on keystroke
/// decoding.
def vw_search_st (query : String) : EditorState :=
    vw_set_search (vw_state "abc") query

/// `Mode.search` as a value, in its own def -- a `Mode` constructor spelled
/// directly in a test body is the shadowing hazard this file's header
/// records (a local named `search` would meet the constructor's name).
def vw_set_search (st : EditorState) (query : String) : EditorState :=
    EditorState.with_mode st (Mode.search query)

// ── The picker's frame ───────────────────────────────────────────────────

/// The picker's body is its list: the header names the directory, and the
/// candidates paint below it -- the buffer's text is GONE while the picker is
/// open, which is what makes it a picker rather than a status message.
#[test]
def test_picker_takes_the_body : Bool :=
    let st : EditorState := vw_picker_state ["a.mo", "b.mo"] "" 0 in
    String.contains (vw_row_joined (vw_screen st) 0) "pick a file"
        && String.contains (vw_row_joined (vw_screen st) 1) "a.mo"
        && String.contains (vw_row_joined (vw_screen st) 2) "b.mo"

/// The highlighted candidate's row is REVERSED, and its neighbors' are not --
/// an unhighlighted list would make Enter's choice invisible.
#[test]
def test_picker_highlights_one_row : Bool :=
    let sh : Shared Screen := vw_screen (vw_picker_state ["a.mo", "b.mo"] "" 1) in
    vw_reverse sh 2 0 && Bool.not (vw_reverse sh 1 0)

/// The picker's filter row is the status line, with the match count: a
/// filter that hides everything says so rather than leaving an empty list to
/// interpret.
#[test]
def test_picker_filter_row_counts_matches : Bool :=
    let st : EditorState := vw_picker_state ["a.mo", "b.mo"] "a" 0 in
    String.contains (vw_status_text (vw_screen st)) "1/2"

/// A state in the picker over `files`, filtered by `query`, highlighting
/// `sel`. The listing arrives through the state's own builder, because the
/// real one arrives as `EditorMsg.picker_files` from `IO.list_dir`.
def vw_picker_state (files : List String) (query : String) (sel : I64) : EditorState :=
    let base : EditorState := EditorState.with_picker_files (vw_state "abc") "" files in
    vw_set_picker base query sel

/// `Mode.picker` as a value.
def vw_set_picker (st : EditorState) (query : String) (sel : I64) : EditorState :=
    EditorState.with_mode st (Mode.picker query sel)

/// Row `row`'s chars, folded into a string (the 40-column fixture width).
#[terminating]
def vw_row_joined (sh : Shared Screen) (row : I64) : String :=
    vw_row_text_at sh row 0 ""

#[terminating]
def vw_row_text_at (sh : Shared Screen) (row : I64) (col : I64) (acc : String) : String :=
    if Bool.not (col < 40)
    then acc
    else vw_row_text_at sh row (col + 1) (String.concat acc (vw_char sh row col))
