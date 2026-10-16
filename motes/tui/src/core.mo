// Terminal UI Library - Core Functions
//
// The value types themselves live in `types.mo` (where their `#[derive]`
// instances expand -- see that file's header for why the split is
// load-bearing). This module holds the functions over them: style
// helpers, screen accessors, rectangle predicates, and `Screen`'s
// hand-rolled `BEq`.

// `Color` and the SGR-code builders come from `std::ansi`. They used to be
// copied in here, because this module's style type was also called `Style` and
// `std::ansi`'s attribute-only `type Style` defeated it once both were loaded:
// in the flattened whole-program namespace a `{ ... }` struct literal resolved
// against the UNION of the two types' constructors and was rejected. Calling
// this one `TextStyle` removes the collision outright, and with it the reason
// for the copy.
use std::ansi { Color, color_fg_code, color_bg_code }

// The types (and their derived `BEq`/`Lens` instances) come from the mote's
// types-only module.
use lib::types { Rect, TextStyle, Cell, LayoutSize, MouseButton, Key, MouseEvent, Event, Screen, CellDelta }

use init::optics {view, set, over}

/// The style with no colors or attributes set.
//
// Fields are listed explicitly (not `{ }`) to work around a compiler bug:
// a struct literal that omits any field with a default value currently
// panics the checker (`raise_core.rs`, "Free(Atom(_)) is missing from
// atom_paths") instead of substituting the default.
pub def style_default : TextStyle :=
    { fg := none, bg := none, bold := false, dim := false, italic := false, underline := false, strikethrough := false }

/// Layer `top` on top of `base`: colors in `top` win when set, otherwise
/// `base`'s colors are kept; attribute flags are OR'd together.
pub def style_merge (base : TextStyle) (top : TextStyle) : TextStyle :=
    {
        fg := option_or top.fg base.fg,
        bg := option_or top.bg base.bg,
        bold := base.bold || top.bold,
        dim := base.dim || top.dim,
        italic := base.italic || top.italic,
        underline := base.underline || top.underline,
        strikethrough := base.strikethrough || top.strikethrough
    }

/// `preferred` if set, else `fallback`.
def option_or (preferred : Option A) (fallback : Option A) : Option A :=
    match preferred {
        some _ => preferred,
        none => fallback
    }

def option_map (f : A -> B) (opt : Option A) : Option B :=
    match opt {
        some x => Option.some (f x),
        none => Option.none
    }

def bool_code (flag : Bool) (code : String) : Option String :=
    if flag then Option.some code else Option.none

/// Append `next`'s SGR code onto `acc`, `;`-separated, skipping `none`.
def append_code (acc : String) (next : Option String) : String :=
    match next {
        none => acc,
        some code => if acc == "" then code else acc ++ ";" ++ code
    }

/// Renders a `TextStyle` as a single combined ANSI SGR escape sequence, e.g.
/// bold + red fg => `"\u{1b}[31;1m"` -- colors first, then the attribute
/// flags, in the order the codes are appended below. Returns `""` when
/// nothing is set, which means a caller EMITTING this to a terminal has to
/// send its own reset; see `render.mo`'s `apply_one`.
pub def style_to_ansi (s : TextStyle) : String :=
    let c0 := append_code "" (option_map color_fg_code s.fg) in
    let c1 := append_code c0 (option_map color_bg_code s.bg) in
    let c2 := append_code c1 (bool_code s.bold "1") in
    let c3 := append_code c2 (bool_code s.dim "2") in
    let c4 := append_code c3 (bool_code s.italic "3") in
    let c5 := append_code c4 (bool_code s.underline "4") in
    let codes := append_code c5 (bool_code s.strikethrough "9") in
    if codes == "" then "" else "\u{1b}[" ++ codes ++ "m"

/// Hand-rolled (not generic `BEq (List A)`): dispatch to a custom element
/// type's `BEq` instance through the generic `List`/`Option` instances is
/// unreliable at runtime (see the equivalent note in `lang/json.mo`).
def cell_list_beq (a b : List Cell) : Bool :=
    match a {
        empty => match b { empty => true, _ => false },
        cons ha ta => match b {
            cons hb tb => ha == hb && cell_list_beq ta tb,
            _ => false
        }
    }

def row_list_beq (a b : List (List Cell)) : Bool :=
    match a {
        empty => match b { empty => true, _ => false },
        cons ha ta => match b {
            cons hb tb => cell_list_beq ha hb && row_list_beq ta tb,
            _ => false
        }
    }

def Screen.beq (a b : Screen) : Bool :=
    a.rows == b.rows && a.cols == b.cols && row_list_beq a.row_cells b.row_cells

instance BEq Screen {
    def beq (a b : Screen) : Bool := Screen.beq a b
}

// ==================== Helper Functions ====================

/// Create a list by replicating a value n times
#[terminating]
def List.replicate (n : I64) (value : A) : List A :=
    if n < 1
    then List.empty
    else List.cons value (List.replicate (n - 1) value)

/// Create a list of lists (2D) by replicating a value for rows x cols
#[terminating]
def screen_cells (rows : I64) (cols : I64) (value : Cell) : List (List Cell) :=
    if rows < 1
    then List.empty
    else List.cons (List.replicate cols value) (screen_cells (rows - 1) cols value)

/// Create an empty screen of given dimensions
pub def empty_screen (rows : I64) (cols : I64) : Screen :=
    let default_cell := mk_cell " " in
    { rows := rows, cols := cols, row_cells := screen_cells rows cols default_cell }

/// Create a cell with the given character and default style
pub def mk_cell (char : String) : Cell :=
    { char := char, style := style_default }

/// Replace the element at `index` (0-indexed); unchanged if out of range.
/// Index-first to match `List.get`.
def List.set_at {A : Type} (index : I64) (value : A) (l : List A) : List A :=
    match l {
        empty => List.empty,
        cons head tail =>
            if index == 0
            then List.cons value tail
            else List.cons head (List.set_at (index - 1) value tail)
    }

/// Get the cell at a specific position
pub def screen_get_cell (screen : Screen) (row : I64) (col : I64) : Option Cell :=
    if row < 0 || Bool.not (row < screen.rows) || col < 0 || Bool.not (col < screen.cols)
    then Option.none
    else
        match List.get row screen.row_cells {
            some cells => List.get col cells,
            none => Option.none
        }

/// Set the cell at a specific position
pub def screen_set_cell (screen : Screen) (row : I64) (col : I64) (cell : Cell) : Screen :=
    if row < 0 || Bool.not (row < screen.rows) || col < 0 || Bool.not (col < screen.cols)
    then screen
    else
        let current_row := Option.get_or_default List.empty (List.get row screen.row_cells) in
        let new_row := List.set_at col cell current_row in
        let new_rows := List.set_at row new_row screen.row_cells in
        { screen with row_cells := new_rows }

/// Check if two rectangles intersect
pub def rect_intersects (a : Rect) (b : Rect) : Bool :=
    a.x < b.x + b.width && a.x + a.width > b.x && a.y < b.y + b.height && a.y + a.height > b.y

/// Check if a rectangle contains a point
pub def rect_contains (r : Rect) (x : I64) (y : I64) : Bool :=
    Bool.not (x < r.x) && x < r.x + r.width && Bool.not (y < r.y) && y < r.y + r.height

/// Clamp a value between min and max
def clamp (value : I64) (min : I64) (max : I64) : I64 :=
    if value < min then min else if value > max then max else value

/// Create a rectangle from position and size
pub def mk_rect (x : I64) (y : I64) (w : I64) (h : I64) : Rect :=
    { x := x, y := y, width := w, height := h }

/// Create a screen of given dimensions
pub def mk_screen (rows : I64) (cols : I64) : Screen :=
    empty_screen rows cols

// ==================== Tests ====================

#[test]
def test_rect_intersects_true : Bool :=
    rect_intersects (mk_rect 0 0 10 10) (mk_rect 5 5 10 10)

#[test]
def test_rect_intersects_false : Bool :=
    Bool.not (rect_intersects (mk_rect 0 0 10 10) (mk_rect 20 20 5 5))

#[test]
def test_rect_contains_inside : Bool :=
    rect_contains (mk_rect 0 0 10 10) 5 5

#[test]
def test_rect_contains_edge_excluded : Bool :=
    Bool.not (rect_contains (mk_rect 0 0 10 10) 10 10)

#[test]
def test_clamp_within_range : Bool :=
    clamp 5 0 10 == 5

#[test]
def test_clamp_below_min : Bool :=
    clamp (0 - 5) 0 10 == 0

#[test]
def test_clamp_above_max : Bool :=
    clamp 15 0 10 == 10

#[test]
def test_mk_screen_in_range_cell_is_space : Bool :=
    match screen_get_cell (mk_screen 3 4) 0 0 {
        some cell => cell.char == " ",
        none => false
    }

#[test]
def test_screen_get_cell_row_out_of_range_is_none : Bool :=
    match screen_get_cell (mk_screen 3 4) 3 0 {
        some _ => false,
        none => true
    }

#[test]
def test_screen_get_cell_negative_index_is_none : Bool :=
    match screen_get_cell (mk_screen 3 4) (0 - 1) 0 {
        some _ => false,
        none => true
    }

#[test]
def test_screen_set_get_roundtrip : Bool :=
    let screen := screen_set_cell (mk_screen 2 2) 0 1 (mk_cell "x") in
    match screen_get_cell screen 0 1 {
        some cell => cell.char == "x",
        none => false
    }

#[test]
def test_screen_set_cell_does_not_affect_other_cells : Bool :=
    let screen := screen_set_cell (mk_screen 2 2) 0 1 (mk_cell "x") in
    match screen_get_cell screen 0 0 {
        some cell => cell.char == " ",
        none => false
    }

#[test]
def test_style_merge_fg_override_wins : Bool :=
    let base : TextStyle := { style_default with bold := true } in
    let top : TextStyle := { style_default with fg := some Color.red, dim := true } in
    let merged : TextStyle := style_merge base top in
    match merged.fg {
        some c => c == Color.red,
        none => false
    }

#[test]
def test_style_merge_bools_are_ored : Bool :=
    let base : TextStyle := { style_default with bold := true } in
    let top : TextStyle := { style_default with dim := true } in
    let merged : TextStyle := style_merge base top in
    merged.bold && merged.dim

#[test]
def test_style_merge_keeps_base_fg_when_top_unset : Bool :=
    let base : TextStyle := { style_default with fg := some Color.green } in
    let merged : TextStyle := style_merge base style_default in
    match merged.fg {
        some c => c == Color.green,
        none => false
    }

#[test]
def test_style_to_ansi_empty_style_is_empty_string : Bool :=
    style_to_ansi style_default == ""

#[test]
def test_style_to_ansi_bold_red_combines_one_sequence : Bool :=
    // The `: TextStyle` annotation is load-bearing: a struct-update
    // `{ x with f := v }` whose result flows into `style_to_ansi` + a String
    // `==` fails to infer its type and lowers as `UnresolvedAtom`. An
    // annotation, a match scrutinee, or `style_merge` consumption all avoid
    // it.
    let s : TextStyle := { style_default with fg := some Color.red, bold := true } in
    style_to_ansi s == "\u{1b}[31;1m"

// ==================== Phase 1b regression tests ====================
// BEq smoke tests. All instances except `Screen`'s are now `#[derive BEq]`
// (the derive backend's Option/nested-struct dispatch bugs are fixed on
// current nightlies); `Screen` keeps its hand-rolled instance because it
// compares `List (List Cell)` and generic-instance dispatch through `List`
// remains unreliable. The nested-concrete-field cases (Cell nesting
// TextStyle, MouseEvent nesting MouseButton, Event nesting Key, CellDelta
// nesting Cell) exercise dispatch through a concrete named type's own
// `BEq` instance.

#[test]
def test_beq_rect : Bool :=
    mk_rect 0 0 10 10 == mk_rect 0 0 10 10
    && Bool.not (mk_rect 0 0 10 10 == mk_rect 0 0 10 11)

#[test]
def test_beq_cell_nested_style : Bool :=
    let base := mk_cell "x" in
    let bold_on : TextStyle := { style_default with bold := true } in
    let bold_off : TextStyle := { style_default with bold := false } in
    let c1 : Cell := { base with style := bold_on } in
    let c2 : Cell := { base with style := bold_on } in
    let c3 : Cell := { base with style := bold_off } in
    c1 == c2 && Bool.not (c1 == c3)

#[test]
def test_beq_layout_size : Bool :=
    LayoutSize.fixed 3 == LayoutSize.fixed 3
    && Bool.not (LayoutSize.fixed 3 == LayoutSize.fill 3)

#[test]
def test_beq_mouse_button : Bool :=
    MouseButton.left == MouseButton.left
    && Bool.not (MouseButton.left == MouseButton.right)

#[test]
def test_beq_key : Bool :=
    Key.char "a" == Key.char "a"
    && Bool.not (Key.char "a" == Key.char "b")
    && Key.enter == Key.enter

#[test]
def test_beq_mouse_event : Bool :=
    MouseEvent.press MouseButton.left 0 0 == MouseEvent.press MouseButton.left 0 0
    && Bool.not (MouseEvent.press MouseButton.left 0 0 == MouseEvent.press MouseButton.right 0 0)

#[test]
def test_beq_event : Bool :=
    Event.key (Key.char "a") == Event.key (Key.char "a")
    && Bool.not (Event.key (Key.char "a") == Event.key (Key.char "b"))
    && Event.tick == Event.tick

#[test]
def test_beq_cell_delta : Bool :=
    CellDelta.set 0 0 (mk_cell "x") == CellDelta.set 0 0 (mk_cell "x")
    && Bool.not (CellDelta.set 0 0 (mk_cell "x") == CellDelta.set 0 0 (mk_cell "y"))
    && CellDelta.clear 0 0 == CellDelta.clear 0 0

#[test]
def test_beq_style_handrolled : Bool :=
    let bold_on : TextStyle := { style_default with bold := true } in
    let red_fg : TextStyle := { style_default with fg := some Color.red } in
    let green_fg : TextStyle := { style_default with fg := some Color.green } in
    style_default == style_default
    && Bool.not (bold_on == style_default)
    && red_fg == red_fg
    && Bool.not (red_fg == green_fg)

#[test]
def test_beq_screen_handrolled : Bool :=
    mk_screen 2 2 == mk_screen 2 2
    && Bool.not (mk_screen 2 2 == mk_screen 2 3)
    && Bool.not (screen_set_cell (mk_screen 2 2) 0 0 (mk_cell "x") == mk_screen 2 2)

#[test]
def test_lens_rect_view_set_over : Bool :=
    let r := mk_rect 1 2 10 10 in
    view Rect.x r == 1
    && view Rect.width (set Rect.width 42 r) == 42
    && view Rect.y (over Rect.y (fn y => y + 1) r) == 3

#[test]
def test_lens_text_style_roundtrip : Bool :=
    let s : TextStyle := { style_default with bold := true } in
    let unbolded := over TextStyle.bold (fn b => Bool.not b) s in
    // The fg comparison matches out the color rather than `==` on
    // `Option Color`: generic `BEq (Option A)` dispatch is the unreliable
    // path this mote avoids elsewhere.
    match view TextStyle.fg (set TextStyle.fg (some Color.red) s) {
        some c => c == Color.red && Bool.not unbolded.bold,
        none => false
    }
