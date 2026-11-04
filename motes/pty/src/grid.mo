// pty / grid -- an ANSI screen model for assertions.
//
// The Python drivers keep a tiny mutable terminal: cursor moves, ESC[2J,
// printable UTF-8, SGR ignored. This is the same model as a PURE fold, so it
// can be rebuilt or advanced incrementally and unit-tested without a pty.
//
// Width comes from `motes/tui/src/text.mo` (`Text.width`), the repo's one
// wcwidth implementation; a wide glyph occupies its left cell and an empty
// continuation cell, so `find`/`row_text` see the glyph once. `Text.col_of_byte`
// maps a byte match offset to the terminal column a mouse report uses.
//
// The parser walks BYTES, not String slices: `String.slice s i 1` returns ""
// at the start of a multi-byte character, and `Text.glyph_at` does not validate
// an incomplete sequence. An explicit UTF-8 length check is what lets
// `feed_from` return the offset of a trailing incomplete glyph/escape; the
// caller retries when the next chunk lands, so a split glyph is never mangled.

use lib::ansi {is_csi_final}
use std::list {List.length, List.intercalate}
use tui::text {Text.width, Text.col_of_byte}

pub struct Grid {
    rows : I64,
    cols : I64,
    cells : List (List String),
    row : I64,
    col : I64,
    clears : I64
}

// ── Construction and cell updates ─────────────────────────────────────────

#[partial]
def blank_row (cols : I64) : List String :=
    if I64.lt cols 1 then List.empty else List.cons " " (blank_row (cols - 1))

#[partial]
def blank_rows (rows : I64) (cols : I64) : List (List String) :=
    if I64.lt rows 1 then List.empty
    else List.cons (blank_row cols) (blank_rows (rows - 1) cols)

pub def Grid.empty (rows : I64) (cols : I64) : Grid :=
    let g : Grid := {
        rows := rows, cols := cols, cells := blank_rows rows cols,
        row := 0, col := 0, clears := 0
    } in
    g

def clamp0 (n : I64) : I64 := if I64.lt n 0 then 0 else n

#[partial]
def set_row_cells (row_cells : List String) (c : I64) (text : String) : List String :=
    match row_cells {
        List.empty => List.empty,
        List.cons x rest =>
            if I64.beq c 0 then List.cons text rest
            else List.cons x (set_row_cells rest (c - 1) text)
    }

#[partial]
def set_row_at (cells : List (List String)) (r : I64) (f : List String -> List String) : List (List String) :=
    match cells {
        List.empty => List.empty,
        List.cons x rest =>
            if I64.beq r 0 then List.cons (f x) rest
            else List.cons x (set_row_at rest (r - 1) f)
    }

#[partial]
def clear_from (row_cells : List String) (c : I64) : List String :=
    match row_cells {
        List.empty => List.empty,
        List.cons x rest =>
            if I64.beq c 0 then List.cons " " (clear_from rest 0)
            else List.cons x (clear_from rest (c - 1))
    }

def Grid.clear (g : Grid) : Grid :=
    let g2 : Grid := { g with cells := blank_rows g.rows g.cols, clears := g.clears + 1 } in
    g2

def Grid.clear_line (g : Grid) : Grid :=
    let c := g.col in
    let cells := set_row_at g.cells g.row (fn (row_cells : List String) => clear_from row_cells c) in
    let g2 : Grid := { g with cells := cells } in
    g2

def Grid.put_at (g : Grid) (r : I64) (c : I64) (text : String) (width : I64) : Grid :=
    let cells1 := set_row_at g.cells r (fn (row_cells : List String) => set_row_cells row_cells c text) in
    let cells2 := if Bool.and (I64.beq width 2) (I64.lt (c + 1) g.cols)
        then set_row_at cells1 r (fn (row_cells : List String) => set_row_cells row_cells (c + 1) "")
        else cells1 in
    let step := if I64.lt width 1 then 1 else width in
    let g2 : Grid := { g with cells := cells2, col := c + step } in
    g2

def Grid.put_char (g : Grid) (text : String) (width : I64) : Grid :=
    let r := g.row in
    let c := g.col in
    let in_rows := Bool.and (Bool.not (I64.lt r 0)) (I64.lt r g.rows) in
    let in_cols := Bool.and (Bool.not (I64.lt c 0)) (I64.lt c g.cols) in
    if Bool.not (Bool.and in_rows in_cols) then { g with col := c + 1 }
    else Grid.put_at g r c text width

// ── Cursor operations ─────────────────────────────────────────────────────

def Grid.goto (g : Grid) (r : I64) (c : I64) : Grid :=
    let g2 : Grid := { g with row := clamp0 r, col := clamp0 c } in g2

def Grid.rel (g : Grid) (dr : I64) (dc : I64) : Grid :=
    let g2 : Grid := { g with row := clamp0 (g.row + dr), col := clamp0 (g.col + dc) } in g2

def Grid.newline (g : Grid) : Grid :=
    let g2 : Grid := { g with row := g.row + 1, col := 0 } in g2

def Grid.tab (g : Grid) : Grid :=
    let g2 : Grid := { g with col := g.col + 8 } in g2

// ── CSI parameters ────────────────────────────────────────────────────────

#[partial]
def parse_dec_go (bs : List U8) (acc : I64) : Option I64 :=
    match bs {
        List.empty => Option.some acc,
        List.cons b rest =>
            if U8.lt b 48u8 then Option.none
            else if U8.gt b 57u8 then Option.none
            else parse_dec_go rest (acc * 10 + (U8.to_i64 b - 48))
    }

def parse_dec (s : String) : Option I64 :=
    if String.is_empty s then Option.none else parse_dec_go (String.to_list s) 0

#[partial]
def split_semi_go (bs : List U8) (cur : List U8) (acc : List String) : List String :=
    match bs {
        List.empty => List.reverse (List.cons (String.from_list (List.reverse cur)) acc),
        List.cons b rest =>
            if U8.beq b 59u8
            then split_semi_go rest List.empty (List.cons (String.from_list (List.reverse cur)) acc)
            else split_semi_go rest (List.cons b cur) acc
    }

def split_semi (s : String) : List String :=
    split_semi_go (String.to_list s) List.empty List.empty

def part_value (part : String) (fallback : I64) : I64 :=
    match parse_dec part {
        Option.some n => n,
        Option.none => fallback
    }

def param_or (params : String) (i : I64) (fallback : I64) : I64 :=
    match List.get i (split_semi params) {
        Option.some part => part_value part fallback,
        Option.none => fallback
    }

def Grid.csi (g : Grid) (params : String) (final : String) : Grid :=
    if final == "H" then
        let r := param_or params 0 1 in
        let c := param_or params 1 1 in
        Grid.goto g (r - 1) (c - 1)
    else if final == "J" then
        if params == "" then Grid.goto (Grid.clear g) 0 0
        else if params == "2" then Grid.clear g
        else g
    else if final == "K" then Grid.clear_line g
    else if final == "A" then Grid.rel g (0 - param_or params 0 1) 0
    else if final == "B" then Grid.rel g (param_or params 0 1) 0
    else if final == "C" then Grid.rel g 0 (param_or params 0 1)
    else if final == "D" then Grid.rel g 0 (0 - param_or params 0 1)
    else g

// ── Byte helpers ─────────────────────────────────────────────────────────

def head_byte (bs : List U8) : U8 :=
    match bs {
        List.cons b _ => b,
        List.empty => 0u8
    }

#[partial]
def take_n (n : I64) (bs : List U8) : List U8 :=
    if I64.lt n 1 then List.empty
    else match bs {
        List.empty => List.empty,
        List.cons b rest => List.cons b (take_n (n - 1) rest)
    }

#[partial]
def drop_n (n : I64) (bs : List U8) : List U8 :=
    if I64.lt n 1 then bs
    else match bs {
        List.empty => List.empty,
        List.cons _b rest => drop_n (n - 1) rest
    }

def slice_n (bs : List U8) (off : I64) (len : I64) : List U8 :=
    take_n len (drop_n off bs)

/// The UTF-8 sequence length implied by a leading byte. Invalid continuations
/// and stray bytes count as one, matching the grid's "advance, don't stall".
def utf8_len (b : U8) : I64 :=
    if U8.lt b 128u8 then 1
    else if U8.lt b 194u8 then 1
    else if U8.lt b 224u8 then 2
    else if U8.lt b 240u8 then 3
    else if U8.lt b 245u8 then 4
    else 1

def chr1 (b : U8) : String := String.from_list (List.cons b List.empty)

#[partial]
def csi_end (bs : List U8) (j : I64) : Option I64 :=
    match List.get j bs {
        Option.some b => if is_csi_final b then Option.some j else csi_end bs (j + 1),
        Option.none => Option.none
    }

#[partial]
def osc_after_esc (bs : List U8) (j : I64) : Option I64 :=
    match List.get (j + 1) bs {
        Option.some b2 => if U8.beq b2 92u8 then Option.some (j + 2) else osc_end bs (j + 1),
        Option.none => Option.none
    }

#[partial]
def osc_end (bs : List U8) (j : I64) : Option I64 :=
    match List.get j bs {
        Option.some b =>
            if U8.beq b 7u8 then Option.some (j + 1)
            else if U8.beq b 27u8 then osc_after_esc bs j
            else osc_end bs (j + 1),
        Option.none => Option.none
    }

// ── The parser: bytes in, consumed count out ─────────────────────────────

#[partial]
def feed_esc (g : Grid) (bs : List U8) : Pair Grid I64 :=
    match List.get 1 bs {
        Option.none => Pair.pair g 0,
        Option.some b1 =>
            if U8.beq b1 91u8 then feed_csi g bs
            else if U8.beq b1 93u8 then feed_osc g bs
            else feed_rest g (drop_n 2 bs) 2
    }

#[partial]
def feed_csi (g : Grid) (bs : List U8) : Pair Grid I64 :=
    match csi_end bs 2 {
        Option.none => Pair.pair g 0,
        Option.some j =>
            let params := String.from_list (slice_n bs 2 (j - 2)) in
            let final := chr1 (head_byte (drop_n j bs)) in
            feed_rest (Grid.csi g params final) (drop_n (j + 1) bs) (j + 1)
    }

#[partial]
def feed_osc (g : Grid) (bs : List U8) : Pair Grid I64 :=
    match osc_end bs 2 {
        Option.none => Pair.pair g 0,
        Option.some j => feed_rest g (drop_n j bs) j
    }

#[partial]
def feed_rest (g : Grid) (bs : List U8) (used : I64) : Pair Grid I64 :=
    match feed_bytes g bs {
        Pair.pair g2 more => Pair.pair g2 (used + more)
    }

#[partial]
def feed_bytes (g : Grid) (bs : List U8) : Pair Grid I64 :=
    match bs {
        List.empty => Pair.pair g 0,
        List.cons b rest =>
            if U8.beq b 27u8 then feed_esc g bs
            else if U8.beq b 10u8 then feed_rest (Grid.newline g) rest 1
            else if U8.beq b 13u8 then feed_rest (Grid.goto g g.row 0) rest 1
            else if U8.beq b 8u8 then feed_rest (Grid.rel g 0 (0 - 1)) rest 1
            else if U8.beq b 9u8 then feed_rest (Grid.tab g) rest 1
            else if U8.lt b 32u8 then feed_rest g rest 1
            else if U8.lt b 128u8 then feed_rest (Grid.put_char g (chr1 b) 1) rest 1
            else feed_utf8 g bs
    }

#[partial]
def feed_utf8 (g : Grid) (bs : List U8) : Pair Grid I64 :=
    let need := utf8_len (head_byte bs) in
    if I64.lt (List.length bs) need then Pair.pair g 0
    else
        let glyph := String.from_list (take_n need bs) in
        feed_rest (Grid.put_char g glyph (Text.width glyph)) (drop_n need bs) need

/// Feed the accumulated text from `start`; returns the grid and the offset of
/// the first byte not consumed (a trailing incomplete glyph/escape).
pub def Grid.feed_from (g : Grid) (s : String) (start : I64) : Pair Grid I64 :=
    let len := String.length s in
    if Bool.not (I64.lt start len) then Pair.pair g start
    else
        let tail := String.slice s start (len - start) in
        match feed_bytes g (String.to_list tail) {
            Pair.pair g2 used => Pair.pair g2 (start + used)
        }

/// Build a grid from a whole output string (tests and one-shot snapshots).
pub def Grid.of_string (rows : I64) (cols : I64) (s : String) : Grid :=
    match Grid.feed_from (Grid.empty rows cols) s 0 {
        Pair.pair g _ => g
    }

// ── Queries ───────────────────────────────────────────────────────────────

#[partial]
def find_at (hay : String) (needle : String) (i : I64) : Option I64 :=
    if I64.gt (i + String.length needle) (String.length hay) then Option.none
    else if String.slice hay i (String.length needle) == needle then Option.some i
    else find_at hay needle (i + 1)

#[partial]
def find_row_go (cells : List (List String)) (needle : String) (r : I64) : Option (Pair I64 I64) :=
    match cells {
        List.empty => Option.none,
        List.cons row rest =>
            let text := String.concat_list row in
            match find_at text needle 0 {
                Option.some b => Option.some (Pair.pair r (Text.col_of_byte text b)),
                Option.none => find_row_go rest needle (r + 1)
            }
    }

/// The `(row, col)` where `needle` starts, as terminal CELL coordinates
/// (byte offset translated by `Text.col_of_byte`, so a wide glyph counts two
/// columns). `Option.none` when absent.
pub def Grid.find (g : Grid) (needle : String) : Option (Pair I64 I64) :=
    find_row_go g.cells needle 0

pub def Grid.row_text (g : Grid) (r : I64) : String :=
    match List.get r g.cells {
        Option.some row => String.concat_list row,
        Option.none => ""
    }

#[partial]
def rows_text (cells : List (List String)) (acc : List String) : List String :=
    match cells {
        List.empty => List.reverse acc,
        List.cons row rest => rows_text rest (List.cons (String.concat_list row) acc)
    }

pub def Grid.text (g : Grid) : String :=
    List.intercalate "\n" (rows_text g.cells List.empty)
