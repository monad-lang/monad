// Terminal UI Library - Display-width text (UTF-8-aware)
//
// `String.length`/`String.slice` are BYTE-oriented; a terminal cell grid is
// not. This module decodes a string into glyphs (whole UTF-8 code points),
// measures the cells they occupy, wraps by cells, and maps byte offsets to
// display columns. The renderer (render.mo) and the input state machine
// (widgets/input.mo) both build on it.
//
// Width is a pragmatic wcwidth: combining marks and format characters are
// zero-width and fold into the previous glyph; East-Asian wide characters
// and emoji are two cells; ambiguous-width characters count as one. Emoji
// ZWJ sequences are merged best-effort (a glyph ending in U+200D takes the
// next glyph with it), and regional-indicator flags are NOT paired. Control
// bytes render as a one-cell space so model output cannot inject ANSI or
// desynchronize the cell grid.

use std::list {List.length}

/// One rendered glyph: its source text, the cells it occupies (0, 1 or 2),
/// and how many source bytes it consumed.
pub struct Glyph {
    text : String,
    width : I64,
    bytes : I64
}

def mk_glyph (text : String) (width : I64) (bytes : I64) : Glyph :=
    { text := text, width := width, bytes := bytes }

/// The glyph starting at byte `off`, or a one-byte space for poison. The
/// byte length is found with `String.slice`'s boundary rule: a cut that is
/// not on a UTF-8 boundary reads as `""`, so the first width that yields a
/// non-empty slice is the whole code point (the same probe as
/// `Input.char_at`).
pub def Text.glyph_at (s : String) (off : I64) : Glyph :=
    if Bool.not (off < String.length s)
    then mk_glyph " " 1 0
    else
        let g1 : String := String.slice s off 1 in
        if Bool.not (String.is_empty g1)
        then text_glyph g1 1
        else
            let g2 : String := String.slice s off 2 in
            if Bool.not (String.is_empty g2)
            then text_glyph g2 2
            else
                let g3 : String := String.slice s off 3 in
                if Bool.not (String.is_empty g3)
                then text_glyph g3 3
                else
                    let g4 : String := String.slice s off 4 in
                    if Bool.not (String.is_empty g4)
                    then text_glyph g4 4
                    else mk_glyph " " 1 1

/// A whole UTF-8 glyph: a control byte becomes a space, everything else is
/// classified by its code point.
def text_glyph (text : String) (n : I64) : Glyph :=
    let bytes : List U8 := String.to_list text in
    let cp : U32 := codepoint bytes 0u32 in
    if U32.lt cp 0x20u32
    then mk_glyph " " 1 n
    else if U32.beq cp 0x7Fu32
    then mk_glyph " " 1 n
    else if Bool.and (Bool.not (U32.lt cp 0x80u32)) (Bool.not (U32.lt 0x9Fu32 cp))
    then mk_glyph " " 1 n
    else mk_glyph text (codepoint_width cp) n

/// The code point's byte value, assembled from its 1-4 bytes. U32 shifts
/// and masks are the only bit operations the language exposes; no cast to
/// I64 exists, and none is needed -- width classification compares U32s.
def codepoint (bytes : List U8) (fallback : U32) : U32 :=
    match bytes {
        List.empty => fallback,
        List.cons b0 rest => match rest {
            List.empty => U8.to_u32 b0,
            List.cons b1 rest1 => match rest1 {
                List.empty => U32.or (U32.shl (U32.and (U8.to_u32 b0) 0x1Fu32) 6u32) (U32.and (U8.to_u32 b1) 0x3Fu32),
                List.cons b2 rest2 => match rest2 {
                    List.empty => U32.or (U32.shl (U32.and (U8.to_u32 b0) 0x0Fu32) 12u32)
                        (U32.or (U32.shl (U32.and (U8.to_u32 b1) 0x3Fu32) 6u32) (U32.and (U8.to_u32 b2) 0x3Fu32)),
                    List.cons b3 _ => U32.or (U32.shl (U32.and (U8.to_u32 b0) 0x07u32) 18u32)
                        (U32.or (U32.shl (U32.and (U8.to_u32 b1) 0x3Fu32) 12u32)
                        (U32.or (U32.shl (U32.and (U8.to_u32 b2) 0x3Fu32) 6u32) (U32.and (U8.to_u32 b3) 0x3Fu32))),
                },
            },
        },
    }

def in_range (cp lo hi : U32) : Bool :=
    Bool.and (Bool.not (U32.lt cp lo)) (Bool.not (U32.lt hi cp))

/// Zero for combining marks, format characters and emoji modifiers; 2 for
/// East-Asian wide and emoji; 1 otherwise.
def codepoint_width (cp : U32) : I64 :=
    if zero_width cp then 0
    else if wide cp then 2
    else 1

def zero_width (cp : U32) : Bool :=
    Bool.or (in_range cp 0x0300u32 0x036Fu32)
        (Bool.or (in_range cp 0x1AB0u32 0x1AFFu32)
        (Bool.or (in_range cp 0x1DC0u32 0x1DFFu32)
        (Bool.or (in_range cp 0x200Bu32 0x200Fu32)
        (Bool.or (in_range cp 0x202Au32 0x202Eu32)
        (Bool.or (in_range cp 0x2060u32 0x2064u32)
        (Bool.or (in_range cp 0x20D0u32 0x20F0u32)
        (Bool.or (in_range cp 0xFE00u32 0xFE0Fu32)
        (Bool.or (in_range cp 0xFE20u32 0xFE2Fu32)
        (Bool.or (in_range cp 0x1F3FBu32 0x1F3FFu32)
              (in_range cp 0xE0100u32 0xE01EFu32))))))))))

def wide (cp : U32) : Bool :=
    Bool.or (in_range cp 0x1100u32 0x115Fu32)
        (Bool.or (in_range cp 0x2E80u32 0x303Eu32)
        (Bool.or (in_range cp 0x3041u32 0x33FFu32)
        (Bool.or (in_range cp 0x3400u32 0x4DBFu32)
        (Bool.or (in_range cp 0x4E00u32 0x9FFFu32)
        (Bool.or (in_range cp 0xA000u32 0xA4CFu32)
        (Bool.or (in_range cp 0xA960u32 0xA97Fu32)
        (Bool.or (in_range cp 0xAC00u32 0xD7A3u32)
        (Bool.or (in_range cp 0xF900u32 0xFAFFu32)
        (Bool.or (in_range cp 0xFE10u32 0xFE19u32)
        (Bool.or (in_range cp 0xFE30u32 0xFE6Fu32)
        (Bool.or (in_range cp 0xFF00u32 0xFF60u32)
        (Bool.or (in_range cp 0xFFE0u32 0xFFE6u32)
        (Bool.or (in_range cp 0x1F1E6u32 0x1F1FFu32)
        (Bool.or (in_range cp 0x1F300u32 0x1FAFFu32)
        (Bool.or (in_range cp 0x20000u32 0x2FFFu32)
              (in_range cp 0x30000u32 0x3FFFu32))))))))))))))))

/// Fold a zero-width or joined glyph into its predecessor: the text is
/// appended, the consumed bytes accumulate, and the predecessor's width
/// wins (a ZWJ sequence is one 2-cell glyph).
def merge_glyph (prev : Glyph) (g : Glyph) : Glyph :=
    { prev with text := String.concat prev.text g.text, bytes := prev.bytes + g.bytes }

/// A leading zero-width glyph has nothing to fold into: render it standalone
/// in one cell.
def standalone (g : Glyph) : Glyph :=
    if g.width == 0 then { g with width := 1 } else g

/// `String.ends_with` reverses both operands byte-wise (`init/string.mo`),
/// which corrupts a multi-byte suffix, so check the ZWJ by slicing its last
/// three bytes instead.
def ends_with_zwj (s : String) : Bool :=
    let n : I64 := String.length s in
    if n < 3 then false else String.slice s (n - 3) 3 == "\u{200d}"

/// `acc` is newest-first. A zero-width glyph folds into the previous one;
/// a glyph following a ZWJ joins it too.
#[terminating]
def push_glyph (acc : List Glyph) (g : Glyph) : List Glyph :=
    match acc {
        List.empty => List.cons (standalone g) List.empty,
        List.cons prev rest =>
            if g.width == 0
            then List.cons (merge_glyph prev g) rest
            else if ends_with_zwj prev.text
            then List.cons (merge_glyph prev g) rest
            else List.cons g acc,
    }

/// The UTF-8 continuation length a lead byte announces: 1 for ASCII (and
/// malformed leads), 2-4 for a multi-byte sequence. Pure byte math, no
/// string walk.
def utf8_need (b : U8) : I64 :=
    let v : U32 := U8.to_u32 b in
    if Bool.not (U32.lt 0x7Fu32 v) then 1
    else if U32.beq (U32.and v 0xE0u32) 0xC0u32 then 2
    else if U32.beq (U32.and v 0xF0u32) 0xE0u32 then 3
    else if U32.beq (U32.and v 0xF8u32) 0xF0u32 then 4
    else 1

/// Take `n` bytes off the front: `(taken, rest)`.
#[terminating]
def take_bytes (n : I64) (bs : List U8) (acc : List U8) : Pair (List U8) (List U8) :=
    if n < 1
    then Pair.pair (List.reverse acc) bs
    else match bs {
        List.empty => Pair.pair (List.reverse acc) List.empty,
        List.cons b rest => take_bytes (n - 1) rest (List.cons b acc),
    }

/// One glyph from the front of the byte list. Decoding from bytes makes
/// `Text.glyphs` a single linear pass: no per-glyph `String.length` (a
/// `strlen` on the compiled backend) and no offset `String.slice` (which
/// walks to the offset and allocates).
#[terminating]
def decode_glyph (bs : List U8) : Pair Glyph (List U8) :=
    match bs {
        List.empty => Pair.pair (mk_glyph " " 1 0) List.empty,
        List.cons b0 rest =>
            match take_bytes (utf8_need b0) bs List.empty {
                Pair.pair got after =>
                    let text : String := String.from_list got in
                    Pair.pair (text_glyph text (List.length got)) after,
            },
    }

#[terminating]
def glyphs_go (bs : List U8) (acc : List Glyph) : List Glyph :=
    match bs {
        List.empty => List.reverse acc,
        _ => match decode_glyph bs {
            Pair.pair g rest => glyphs_go rest (push_glyph acc g),
        },
    }

/// The string's glyphs, in order. Poison bytes are consumed one at a time as
/// one-cell spaces.
pub def Text.glyphs (s : String) : List Glyph :=
    glyphs_go (String.to_list s) List.empty

#[terminating]
def width_go (gs : List Glyph) (acc : I64) : I64 :=
    match gs {
        List.empty => acc,
        List.cons g rest => width_go rest (acc + g.width),
    }

/// The display width of `s` in cells.
pub def Text.width (s : String) : I64 := width_go (Text.glyphs s) 0

#[terminating]
def take_width_go (gs : List Glyph) (budget : I64) (used : I64) (acc : List String) : List String :=
    match gs {
        List.empty => List.reverse acc,
        List.cons g rest =>
            if budget < used + g.width
            then List.reverse acc
            else take_width_go rest budget (used + g.width) (List.cons g.text acc),
    }

/// The longest prefix of `s` that fits in `w` cells; never splits a glyph.
/// A first glyph wider than `w` yields `""` (the caller decides whether to
/// paint it alone).
pub def Text.take_width (s : String) (w : I64) : String :=
    String.concat_list (take_width_go (Text.glyphs s) w 0 List.empty)

#[terminating]
def drop_cols_go (gs : List Glyph) (n : I64) (used : I64) : Pair String I64 :=
    match gs {
        List.empty => Pair.pair "" used,
        List.cons g rest =>
            if n < used + g.width
            then Pair.pair (join_glyphs (List.cons g rest)) used
            else drop_cols_go rest n (used + g.width),
    }

#[terminating]
def glyph_texts (gs : List Glyph) (acc : List String) : List String :=
    match gs {
        List.empty => List.reverse acc,
        List.cons g rest => glyph_texts rest (List.cons g.text acc),
    }

/// One allocation's join: a right-nested `String.concat` re-copies the
/// accumulated prefix on every glyph (quadratic on the compiled backend).
def join_glyphs (gs : List Glyph) : String :=
    String.concat_list (glyph_texts gs List.empty)

/// Drop `n` complete display columns from the front: `(rest, dropped)`.
/// A wide glyph straddling the boundary is kept (the window starts a column
/// early rather than in the middle of a glyph).
pub def Text.drop_cols (s : String) (n : I64) : Pair String I64 :=
    drop_cols_go (Text.glyphs s) n 0

#[terminating]
def col_of_byte_go (gs : List Glyph) (target : I64) (off : I64) (col : I64) : I64 :=
    match gs {
        List.empty => col,
        List.cons g rest =>
            if target < off + g.bytes
            then col
            else col_of_byte_go rest target (off + g.bytes) (col + g.width),
    }

/// The display column of byte offset `b`; a mid-glyph offset snaps down.
pub def Text.col_of_byte (s : String) (b : I64) : I64 :=
    col_of_byte_go (Text.glyphs s) b 0 0

#[terminating]
def prev_boundary_go (gs : List Glyph) (off : I64) (b : I64) (last : I64) : I64 :=
    match gs {
        List.empty => last,
        List.cons g rest =>
            let next : I64 := off + g.bytes in
            if Bool.not (next < b)
            then last
            else prev_boundary_go rest next b next,
    }

/// The largest glyph boundary strictly before `b` (0 at the start).
pub def Text.prev_boundary (s : String) (b : I64) : I64 :=
    prev_boundary_go (Text.glyphs s) 0 b 0

#[terminating]
def next_boundary_go (gs : List Glyph) (off : I64) (b : I64) : I64 :=
    match gs {
        List.empty => off,
        List.cons g rest =>
            let next : I64 := off + g.bytes in
            if b < next then next else next_boundary_go rest next b,
    }

/// The smallest glyph boundary strictly after `b` (the end at the end).
pub def Text.next_boundary (s : String) (b : I64) : I64 :=
    next_boundary_go (Text.glyphs s) 0 b

#[terminating]
def byte_at_col_go (gs : List Glyph) (target : I64) (off : I64) (col : I64) : I64 :=
    match gs {
        List.empty => off,
        List.cons g rest =>
            if target < col + g.width
            then off
            else byte_at_col_go rest target (off + g.bytes) (col + g.width),
    }

/// The byte offset whose display column is `c` (snaps to the glyph start
/// when `c` falls inside a wide glyph).
pub def Text.byte_at_col (s : String) (c : I64) : I64 :=
    byte_at_col_go (Text.glyphs s) c 0 0

#[terminating]
def slice_cols_go (gs : List Glyph) (c0 c1 : I64) (col : I64) (acc : List String) : List String :=
    match gs {
        List.empty => List.reverse acc,
        List.cons g rest =>
            let start : I64 := col in
            let end : I64 := col + g.width in
            let hit : Bool := Bool.and (Bool.not (end < c0 + 1)) (Bool.not (c1 < start + 1)) in
            let acc2 : List String := if hit then List.cons g.text acc else acc in
            slice_cols_go rest c0 c1 end acc2,
    }

/// The text covering display columns `[c0, c1)`. A wide glyph that the
/// range intersects is included whole; zero-width marks ride with it.
pub def Text.slice_cols (s : String) (c0 : I64) (c1 : I64) : String :=
    if Bool.not (c0 < c1) then "" else String.concat_list (slice_cols_go (Text.glyphs s) c0 c1 0 List.empty)

#[terminating]
def pad_go (n : I64) (acc : String) : String :=
    if n < 1 then acc else pad_go (n - 1) (String.concat acc " ")

/// `slice_cols`, padded with spaces to exactly `c1 - c0` cells -- the
/// highlight segment needs a fixed width so the trailing cells are painted
/// too.
pub def Text.padded_slice_cols (s : String) (c0 : I64) (c1 : I64) : String :=
    let text : String := Text.slice_cols s c0 c1 in
    let need : I64 := (c1 - c0) - Text.width text in
    if need < 1 then text else String.concat text (pad_go need "")

#[terminating]
def snap_span_go (gs : List Glyph) (c0 c1 : I64) (col : I64) (a b : I64) : Pair I64 I64 :=
    match gs {
        List.empty => Pair.pair a b,
        List.cons g rest =>
            let start : I64 := col in
            let end : I64 := col + g.width in
            let a2 : I64 := if Bool.and (a < 0) (Bool.not (end < c0 + 1)) then start else a in
            let b2 : I64 := if Bool.and (b < 0) (c1 < end) then end else b in
            snap_span_go rest c0 c1 end a2 b2,
    }

/// Floor `c0` to a glyph start and ceil `c1` to a glyph end, so a selection
/// never splits a glyph.
pub def Text.snap_span (s : String) (c0 : I64) (c1 : I64) : Pair I64 I64 :=
    match snap_span_go (Text.glyphs s) c0 c1 0 (0 - 1) (0 - 1) {
        Pair.pair a b => Pair.pair (if a < 0 then c0 else a) (if b < 0 then c1 else b),
    }

// ==================== wrapping ====================

/// The prefix of `gs` that fits `w` cells and the rest, breaking at the
/// last space that fits when one exists after the first glyph.
struct WrapSplit {
    line : List Glyph,
    rest : List Glyph,
    broke : Bool
}

#[terminating]
def wrap_split_go (gs : List Glyph) (w : I64) (used : I64) (line_rev : List Glyph)
        (space_line : List Glyph) (space_rest : List Glyph) : WrapSplit :=
    match gs {
        List.empty => { line := List.reverse line_rev, rest := List.empty, broke := false },
        List.cons g rest =>
            if w < used + g.width
            then
                if Bool.not (List.is_empty space_rest)
                then { line := List.reverse space_line, rest := space_rest, broke := true }
                else if List.is_empty line_rev
                then { line := List.cons g List.empty, rest := rest, broke := true }
                else { line := List.reverse line_rev, rest := List.cons g rest, broke := true }
            else
                let used2 : I64 := used + g.width in
                let line2 : List Glyph := List.cons g line_rev in
                // A space at the very start is not a break point: the old
                // wrapper kept it (a leading space must not produce an
                // empty first row).
                if Bool.and (g.text == " ") (Bool.not (List.is_empty line_rev))
                then wrap_split_go rest w used2 line2 line_rev rest
                else wrap_split_go rest w used2 line2 space_line space_rest,
    }

def wrap_split (w : I64) (gs : List Glyph) : WrapSplit :=
    wrap_split_go gs w 0 List.empty List.empty List.empty

/// Drop the glyphs after the last non-space, from a reversed list. One
/// reverse in, at most one out -- the old trailing-space test re-scanned
/// the whole remainder for every row (quadratic on long lines).
#[terminating]
def drop_trailing_go (rev : List Glyph) : List Glyph :=
    match rev {
        List.empty => List.empty,
        List.cons g rest => if g.text == " " then drop_trailing_go rest else List.reverse rev,
    }

def drop_trailing_spaces (gs : List Glyph) : List Glyph :=
    drop_trailing_go (List.reverse gs)

#[terminating]
def wrap_go (w : I64) (gs : List Glyph) : List String :=
    let split : WrapSplit := wrap_split w gs in
    if Bool.not split.broke
    then List.cons (join_glyphs split.line) List.empty
    else List.cons (join_glyphs split.line) (wrap_go w split.rest)

/// Split `line` into rows of at most `width` CELLS: word-wrap at the last
/// space that fits, hard-break a glyph run longer than the width, never
/// split a code point. Trailing spaces do not produce an empty final row.
/// Widths below 1 clamp to 1 (a zero width would never advance).
pub def Text.wrap (width : I64) (line : String) : List String :=
    let w : I64 := if width < 1 then 1 else width in
    if String.is_empty line
    then [""]
    else
        let gs : List Glyph := Text.glyphs line in
        let trimmed : List Glyph := drop_trailing_spaces gs in
        // A line of only spaces keeps its old single row; an ordinary
        // line is wrapped from the trimmed glyph list.
        if List.is_empty trimmed then [join_glyphs gs] else wrap_go w trimmed

// ==================== tests ====================

#[test]
def test_width_ascii : Bool := Text.width "abc" == 3

#[test]
def test_width_latin1 : Bool := Text.width "æøå" == 3

#[test]
def test_width_cjk : Bool := Text.width "日本" == 4

#[test]
def test_width_emoji : Bool := Text.width "😀" == 2

#[test]
def test_glyph_count_latin1 : Bool := List.length (Text.glyphs "æøå") == 3

#[test]
def test_control_renders_as_space : Bool := Text.take_width "\tA" 4 == " A"

#[test]
def test_wrap_ascii_exact_fit : Bool := Text.wrap 5 "abcde" == ["abcde"]

#[test]
def test_wrap_ascii_word : Bool := Text.wrap 6 "hello world" == ["hello", "world"]

#[test]
def test_wrap_ascii_hard : Bool := Text.wrap 3 "abcdefg" == ["abc", "def", "g"]

#[test]
def test_wrap_latin1 : Bool := Text.wrap 3 "æøå" == ["æøå"]

#[test]
def test_wrap_wide : Bool := Text.wrap 2 "日本" == ["日", "本"]

#[test]
def test_width_skin_tone : Bool := Text.width "👍🏽" == 2

#[test]
def test_width_zwj_family : Bool := Text.width "👨‍👩‍👧" == 2

#[test]
def test_width_combining : Bool := Text.width "e\u{301}" == 1

#[test]
def test_wrap_trailing_space_drops_the_empty_row : Bool := Text.wrap 3 "abc " == ["abc"]

#[test]
def test_wrap_all_spaces_keeps_one_row : Bool := Text.wrap 3 "   " == ["   "]

#[test]
def test_wrap_leading_space_is_not_a_break : Bool := Text.wrap 3 " abc" == [" ab", "c"]

#[test]
def test_wrap_mixed_wide : Bool := Text.wrap 4 "a日本b" == ["a日", "本b"]

#[test]
def test_slice_cols_wide_is_whole : Bool := Text.slice_cols "日本" 0 2 == "日"

#[test]
def test_padded_slice_cols_pads : Bool := Text.padded_slice_cols "ab" 1 4 == "b  "

#[test]
def test_snap_span_floor_and_ceil : Bool :=
    match Text.snap_span "日本" 1 3 {
        Pair.pair a b => a == 0 && b == 4,
    }

#[test]
def test_take_width_never_splits : Bool := Text.take_width "日本" 3 == "日"

#[test]
def test_col_of_byte_multibyte : Bool := Text.col_of_byte "æø" 2 == 1

#[test]
def test_prev_boundary_multibyte : Bool := Text.prev_boundary "æø" 2 == 0

#[test]
def test_next_boundary_multibyte : Bool := Text.next_boundary "æø" 0 == 2
