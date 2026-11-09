/// Position tests: the inputs where a byte, a code point and a UTF-16 code unit
/// disagree, and the round trip that has to hold at every boundary.
///
/// A position bug is invisible in review and nearly invisible at the cursor. The
/// cheap implementation -- `column - 1` -- is exactly right for ASCII text, so
/// it passes every hand-check anyone is likely to run, and it is wrong only past
/// the first character outside the BMP. The two fixtures below are chosen so
/// that one of them (an em dash, BMP) still agrees with the cheap answer and the
/// other (an emoji, astral) does not; a test suite that only had the first would
/// pass on an implementation that is wrong on every emoji, which is the exact
/// shape AGENTS.md item 40 warns about.
///
/// Every read of a struct field happens inside a helper def here, never inside a
/// `#[test]` def: a `#[test]` def that touches a field is a recorded self-hosted
/// codegen hazard (the def picks up the FIELD's LLVM type as its own return
/// type), and the remedy in this repo is a typed accessor. The helpers below are
/// that remedy -- `pt_*` names, and a collision-avoiding prefix because the
/// whole-program scope is shared with every other mote's tests.
use toolkit::bytes {is_continuation_byte}
use toolkit::position {
    LineIndex, LineInfo, PositionEncoding, WirePosition, WireRange, line_count,
    line_index_of_source, line_info_is_ascii, line_info_start, line_info_stop, line_at,
    line_of_offset, offset_after_char, offset_of_wire, position_encoding_default,
    position_encoding_from_string, position_encoding_name, utf16_units_between,
    wire_of_location, wire_position_character, wire_position_line, wire_position_mk,
    wire_range_end, wire_range_mk, wire_range_of_offsets, wire_range_of_points,
    wire_range_start,
}

// --- Fixtures ---
//
// Byte layouts are spelled out where they are used, so every expected number in
// this file is arithmetic a reader can check rather than a value copied out of a
// run.

/// `// — x` then `def y : I64 := 1`: one BMP non-ASCII character on line 1, and
/// a pure-ASCII line 2 so both branches of the ASCII fast path are exercised by
/// one source.
def pt_mixed : String := "// — x\ndef y : I64 := 1\n"

/// An astral character: ONE code point, TWO UTF-16 code units, FOUR bytes. The
/// single input on which `column - 1`, `offset - line_start` and the UTF-16
/// count are three different answers.
def pt_astral : String := "😀x"

/// No trailing newline on line 3, and a CRLF on line 2: the two line-terminator
/// shapes a `stop` has to get right at once.
def pt_crlf : String := "a\nbb\r\nccc"

def pt_trailing_newline : String := "a\n"

def pt_empty : String := ""

// --- Helpers ---
//
// A wire position in, scalars out, so no test def ever holds a struct value it
// then reaches into.
//
// THE LINE NUMBERS DIFFER BETWEEN THESE TWO FAMILIES, and that is inherited from
// the API rather than chosen here: `pt_wire`/`pt_char`/`pt_online` take a SOURCE
// line (1-based, `lang`'s convention) because they call `wire_of_location`, while
// `pt_off` takes a WIRE line (0-based) because it builds a `WirePosition`. The
// first draft of this file had four assertions that confused the two, which is
// why both families say which they are in the helper's own name.

/// The wire position of SOURCE `(line, offset)`, or a sentinel no assertion can
/// mistake for a real one.
#[partial]
def pt_wire (enc : PositionEncoding) (src : String) (line : I64) (off : I64) : WirePosition :=
    match wire_of_location enc (line_index_of_source src) src line off {
        Option.none => wire_position_mk (-1) (-1),
        Option.some p => p,
    }

/// The wire CHARACTER of SOURCE `(line, offset)` under `enc`.
#[partial]
def pt_char (enc : PositionEncoding) (src : String) (line : I64) (off : I64) : I64 :=
    wire_position_character (pt_wire enc src line off)

/// The wire LINE of SOURCE `(line, offset)` under `enc`, which must be `line - 1`.
#[partial]
def pt_online (enc : PositionEncoding) (src : String) (line : I64) (off : I64) : I64 :=
    wire_position_line (pt_wire enc src line off)

/// The byte offset WIRE `(line, character)` names, or -1 when the line does not
/// exist.
#[partial]
def pt_off (enc : PositionEncoding) (src : String) (wire_line : I64) (character : I64) : I64 :=
    match offset_of_wire enc (line_index_of_source src) src (wire_position_mk wire_line character) {
        Option.none => -1,
        Option.some o => o,
    }

#[partial]
def pt_start (ix : LineIndex) (line : I64) : I64 :=
    match line_at ix line {
        Option.none => -1,
        Option.some li => line_info_start li,
    }

#[partial]
def pt_stop (ix : LineIndex) (line : I64) : I64 :=
    match line_at ix line {
        Option.none => -1,
        Option.some li => line_info_stop li,
    }

#[partial]
def pt_is_ascii (ix : LineIndex) (line : I64) : Bool :=
    match line_at ix line {
        Option.none => false,
        Option.some li => line_info_is_ascii li,
    }

/// The byte at `i`, or 0. A list walk rather than `String.get`, which is the
/// O(1) byte read this would prefer but is not `pub` outside its own mote.
#[partial]
def pt_byte_at (src : String) (i : I64) : U8 :=
    pt_byte_at_go (String.to_list src) i

#[partial]
def pt_byte_at_go (bs : List U8) (i : I64) : U8 :=
    match bs {
        List.empty => 0u8,
        List.cons b rest => if I64.beq i 0 then b else pt_byte_at_go rest (I64.sub i 1),
    }

/// Both encodings give the same `character` for an ASCII source. Asserted rather
/// than assumed, since the two take different code paths even here.
def pt_agree (src : String) (line : I64) (off : I64) : Bool :=
    I64.beq (pt_char PositionEncoding.utf8 src line off)
        (pt_char PositionEncoding.utf16 src line off)

// --- Round trip, at every boundary ---
//
// The property the pair of converters owes its callers: a byte offset that is a
// real character boundary survives a trip out to the wire and back. Only
// BOUNDARIES are candidates -- a UTF-16 offset between the two units of a
// surrogate pair names no byte, and that case is pinned as a clamp below rather
// than folded in here.

#[partial]
def pt_roundtrip_all (enc : PositionEncoding) (src : String) : Bool :=
    let ix : LineIndex := line_index_of_source src in
    pt_roundtrip_lines enc src ix 1 (line_count ix)

#[partial]
def pt_roundtrip_lines (enc : PositionEncoding) (src : String) (ix : LineIndex) (line : I64)
    (total : I64) : Bool :=
    if I64.gt line total
    then true
    else
        if pt_roundtrip_bytes enc src line (pt_start ix line) (pt_stop ix line)
        then pt_roundtrip_lines enc src ix (I64.add line 1) total
        else false

/// Walk `line`'s bytes, and at every byte that starts a character check that the
/// wire position of that byte converts back to it.
#[partial]
def pt_roundtrip_bytes (enc : PositionEncoding) (src : String) (line : I64) (i : I64)
    (stop : I64) : Bool :=
    if I64.lt i stop
    then
        if is_continuation_byte (pt_byte_at src i)
        then pt_roundtrip_bytes enc src line (I64.add i 1) stop
        else
            if I64.beq (pt_off enc src (I64.sub line 1) (pt_char enc src line i)) i
            then pt_roundtrip_bytes enc src line (I64.add i 1) stop
            else false
    else true

/// The whole file, both encodings, every boundary.
def pt_roundtrip_both (src : String) : Bool :=
    pt_roundtrip_all PositionEncoding.utf8 src && pt_roundtrip_all PositionEncoding.utf16 src

#[test]
def test_position_round_trips_over_ascii : Bool :=
    pt_roundtrip_both pt_crlf

#[test]
def test_position_round_trips_over_a_bmp_character : Bool :=
    pt_roundtrip_both pt_mixed

/// The astral case, which is the one where a naive round trip through
/// `character` would still pass while the COUNT was wrong -- hence the explicit
/// `character` assertions next to it.
#[test]
def test_position_round_trips_over_an_astral_character : Bool :=
    pt_roundtrip_both pt_astral

// --- The three counts, kept apart ---

/// An em dash is 3 bytes and 1 code point, so the two encodings must disagree,
/// and the UTF-16 count must agree with `lang`'s column-1 (`5` at byte 7, which
/// `test_resolve_offsets_column_counts_characters` in lang/parser/position.mo
/// pins as column 6).
#[test]
def test_bmp_character_separates_byte_and_utf16_offsets : Bool :=
    I64.beq (pt_char PositionEncoding.utf8 pt_mixed 1 7) 7
        && I64.beq (pt_char PositionEncoding.utf16 pt_mixed 1 7) 5
        && I64.beq (pt_online PositionEncoding.utf16 pt_mixed 1 7) 0

/// THE test this module exists for. An emoji is 4 bytes but 2 UTF-16 code units,
/// and `lang` counts it as ONE column, so at byte 4 the three counts are 4, 2 and
/// 1. An implementation that used `column - 1` answers 1 here; one that used
/// `offset - line_start` answers 4. Both are wrong, and both are right on every
/// other line of every other fixture in this repo.
#[test]
def test_astral_character_separates_all_three_counts : Bool :=
    I64.beq (String.length "😀") 4
        && I64.beq (pt_char PositionEncoding.utf8 pt_astral 1 4) 4
        && I64.beq (pt_char PositionEncoding.utf16 pt_astral 1 4) 2

/// The same fact read through `utf16_units_between` directly, so the count does
/// not rest only on the path through the line index.
#[test]
def test_utf16_units_between_counts_an_astral_character_as_two : Bool :=
    I64.beq (utf16_units_between pt_astral 0 4) 2
        && I64.beq (utf16_units_between pt_astral 0 5) 3
        && I64.beq (utf16_units_between pt_mixed 0 7) 5
        && I64.beq (utf16_units_between pt_mixed 0 8) 6

/// UTF-8 counts bytes, so it is the one encoding that needs no knowledge of the
/// text at all -- asserted on a line that is NOT ASCII, where a shared scan could
/// plausibly have been wired in and got this wrong.
#[test]
def test_utf8_character_is_a_byte_offset_even_on_a_non_ascii_line : Bool :=
    I64.beq (pt_char PositionEncoding.utf8 pt_mixed 1 8) 8
        && I64.beq (pt_char PositionEncoding.utf8 pt_astral 1 5) 5

#[test]
def test_ascii_lines_agree_across_encodings : Bool :=
    pt_agree pt_crlf 1 1
        && pt_agree pt_crlf 3 2
        && pt_agree pt_mixed 2 6
        && pt_agree pt_empty 1 0

// --- The line index ---

/// Starts and stops for the three terminator shapes: a bare `\n`, a CRLF whose
/// `\r` must NOT be part of the line, and a final line with no terminator at all.
#[test]
def test_line_index_handles_lf_crlf_and_a_missing_final_newline : Bool :=
    let ix : LineIndex := line_index_of_source pt_crlf in
    I64.beq (line_count ix) 3
        && I64.beq (pt_start ix 1) 0 && I64.beq (pt_stop ix 1) 1
        && I64.beq (pt_start ix 2) 2 && I64.beq (pt_stop ix 2) 4
        && I64.beq (pt_start ix 3) 6 && I64.beq (pt_stop ix 3) 9

/// A file ending in a newline has an empty LAST line, because an editor shows one
/// and will put a cursor on it.
///
/// Its start is the file's LENGTH (2), not the index of the newline (1). That is
/// the point rather than an off-by-one: no line's `[start, stop)` contains a
/// terminator byte, so the newline at byte 1 belongs to no line at all and the
/// empty line after it begins at the byte past it.
#[test]
def test_a_trailing_newline_opens_an_empty_final_line : Bool :=
    let ix : LineIndex := line_index_of_source pt_trailing_newline in
    I64.beq (line_count ix) 2 && I64.beq (pt_start ix 2) 2 && I64.beq (pt_stop ix 2) 2

/// The empty document is one empty line, not zero lines: an editor with an empty
/// buffer is showing line 1, and `initialize` on a new file must be able to name
/// position 0/0.
#[test]
def test_the_empty_source_is_one_empty_line : Bool :=
    let ix : LineIndex := line_index_of_source pt_empty in
    I64.beq (line_count ix) 1 && I64.beq (pt_start ix 1) 0 && I64.beq (pt_stop ix 1) 0

/// The ASCII flag drives which conversion path runs, so it is asserted on both
/// sides rather than only where it is convenient.
#[test]
def test_only_the_line_with_the_em_dash_is_marked_non_ascii : Bool :=
    let ix : LineIndex := line_index_of_source pt_mixed in
    Bool.not (pt_is_ascii ix 1) && pt_is_ascii ix 2 && pt_is_ascii ix 3

/// Line 3 exists because of the trailing newline and is empty, so it is ASCII.
#[test]
def test_an_empty_final_line_is_ascii : Bool :=
    pt_is_ascii (line_index_of_source pt_mixed) 3

// --- Clamping, and the line that is not there ---

/// A character past the end of a line means the end of the line, per the
/// specification.
///
/// The third assertion is the one with teeth: wire line 0 of `pt_mixed` stops at
/// byte 8, and character 99 must clamp to 8 rather than run on into line 2. A
/// clamp to the END OF THE FILE would give 26 here and pass on the astral
/// fixture, which is a single line.
#[test]
def test_a_character_past_the_line_end_clamps_to_the_line_end : Bool :=
    I64.beq (pt_off PositionEncoding.utf16 pt_astral 0 99) 5
        && I64.beq (pt_off PositionEncoding.utf8 pt_astral 0 99) 5
        && I64.beq (pt_off PositionEncoding.utf16 pt_mixed 0 99) 8

/// THE clamp that distinguishes up from down. UTF-16 character 1 on `😀x` sits
/// BETWEEN the surrogate pair, so no byte offset names it. Clamping down gives
/// byte 0 (the start of the emoji, where the cursor actually is); clamping up
/// would give byte 4 and move the cursor past the character the client placed it
/// in.
#[test]
def test_a_character_inside_a_surrogate_pair_clamps_down_to_the_character_start : Bool :=
    I64.beq (pt_off PositionEncoding.utf16 pt_astral 0 1) 0
        && I64.beq (pt_off PositionEncoding.utf16 pt_astral 0 0) 0
        && I64.beq (pt_off PositionEncoding.utf16 pt_astral 0 2) 4

/// A byte offset inside a multi-byte character cannot arise from the wire, but it
/// can arise from a corrupt or synthesized location, and `String.slice`-based
/// counting would answer 0 for a whole line rather than a wrong number. The count
/// is over the bytes actually before the offset, so the partial character counts
/// as its own single unit -- the same rule `lang/parser/position.mo`'s
/// mid-character test pins on its own side.
#[test]
def test_a_mid_character_offset_counts_the_bytes_before_it : Bool :=
    I64.beq (utf16_units_between pt_mixed 0 4) 4
        && I64.beq (utf16_units_between pt_mixed 0 5) 4

/// A line past the end is `Option.none`, which is NOT the same answer as a clamp
/// and must not be conflated: reporting it is a client bug, while a character
/// past a line's end is routine.
#[test]
def test_a_line_past_the_end_has_no_position : Bool :=
    I64.beq (pt_off PositionEncoding.utf16 pt_astral 5 0) (-1)
        && I64.beq (pt_char PositionEncoding.utf16 pt_astral 5 0) (-1)

/// The last line of a trailing-newline file IS a real line and must convert, in
/// both directions: wire line 1 is source line 2, and its only legal offset is
/// byte 2.
#[test]
def test_the_empty_final_line_converts : Bool :=
    I64.beq (pt_off PositionEncoding.utf16 pt_trailing_newline 1 0) 2
        && I64.beq (pt_char PositionEncoding.utf16 pt_trailing_newline 2 2) 0

/// A negative character clamps to the start of the line rather than wrapping into
/// the previous one through `start + character`. Source line 2 starts at byte 9,
/// so a clamp that used the line's own start answers 9; one that did the addition
/// anyway would answer 5, which is on line 1.
#[test]
def test_a_negative_character_clamps_to_the_line_start : Bool :=
    I64.beq (pt_off PositionEncoding.utf16 pt_mixed 1 (0 - 4)) 9

// --- The encoding name, on the wire ---

#[test]
def test_encoding_names_round_trip : Bool :=
    match position_encoding_from_string "utf-8" {
        Option.none => false,
        Option.some e => String.beq (position_encoding_name e) "utf-8",
    }

#[test]
def test_utf16_is_spelled_with_a_hyphen_and_no_capital : Bool :=
    String.beq (position_encoding_name PositionEncoding.utf16) "utf-16"

/// An unrecognized name answers `Option.none` rather than defaulting silently: a
/// client that asked for something else and was quietly given utf-16 is exactly
/// the desynchronization this module is built to prevent.
#[test]
def test_an_unknown_encoding_name_is_rejected_not_defaulted : Bool :=
    match position_encoding_from_string "utf-32" {
        Option.none => true,
        Option.some _e => false,
    }

#[test]
def test_the_default_encoding_is_utf16 : Bool :=
    match position_encoding_default {
        PositionEncoding.utf8 => false,
        PositionEncoding.utf16 => true,
    }

// --- `offset_after_char`: where a one-character range ends ---
//
// The byte lengths here are the point of the whole module restated at the
// smallest scale: an em dash is 3 bytes and an astral character is 4, so "advance
// by one" is not "advance by one byte" and a `+ 1` would be right only for ASCII.

/// `"abc"`: every character one byte, so the walk is the arithmetic it would be
/// if UTF-8 did not exist.
#[test]
def test_advancing_an_ascii_character_costs_one_byte : Bool :=
    I64.beq (offset_after_char "abc" 0) 1 && I64.beq (offset_after_char "abc" 2) 3

/// THE case a `+ 1` gets wrong. `pt_mixed`'s em dash is `E2 80 94` at bytes 3-5,
/// so the character after the one at byte 3 begins at byte 6.
#[test]
def test_advancing_an_em_dash_costs_three_bytes : Bool :=
    I64.beq (offset_after_char pt_mixed 3) 6

/// An astral character is FOUR bytes and one code point. A `+ 1` here would name
/// a byte inside the emoji.
#[test]
def test_advancing_an_astral_character_costs_four_bytes : Bool :=
    I64.beq (offset_after_char pt_astral 0) 4

/// Started from INSIDE a character -- byte 4 of the em dash -- the answer is the
/// same next boundary, not one past the offset. This is the case a slice-based
/// implementation reports as `offset` itself, which would silently produce a
/// zero-width range where a one-character range was wanted.
#[test]
def test_advancing_from_inside_a_character_reaches_the_next_boundary : Bool :=
    I64.beq (offset_after_char pt_mixed 4) 6

/// At the last byte of the source the answer is the source's length, and past it
/// it does not run off the end.
#[test]
def test_advancing_at_the_end_of_the_source_is_clamped : Bool :=
    I64.beq (offset_after_char pt_astral 4) 5
        && I64.beq (offset_after_char pt_astral 5) 5
        && I64.beq (offset_after_char pt_empty 0) 0

/// A point ON a terminator widens over that terminator and no further: the CRLF
/// fixture at byte 4 (the `\r`) stops at byte 5 (the `\n`), and the `\n` at byte
/// 5 stops at byte 6, which is the first `c`. Neither runs to the end of the
/// line.
#[test]
def test_advancing_over_a_terminator_stops_at_the_next_character : Bool :=
    I64.beq (offset_after_char pt_crlf 4) 5 && I64.beq (offset_after_char pt_crlf 5) 6

// --- `wire_range_of_points`: a point becomes a range ---

/// The sentinel `pt_range` hands back for `Option.none`: a line of -1 cannot
/// come out of a real source, so an assertion that sees one knows the conversion
/// failed rather than silently comparing against a plausible position. The two
/// tests that care about the distinction read the `Option` directly, which is
/// clearer than unwrapping it -- this exists so the range-comparing helpers can
/// return a `WireRange` at all.
def pt_range_missing : WireRange :=
    wire_range_mk (wire_position_mk (-1) (-1)) (wire_position_mk (-1) (-1))

/// The range of SOURCE `[so, eo)` on lines `[sl, el]`, or that sentinel.
#[partial]
def pt_range (enc : PositionEncoding) (src : String) (sl : I64) (so : I64) (el : I64)
    (eo : I64) : WireRange :=
    match wire_range_of_points enc (line_index_of_source src) src sl so el eo {
        Option.none => pt_range_missing,
        Option.some r => r,
    }

/// Compare a converted range against four scalars, so no test def holds a
/// `WireRange` it then reaches into.
#[partial]
def pt_range_eq (enc : PositionEncoding) (src : String) (sl : I64) (so : I64) (el : I64)
    (eo : I64) (rl : I64) (rc : I64) (ql : I64) (qc : I64) : Bool :=
    let r : WireRange := pt_range enc src sl so el eo in
    I64.beq (wire_position_line (wire_range_start r)) rl
        && I64.beq (wire_position_character (wire_range_start r)) rc
        && I64.beq (wire_position_line (wire_range_end r)) ql
        && I64.beq (wire_position_character (wire_range_end r)) qc

/// A real range is translated and NOT touched: declaration ranges are the
/// caller that must come through unchanged, and a widening that fired on a
/// non-empty range would move every declaration's end.
#[test]
def test_a_non_empty_range_is_translated_unchanged : Bool :=
    pt_range_eq PositionEncoding.utf8 pt_mixed 1 0 1 3 0 0 0 3
        && pt_range_eq PositionEncoding.utf16 pt_mixed 1 0 1 3 0 0 0 3

/// A whole-file range, line 1 to the empty final line. Ranges cross lines
/// routinely; this pins that the two ends are converted independently.
#[test]
def test_a_range_may_span_lines : Bool :=
    pt_range_eq PositionEncoding.utf8 pt_mixed 1 0 3 26 0 0 2 0

/// A zero-width point mid-line becomes one character wide, in both encodings.
#[test]
def test_a_point_becomes_a_one_character_range : Bool :=
    pt_range_eq PositionEncoding.utf8 pt_mixed 1 1 1 1 0 1 0 2
        && pt_range_eq PositionEncoding.utf16 pt_mixed 1 1 1 1 0 1 0 2

/// The same point under the two encodings, on the one line where they disagree:
/// `// — x`, an em dash at bytes 3-5. Widening covers the whole character, so
/// UTF-8 advances three units and UTF-16 one.
#[test]
def test_widening_covers_the_whole_character_in_both_encodings : Bool :=
    pt_range_eq PositionEncoding.utf8 pt_mixed 1 3 1 3 0 3 0 6
        && pt_range_eq PositionEncoding.utf16 pt_mixed 1 3 1 3 0 3 0 4

/// An astral character: one code point, two UTF-16 units, four bytes. A widening
/// that advanced one WIRE unit would underline half a surrogate pair.
#[test]
def test_widening_an_astral_point_is_four_bytes_and_two_units : Bool :=
    pt_range_eq PositionEncoding.utf8 pt_astral 1 0 1 0 0 0 0 4
        && pt_range_eq PositionEncoding.utf16 pt_astral 1 0 1 0 0 0 0 2

#[test]
def test_widening_the_character_after_an_astral_one : Bool :=
    pt_range_eq PositionEncoding.utf8 pt_astral 1 4 1 4 0 4 0 5
        && pt_range_eq PositionEncoding.utf16 pt_astral 1 4 1 4 0 2 0 3

/// A point at the end of the source has no character to widen over, so it stays
/// zero-width rather than inventing a byte.
#[test]
def test_a_point_at_the_end_of_the_source_stays_empty : Bool :=
    pt_range_eq PositionEncoding.utf16 pt_astral 1 5 1 5 0 3 0 3
        && pt_range_eq PositionEncoding.utf8 pt_empty 1 0 1 0 0 0 0 0

/// THE RESIDUAL CASE the function's doc records: byte 1 of `😀x` is inside the
/// emoji, and both the mid-character offset and its successor round up to the
/// same wire character, so the range stays empty. Pinned so that a change to the
/// widening shows up here rather than as an inexplicable squiggle.
#[test]
def test_a_point_inside_a_character_cannot_widen : Bool :=
    pt_range_eq PositionEncoding.utf16 pt_astral 1 1 1 1 0 2 0 2
        && pt_range_eq PositionEncoding.utf8 pt_astral 1 1 1 1 0 1 0 4

/// A line past the last one answers no range at all, which is distinct from an
/// empty range on a real line -- the caller must not conflate them, since one is
/// a client bug and the other is routine.
#[test]
def test_a_line_past_the_end_answers_no_range : Bool :=
    match wire_range_of_points PositionEncoding.utf8 (line_index_of_source pt_mixed)
        pt_mixed 9 0 9 0 {
        Option.none => true,
        Option.some _r => false,
    }

/// The same distinction seen from the other side: a range on a real line is
/// `Option.some` even when it is empty, so "no range" and "empty range" are
/// different answers from this function rather than both being `Option.none`.
#[test]
def test_an_empty_range_on_a_real_line_is_still_a_range : Bool :=
    match wire_range_of_points PositionEncoding.utf8 (line_index_of_source pt_empty)
        pt_empty 1 0 1 0 {
        Option.none => false,
        Option.some _r => true,
    }

// --- The other direction: an offset names its line ---
//
// `line_of_offset` answers what `line_at` cannot: not "where is line 4" but
// "which line is byte 37 on". It is the half of a cursor conversion the wire
// side does not need -- `offset_of_wire` goes the other way -- and the half a
// text scan DOES need, since what a scan for the identifier under the cursor
// produces is a pair of byte offsets.

/// `line_of_offset`, as a number, or -1 for the absent answer.
#[partial]
def pt_line_of (src : String) (off : I64) : I64 :=
    match line_of_offset (line_index_of_source src) off {
        Option.none => -1,
        Option.some n => n,
    }

/// A range built from two BYTE offsets, compared against four scalars -- the
/// offset-space twin of `pt_range_eq`, and the shape hover and a symbol's own
/// text span both hand in.
#[partial]
def pt_off_range_eq (enc : PositionEncoding) (src : String) (so : I64) (eo : I64)
    (rl : I64) (rc : I64) (ql : I64) (qc : I64) : Bool :=
    match wire_range_of_offsets enc (line_index_of_source src) src so eo {
        Option.none => false,
        Option.some r =>
            I64.beq (wire_position_line (wire_range_start r)) rl
                && I64.beq (wire_position_character (wire_range_start r)) rc
                && I64.beq (wire_position_line (wire_range_end r)) ql
                && I64.beq (wire_position_character (wire_range_end r)) qc,
    }

/// `pt_mixed`'s layout, so the numbers below are arithmetic a reader can check:
/// line 1 is `// — x`, bytes 0-7 with its newline at 8; line 2 starts at 9 and is
/// `def y : I64 := 1`, bytes 9-24 with its newline at 25; line 3 is the empty
/// final line starting at 26, which is the source's length.
///
/// EVERY BOUNDARY IS ASSERTED, and the three that matter are the ones at 8, 25 and
/// 26. Byte 8 is line 1's `\n`, which belongs to NO line's `[start, stop)` -- yet
/// `wire_character` clamps it into line 1, so the only rule that makes the two
/// functions agree about where that byte is, is "the last line starting at or
/// before it". Byte 25 is the same case one line down, and byte 26 is the START of
/// the empty final line rather than the end of line 2, which is the distinction a
/// `<=` written the other way round would get wrong.
#[test]
def test_an_offset_resolves_to_its_own_line : Bool :=
    I64.beq (pt_line_of pt_mixed 0) 1
        && I64.beq (pt_line_of pt_mixed 7) 1
        && I64.beq (pt_line_of pt_mixed 8) 1
        && I64.beq (pt_line_of pt_mixed 9) 2
        && I64.beq (pt_line_of pt_mixed 24) 2
        && I64.beq (pt_line_of pt_mixed 25) 2
        && I64.beq (pt_line_of pt_mixed 26) 3

/// Past the end of the source is the last line rather than an absence, matching
/// `wire_character`'s clamp: a byte offset past the end is routine for a span whose
/// stop is at end-of-file, while a LINE past the end is a client bug that
/// `line_at` reports as an absence. The two are different questions and
/// deliberately have different answers.
#[test]
def test_an_offset_past_the_end_is_the_last_line : Bool :=
    I64.beq (pt_line_of pt_mixed 99) 3
        && I64.beq (pt_line_of pt_empty 0) 1

/// An identifier's byte span becomes a range, on the one line where the two
/// encodings disagree -- the em dash at bytes 3-5, so bytes 3 through 6 are
/// characters 3-6 in UTF-8 and 3-4 in UTF-16.
#[test]
def test_a_byte_span_becomes_its_range : Bool :=
    pt_off_range_eq PositionEncoding.utf8 pt_mixed 3 6 0 3 0 6
        && pt_off_range_eq PositionEncoding.utf16 pt_mixed 3 6 0 3 0 4

/// A span whose two ends are on DIFFERENT lines. The end offset is the first byte
/// of line 2, so its wire character is 0 rather than the newline's column -- the
/// case a version that resolved only the START's line would get wrong by putting
/// the end on line 1 at character 9.
#[test]
def test_a_byte_span_may_cross_a_line : Bool :=
    pt_off_range_eq PositionEncoding.utf8 pt_mixed 0 9 0 0 1 0
        && pt_off_range_eq PositionEncoding.utf16 pt_mixed 0 9 0 0 1 0

/// A zero-width span widens by one character here too, because the widening lives
/// in `wire_range_of_points` rather than in this entry point. A cursor with no
/// selection is exactly this input, and a hover whose range is empty is a hover no
/// client underlines.
#[test]
def test_a_zero_width_span_widens_the_same_way : Bool :=
    pt_off_range_eq PositionEncoding.utf8 pt_mixed 3 3 0 3 0 6
        && pt_off_range_eq PositionEncoding.utf16 pt_mixed 3 3 0 3 0 4

/// The empty list of lines, named rather than written as a bare `List.empty` in
/// argument position, whose element type would have to be inferred from the
/// constructor.
def pt_no_lines : List LineInfo := List.empty

/// A HAND-BUILT index with no lines is the one input for which both new functions
/// answer an absence, and it is reachable because `LineIndex` is a struct with a
/// public field. The alternative -- treating "no lines" as "line 1" -- would put a
/// cursor in a document that has no text.
#[test]
def test_an_index_with_no_lines_has_no_line : Bool :=
    match line_of_offset (LineIndex.mk pt_no_lines) 0 {
        Option.none => true,
        Option.some _n => false,
    }

/// The same absence one level up, so that a caller which skipped `line_of_offset`
/// cannot get a range out of a source with no lines.
#[test]
def test_a_span_in_an_index_with_no_lines_has_no_range : Bool :=
    match wire_range_of_offsets PositionEncoding.utf8 (LineIndex.mk pt_no_lines) "" 0 0 {
        Option.none => true,
        Option.some _r => false,
    }

// --- A source far larger than one native stack ---
//
// `line_index_of_source` walks its input one byte at a time, so its recursion
// DEPTH is the file size. Written naively that is a real machine call per byte,
// and it exhausts the compiled binary's stack somewhere between 100 KB and 209 KB
// of source -- measured, and the failure is a SIGSEGV inside the garbage
// collector's own stack-clearing loop rather than a clean error, which is why it
// reads as a mysterious crash rather than as a stack overflow. `lang/src/scope.mo`
// (435 KB) and `lang/src/module.mo` (331 KB) are both far past that, i.e. exactly
// the files an editor opens, so this is not a hypothetical input.
//
// The remedy is not a smaller input. It is the shape of the scan: the compiler
// rewrites a self-recursive tail call into a loop (`lang/src/codegen/tco.mo`), and
// that rewrite fires only when a merge point is fed by at most ONE self-call. The
// original `if/else` whose BOTH branches recursed fed a single merge two of them,
// so pruning the site would have emptied its phi and the pass abandoned the whole
// transform -- leaving the per-byte call. This test is the pin that keeps the
// scan in a shape the rewrite accepts, and its size is the point rather than an
// accident: at 320 KB it is past every measured threshold with room to spare, and
// small enough that a broken scan still fails as a crash rather than as a timeout.

/// One 40-byte line: 39 filler bytes and a newline. Its length is asserted in the
/// test below rather than trusted to a hand count of the literal.
def pt_big_line : String :=
    "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n"

/// Four of them, so the doubling below starts from a block rather than a single
/// line and needs fewer steps for the same size.
def pt_big_block : String :=
    String.concat (String.concat pt_big_line pt_big_line)
        (String.concat pt_big_line pt_big_line)

/// `s` doubled on itself `n` times.
///
/// Doubling rather than concatenating line by line on purpose: `String.concat`
/// copies both sides, so a fold over 8192 pieces recopies the accumulated prefix
/// at every step and is quadratic in the total length. Eleven doublings of a
/// 160-byte block reach 320 KB in eleven copies of at most 320 KB instead.
///
/// The recursion here is 11 deep and one branch recurses, which is the shape
/// `tco.mo` accepts -- a fixture that overflowed the stack on its own way to
/// testing an overflow would be a poor probe.
#[partial]
def pt_big_grow (n : I64) (s : String) : String :=
    if I64.lt n 1
    then s
    else pt_big_grow (I64.sub n 1) (String.concat s s)

/// 160 * 2^`n` bytes of a regular, pure-ASCII text file.
def pt_big_source (n : I64) : String :=
    pt_big_grow n pt_big_block

/// `line_of_offset` on an index the caller already holds, -1 for the absent
/// answer -- the big-source twin of `pt_line_of`, which rebuilds the index.
#[partial]
def pt_big_line_of (ix : LineIndex) (off : I64) : I64 :=
    match line_of_offset ix off {
        Option.none => -1,
        Option.some n => n,
    }

/// The scan over a source past every measured stack threshold. `pt_big_source 11`
/// is 327,680 bytes: 8192 lines of 40, and the empty final line a trailing newline
/// always leaves, so 8193 lines.
///
/// The offsets asserted are the three that a per-byte scan can plausibly get
/// wrong at this scale -- the first line's extent, the LAST line's start (which is
/// the source's length, one past the final newline), and an offset past the end
/// (which `line_of_offset` answers as the last line rather than as an absence).
/// A scan that silently stopped early would still pass a `line_count` assertion
/// alone only if it also miscounted, so both are checked.
#[test]
def test_line_index_scans_a_source_far_larger_than_one_stack : Bool :=
    let src : String := pt_big_source 11 in
    let ix : LineIndex := line_index_of_source src in
    I64.beq (String.length pt_big_line) 40
        && I64.beq (String.length src) 327680
        && I64.beq (line_count ix) 8193
        && I64.beq (pt_start ix 1) 0
        && I64.beq (pt_stop ix 1) 39
        && pt_is_ascii ix 1
        && I64.beq (pt_start ix 8192) 327640
        && I64.beq (pt_stop ix 8192) 327679
        && I64.beq (pt_start ix 8193) 327680
        && I64.beq (pt_big_line_of ix 0) 1
        && I64.beq (pt_big_line_of ix 39) 1
        && I64.beq (pt_big_line_of ix 40) 2
        && I64.beq (pt_big_line_of ix 327679) 8192
        && I64.beq (pt_big_line_of ix 327680) 8193

/// The same source read the other way: a wire position back to its byte offset,
/// which resolves through the index twice (line, then the character's bytes
/// within it). The three positions are the file's first byte, the final newline
/// (wire line 8191 -- source line 8192, since the wire is 0-based) and the empty
/// final line's own start, which is the source length. A scan that lost its tail
/// is caught by the far end rather than only by the near one.
#[test]
def test_the_big_source_converts_in_both_directions : Bool :=
    I64.beq (pt_off PositionEncoding.utf8 (pt_big_source 11) 0 0) 0
        && I64.beq (pt_off PositionEncoding.utf8 (pt_big_source 11) 8191 39) 327679
        && I64.beq (pt_off PositionEncoding.utf8 (pt_big_source 11) 8192 0) 327680
