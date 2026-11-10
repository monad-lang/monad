/// The wire shapes for a range and a location: what a jump target and an outline
/// entry are made of.
///
/// THIS FILE EXISTS BECAUSE TWO FEATURES NOW READ THE SAME CONVERSION. The
/// diagnostic tests pin what a squiggle looks like on the wire, and they do it
/// through `wire_diagnostic_of_lang`, which is a diagnostic's whole path. The
/// conversion underneath it -- `lang`'s two `Location`s to a `WireRange` -- is now
/// read directly by definition, by `documentSymbol` and by hover's cursor range,
/// and none of those takes the diagnostic path. So the conversion is pinned here
/// on its own, at the four places its own contract has edges: an ordinary
/// declaration, a point range, a non-ASCII line, and a range that CANNOT be
/// placed.
///
/// THE UNPLACEABLE RANGE IS THE CASE WORTH THE FILE. `wire_range_of_source_range`
/// answers an `Option`, and a diagnostic and a jump target disagree about what to
/// do with the absence -- the diagnostic reports at the origin, because a broken
/// file shown as clean is worse than a marker in the wrong place, while a jump to
/// the origin is a lie the user will follow. So the absence is a value here rather
/// than something each caller decides by inspecting a range, and the test pins
/// that the absence is REACHABLE rather than asserting a branch no input takes.
///
/// EXPECTED WIRE TEXT IS AN EXACT STRING. The shapes are the specification's, its
/// objects are unordered, and `Json.to_string` walks a `BTreeMap` -- so the keys
/// come out sorted (`end` before `start`, `character` before `line`, `range`
/// before `uri`). Writing the expected string in the order the fields are
/// CONSTRUCTED would fail, and that is the point of asserting text: a client
/// parses by key, so key order is a wire detail, but a test that compared
/// something looser would not notice a missing field or an invented separator.
///
/// Field reads go through typed accessor defs (`wt_*`), never inline in a
/// `#[test]` def, per this repo's recorded `#[test]` plus struct-field codegen
/// hazard. The `wt_` prefix is collision-avoiding: whole-program scope is shared
/// with every other mote's tests.
use json::json {Json}
use lang::types {Location, SourceRange}
use std::path {Path}
use toolkit::position {
    LineIndex, PositionEncoding, WirePosition, WireRange, line_index_of_source,
    wire_position_character, wire_position_line, wire_range_end, wire_range_start,
}
use toolkit::wire {
    location_json, location_json_of_source_range, wire_position_json, wire_range_json,
    wire_range_of_source_range, wire_range_origin,
}

// --- Fixtures ---

/// Two defs, one per line, so the second one's offsets are arithmetic a reader can
/// check by hand: line 1 is `def a : I64 := 1` (bytes 0-15, newline at 16), so line
/// 2 starts at 17, is `def b : I64 := 2` (bytes 17-32), and has its newline at 33.
/// The whole source is 34 bytes.
///
/// The same text `diagnostic_tests.mo` uses, and deliberately not shared BY
/// reference: a test file that imported another test file's fixture would make one
/// file's failure two files' failure.
def wt_two_defs : String := "def a : I64 := 1\ndef b : I64 := 2\n"

/// A source whose FIRST line contains a three-byte character, because that is the
/// only shape that tells the two encodings apart: for ASCII they agree, so every
/// assertion below would pass against a converter that ignored the negotiation
/// entirely. `// — x` is 8 bytes -- `//`, a space, the em dash's three, a space, `x`
/// -- so an em dash at byte 3 ends at byte 6.
def wt_non_ascii : String := "// — x\ndef y : I64 := 1\n"

def wt_path : String := "file:///w/probe.mo"

// --- Building a range from scalars ---

/// One field read each, one explicit return type each: `lang`'s `Location` and
/// `SourceRange` have no accessors, and a field read written inline is the recorded
/// codegen hazard.
#[partial]
def wt_loc (offset : I64) (line : I64) (column : I64) : Location :=
    Location.mk offset line column

#[partial]
def wt_span_of (so : I64) (sl : I64) (sc : I64) (eo : I64) (el : I64) (ec : I64) : SourceRange :=
    SourceRange.mk (wt_loc so sl sc) (wt_loc eo el ec) (Option.some (Path.unsafe wt_path))

/// `def b : I64 := 2` -- bytes 17 to 33, both on line 2.
#[partial]
def wt_decl_b : SourceRange := wt_span_of 17 2 1 33 2 17

// --- The conversion, once, so no test repeats the index ---

/// The conversion under test, with the `LineIndex` built from the same text the
/// span's offsets are in -- which is the caller's contract and the one thing a test
/// can get wrong while still passing.
#[partial]
def wt_convert (enc : PositionEncoding) (src : String) (sr : SourceRange) : Option WireRange :=
    wire_range_of_source_range enc (line_index_of_source src) src sr

// --- Rendering a result ---

/// A wire range as `line:character-line:character`, or `<none>`.
///
/// A rendering rather than a comparison against the constructors: the numbers are
/// what the client sees, and a test asserting "the start is a `WirePosition`" would
/// pass for any position at all.
#[partial]
def wt_range_text (o : Option WireRange) : String :=
    match o {
        Option.none => "<none>",
        Option.some r => wt_point (wire_range_start r) ++ "-" ++ wt_point (wire_range_end r),
    }

#[partial]
def wt_point (p : WirePosition) : String :=
    I64.to_string (wire_position_line p) ++ ":" ++ I64.to_string (wire_position_character p)

/// The wire range a conversion produced, for a test that has already established it
/// converts. `wire_range_origin` is the fallback so that a conversion which started
/// answering `<none>` fails the JSON comparison rather than crashing here -- the
/// "unplaceable" test below is what makes that fallback unreachable for these.
#[partial]
def wt_first (o : Option WireRange) : WireRange :=
    match o {
        Option.none => wire_range_origin,
        Option.some r => r,
    }

/// The one place `Json` appears in a TYPE position in this file. Every assertion
/// below compares wire text, so without this def the import resolves only as a
/// qualified prefix (`Json.to_string`) and the unused-import pass reports it -- the
/// trap `jsonrpc_tests.mo` and `diagnostic_tests.mo` both record.
def wt_json_text (j : Json) : String := Json.to_string j

#[partial]
def wt_opt_text (o : Option Json) : String :=
    match o {
        Option.none => "<none>",
        Option.some j => wt_json_text j,
    }

// --- The conversion ---

/// The ordinary case: a declaration's two ends, on one line, in bytes that happen
/// to be the characters.
#[test]
def test_a_declaration_span_becomes_its_two_wire_points : Bool :=
    String.beq (wt_range_text (wt_convert PositionEncoding.utf8 wt_two_defs wt_decl_b)) "1:0-1:16"
        && String.beq (wt_range_text (wt_convert PositionEncoding.utf16 wt_two_defs wt_decl_b))
            "1:0-1:16"

/// A POINT -- `start = end` -- is widened one character, and the widening has to
/// survive the move into this module rather than living only on the diagnostic
/// path. It is the shape `lang` builds for every parse failure (`ranged_parse_
/// failure` makes both ends the same `Location`) and the shape hover sends for an
/// identifier that is one character long.
#[test]
def test_a_point_range_is_widened_one_character : Bool :=
    let point : SourceRange := wt_span_of 17 2 1 17 2 1 in
    String.beq (wt_range_text (wt_convert PositionEncoding.utf8 wt_two_defs point)) "1:0-1:1"

/// The same source read as two encodings, and the numbers differ because the
/// character IS three bytes: byte 3 through byte 6 is characters 3-6 in UTF-8 and
/// 3-4 in UTF-16.
///
/// A converter that ignored the negotiated encoding -- or that assumed ASCII, which
/// this corpus's comments make fatal -- would answer `0:3-0:6` for both. The
/// asymmetric assertion is what makes that failure visible: checking only utf-8
/// would pass.
#[test]
def test_a_non_ascii_span_differs_between_the_encodings : Bool :=
    let dash : SourceRange := wt_span_of 3 1 3 6 1 6 in
    String.beq (wt_range_text (wt_convert PositionEncoding.utf8 wt_non_ascii dash)) "0:3-0:6"
        && String.beq (wt_range_text (wt_convert PositionEncoding.utf16 wt_non_ascii dash)) "0:3-0:4"

/// A range whose START line is not in the index has no wire form, and the absence
/// is stated rather than filled in with a made-up position.
///
/// Line 99 is past the end of a two-line source. `position.mo`'s converter declines
/// on exactly this input and nothing else, so this is the reachable half of the
/// `Option` and the reason the return type is not a bare `WireRange`.
#[test]
def test_an_unplaceable_range_has_no_wire_form : Bool :=
    let beyond : SourceRange := wt_span_of 0 99 1 0 99 1 in
    String.beq (wt_range_text (wt_convert PositionEncoding.utf8 wt_two_defs beyond)) "<none>"

/// The span's own `path` is NOT on the wire, and this is the decision behind
/// `location_json`'s URI argument. `lang`'s path is the compiler's notion of a file
/// -- the one `check` prints -- while the wire wants the URI the client named the
/// document by, and neither is recoverable from the other without deciding how a
/// workspace root maps to URIs.
///
/// Two spans differing ONLY in path, converting to the same wire range, is what
/// pins that the path is dropped rather than quietly preferred to the caller's URI.
#[test]
def test_the_spans_own_path_is_not_on_the_wire : Bool :=
    let other : SourceRange :=
        SourceRange.mk (wt_loc 17 2 1) (wt_loc 33 2 17) (Option.some (Path.unsafe "/a/path")) in
    String.beq (wt_json_text (wire_range_json (wt_first (wt_convert PositionEncoding.utf8
        wt_two_defs other))))
        (wt_json_text (wire_range_json (wt_first (wt_convert PositionEncoding.utf8
            wt_two_defs wt_decl_b))))

// --- The shapes ---

/// The position, byte for byte: sorted keys, no separators invented.
#[test]
def test_a_position_is_a_line_and_a_character : Bool :=
    String.beq (wt_json_text (wire_position_json (wire_range_start
        (wt_first (wt_convert PositionEncoding.utf8 wt_two_defs wt_decl_b)))))
        "{\"character\":0,\"line\":1}"

/// The range, byte for byte, including the nesting.
#[test]
def test_a_range_is_two_positions : Bool :=
    String.beq (wt_json_text (wire_range_json (wt_first (wt_convert PositionEncoding.utf8
        wt_two_defs wt_decl_b))))
        "{\"end\":{\"character\":16,\"line\":1},\"start\":{\"character\":0,\"line\":1}}"

/// The origin, pinned as the two zeroes it is. A fallback whose position drifted
/// would move every diagnostic the checker could not place, which is a change no
/// other assertion in either test file would notice.
#[test]
def test_the_origin_is_the_first_character_of_the_first_line : Bool :=
    String.beq (wt_json_text (wire_range_json wire_range_origin))
        "{\"end\":{\"character\":0,\"line\":0},\"start\":{\"character\":0,\"line\":0}}"

/// A location: the caller's URI and the range. The URI is the caller's and is not
/// derived from anything, so the assertion uses one no `lang` path could have
/// produced -- a client that opened an unsaved buffer names it exactly this way.
#[test]
def test_a_location_is_a_uri_and_a_range : Bool :=
    String.beq (wt_json_text (location_json "untitled:Untitled-1"
        (wt_first (wt_convert PositionEncoding.utf8 wt_two_defs wt_decl_b))))
        (String.concat "{\"range\":{\"end\":{\"character\":16,\"line\":1},\"start\":{\"character\":0,\"line\":1}},\"uri\":\""
            (String.concat "untitled:Untitled-1" "\"}"))

/// The composed conversion -- what definition and `documentSymbol` actually call --
/// in both directions. The absent arm is the one that matters: a target that cannot
/// be placed must produce NO location rather than a location at the origin, because
/// the origin is the one wrong answer a client will happily act on.
///
/// The second half converts a two-def span against the index of the EMPTY source,
/// which is the smallest reachable way to make the start line absent.
#[test]
def test_a_location_of_a_source_range_composes : Bool :=
    let ix : LineIndex := line_index_of_source wt_two_defs in
    let empty : LineIndex := line_index_of_source "" in
    String.beq (wt_opt_text (location_json_of_source_range wt_path PositionEncoding.utf8 ix
        wt_two_defs wt_decl_b))
        (String.concat "{\"range\":{\"end\":{\"character\":16,\"line\":1},\"start\":{\"character\":0,\"line\":1}},\"uri\":\""
            (String.concat wt_path "\"}"))
        && String.beq (wt_opt_text (location_json_of_source_range wt_path PositionEncoding.utf8
            empty wt_two_defs wt_decl_b)) "<none>"
