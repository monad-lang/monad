/// Diagnostic tests: the message reduction, the range, and the exact bytes.
///
/// THE MESSAGE FIXTURES ARE VERBATIM, not paraphrased, and that matters more
/// than it looks. The reduction's whole job is to cut `lang`'s rendered
/// terminal output down to its header line, so a fixture invented from the
/// shape of the renderer would test the fixture rather than the renderer's
/// actual output. Both strings below were read off a real run (the type error
/// from `lang/src/tests/unify_tests.mo`'s "type mismatch" case, the parse error
/// from `lang/src/tests/decl_range_tests.mo`, printed through `cat -A` so the
/// caret alignment is copied rather than guessed); the only edit is the path,
/// replaced with a fixed one because the real path carries a pid and a shared
/// `/tmp` name collides across sharded runs.
///
/// The two are different SHAPES, which is the reason to have both: a type error
/// renders as header plus a `-->` arrow and stops, while a parse error renders
/// header, arrow, and then two lines of source with a caret under the offending
/// column. A reduction that cut at a fixed byte count, or that assumed the arrow
/// was the last line, would pass on one of these and fail on the other. Note
/// also that the parse fixture's second context line is EMPTY (`  2 | `) -- a
/// trailing-space line, so a reduction that trimmed whitespace per line would
/// still pass but a fixture written without the space would not be the real
/// output.
///
/// THE JSON ASSERTIONS ARE EXACT STRINGS, which is the only way to pin the
/// things that matter on the wire: that `BTreeMap` sorts keys alphabetically
/// (`message`, `range`, `severity`, `source`), that a range nests `start`/`end`
/// with `character` before `line`, and that no separators are invented. Every
/// expected string here was OBSERVED from a run before being written down; the
/// first draft of two of them was wrong by hand and the failure output is what
/// corrected them.
///
/// Field reads go through typed accessor defs (`dt_*`), never inline in a
/// `#[test]` def, per this repo's recorded `#[test]` plus struct-field codegen
/// hazard. The `dt_` prefix is collision-avoiding because whole-program scope is
/// shared with every other mote's tests, and `position_tests.mo` already holds
/// `pt_`.
use json::json {Json}
use lang::module {Diagnostic}
use lang::types {Location, SourceRange}
use toolkit::diagnostic {
    WireDiagnostic, diag_severity_error, diag_severity_hint, diag_severity_information,
    diag_severity_warning, diagnostic_header, diagnostic_source_name, wire_diagnostic_json,
    wire_diagnostic_message, wire_diagnostic_of_lang, wire_diagnostic_range,
    wire_diagnostic_severity, wire_diagnostics_json,
}
use toolkit::position {
    PositionEncoding, WireRange, line_index_of_source, wire_position_character,
    wire_position_line, wire_range_end, wire_range_start,
}

// --- Fixtures: real renderer output ---

/// `render_type_error` on an `unknown_var`, the most common user-facing
/// diagnostic there is. Two lines: header and arrow, with no source context --
/// that renderer has no source to quote, only a path.
def dt_type_message : String :=
    "error: unknown variable 'no_such_name' in bad\n" ++ "  --> /tmp/dt/probe.mo\n"

/// `render_parse_error` on `def bad ((( :=`, the unterminated group. Header,
/// arrow, and the `N | source` / caret context lines, ending with the blank line
/// the renderer adds after the second context line. Copied byte for byte from
/// the `cat -A` capture, path substituted: the context line is `  N | ` with
/// THREE leading spaces, and the caret sits at `6 + column - 1` -- fifteen
/// spaces for column 10.
def dt_parse_message : String :=
    "error: expected identifier at 1:10\n"
        ++ "  --> /tmp/dt/broken.mo:1:10\n"
        ++ "  1 | def bad ((( :=\n"
        ++ "               ^---\n"
        ++ "  2 | \n"

/// The source declaration ranges are taken from: two defs, one per line, so the
/// second one's offsets are arithmetic a reader can check by hand. Line 2 is
/// `def b : I64 := 2`, bytes 17-32, with its newline at 33 -- so the declaration
/// ends at offset 33, the first byte of the following line, which is the
/// exclusive end a caller wants.
def dt_two_defs : String := "def a : I64 := 1\ndef b : I64 := 2\n"

/// A source whose FIRST line contains a three-byte character, so a range on
/// line 1 converts to different wire characters under the two encodings. Same
/// text `position_tests.mo` uses, and the reason is worth restating: a server
/// that counted bytes would be right for ASCII and silently shift every range on
/// a line containing a comment with an em dash in it, which this corpus is full
/// of.
def dt_non_ascii : String := "// — x\ndef y : I64 := 1\n"

/// The message an em dash in a diagnostic would arrive in, to pin that the
/// prefix slice is a character boundary. `error: ` is seven ASCII bytes, so the
/// slice starts before the multi-byte character and cannot split it -- but the
/// assertion is what keeps a future change to the prefix's length honest.
def dt_non_ascii_message : String :=
    "error: unknown type '→' in fwd\n" ++ "  --> /tmp/dt/probe.mo\n"

// --- Accessors ---

def dt_loc (offset : I64) (line : I64) (column : I64) : Location :=
    Location.mk offset line column

def dt_span (a : Location) (b : Location) : SourceRange :=
    SourceRange.mk a b (Option.some "/tmp/dt/probe.mo")

def dt_make (msg : String) (r : Option SourceRange) : Diagnostic := Diagnostic.mk msg r

/// The one place `Json` appears in a TYPE position in this file. Every
/// assertion below compares wire text, so without this def the import is used
/// only as a qualified prefix (`Json.to_string`) and the unused-import pass
/// reports it -- the same trap `jsonrpc_tests.mo` records.
def dt_json_text (j : Json) : String := Json.to_string j

#[partial]
def dt_wire (enc : PositionEncoding) (src : String) (dg : Diagnostic) : WireDiagnostic :=
    wire_diagnostic_of_lang enc (line_index_of_source src) src dg

def dt_msg (d : WireDiagnostic) : String := wire_diagnostic_message d

def dt_sev (d : WireDiagnostic) : I64 := wire_diagnostic_severity d

def dt_range (d : WireDiagnostic) : WireRange := wire_diagnostic_range d

def dt_start_line (d : WireDiagnostic) : I64 :=
    wire_position_line (wire_range_start (dt_range d))

def dt_start_char (d : WireDiagnostic) : I64 :=
    wire_position_character (wire_range_start (dt_range d))

def dt_end_line (d : WireDiagnostic) : I64 := wire_position_line (wire_range_end (dt_range d))

def dt_end_char (d : WireDiagnostic) : I64 := wire_position_character (wire_range_end (dt_range d))

/// A diagnostic carrying a span, built from scalars so no test def ever holds a
/// `Location` or a `SourceRange` local.
#[partial]
def dt_span_of (msg : String) (enc : PositionEncoding) (src : String) (so : I64) (sl : I64)
    (sc : I64) (eo : I64) (el : I64) (ec : I64) : WireDiagnostic :=
    dt_wire enc src (dt_make msg (Option.some (dt_span (dt_loc so sl sc) (dt_loc eo el ec))))

/// The declaration `def b : I64 := 2` on `dt_two_defs`, as a diagnostic.
#[partial]
def dt_decl_b (msg : String) (enc : PositionEncoding) : WireDiagnostic :=
    dt_span_of msg enc dt_two_defs 17 2 1 33 2 17

// --- The message reduction ---

/// THE pin for the whole module: a type error's rendered terminal output becomes
/// the one sentence an editor should show. Everything the renderer added -- the
/// `error: ` prefix, the arrow, the path -- is gone, and the part a human reads
/// survives byte for byte.
#[test]
def test_a_type_error_message_reduces_to_its_header : Bool :=
    String.beq (diagnostic_header dt_type_message) "unknown variable 'no_such_name' in bad"

/// The other shape. A reduction that stopped at a fixed byte count, or that
/// dropped a fixed number of trailing lines, would pass the test above and fail
/// this one -- this message is four lines longer and its header is a third of the
/// length.
#[test]
def test_a_parse_error_message_reduces_to_its_header : Bool :=
    String.beq (diagnostic_header dt_parse_message) "expected identifier at 1:10"

/// The position inside the header -- `at 1:10` -- is KEPT, and deliberately. For
/// a parse error the range is one character wide and often on a later line than
/// the one the user is reading, so the header's line and column are doing work
/// the range alone cannot. Nothing strips them.
#[test]
def test_the_position_inside_a_parse_header_is_kept : Bool :=
    let h : String := diagnostic_header dt_parse_message in
    String.contains h "at 1:10" && Bool.not (String.contains h "-->")

/// A message with no newline at all never went through a renderer -- a
/// termination check's, say -- and comes back unchanged.
#[test]
def test_a_single_line_message_with_no_prefix_is_unchanged : Bool :=
    String.beq (diagnostic_header "strictly positive check failed")
        "strictly positive check failed"

/// ...and one that happens to carry the prefix has it stripped, since the
/// prefix is a rendering convention rather than a guarantee about the producer.
#[test]
def test_a_single_line_message_with_a_prefix_is_stripped : Bool :=
    String.beq (diagnostic_header "error: bad thing") "bad thing"

/// The prefix is matched EXACTLY, including its trailing space. `error:` with
/// nothing after it is a message whose author meant the colon, and slicing seven
/// bytes off it would leave nothing.
#[test]
def test_the_prefix_is_not_a_bare_colon : Bool :=
    String.beq (diagnostic_header "error:") "error:"

/// The non-empty-out guard, first arm: a header that is nothing but the prefix
/// falls back to the UNSTRIPPED header rather than returning "".
#[test]
def test_a_message_that_is_only_the_prefix_keeps_its_prefix : Bool :=
    String.beq (diagnostic_header "error: ") "error: "

/// The guard's second arm: a message whose own header line is empty falls back
/// to the whole message. A leading newline is malformed, but a client showing a
/// blank popup reads as a broken server rather than as a missing message.
#[test]
def test_a_message_whose_first_line_is_empty_falls_back_to_all_of_it : Bool :=
    String.beq (diagnostic_header "\n  --> /tmp/dt/probe.mo\n")
        "\n  --> /tmp/dt/probe.mo\n"

/// An empty message stays empty: the guard is "non-empty in, non-empty out",
/// and a caller that hands this module nothing gets nothing back rather than a
/// fabricated placeholder.
#[test]
def test_an_empty_message_stays_empty : Bool := String.beq (diagnostic_header "") ""

/// The prefix slice is seven ASCII bytes, so it cannot split a character even
/// when the message's own text starts with a multi-byte one. This is the
/// boundary case the reduction would corrupt if it sliced by character count
/// instead of by the prefix's known length.
#[test]
def test_a_prefix_is_stripped_before_a_multi_byte_character : Bool :=
    String.beq (diagnostic_header dt_non_ascii_message) "unknown type '→' in fwd"

// --- The range ---

/// A declaration-shaped span on line 2 becomes the wire range an editor can
/// highlight: `def b : I64 := 2` occupies characters 0 through 16 of line 1
/// (0-based), end exclusive.
#[test]
def test_a_declaration_span_becomes_its_wire_range : Bool :=
    let d : WireDiagnostic := dt_decl_b "type mismatch" PositionEncoding.utf8 in
    I64.beq (dt_start_line d) 1
        && I64.beq (dt_start_char d) 0
        && I64.beq (dt_end_line d) 1
        && I64.beq (dt_end_char d) 16

/// A `lang` `Location` is a POINT, and a parse failure builds a range whose two
/// ends are the same point. A zero-width range highlights nothing in an editor,
/// so the end is widened by one character -- which is the whole visible
/// difference between a diagnostic the user can see and one they cannot.
#[test]
def test_a_point_range_is_widened_by_one_character : Bool :=
    let d : WireDiagnostic :=
        dt_span_of "expected identifier at 1:10" PositionEncoding.utf8 dt_two_defs 17 2 1 17 2 1
    in
    I64.beq (dt_start_char d) 0 && I64.beq (dt_end_char d) 1

/// A point ON the final newline widens OVER that newline and stops at the
/// exclusive end of THAT line -- it does not land at the start of a next line,
/// and this is the one widening case where those two are different answers.
///
/// The terminator belongs to the line it ends: `def b : I64 := 2\n` is seventeen
/// wire characters wide, the last of which is the newline, so byte 33 is
/// character 16 of the line and the widened end is character 17 of the SAME
/// line. Reporting `{2, 0}` instead would name a line the editor may not even
/// have, which is the kind of plausible-looking wrong range that survives
/// review. (Measured, not inferred -- a first draft of this test asserted the
/// other answer and failed.)
#[test]
def test_a_point_on_the_final_newline_widens_over_it : Bool :=
    let n : WireDiagnostic :=
        dt_span_of "truncated" PositionEncoding.utf8 dt_two_defs 33 2 17 33 2 17
    in
    I64.beq (dt_start_line n) 1
        && I64.beq (dt_start_char n) 16
        && I64.beq (dt_end_line n) 1
        && I64.beq (dt_end_char n) 17

/// A point already AT the exclusive end of the last line -- offset 34 of a
/// 34-byte source -- has no character left to widen over, so the range stays
/// empty. An empty range draws nothing, and here that is right: the diagnostic
/// is about the file ending, and there is nothing on screen to underline.
#[test]
def test_a_point_at_the_exclusive_end_stays_empty : Bool :=
    let e : WireDiagnostic :=
        dt_span_of "truncated" PositionEncoding.utf8 dt_two_defs 34 2 18 34 2 18
    in
    I64.beq (dt_start_line e) 1
        && I64.beq (dt_start_char e) 17
        && I64.beq (dt_end_line e) 1
        && I64.beq (dt_end_char e) 17

/// A diagnostic with NO range -- the truncation path, where the lenient parser
/// stopped and there was no declaration to place it on -- is reported at the top
/// of the file. Reported, not dropped: an editor whose server discards what it
/// cannot locate shows a broken file as clean.
#[test]
def test_a_diagnostic_with_no_range_lands_at_the_origin : Bool :=
    let d : WireDiagnostic := dt_wire PositionEncoding.utf8 dt_two_defs (dt_make "boom" Option.none)
    in
    I64.beq (dt_start_line d) 0
        && I64.beq (dt_start_char d) 0
        && I64.beq (dt_end_line d) 0
        && I64.beq (dt_end_char d) 0

/// The message is reduced on the no-range path too. It is easy to route the
/// reduction only through the arm that has a range and leave the fallbacks
/// echoing the whole terminal rendering.
#[test]
def test_the_message_is_reduced_even_without_a_range : Bool :=
    let d : WireDiagnostic :=
        dt_wire PositionEncoding.utf8 dt_two_defs (dt_make dt_parse_message Option.none)
    in
    String.beq (dt_msg d) "expected identifier at 1:10"

/// THE end-to-end encoding test, and the one case where the two negotiated
/// encodings disagree. A span covering `// — ` ends at byte 6; that is six
/// characters in UTF-8 and FOUR code units in UTF-16, because the em dash is
/// three bytes and one unit. A server that ignored the negotiation and always
/// spoke one of them would put every diagnostic on a non-ASCII line in the wrong
/// place.
#[test]
def test_a_non_ascii_span_differs_between_the_encodings : Bool :=
    let u8 : WireDiagnostic :=
        dt_span_of "type mismatch" PositionEncoding.utf8 dt_non_ascii 0 1 1 6 1 7
    in
    let u16 : WireDiagnostic :=
        dt_span_of "type mismatch" PositionEncoding.utf16 dt_non_ascii 0 1 1 6 1 7
    in
    I64.beq (dt_start_char u8) 0
        && I64.beq (dt_end_char u8) 6
        && I64.beq (dt_start_char u16) 0
        && I64.beq (dt_end_char u16) 4

/// Severity is uniformly Error here, and that is a statement about `lang`: its
/// `Diagnostic` has no severity field and no producer emits anything softer. The
/// test exists so that the day a warning producer lands, it fails here first
/// rather than shipping every warning with an error's gutter glyph.
#[test]
def test_every_diagnostic_from_lang_is_an_error : Bool :=
    I64.beq (dt_sev (dt_decl_b "x" PositionEncoding.utf8)) diag_severity_error
        && I64.beq (dt_sev (dt_wire PositionEncoding.utf8 dt_two_defs (dt_make "x" Option.none)))
            diag_severity_error

/// The four severity numbers are wire constants: a client draws its gutter glyph
/// from the value, so a transposition between any two is invisible until a user
/// notices the wrong icon. They are asserted in specification order.
#[test]
def test_the_severity_constants_are_the_specified_values : Bool :=
    I64.beq diag_severity_error 1
        && I64.beq diag_severity_warning 2
        && I64.beq diag_severity_information 3
        && I64.beq diag_severity_hint 4

/// The same string the Rust server being replaced sends, so a user switching
/// servers sees no change in the gutter label beside their diagnostics.
#[test]
def test_the_source_name_is_monad : Bool := String.beq diagnostic_source_name "monad"

// --- The wire JSON ---

/// The wire text for the declaration diagnostic, one string literal so the byte
/// sequence is unmistakable rather than assembled from pieces a reader has to
/// concatenate in their head. Written here from a RUN, not from the code.
///
/// Three things a reader should check this against the module: the keys are
/// alphabetical (`message`, `range`, `severity`, `source`) because `Json` walks a
/// `BTreeMap` and NOT in the order `wire_diagnostic_json` builds them; the range
/// nests `start` and `end` as whole positions rather than flattening to
/// `startLine`/`endLine`; and inside a position `character` precedes `line`.
def dt_expected_decl : String :=
    "{\"message\":\"unknown variable 'no_such_name' in bad\",\"range\":{\"end\":{\"character\":16,\"line\":1},\"start\":{\"character\":0,\"line\":1}},\"severity\":1,\"source\":\"monad\"}"

/// The same for the widened point range, so the array test below can reuse both
/// halves instead of repeating them.
def dt_expected_point : String :=
    "{\"message\":\"expected identifier at 1:10\",\"range\":{\"end\":{\"character\":1,\"line\":1},\"start\":{\"character\":0,\"line\":1}},\"severity\":1,\"source\":\"monad\"}"

/// A list of diagnostics with nothing in it, pinned by a def rather than written
/// as a bare `List.empty`. An unannotated empty list is the shape that resolved
/// to the wrong instance in this repository's `Map.empty` bug, and the
/// annotation costs one line.
def diag_no_wire : List WireDiagnostic := List.empty

/// One diagnostic, byte for byte.
#[test]
def test_one_diagnostic_is_an_exact_object_on_the_wire : Bool :=
    let d : WireDiagnostic :=
        dt_decl_b "unknown variable 'no_such_name' in bad" PositionEncoding.utf8
    in
    String.beq (dt_json_text (wire_diagnostic_json d)) dt_expected_decl

/// An empty list is an empty ARRAY, not `null` and not an absent key. The
/// difference is visible to a user as "the squiggles cleared" versus "the
/// squiggles stayed" -- a client that received `null` where it expected an array
/// keeps the previous diagnostics on screen, which is exactly the failure mode
/// that makes a fixed error look unfixed.
#[test]
def test_no_diagnostics_is_an_empty_array : Bool :=
    String.beq (dt_json_text (wire_diagnostics_json diag_no_wire)) "[]"

/// Two diagnostics, in the ORDER they were given. The array is built by folding,
/// which reverses, so reversing back is a real step that could be dropped -- and
/// a dropped reversal would put the parse error above the type error for no
/// reason a reader could see.
#[test]
def test_two_diagnostics_keep_their_order_on_the_wire : Bool :=
    let a : WireDiagnostic :=
        dt_decl_b "unknown variable 'no_such_name' in bad" PositionEncoding.utf8
    in
    let b : WireDiagnostic :=
        dt_span_of "expected identifier at 1:10" PositionEncoding.utf8 dt_two_defs 17 2 1 17 2 1
    in
    String.beq (dt_json_text (wire_diagnostics_json (List.cons a (List.cons b diag_no_wire))))
        ("[" ++ dt_expected_decl ++ "," ++ dt_expected_point ++ "]")

/// A single-element array, which is the shape `publishDiagnostics` sends for the
/// overwhelmingly common case. It exists because it is where a fold-and-reverse
/// bug is INVISIBLE: with one element, a missing reversal produces the right
/// answer, so this test cannot catch it -- the test above is the one that does.
/// What this pins instead is the bracketing and the absence of a trailing comma,
/// which a naive join would introduce.
#[test]
def test_one_diagnostic_is_a_one_element_array : Bool :=
    let b : WireDiagnostic :=
        dt_span_of "expected identifier at 1:10" PositionEncoding.utf8 dt_two_defs 17 2 1 17 2 1
    in
    String.beq (dt_json_text (wire_diagnostics_json (List.cons b diag_no_wire)))
        ("[" ++ dt_expected_point ++ "]")
