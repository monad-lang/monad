/// Rust-mirroring parse error diagnostic rendering for the self-hosted
/// parser. Mirrors `core/src/diag.rs`'s `render_diagnostic` format —
/// `error: <message> at L:C\n  --> path:L:C\n<context lines>` — using
/// `lang/parser/core.mo`'s `ParseError` (which carries the input
/// remaining at the point of failure) and
/// `lang/parser/position.mo`'s `location_of_remaining` to recover a
/// real line:column. No ANSI color codes (mirrors the Rust renderer's
/// `use_colors: false` path) — this is a CLI-and-log-friendly plain
/// rendering, not a byte-for-byte reproduction of every `diag.rs`
/// feature (sub-diagnostics, suggestions, colorized spans): just the
/// core "where did this fail and what does the surrounding source look
/// like" diagnostic, which is what a parse failure actually needs.

use lang.types {Location}
use lang.parser.core {ParseError, parse_error_remaining}
use lang.parser.position {location_of_remaining}

/// A human-readable description of what went wrong — `tag` failures
/// (the vast majority, since almost every leaf-level literal match goes
/// through `combinators.mo`'s `tag`) render as `expected '<text>'`;
/// `custom` failures already carry their own full message.
#[partial]
def error_message (err : ParseError) : String :=
	match err {
		ParseError.tag expected _ => String.concat "expected '" (String.concat expected "'"),
		ParseError.custom msg _ => msg,
	}

/// Render a full Rust-diag.rs-style diagnostic for a parse failure.
/// `source` must be the SAME full text `err`'s remaining was produced
/// from (i.e. what was originally handed to `decls_parser`/whichever
/// top-level parser call failed) — `location_of_remaining` diffs
/// against it to recover a position, so a mismatched `source` silently
/// produces a nonsense location rather than an error (same caveat as
/// `location_of_remaining` itself).
#[partial]
def render_parse_error (source : String) (path : Option String) (err : ParseError) : String :=
	let msg : String := error_message err in
	let loc : Location := location_of_remaining source (parse_error_remaining err) in
	match loc {
		Location.mk offset line col =>
			let header : String := render_header msg line col in
			let arrow : String := render_arrow_line path line col in
			let context : String := render_source_context source line col offset in
			String.concat header (String.concat arrow context)
	}

#[partial]
def render_header (msg : String) (line : I64) (col : I64) : String :=
	let loc_str : String := String.concat (I64.to_string line) (String.concat ":" (I64.to_string col)) in
	String.concat "error: " (String.concat msg (String.concat " at " (String.concat loc_str "\n")))

#[partial]
def render_arrow_line (path : Option String) (line : I64) (col : I64) : String :=
	let path_str : String := match path {
		Option.some p => p,
		Option.none => "",
	} in
	let loc_str : String := String.concat (I64.to_string line) (String.concat ":" (I64.to_string col)) in
	String.concat "  --> " (String.concat path_str (String.concat ":" (String.concat loc_str "\n")))

// --- Source context (the `L | source` / `  | ^---` lines) ---
//
// Finds the failing line (and its immediate neighbors) by scanning
// *locally* from the already-known error `offset` — backward and
// forward to the nearest newlines — rather than splitting the entire
// `source` into lines up front. A whole-file split was tried first and
// crashed on `lang/json.mo` (~37KB): the interpreter has no tail-call
// optimization at all (confirmed by direct measurement — a bare
// self-recursive countdown from 1500 overflows the stack even inside
// the test runner's dedicated 64MB thread, from 1000 doesn't), so ANY
// single recursive pass over a whole large file — tail-recursive or
// not — blows the stack once it's long enough; `location_of_remaining`
// hits the same wall and is fixed the same way, via divide-and-conquer
// (`LineColScan`, lang/parser/position.mo). Divide-and-conquer isn't
// needed *here* because finding 3 lines of context is inherently local:
// scanning for the nearest newline in each direction is bounded by
// *line length* (typically well under a hundred characters for real
// source), never by file size.

def newline_byte : U8 := 10u8

/// The start of the line containing byte offset `pos` — scans backward
/// for the nearest preceding `\n`, returning the position right after
/// it (or 0 if none exists, i.e. `pos` is on the first line).
#[partial]
def line_start_before (s : String) (pos : I64) : I64 :=
	line_start_before_go s (pos - 1)

#[partial]
def line_start_before_go (s : String) (pos : I64) : I64 :=
	if I64.lt pos 0
	then 0
	else match String.get s pos {
		Option.some byte =>
			if U8.beq byte newline_byte
			then I64.add pos 1
			else line_start_before_go s (pos - 1),
		Option.none => 0
	}

/// The end of the line containing byte offset `pos` (exclusive) — scans
/// forward for the nearest following `\n`, returning its position, or
/// `String.length s` if none exists (the line runs to EOF).
#[partial]
def line_end_after (s : String) (pos : I64) : I64 :=
	line_end_after_go s pos (String.length s)

#[partial]
def line_end_after_go (s : String) (pos : I64) (len : I64) : I64 :=
	if Bool.not (I64.lt pos len)
	then len
	else match String.get s pos {
		Option.some byte =>
			if U8.beq byte newline_byte
			then pos
			else line_end_after_go s (I64.add pos 1) len,
		Option.none => len
	}

/// Right-justify a line number to `width` (mirrors `diag.rs`'s
/// `{:>width$}`) — `width` is computed once per diagnostic from the
/// widest line number actually shown (see `render_source_context`), with
/// a minimum of 3, so every displayed line (the error line and its
/// context neighbors alike) lines up its `|` in the same column. If `n`
/// itself needs more digits than `width`, the field just grows (no
/// truncation), same as Rust's own formatter.
#[partial]
def pad_line_num (width : I64) (n : I64) : String :=
	let s : String := I64.to_string n in
	if I64.lt (String.length s) width
	then pad_line_num_loop width s
	else s

#[partial]
def pad_line_num_loop (width : I64) (s : String) : String :=
	if I64.lt (String.length s) width
	then pad_line_num_loop width (String.concat " " s)
	else s

/// Bounded by `n` (a column number — line length, not file size).
#[partial]
def spaces (n : I64) : String :=
	if I64.gt n 0
	then String.concat " " (spaces (n - 1))
	else ""

/// Every displayed line — error line and context neighbors alike — uses
/// the SAME `width`-padded number field followed by `" | "`, with no
/// extra literal prefix on either branch, so the gutters all align.
#[partial]
def render_context_line (width : I64) (line_num : I64) (content : String) (is_error_line : Bool) (col : I64) : String :=
	let prefix : String := String.concat (pad_line_num width line_num) (String.concat " | " content) in
	if is_error_line
	then String.concat prefix (String.concat "\n" (render_caret width col))
	else String.concat prefix "\n"

/// Caret indent is `width + 3` spaces (the number field plus the literal
/// `" | "`) so it lands under the first character of the error line's
/// own content, then `col - 1` more spaces to reach the actual column.
#[partial]
def render_caret (width : I64) (col : I64) : String :=
	if I64.gt col 0
	then String.concat (spaces (I64.add width 3)) (String.concat (spaces (col - 1)) "^---\n")
	else ""

/// Number of decimal digits in a non-negative line number.
#[partial]
def digit_count (n : I64) : I64 :=
	String.length (I64.to_string n)

def i64_max (a : I64) (b : I64) : I64 :=
	if I64.gt a b then a else b

/// Renders up to 3 lines centered on `line` (the failing line, plus one
/// before and after, clamped to the file's real extent) plus a `^---`
/// caret positioned under `col` right after the failing line — mirrors
/// `diag.rs`'s `write_source_context`. `offset` is the failing byte
/// position (`location_of_remaining`'s own `Location.offset`), which is
/// what anchors the local backward/forward scans described above.
#[partial]
def render_source_context (source : String) (line : I64) (col : I64) (offset : I64) : String :=
	if I64.beq line 0
	then ""
	else
		let cur_start : I64 := line_start_before source offset in
		let cur_end : I64 := line_end_after source offset in
		let cur_content : String := String.slice source cur_start (cur_end - cur_start) in
		let has_next : Bool := I64.lt cur_end (String.length source) in
		// The gutter width is shared across the whole 3-line window, based
		// on the widest line number actually shown (mirrors `diag.rs`'s
		// `end_line`) — a next line, if there is one, is always the widest.
		let end_line : I64 := if has_next then I64.add line 1 else line in
		let width : I64 := i64_max 3 (digit_count end_line) in
		let prev_str : String :=
			if I64.gt line 1
			then
				let prev_end : I64 := (cur_start - 1) in
				let prev_start : I64 := line_start_before source prev_end in
				let prev_content : String := String.slice source prev_start (prev_end - prev_start) in
				render_context_line width (line - 1) prev_content false 0
			else ""
		in
		let cur_str : String := render_context_line width line cur_content true col in
		let next_str : String :=
			if has_next
			then
				let next_start : I64 := I64.add cur_end 1 in
				let next_end : I64 := line_end_after source next_start in
				let next_content : String := String.slice source next_start (next_end - next_start) in
				render_context_line width (I64.add line 1) next_content false 0
			else ""
		in
		String.concat prev_str (String.concat cur_str next_str)

// --- Tests ---

#[test]
def test_error_message_tag : Bool :=
	String.beq (error_message (ParseError.tag "}" "abc")) "expected '}'"

#[test]
def test_error_message_custom : Bool :=
	String.beq (error_message (ParseError.custom "unknown declaration" "abc")) "unknown declaration"

#[test]
def test_render_parse_error_simple : Bool :=
	let source : String := "def f := x" in
	let err : ParseError := ParseError.custom "unknown declaration" "x" in
	let rendered : String := render_parse_error source Option.none err in
	// "error: unknown declaration at 1:10\n  --> :1:10\n  1 | def f := x\n               ^---\n"
	String.contains rendered "error: unknown declaration at 1:10"
		&& String.contains rendered "--> :1:10"
		&& String.contains rendered "def f := x"

#[test]
def test_render_parse_error_with_path : Bool :=
	let source : String := "def f := x" in
	let err : ParseError := ParseError.custom "unknown declaration" "x" in
	let rendered : String := render_parse_error source (Option.some "examples/foo.mo") err in
	String.contains rendered "--> examples/foo.mo:1:10"

#[test]
def test_render_parse_error_multi_line : Bool :=
	let source : String := "def a := 1\ndef b := bad_here\ndef c := 3" in
	// `remaining` must be a genuine suffix of `source` (as it always is
	// in real usage — a `ParseError`'s `remaining` field is always
	// literally the still-unconsumed tail of whatever was being parsed),
	// not just the offending token on its own.
	let err : ParseError := ParseError.custom "unknown declaration" "bad_here\ndef c := 3" in
	let rendered : String := render_parse_error source Option.none err in
	// error is on line 2, column 10 ("def b := " is 9 chars before "bad_here")
	String.contains rendered "at 2:10"
		&& String.contains rendered "def a := 1"
		&& String.contains rendered "def b := bad_here"
		&& String.contains rendered "def c := 3"

#[test]
def test_render_source_context_first_line_no_prev : Bool :=
	let source : String := "bad_here\ndef b := 1\ndef c := 3" in
	let err : ParseError := ParseError.custom "unknown declaration" source in
	let rendered : String := render_parse_error source Option.none err in
	String.contains rendered "at 1:1"
		&& String.contains rendered "1 | bad_here"
		&& String.contains rendered "2 | def b := 1"
		&& Bool.not (String.contains rendered "0 |")

#[test]
def test_render_source_context_last_line_no_next : Bool :=
	let source : String := "def a := 1\ndef b := 2\nbad_here" in
	let err : ParseError := ParseError.custom "unknown declaration" "bad_here" in
	let rendered : String := render_parse_error source Option.none err in
	String.contains rendered "at 3:1"
		&& String.contains rendered "2 | def b := 2"
		&& String.contains rendered "3 | bad_here"

/// Regression test for the gutter/caret indentation bug (matching
/// `core/src/diag.rs`'s own `gutter_aligns_error_line_with_context_lines`
/// test): the error line and a context neighbor must share the exact
/// same "N | " gutter width — this line-1/line-2 fixture used to render
/// with the context line ("2 | ...") indented 3 extra stray spaces past
/// the error line ("1 | ..."), and the caret 2 columns short of the
/// content it was supposed to point at. `String.contains`
/// (init/string.mo) checks a LITERAL substring, so matching these exact
/// strings (exact leading-space counts included) really does pin down
/// the alignment, not just presence of the text.
#[test]
def test_render_source_context_gutter_alignment_exact : Bool :=
	let source : String := "abcdefghij\nklmnop" in
	// remaining is the genuine unconsumed suffix starting at column 5 ('e').
	let err : ParseError := ParseError.custom "unknown declaration" "efghij\nklmnop" in
	let rendered : String := render_parse_error source Option.none err in
	// width = 3 (only 1- and 2-digit line numbers shown): error line's
	// "  1 | " gutter and the context line's "  2 | " gutter must match
	// exactly, and the caret (6-char prefix + 4 more for column 5) must
	// land under the content, not 2 columns short.
	String.contains rendered "  1 | abcdefghij\n          ^---\n  2 | klmnop\n"

/// Regression test for the latent width bug alongside the gutter fix:
/// once the window's widest line number needs 4 digits (999/1000/1001),
/// EVERY displayed line — including the 3-digit "999" one — must pad out
/// to that same shared width, not just the 4-digit ones. Mirrors
/// `core/src/diag.rs`'s own
/// `gutter_width_grows_for_four_digit_line_numbers` test.
#[test]
def test_render_source_context_gutter_width_grows_for_wide_line_numbers : Bool :=
	let padding : String := repeat_line "// padding line to bulk up the source\n" 999 in
	let source : String := String.concat padding "bad_here\nfinal_line" in
	let err : ParseError := ParseError.custom "unknown declaration" "bad_here\nfinal_line" in
	let rendered : String := render_parse_error source Option.none err in
	String.contains rendered "at 1000:1"
		&& String.contains rendered " 999 | // padding line to bulk up the source\n"
		&& String.contains rendered "1000 | bad_here\n       ^---\n"
		&& String.contains rendered "1001 | final_line\n"

/// Regression test for the specific bug this whole rewrite fixes: a
/// linear (even tail-recursive) scan over the *entire* source to find
/// line boundaries overflows the interpreter's stack on a real-sized
/// file — `lang/json.mo` (~37KB) is the exact file that surfaced this
/// while bisecting its own parse-truncation point with
/// `decls_parser_strict` + `render_parse_error`. `render_source_context`
/// must only ever scan the few lines immediately around the failure,
/// never the whole source, regardless of file size.
#[test]
def test_render_parse_error_large_source_does_not_overflow : Bool :=
	let padding : String := repeat_line "// padding line to bulk up the source\n" 2000 in
	let source : String := String.concat padding "bad_here" in
	let err : ParseError := ParseError.custom "unknown declaration" "bad_here" in
	let rendered : String := render_parse_error source Option.none err in
	String.contains rendered "at 2001:1" && String.contains rendered "bad_here"

/// Divide-and-conquer for the same reason as `LineColScan`
/// (lang/parser/position.mo) — this test helper needs to build a source
/// string over 1000 lines long to actually exercise the bug it's
/// guarding against, and a naive linear-recursive repeat would overflow
/// the stack building its own test fixture.
#[partial]
def repeat_line (line : String) (n : I64) : String :=
	if I64.beq n 0
	then ""
	else if I64.lt n 50
	then repeat_line_direct line n
	else
		let half : I64 := I64.div n 2 in
		String.concat (repeat_line line half) (repeat_line line (n - half))

#[partial]
def repeat_line_direct (line : String) (n : I64) : String :=
	if I64.beq n 0
	then ""
	else String.concat line (repeat_line_direct line (n - 1))
