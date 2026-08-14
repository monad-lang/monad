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
use lang.parser.combinators {utf8_char_width}

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
		Location.mk _offset line col =>
			let header : String := render_header msg line col in
			let arrow : String := render_arrow_line path line col in
			let context : String := render_source_context source line col in
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

/// Split a string into lines on `\n` (no native `String.split` exists —
/// see this module's own doc comment for the pattern this mirrors).
/// UTF-8-aware (`utf8_char_width`) like every other scanner in this
/// parser.
#[partial]
def split_lines (s : String) : List String :=
	split_lines_go s ""

#[partial]
def split_lines_go (s : String) (acc : String) : List String :=
	if String.is_empty s
	then List.cons acc List.empty
	else
		let width : I64 := utf8_char_width s in
		let ch : String := String.slice s 0 width in
		let rest : String := String.drop width s in
		if String.beq "\n" ch
		then List.cons acc (split_lines_go rest "")
		else split_lines_go rest (String.concat acc ch)

#[partial]
def nth_line (lines : List String) (n : I64) : Option String :=
	match lines {
		List.empty => Option.none,
		List.cons hd rest =>
			if I64.beq n 1
			then Option.some hd
			else nth_line rest (I64.sub n 1)
	}

/// Right-justify a line number to width 3 (mirrors `diag.rs`'s
/// `{:>3}`) — approximate for line numbers over 999 (no truncation, the
/// field just grows, same as Rust's own formatter).
#[partial]
def pad_line_num (n : I64) : String :=
	let s : String := I64.to_string n in
	if I64.lt (String.length s) 3
	then pad_line_num_loop s
	else s

#[partial]
def pad_line_num_loop (s : String) : String :=
	if I64.lt (String.length s) 3
	then pad_line_num_loop (String.concat " " s)
	else s

#[partial]
def spaces (n : I64) : String :=
	if I64.gt n 0
	then String.concat " " (spaces (I64.sub n 1))
	else ""

/// Renders up to 3 lines centered on `line` (the failing line, plus one
/// before and after, clamped to the file's real extent) plus a `^---`
/// caret positioned under `col` right after the failing line — mirrors
/// `diag.rs`'s `write_source_context` exactly.
#[partial]
def render_source_context (source : String) (line : I64) (col : I64) : String :=
	let lines : List String := split_lines source in
	let total : I64 := List.length lines in
	if I64.beq line 0
	then ""
	else if I64.gt line total
	then ""
	else
		let start_line : I64 := if I64.gt line 1 then I64.sub line 1 else 1 in
		let end_line : I64 := if I64.lt line total then I64.add line 1 else total in
		render_context_lines lines start_line end_line line col total

#[partial]
def render_context_lines (lines : List String) (i : I64) (end_line : I64) (error_line : I64) (col : I64) (total : I64) : String :=
	if I64.gt i end_line
	then ""
	else if I64.gt i total
	then ""
	else
		let content : String := match nth_line lines i {
			Option.some c => c,
			Option.none => "",
		} in
		let this_line : String :=
			if I64.beq i error_line
			then String.concat (pad_line_num i) (String.concat " | " (String.concat content (String.concat "\n" (render_caret col))))
			else String.concat "   " (String.concat (pad_line_num i) (String.concat " | " (String.concat content "\n")))
		in
		String.concat this_line (render_context_lines lines (I64.add i 1) end_line error_line col total)

#[partial]
def render_caret (col : I64) : String :=
	if I64.gt col 0
	then String.concat "    " (String.concat (spaces (I64.sub col 1)) "^---\n")
	else ""

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
	// "error: unknown declaration at 1:10\n  --> :1:10\n  1 | def f := x\n    ...^---\n"
	String_contains rendered "error: unknown declaration at 1:10"
		&& String_contains rendered "--> :1:10"
		&& String_contains rendered "def f := x"

#[partial]
def String_contains (haystack : String) (needle : String) : Bool :=
	String_contains_go haystack needle

#[partial]
def String_contains_go (haystack : String) (needle : String) : Bool :=
	if String.is_empty needle
	then true
	else if I64.gt (String.length needle) (String.length haystack)
	then false
	else if String_starts_with haystack needle
	then true
	else if String.is_empty haystack
	then false
	else String_contains_go (String.drop 1 haystack) needle

#[partial]
def String_starts_with (haystack : String) (needle : String) : Bool :=
	String.beq (String.slice haystack 0 (String.length needle)) needle

#[test]
def test_render_parse_error_with_path : Bool :=
	let source : String := "def f := x" in
	let err : ParseError := ParseError.custom "unknown declaration" "x" in
	let rendered : String := render_parse_error source (Option.some "examples/foo.mo") err in
	String_contains rendered "--> examples/foo.mo:1:10"

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
	String_contains rendered "at 2:10"
		&& String_contains rendered "def a := 1"
		&& String_contains rendered "def b := bad_here"
		&& String_contains rendered "def c := 3"

#[test]
def test_split_lines_basic : Bool :=
	let lines : List String := split_lines "a\nb\nc" in
	match lines {
		List.cons l1 rest1 =>
			match rest1 {
				List.cons l2 rest2 =>
					match rest2 {
						List.cons l3 rest3 =>
							String.beq l1 "a" && String.beq l2 "b" && String.beq l3 "c" && (match rest3 { List.empty => true, _ => false }),
						List.empty => false
					},
				List.empty => false
			},
		List.empty => false
	}
