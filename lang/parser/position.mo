/// Position tracking utilities for the self-hosted parser
/// Extracted from parser.mo as part of Phase C

use lang.types {LocatedSpan, Location, mk}
use lang.parser.combinators {utf8_char_width}

/// Create a new LocatedSpan starting at offset 0, line 1, column 1
#[partial]
def new_span (s : String) : LocatedSpan :=
	LocatedSpan.mk s (Location.mk 0 1 1)

/// Extract the location from a LocatedSpan
#[partial]
def span_location (span : LocatedSpan) : Location :=
	match span {
		mk frag loc => loc
	}

/// Extract the fragment string from a LocatedSpan
#[partial]
def span_fragment (span : LocatedSpan) : String :=
	match span {
		mk frag loc => frag
	}

// --- Divide-and-conquer line/column scanning ---
//
// The Rust reference interpreter (core_eval.rs) has no tail-call
// optimization: a single recursive call chain longer than roughly
// 1000-1500 frames overflows the stack, even inside the test runner's
// dedicated 64MB thread (confirmed by direct measurement — a bare
// self-recursive countdown from 1500 crashes, from 1000 doesn't; this
// is a pre-existing, systemic limitation of the interpreter itself, not
// specific to any one function — `lang.parser.combinators.take_while`,
// used throughout the whole grammar, crashes the exact same way if
// asked to scan an entire large file in one call, though nothing in
// normal parsing ever does that since every real token/construct is far
// shorter than 1000 characters).
//
// `lang/json.mo` alone is ~37,000 characters, so a naive
// one-character-at-a-time linear scan over its full consumed prefix (as
// `location_of_remaining` needs to do to recover a line:column) crashes
// well before reaching the end. `LineColScan` fixes this by scanning
// via divide-and-conquer: split a chunk in half, scan each half
// independently (recursing further only on chunks still over a safe
// small threshold), then *combine* the two results — an associative,
// monoid-shaped operation, so the combining itself doesn't care how the
// splits were arranged. This keeps the recursion *depth* at O(log n)
// (~16 for a file this size) while the *total* work stays O(n) — depth
// is what the interpreter's stack can't afford, not total work.
struct LineColScan {
	newlines : I64,
	chars : I64,
	/// Characters since the last newline *within this chunk alone* — if
	/// this chunk has no newline of its own, the whole chunk is
	/// "trailing" (equal to `chars`).
	trailing : I64,
}

/// Combine two adjacent chunks' scans, left-to-right.
#[partial]
def combine_line_col_scan (left : LineColScan) (right : LineColScan) : LineColScan :=
	match left {
		mk l_nl l_chars l_trail =>
			match right {
				mk r_nl r_chars r_trail =>
					let trailing : I64 := if I64.gt r_nl 0 then r_trail else I64.add l_trail r_trail in
					{ newlines := I64.add l_nl r_nl, chars := I64.add l_chars r_chars, trailing := trailing }
			}
	}

/// Base case: scan a small chunk directly, one character at a time.
/// Only ever called on chunks already below `dc_threshold` (see
/// `line_col_scan`), so this stays well within the interpreter's real
/// recursion-depth ceiling.
#[partial]
def line_col_scan_direct (s : String) (nl : I64) (chars : I64) (trailing : I64) : LineColScan :=
	if String.is_empty s
	then { newlines := nl, chars := chars, trailing := trailing }
	else
		let width : I64 := utf8_char_width s in
		let ch : String := String.slice s 0 width in
		let rest : String := String.drop width s in
		if String.beq "\n" ch
		then line_col_scan_direct rest (I64.add nl 1) (I64.add chars 1) 0
		else line_col_scan_direct rest nl (I64.add chars 1) (I64.add trailing 1)

/// Byte length above which `line_col_scan` splits rather than scanning
/// directly — comfortably under the interpreter's ~1000-1500 frame
/// ceiling (a UTF-8 chunk of this many *bytes* has at most this many
/// characters, usually fewer), with margin for whatever's already on
/// the stack from the caller (`decls_parser_strict`'s own parse attempt,
/// `render_parse_error`'s own call chain).
def dc_threshold : I64 := 400

/// Scan `s` for newline/character/trailing-column bookkeeping via
/// divide-and-conquer. See this module's own doc comment above
/// (`LineColScan`) for why this can't just be a single linear scan.
#[partial]
def line_col_scan (s : String) : LineColScan :=
	if I64.lt (String.length s) dc_threshold
	then line_col_scan_direct s 0 0 0
	else
		let raw_mid : I64 := I64.div (String.length s) 2 in
		let mid : I64 := safe_split_offset s raw_mid in
		let left : String := String.slice s 0 mid in
		let right : String := String.drop mid s in
		combine_line_col_scan (line_col_scan left) (line_col_scan right)

/// A byte in the 0x80-0xBF (128-191) range is a UTF-8 *continuation*
/// byte — never a valid place to split a string, since it's the middle
/// of a multi-byte character (see `utf8_char_width`'s own doc comment,
/// lang/parser/combinators.mo, for the encoding rule this checks
/// against).
#[partial]
def is_utf8_continuation_byte (byte : U8) : Bool :=
	U8.gt byte 127u8 && U8.lt byte 192u8

/// Nudge `approx` forward (at most 3 times — the longest a UTF-8
/// sequence can be past its lead byte) until it lands on a real
/// character boundary, so `line_col_scan`'s divide-and-conquer split
/// never cuts a multi-byte character in half.
#[partial]
def safe_split_offset (s : String) (approx : I64) : I64 :=
	match String.get s approx {
		Option.some byte =>
			if is_utf8_continuation_byte byte
			then safe_split_offset s (I64.add approx 1)
			else approx,
		// Past the end of `s` (or `approx` already lands exactly on the
		// end) — `String.slice`/`String.drop` already clamp out-of-range
		// offsets safely, nothing further to adjust.
		Option.none => approx
	}

/// Advance a location past the given consumed string, using
/// `line_col_scan`'s divide-and-conquer scan rather than a linear pass —
/// safe for a consumed prefix of any size (see this module's own doc
/// comment on `LineColScan`). `consumed`'s own byte length determines
/// the new `offset` (matching `String.slice`/`String.drop`'s byte
/// semantics).
#[partial]
def advance_location (loc : Location) (consumed : String) : Location :=
	match loc {
		mk off line col =>
			let byte_len : I64 := String.length consumed in
			let new_off : I64 := I64.add off byte_len in
			match line_col_scan consumed {
				mk newlines _chars trailing =>
					if I64.beq newlines 0
					then Location.mk new_off line (I64.add col trailing)
					else Location.mk new_off (I64.add line newlines) (I64.add 1 trailing)
			}
	}

/// Consume n bytes from a LocatedSpan, advancing the location
#[partial]
def consume_span (span : LocatedSpan) (n : I64) : LocatedSpan :=
	match span {
		mk frag loc =>
			let consumed : String := String.slice frag 0 n in
			let rest : String := String.drop n frag in
			let new_loc : Location := advance_location loc consumed in
			LocatedSpan.mk rest new_loc
	}

/// Compute the `Location` where `remaining` begins within `original` —
/// how this parser surfaces error positions: rather than threading a
/// `LocatedSpan` through every one of ~450 grammar functions (the Rust
/// reference's nom-locate approach, core/src/parser/locate.rs), every
/// `ParseError` already carries the input remaining right at the point
/// of failure (see `ParseError`'s own doc comment, lang/parser/core.mo);
/// this converts that back into a `Location` by diffing against the
/// original full source text, computed once on demand when rendering a
/// diagnostic, not threaded through every parse step. `remaining` is
/// always a suffix of `original` at a valid UTF-8 boundary (every
/// scanner in this parser now steps by `utf8_char_width`, never a raw
/// byte), so the byte-length diff below always lands on one too.
#[partial]
def location_of_remaining (original : String) (remaining : String) : Location :=
	location_of_remaining_len original (String.length remaining)

/// The same arithmetic from a recorded remaining-input LENGTH rather
/// than the remainder string itself, which is what a `ParseSpan` stores
/// (see `ParseSpan`'s own doc comment, lang/types.mo, for why the
/// parser records lengths and not absolute offsets). `decls_parser`'s
/// located twin goes through here: the parser already recorded where
/// each declaration began, so the position is a projection over that
/// span rather than a second parse that re-derives it.
#[partial]
def location_of_remaining_len (original : String) (remaining_len : I64) : Location :=
	let consumed_len : I64 := String.length original - remaining_len in
	let consumed : String := String.slice original 0 consumed_len in
	advance_location (Location.mk 0 1 1) consumed
