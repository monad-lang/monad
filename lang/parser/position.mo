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

/// Count the number of newline characters in a string. Steps by
/// `utf8_char_width` rather than a hardcoded 1 byte — a 1-byte slice
/// into the middle of a multi-byte UTF-8 character isn't a valid
/// boundary on either end, so both the char slice AND the remaining-
/// string drop silently return "" (see `utf8_char_width`'s own doc
/// comment, lang/parser/combinators.mo), which previously made this
/// function stop counting entirely as soon as it hit any multi-byte
/// character rather than just miscounting that one character.
#[partial]
def count_newlines (s : String) (acc : I64) : I64 :=
	if String.is_empty s
	then acc
	else
		let width : I64 := utf8_char_width s in
		count_newlines_tail (String.slice s 0 width) (String.drop width s) acc

/// Helper for count_newlines
#[partial]
def count_newlines_tail (c : String) (s : String) (acc : I64) : I64 :=
	if String.beq "\n" c
	then count_newlines s (I64.add acc 1)
	else count_newlines s acc

/// Count the characters (codepoints, not bytes) in a string, stepping by
/// `utf8_char_width` like every other scanner in this module.
#[partial]
def char_count (s : String) (acc : I64) : I64 :=
	if String.is_empty s
	then acc
	else
		let width : I64 := utf8_char_width s in
		char_count (String.drop width s) (I64.add acc 1)

/// The substring of `s` after its last newline (the whole string if it
/// has none) — used to compute the column after a multi-line consumed
/// span: characters *before* the last newline don't affect the column,
/// only how many come after it.
#[partial]
def text_after_last_newline (s : String) : String :=
	text_after_last_newline_go s s

/// `remaining_from_last_nl` trails `s` by one position each iteration
/// while we scan `s` forward; whenever `s`'s head is a newline, we reset
/// `remaining_from_last_nl` back to `s`'s current (post-newline) tail —
/// so by the time `s` is exhausted, `remaining_from_last_nl` holds
/// everything after the *last* newline seen (or the original string
/// untouched if there was none).
#[partial]
def text_after_last_newline_go (s : String) (remaining_from_last_nl : String) : String :=
	if String.is_empty s
	then remaining_from_last_nl
	else
		let width : I64 := utf8_char_width s in
		let ch : String := String.slice s 0 width in
		let rest : String := String.drop width s in
		if String.beq "\n" ch
		then text_after_last_newline_go rest rest
		else text_after_last_newline_go rest remaining_from_last_nl

/// Advance a location past the given consumed string. `consumed`'s own
/// byte length determines the new `offset` (matching `String.slice`/
/// `String.drop`'s byte semantics); `line`/`column` are derived from
/// `consumed`'s actual newlines and characters, not a caller-supplied
/// count — a previous version took a redundant `n` parameter and, worse,
/// unconditionally reset `column` to 1 whenever `consumed` contained
/// *any* newline, silently ignoring every character after the *last*
/// one (e.g. consuming `"a\nbc"` produced column 1, not the correct 3) —
/// untested before now since `consume_span`'s own existing tests always
/// happened to consume exactly up through a trailing newline, never past
/// one.
#[partial]
def advance_location (loc : Location) (consumed : String) : Location :=
	match loc {
		mk off line col =>
			let byte_len : I64 := String.length consumed in
			let new_off : I64 := I64.add off byte_len in
			let newlines : I64 := count_newlines consumed 0 in
			if I64.beq newlines 0
			then Location.mk new_off line (I64.add col (char_count consumed 0))
			else
				let tail : String := text_after_last_newline consumed in
				Location.mk new_off (I64.add line newlines) (I64.add 1 (char_count tail 0))
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
	let consumed_len : I64 := I64.sub (String.length original) (String.length remaining) in
	let consumed : String := String.slice original 0 consumed_len in
	advance_location (Location.mk 0 1 1) consumed
