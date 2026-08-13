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

/// Advance a location by the given consumed string and character count
#[partial]
def advance_location (loc : Location) (consumed : String) (n : I64) : Location :=
	match loc {
		mk off line col =>
			let newlines : I64 := count_newlines consumed 0 in
			if I64.beq newlines 0
			then Location.mk (I64.add off n) line (I64.add col n)
			else Location.mk (I64.add off n) (I64.add line newlines) 1
	}

/// Consume n characters from a LocatedSpan, advancing the location
#[partial]
def consume_span (span : LocatedSpan) (n : I64) : LocatedSpan :=
	match span {
		mk frag loc =>
			let consumed : String := String.slice frag 0 n in
			let rest : String := String.drop n frag in
			let new_loc : Location := advance_location loc consumed n in
			LocatedSpan.mk rest new_loc
	}
