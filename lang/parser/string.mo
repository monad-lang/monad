/// String literal parser for the self-hosted parser
/// Extracted from parser.mo as part of Phase C

use lang.types {Term, lit, str}
use lang.parser.core {ParseResult, fail, success, tag}
use lang.parser.combinators {delimited_by, tag, take_while}

open ParseResult {fail, success}

/// Check if a character is not a quote
#[partial]
def is_not_quote (c : String) : Bool :=
	if String.beq "\"" c then false
	else true

/// Parse a string literal and return it as a Term
#[partial]
def string_parse (input: String) : ParseResult Term :=
	match delimited_by (tag "\"") (take_while is_not_quote) (tag "\"") input {
		success rem content => success rem (Term.lit (Literal.str content)),
		fail e => fail e
	}
