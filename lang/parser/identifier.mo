/// Identifier parser for the self-hosted parser
/// Extracted from parser.mo as part of Phase C

use lang.types
use lang.parser.core
use lang.parser.char_preds
use lang.parser.combinators

open ParseResult

/// Check if a character can start an identifier (letter or underscore)
@[partial]
def ident_start (c : String) : Bool :=
	if is_alpha c then true
	else String.beq "_" c

/// Parse an identifier from the input string
/// Returns the parsed identifier string and remaining input
@[partial]
def identifier (input : String) : ParseResult String :=
	identifier_try (take_while is_ident_char input)

/// Helper: validate and return the parsed identifier
@[partial]
def identifier_try (r : ParseResult String) : ParseResult String :=
	match r {
		success rem out =>
			if String.is_empty out
			then fail (ParseError.custom "expected identifier")
			else identifier_check_start out rem,
			fail e => fail e
	}

/// Check if the identifier starts with a valid character
@[partial]
def identifier_check_start (s : String) (rem : String) : ParseResult String :=
	if ident_start (String.slice s 0 1)
	then identifier_check_kw s rem
	else fail (ParseError.custom "identifier cannot start with digit")

/// Check if the identifier is a reserved keyword
@[partial]
def identifier_check_kw (s : String) (rem : String) : ParseResult String :=
	if is_keyword s
	then fail (ParseError.custom ("reserved keyword: " ++ s))
	else success rem s
