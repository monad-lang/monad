/// Identifier parser for the self-hosted parser
/// Extracted from parser.mo as part of Phase C

use lang.types {custom}
use lang.parser.core {ParseResult, custom, fail, is_empty, success}
use lang.parser.char_preds {ident_start, is_ident_char, is_keyword}
use lang.parser.combinators {take_while}

open ParseResult {fail, success}

/// Parse an identifier from the input string
/// Returns the parsed identifier string and remaining input
#[partial]
def identifier (input : String) : ParseResult String :=
	identifier_try (take_while is_ident_char input)

/// Helper: validate and return the parsed identifier
#[partial]
def identifier_try (r : ParseResult String) : ParseResult String :=
	match r {
		success rem out =>
			if String.is_empty out
			then fail (ParseError.custom "expected identifier" rem)
			else identifier_check_start out rem,
			fail e => fail e
	}

/// Check if the identifier starts with a valid character
#[partial]
def identifier_check_start (s : String) (rem : String) : ParseResult String :=
	if ident_start (String.slice s 0 1)
	then identifier_check_kw s rem
	else fail (ParseError.custom "identifier cannot start with digit" rem)

/// Check if the identifier is a reserved keyword
#[partial]
def identifier_check_kw (s : String) (rem : String) : ParseResult String :=
	if is_keyword s
	then fail (ParseError.custom ("reserved keyword: " ++ s) rem)
	else success rem s
