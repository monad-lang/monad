/// Whitespace parsing functions for the self-hosted Monad parser.

use lang.parser.core {ParseResult, custom, fail, is_empty, success}
use lang.parser.char_preds {is_space_byte}
use lang.parser.combinators {take_while_byte}

open ParseResult {fail, success}


// --- Whitespace ---

#[partial]
def spaces (input : String) : ParseResult String :=
	take_while_byte is_space_byte input


#[partial]
def ws0 (input : String) : ParseResult String :=
	take_while_byte is_space_byte input


#[partial]
def ws1 (input : String) : ParseResult String :=
	ws1_body (take_while_byte is_space_byte input) input


#[partial]
def ws1_body (r : ParseResult String) (input : String) : ParseResult String :=
	match r {
		success rem out => if is_empty out then fail (ParseError.custom "expected whitespace" input) else success rem out,
		fail e => fail e
	}


#[partial]
def skip_spaces (input : String) : String :=
	skip_spaces_match (take_while_byte is_space_byte input) input


#[partial]
def skip_spaces_match (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => rem,
		fail _ => orig
	}
