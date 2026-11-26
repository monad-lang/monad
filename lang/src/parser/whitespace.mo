/// Whitespace parsing functions for the self-hosted Monad parser.

use parsec::core {ParseResult, custom, is_empty, Text}
use parsec::char_preds {is_space_byte}
use parsec::combinators {take_while_byte}

open ParseResult {fail, success}

// --- Whitespace ---

#[partial]
def spaces (input : Text) : ParseResult Text String :=
    take_while_byte is_space_byte input

#[partial]
def ws0 (input : Text) : ParseResult Text String :=
    take_while_byte is_space_byte input

#[partial]
def ws1 (input : Text) : ParseResult Text String :=
    ws1_body (take_while_byte is_space_byte input) input

#[partial]
def ws1_body (r : ParseResult Text String) (input : Text) : ParseResult Text String :=
    match r {
        success rem out => if is_empty out then fail (ParseError.custom "expected whitespace" input) else success rem out,
        fail e => fail e
    }

#[partial]
/// Skip whitespace and answer the cursor after it -- a CURSOR helper, not a
/// string one: it is the remainder of a parse, and every grammar step chains
/// it into the next parser.
pub def skip_spaces (input : Text) : Text :=
    skip_spaces_match (take_while_byte is_space_byte input) input

#[partial]
pub def skip_spaces_match (r : ParseResult Text String) (orig : Text) : Text :=
    match r {
        success rem _ => rem,
        fail _ => orig
    }
