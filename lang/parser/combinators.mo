/// Parser combinator functions for the self-hosted Monad parser.

use lang.parser.core
use lang.parser.char_preds
use lang.types
use std.list

open ParseResult

// --- Combinators ---

@[partial]
def tag (s : String) (input : String) : ParseResult String :=
	if is_prefix s input
	then success (String.drop (String.length s) input) s
	else fail (ParseError.tag s)


@[partial]
def alt (a : String -> ParseResult A) (b : String -> ParseResult A) (input : String) : ParseResult A :=
	alt_body (a input) b input


@[partial]
def alt_body (r : ParseResult A) (b : String -> ParseResult A) (input : String) : ParseResult A :=
	match r {
		success rem out => success rem out,
		fail e1 => alt_second (b input) e1
	}


@[partial]
def alt_second (r : ParseResult A) (e1 : ParseError) : ParseResult A :=
	match r {
		success rem out => success rem out,
		fail e2 => fail (ParseError.custom "both alt failed")
	}


// --- many0 / many1 ---

@[partial]
def many0 (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	many0_body (p input) p input


@[partial]
def many0_body (r : ParseResult A) (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	match r {
		success rem out =>
			many0_next (many0 p rem) out rem,
		fail _ => success input List.empty
	}


@[partial]
def many0_next (r : ParseResult (List A)) (out : A) (rem : String) : ParseResult (List A) :=
	match r {
		success rem2 rest => success rem2 (List.cons out rest),
		fail _ => success rem (List.cons out List.empty)
	}


@[partial]
def many1 (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	match many0 p input {
		success rem out =>
			if List.is_empty out
			then fail (ParseError.custom "expected at least one")
			else success rem out,
		fail e => fail e
	}


// --- Extended combinators (Phase 1.1) ---

@[partial]
def map_parse (f : A -> B) (p : String -> ParseResult A) (input : String) : ParseResult B :=
	map_parse_body (p input) f


@[partial]
def map_parse_body (r : ParseResult A) (f : A -> B) : ParseResult B :=
	match r {
		success rem out => map_parse_ok rem out f,
		fail e => map_parse_fail e
	}


@[partial]
def map_parse_ok (rem : String) (out : A) (f : A -> B) : ParseResult B :=
	success rem (f out)


@[partial]
def map_parse_fail (e : ParseError) : ParseResult B :=
	fail e


@[partial]
def bind_parse (p : String -> ParseResult A) (f : A -> String -> ParseResult B) (input : String) : ParseResult B :=
	bind_parse_body (p input) f


@[partial]
def bind_parse_body (r : ParseResult A) (f : A -> String -> ParseResult B) : ParseResult B :=
	match r {
		success rem out => f out rem,
		fail e => bind_parse_fail e
	}


@[partial]
def bind_parse_fail (e : ParseError) : ParseResult B :=
	fail e


@[partial]
def alt_fold (parsers : List (String -> ParseResult A)) (input : String) : ParseResult A :=
	match parsers {
		List.cons p ps => alt_fold_try (p input) ps input,
		List.empty => fail (ParseError.custom "alt_fold: empty list")
	}


@[partial]
def alt_fold_try (r : ParseResult A) (parsers : List (String -> ParseResult A)) (input : String) : ParseResult A :=
	match r {
		success rem out => alt_fold_ok rem out,
		fail e => alt_fold parsers input
	}


@[partial]
def alt_fold_ok (rem : String) (out : A) : ParseResult A :=
	success rem out


// --- Position-based combinators ---

@[partial]
def preceded_by (before : String -> ParseResult A) (p : String -> ParseResult B) (input : String) : ParseResult B :=
	preceded_by_body (before input) p


@[partial]
def preceded_by_body (r : ParseResult A) (p : String -> ParseResult B) : ParseResult B :=
	match r {
		success rem _ => p rem,
		fail e => preceded_by_err e
	}


@[partial]
def preceded_by_err (e : ParseError) : ParseResult B :=
	fail e


@[partial]
def terminated_by (p : String -> ParseResult A) (after : String -> ParseResult B) (input : String) : ParseResult A :=
	terminated_by_body (p input) after


@[partial]
def terminated_by_body (r : ParseResult A) (after : String -> ParseResult B) : ParseResult A :=
	match r {
		success rem out => terminated_by_after (after rem) out,
		fail e => terminated_by_err e
	}


@[partial]
def terminated_by_after (r : ParseResult B) (out : A) : ParseResult A :=
	match r {
		success rem _ => terminated_by_ok rem out,
		fail e => terminated_by_err e
	}


@[partial]
def terminated_by_ok (rem : String) (out : A) : ParseResult A :=
	success rem out


@[partial]
def terminated_by_err (e : ParseError) : ParseResult A :=
	fail e


@[partial]
def delimited_by (before : String -> ParseResult A) (p : String -> ParseResult B) (after : String -> ParseResult C) (input : String) : ParseResult B :=
	delimited_by_before (before input) p after


@[partial]
def delimited_by_before (r : ParseResult A) (p : String -> ParseResult B) (after : String -> ParseResult C) : ParseResult B :=
	match r {
		success rem _ => delimited_by_body (p rem) after,
		fail e => delimited_by_err e
	}


@[partial]
def delimited_by_body (r : ParseResult B) (after : String -> ParseResult C) : ParseResult B :=
	match r {
		success rem out => delimited_by_after (after rem) out,
		fail e => delimited_by_err e
	}


@[partial]
def delimited_by_after (r : ParseResult C) (out : B) : ParseResult B :=
	match r {
		success rem _ => delimited_by_ok rem out,
		fail e => delimited_by_err e
	}


@[partial]
def delimited_by_ok (rem : String) (out : B) : ParseResult B :=
	success rem out


@[partial]
def delimited_by_err (e : ParseError) : ParseResult B :=
	fail e


@[partial]
def separated_by (sep : String -> ParseResult A) (p : String -> ParseResult B) (input : String) : ParseResult (List B) :=
	separated_by_body (p input) p sep input List.empty


@[partial]
def separated_by_body (r : ParseResult B) (p : String -> ParseResult B) (sep : String -> ParseResult A) (input : String) (acc : List B) : ParseResult (List B) :=
	match r {
		success rem out => separated_by_loop (sep rem) rem out p sep acc,
		fail e => separated_by_ok input acc
	}


@[partial]
def separated_by_loop (r : ParseResult A) (rem : String) (out : B) (p : String -> ParseResult B) (sep : String -> ParseResult A) (acc : List B) : ParseResult (List B) :=
	match r {
		success rem2 _ => separated_by_body (p rem2) p sep rem2 (List.cons out acc),
		fail e => separated_by_ok rem (List.cons out acc)
	}


@[partial]
def separated_by_ok (input : String) (acc : List B) : ParseResult (List B) :=
	success input (list_reverse acc)


// --- take_while combinator ---

@[partial]
def take_while (pred : String -> Bool) (input : String) : ParseResult String :=
	take_while_loop pred "" input


@[partial]
def take_while_loop (pred : String -> Bool) (acc : String) (input : String) : ParseResult String :=
	if is_empty input
	then success input acc
	else take_while_check pred acc input (String.slice input 0 1) (String.drop 1 input)


@[partial]
def take_while_check (pred : String -> Bool) (acc : String) (input : String) (ch : String) (rest : String) : ParseResult String :=
	if pred ch
	then take_while_loop pred (String.concat acc ch) rest
	else success input acc


// --- Optional parser ---

@[partial]
def opt (p : String -> ParseResult A) (input : String) : ParseResult (Option A) :=
	opt_body (p input) input


@[partial]
def opt_body (r : ParseResult A) (input : String) : ParseResult (Option A) :=
	match r {
		success rem out => opt_some rem out,
		fail e => opt_none input
	}


@[partial]
def opt_some (rem : String) (out : A) : ParseResult (Option A) :=
	success rem (Option.some out)


@[partial]
def opt_none (input : String) : ParseResult (Option A) :=
	success input Option.none


// --- End of combinators ---
