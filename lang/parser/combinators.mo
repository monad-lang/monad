/// Parser combinator functions for the self-hosted Monad parser.

use lang.parser.core {
  ParseError, ParseResult, custom, fail, is_empty, parse_error_remaining,
  success, tag,
}
use lang.parser.char_preds {byte_at, is_ident_char, is_prefix}
use lang.types {custom, list_reverse}
use std.list {length}

open ParseResult {fail, success}

// --- Combinators ---

#[partial]
def tag (s : String) (input : String) : ParseResult String :=
	if is_prefix s input
	then success (String.drop (String.length s) input) s
	else fail (ParseError.tag s input)

/// Like `tag`, but for a KEYWORD specifically: `tag` alone is a bare
/// `is_prefix` check, so `tag "return" "return_foo 41"` succeeds,
/// consuming only `"return"` and leaving `"_foo 41"` -- wrongly treating
/// the ordinary identifier `return_foo` as the keyword `return` followed
/// by a separate expression. Confirmed as a real bug via a direct repro
/// (`def return_foo (x : I64) : I64 := x`, called as `return_foo 41`
/// elsewhere): `check` (which never calls `return_shorthand_parser`/
/// `do_stmt_return` on that reference position) accepts it, but `compile`
/// hit `unknown variable '_foo'`, and the self-hosted compiler's own
/// `bootstrap compile lang/main.mo monad` self-compile hit the identical
/// class of bug on `lang/scope.mo`'s own `return_type_after_n_args`
/// (compiled to a call to undefined `@_type_after_n_args` plus a spurious
/// `@Monad_pure` wrap) -- see `implementations/2026-08-29-return-
/// prefixed-def-name-mangled-with-spurious-monad-pure.md`. Requires a
/// genuine word boundary after the keyword (end of input, or a
/// non-identifier character) before accepting the match -- mirrors
/// `lang.parser.identifier`'s own correct pattern of parsing a FULL
/// identifier first and checking `is_keyword` on the whole thing, just
/// inverted (here the keyword is checked FIRST, so the boundary has to be
/// checked explicitly afterward instead of getting it for free).
#[partial]
def tag_keyword (s : String) (input : String) : ParseResult String :=
	match tag s input {
		success rem matched =>
			if keyword_boundary_ok rem
			then success rem matched
			else fail (ParseError.tag s input),
		fail e => fail e,
	}

#[partial]
def keyword_boundary_ok (rem : String) : Bool :=
	if String.is_empty rem
	then true
	else not (is_ident_char (String.slice rem 0 1))


/// "Furthest progress wins" error selection — mirrors the Rust
/// reference's `ParseError::or`/`append` (core/src/parser/error.rs),
/// which compare `input.input_len()` between two candidate errors and
/// keep whichever consumed more before failing (i.e. the deeper, more
/// specific failure), rather than discarding one arbitrarily. A
/// shorter `remaining` means more of the input was consumed before
/// this error fired, so it wins; ties keep `e1` (matches Rust's `or`,
/// which only replaces on strictly deeper progress).
#[partial]
def furthest_error (e1 : ParseError) (e2 : ParseError) : ParseError :=
	if I64.lt (String.length (parse_error_remaining e2)) (String.length (parse_error_remaining e1))
	then e2
	else e1


#[partial]
def alt (a : String -> ParseResult A) (b : String -> ParseResult A) (input : String) : ParseResult A :=
	alt_body (a input) b input


#[partial]
def alt_body (r : ParseResult A) (b : String -> ParseResult A) (input : String) : ParseResult A :=
	match r {
		success rem out => success rem out,
		fail e1 => alt_second (b input) e1 input
	}


#[partial]
def alt_second (r : ParseResult A) (e1 : ParseError) (input : String) : ParseResult A :=
	match r {
		success rem out => success rem out,
		fail e2 => fail (furthest_error e1 e2)
	}


// --- many0 / many1 ---

#[partial]
def many0 (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	many0_body (p input) p input


#[partial]
def many0_body (r : ParseResult A) (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	match r {
		success rem out =>
			many0_next (many0 p rem) out rem,
		fail _ => success input List.empty
	}


#[partial]
def many0_next (r : ParseResult (List A)) (out : A) (rem : String) : ParseResult (List A) :=
	match r {
		success rem2 rest => success rem2 (List.cons out rest),
		fail _ => success rem (List.cons out List.empty)
	}


#[partial]
def many1 (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	match many0 p input {
		success rem out =>
			if List.is_empty out
			then fail (ParseError.custom "expected at least one" input)
			else success rem out,
		fail e => fail e
	}


// --- Extended combinators (Phase 1.1) ---

#[partial]
def map_parse (f : A -> B) (p : String -> ParseResult A) (input : String) : ParseResult B :=
	map_parse_body (p input) f


#[partial]
def map_parse_body (r : ParseResult A) (f : A -> B) : ParseResult B :=
	match r {
		success rem out => map_parse_ok rem out f,
		fail e => map_parse_fail e
	}


#[partial]
def map_parse_ok (rem : String) (out : A) (f : A -> B) : ParseResult B :=
	success rem (f out)


#[partial]
def map_parse_fail (e : ParseError) : ParseResult B :=
	fail e


#[partial]
def bind_parse (p : String -> ParseResult A) (f : A -> String -> ParseResult B) (input : String) : ParseResult B :=
	bind_parse_body (p input) f


#[partial]
def bind_parse_body (r : ParseResult A) (f : A -> String -> ParseResult B) : ParseResult B :=
	match r {
		success rem out => f out rem,
		fail e => bind_parse_fail e
	}


#[partial]
def bind_parse_fail (e : ParseError) : ParseResult B :=
	fail e


#[partial]
def alt_fold (parsers : List (String -> ParseResult A)) (input : String) : ParseResult A :=
	match parsers {
		List.cons p ps => alt_fold_try (p input) ps input Option.none,
		List.empty => fail (ParseError.custom "alt_fold: empty list" input)
	}


/// `best` is the furthest-progressed error seen across every alternative
/// tried so far (see `furthest_error`) — threaded through the fold so
/// that when every alternative fails, the final error reported is the
/// deepest real failure among them, not whichever alternative happened
/// to be tried last.
#[partial]
def alt_fold_try (r : ParseResult A) (parsers : List (String -> ParseResult A)) (input : String) (best : Option ParseError) : ParseResult A :=
	match r {
		success rem out => alt_fold_ok rem out,
		fail e => alt_fold_next parsers input (Option.some (alt_fold_merge_best best e))
	}


#[partial]
def alt_fold_merge_best (best : Option ParseError) (e : ParseError) : ParseError :=
	match best {
		Option.some b => furthest_error b e,
		Option.none => e
	}


#[partial]
def alt_fold_next (parsers : List (String -> ParseResult A)) (input : String) (best : Option ParseError) : ParseResult A :=
	match parsers {
		List.cons p ps => alt_fold_try (p input) ps input best,
		List.empty => fail (alt_fold_best_or_default best input)
	}


#[partial]
def alt_fold_best_or_default (best : Option ParseError) (input : String) : ParseError :=
	match best {
		Option.some e => e,
		Option.none => ParseError.custom "alt_fold: empty list" input
	}


#[partial]
def alt_fold_ok (rem : String) (out : A) : ParseResult A :=
	success rem out


// --- Position-based combinators ---

#[partial]
def preceded_by (before : String -> ParseResult A) (p : String -> ParseResult B) (input : String) : ParseResult B :=
	preceded_by_body (before input) p


#[partial]
def preceded_by_body (r : ParseResult A) (p : String -> ParseResult B) : ParseResult B :=
	match r {
		success rem _ => p rem,
		fail e => preceded_by_err e
	}


#[partial]
def preceded_by_err (e : ParseError) : ParseResult B :=
	fail e


#[partial]
def terminated_by (p : String -> ParseResult A) (after : String -> ParseResult B) (input : String) : ParseResult A :=
	terminated_by_body (p input) after


#[partial]
def terminated_by_body (r : ParseResult A) (after : String -> ParseResult B) : ParseResult A :=
	match r {
		success rem out => terminated_by_after (after rem) out,
		fail e => terminated_by_err e
	}


#[partial]
def terminated_by_after (r : ParseResult B) (out : A) : ParseResult A :=
	match r {
		success rem _ => terminated_by_ok rem out,
		fail e => terminated_by_err e
	}


#[partial]
def terminated_by_ok (rem : String) (out : A) : ParseResult A :=
	success rem out


#[partial]
def terminated_by_err (e : ParseError) : ParseResult A :=
	fail e


#[partial]
def delimited_by (before : String -> ParseResult A) (p : String -> ParseResult B) (after : String -> ParseResult C) (input : String) : ParseResult B :=
	delimited_by_before (before input) p after


#[partial]
def delimited_by_before (r : ParseResult A) (p : String -> ParseResult B) (after : String -> ParseResult C) : ParseResult B :=
	match r {
		success rem _ => delimited_by_body (p rem) after,
		fail e => delimited_by_err e
	}


#[partial]
def delimited_by_body (r : ParseResult B) (after : String -> ParseResult C) : ParseResult B :=
	match r {
		success rem out => delimited_by_after (after rem) out,
		fail e => delimited_by_err e
	}


#[partial]
def delimited_by_after (r : ParseResult C) (out : B) : ParseResult B :=
	match r {
		success rem _ => delimited_by_ok rem out,
		fail e => delimited_by_err e
	}


#[partial]
def delimited_by_ok (rem : String) (out : B) : ParseResult B :=
	success rem out


#[partial]
def delimited_by_err (e : ParseError) : ParseResult B :=
	fail e


#[partial]
def separated_by (sep : String -> ParseResult A) (p : String -> ParseResult B) (input : String) : ParseResult (List B) :=
	separated_by_body (p input) p sep input List.empty


#[partial]
def separated_by_body (r : ParseResult B) (p : String -> ParseResult B) (sep : String -> ParseResult A) (input : String) (acc : List B) : ParseResult (List B) :=
	match r {
		success rem out => separated_by_loop (sep rem) rem out p sep acc,
		fail e => separated_by_ok input acc
	}


#[partial]
def separated_by_loop (r : ParseResult A) (rem : String) (out : B) (p : String -> ParseResult B) (sep : String -> ParseResult A) (acc : List B) : ParseResult (List B) :=
	match r {
		success rem2 _ => separated_by_body (p rem2) p sep rem2 (List.cons out acc),
		fail e => separated_by_ok rem (List.cons out acc)
	}


#[partial]
def separated_by_ok (input : String) (acc : List B) : ParseResult (List B) :=
	success input (list_reverse acc)


// --- UTF-8 codepoint-width stepping ---
//
// `String.slice`/`String.drop` are byte-oriented (see their own doc
// comments in core/src/core_native.rs); stepping by a hardcoded 1 byte
// per iteration — as every scanner here used to — silently returns ""
// once the offset lands mid-character for any multi-byte UTF-8 codepoint
// (the native slice/drop fall back to empty rather than panic on a
// non-boundary index). A scanner then sees `ch="" rest=""`, indistinguishable
// from genuine end-of-input, and truncates everything after the
// multi-byte character with zero diagnostic. Hit by any `take_while`-based
// scan (comments, whitespace, `is_not_*`-style delimiters, ...) — not a
// theoretical edge case: `lang/json.mo`/`lang/toml.mo` both hit this on
// an em dash before their first real declaration.
//
// `utf8_char_width` reads just the lead byte (`String.get`, an O(1) byte
// lookup — deliberately NOT `String.get_char`, which decodes the whole
// remaining string into a `Vec<char>` on every call and would make every
// scan quadratic) and applies the standard UTF-8 rule to determine how
// many bytes the character it starts occupies, so a scanner can step by
// the right amount instead of always 1.

#[partial]
def utf8_char_width (s : String) : I64 :=
	match String.get s 0 {
		Option.some byte => utf8_char_width_of_byte byte,
		// Empty input — width is moot (take_while_loop already checks
		// is_empty first), but 1 keeps this total.
		Option.none => 1
	}

/// Standard UTF-8 lead-byte rule: `0xxxxxxx` (<0x80, i.e. <128u8) is a
/// 1-byte ASCII char; `110xxxxx` (0xC0-0xDF, 192-223) starts a 2-byte
/// sequence; `1110xxxx` (0xE0-0xEF, 224-239) starts 3 bytes; `11110xxx`
/// (0xF0-0xF7, 240-247) starts 4. A byte in 0x80-0xBF (128-191) is a
/// *continuation* byte — it should never be seen as a lead byte by a
/// scanner that's stepping correctly, but falls back to width 1 rather
/// than looping forever on malformed input.
#[partial]
def utf8_char_width_of_byte (byte : U8) : I64 :=
	if U8.lt byte 128u8 then 1
	else if U8.lt byte 192u8 then 1
	else if U8.lt byte 224u8 then 2
	else if U8.lt byte 240u8 then 3
	else 4


// --- take_while combinator ---
//
// Tracks the ORIGINAL input alongside the shrinking remainder instead of
// building the matched text char-by-char via `String.concat` (the old
// approach: O(L^2) byte-copies for a matched run of length L, on top of
// `String.slice`/`String.drop` themselves -- see `shared_str.rs`'s doc
// comment for why those are now O(1)). Once `slice` is O(1), the correct
// shape is: keep consuming from `input`, and when the predicate first
// fails (or input is exhausted), take exactly ONE slice of `original`
// from its start to how far `input` has shrunk -- one O(1) slice instead
// of L accumulator concats. Benefits every `take_while`-based scan at
// once (identifiers, numbers, whitespace-skipping, comment-skipping),
// not just call sites that discard the matched text.

#[partial]
def take_while (pred : String -> Bool) (input : String) : ParseResult String :=
	take_while_loop pred input input


// Deliberately SELF-tail-recursive: the previous shape split the loop
// into a `take_while_loop`/`take_while_check` MUTUAL tail recursion
// (check called loop, loop called check), which compiled binaries can
// not grow through -- the self-hosted backend's tail-call optimization
// (`apply_self_tco`, lang/codegen/emit.mo) rewrites only SELF-recursion
// into loops; mutual tail recursion would need LLVM `musttail`, not
// implemented. A whole-file scan then cost two real stack frames per
// input char and a ~225KB file blew the 8MB stack at ~11K chars
// (measured: backtrace of 22.7K alternating frames, rsp pinned at the
// stack guard page -- /tmp probe over lang/scope.mo's own text, the
// `check lang/main.mo` rung-2 blocker). Merging the predicate check
// into the loop body puts the recursive call in the same Def, where
// `apply_self_tco` turns it into a `br` back-edge: constant stack for
// any input length. The interpreted side is unaffected (same
// per-char work, one call less).
#[partial]
def take_while_loop (pred : String -> Bool) (original : String) (input : String) : ParseResult String :=
	if is_empty input
	then take_while_done original input
	else
		let width : I64 := utf8_char_width input in
		let ch : String := String.slice input 0 width in
		let rest : String := String.drop width input in
		if pred ch
		then take_while_loop pred original rest
		else take_while_done original input


#[partial]
def take_while_done (original : String) (remaining : String) : ParseResult String :=
	let consumed : I64 := I64.sub (String.length original) (String.length remaining) in
	success remaining (String.slice original 0 consumed)


// --- Byte-indexed take_while --------------------------------------
//
// Same contract as `take_while` above, for the ASCII character classes
// (`is_space_byte`/`is_ident_char_byte`/`is_digit_byte`/... in
// `lang/parser/char_preds.mo`). The difference is what it costs per
// input character.
//
// `take_while_loop` does, per character: `is_empty`, `utf8_char_width`
// (a `String.get` plus up to four `U8.lt`), `String.slice input 0 width`
// -- which ALLOCATES a fresh one-character string -- the predicate call
// on that string, and a `String.drop` to produce the tail it recurses
// on. Two allocations per character, plus a `String.beq` chain inside
// the predicate.
//
// This scans a byte index instead and slices exactly twice, at the token
// boundary: two allocations per TOKEN rather than per character, and the
// predicate compares numbers. See `bench/parser_take_while.mo` for the
// measurement this was built against, and `char_preds.mo`'s own note for
// why byte-wise scanning is correct for ASCII classes specifically (a
// UTF-8 lead or continuation byte fails all of them, so a scan stops
// cleanly at a character boundary rather than splitting one).
//
// Deliberately NOT expressed as a `match` on `String.get`: the loop has
// to stay a self-tail-recursive `if`/`else` chain in ONE def, for the
// reason `take_while_loop` documents above -- `apply_self_tco`
// (`lang/codegen/emit.mo`) rewrites only self-recursion into a loop, and
// anything else costs a real stack frame per character in a compiled
// binary. `byte_at` (`char_preds.mo`) absorbs the `Option`.
#[partial]
def take_while_byte (pred : U8 -> Bool) (input : String) : ParseResult String :=
	take_while_byte_at pred input 0 (String.length input)


#[partial]
def take_while_byte_at (pred : U8 -> Bool) (input : String) (i : I64) (n : I64) : ParseResult String :=
	if I64.beq i n
	then take_while_byte_done input i
	else if pred (byte_at input i)
	then take_while_byte_at pred input (i + 1) n
	else take_while_byte_done input i


#[partial]
def take_while_byte_done (input : String) (i : I64) : ParseResult String :=
	success (String.drop i input) (String.slice input 0 i)


// --- Optional parser ---

#[partial]
def opt (p : String -> ParseResult A) (input : String) : ParseResult (Option A) :=
	opt_body (p input) input


#[partial]
def opt_body (r : ParseResult A) (input : String) : ParseResult (Option A) :=
	match r {
		success rem out => opt_some rem out,
		fail e => opt_none input
	}


#[partial]
def opt_some (rem : String) (out : A) : ParseResult (Option A) :=
	success rem (Option.some out)


#[partial]
def opt_none (input : String) : ParseResult (Option A) :=
	success input Option.none


// --- Tests: furthest-failure-wins (alt / alt_fold) ---

#[test]
def test_furthest_error_picks_deeper : Bool :=
	let e1 : ParseError := ParseError.tag "x" "abc" in
	let e2 : ParseError := ParseError.custom "deep" "c" in
	String.beq (parse_error_remaining (furthest_error e1 e2)) "c"

#[test]
def test_furthest_error_tie_keeps_first : Bool :=
	let e1 : ParseError := ParseError.tag "x" "abc" in
	let e2 : ParseError := ParseError.custom "other" "def" in
	String.beq (parse_error_remaining (furthest_error e1 e2)) "abc"

#[partial]
def test_shallow_fail (input : String) : ParseResult String :=
	fail (ParseError.tag "shallow" input)

#[partial]
def test_deep_fail (input : String) : ParseResult String :=
	fail (ParseError.custom "deep failure" (String.drop 3 input))

/// Both branches of `alt` fail here, but `test_deep_fail` consumed more
/// (dropped 3 chars) before failing — the combined error must report
/// that deeper failure, not a generic "both alt failed" anchored at the
/// very start of the input.
#[test]
def test_alt_prefers_deeper_failure : Bool :=
	match alt test_shallow_fail test_deep_fail "abcdef" {
		success _ _ => false,
		fail e => String.beq (parse_error_remaining e) "def"
	}

#[test]
def test_alt_order_independent : Bool :=
	match alt test_deep_fail test_shallow_fail "abcdef" {
		success _ _ => false,
		fail e => String.beq (parse_error_remaining e) "def"
	}

#[partial]
def test_fold_fail_a (input : String) : ParseResult String :=
	fail (ParseError.tag "a" input)

#[partial]
def test_fold_fail_b (input : String) : ParseResult String :=
	fail (ParseError.custom "deepest" (String.drop 4 input))

#[partial]
def test_fold_fail_c (input : String) : ParseResult String :=
	fail (ParseError.tag "c" input)

/// Same idea as `test_alt_prefers_deeper_failure` but across an
/// `alt_fold` list of more than two alternatives, with the deepest
/// failure in the middle — confirms the running best-so-far survives
/// the whole fold, not just a pairwise comparison.
#[test]
def test_alt_fold_prefers_deepest_failure : Bool :=
	match alt_fold [test_fold_fail_a, test_fold_fail_b, test_fold_fail_c] "abcdefgh" {
		success _ _ => false,
		fail e => String.beq (parse_error_remaining e) "efgh"
	}

#[test]
def test_alt_fold_empty_list_still_fails : Bool :=
	match alt_fold ([] : List (String -> ParseResult String)) "abc" {
		success _ _ => false,
		fail _ => true
	}

// --- End of combinators ---
