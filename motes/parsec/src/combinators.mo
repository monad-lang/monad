/// Parser combinator functions.
///
/// Two shapes live here and they are deliberately different:
///
/// * **Structural** combinators (`alt`, `many0`, `map_parse`, ...) are generic
///   over the cursor `S`. They never look inside a byte, only thread the
///   cursor, so they cost nothing per byte: they need `[Copy S]` because they
///   hand the same cursor to more than one parser, and the two that must
///   *build* an error need `[Input S]` for its offset.
/// * **Text primitives** (`tag`, `take_while`, `take_while_byte`) name `Text`
///   concretely. That is what lets `alt (tag "a") (tag "b")` solve `S = Text`
///   from the leaves without an annotation, and it keeps a dictionary out of
///   the per-token path.
///
/// Binary primitives live in `binary.mo`.

use lib::core {
    ParseError, ParseResult, is_empty, parse_error_at, parse_error_remaining
}
use lib::input {Input, Text}
use lib::char_preds {
    byte_at, is_ident_char, is_ident_char_byte, is_space, is_space_byte
}
use std::list {}

open ParseResult {fail, success}

// --- Combinators ---

#[partial]
pub def tag (s : String) (input : Text) : ParseResult Text String :=
    if Input.input_starts_with s input
    then success (Input.input_advance (String.length s) input) s
    else fail (ParseError.tag s input)

/// Like `tag`, but for a KEYWORD specifically: `tag` alone is a bare
/// prefix check, so `tag "return" "return_foo 41"` succeeds,
/// consuming only `"return"` and leaving `"_foo 41"` -- wrongly treating
/// the ordinary identifier `return_foo` as the keyword `return` followed
/// by a separate expression. Requires a genuine word boundary after the
/// keyword (end of input, or a non-identifier byte) before accepting the
/// match. The boundary test reads one byte through the cursor
/// (`Input.input_head`) instead of the old `String.is_empty` -- a full
/// `strlen` of the remaining file, paid per keyword alternative.
#[partial]
pub def tag_keyword (s : String) (input : Text) : ParseResult Text String :=
    match tag s input {
        success rem matched => tag_keyword_boundary rem matched s input,
        fail e => fail e,
    }

#[partial]
def tag_keyword_boundary (rem : Text) (matched : String) (s : String) (input : Text) : ParseResult Text String :=
    if keyword_boundary_ok rem
    then success rem matched
    else fail (ParseError.tag s input)

#[partial]
def keyword_boundary_ok (rem : Text) : Bool :=
    match Input.input_head rem {
        Option.none => true,
        Option.some b => not (is_ident_char_byte b)
    }

/// "Furthest progress wins" error selection — mirrors the Rust
/// reference's `ParseError::or`/`append` (rust/core/src/parser/error.rs),
/// which compare `input.input_len()` between two candidate errors and
/// keep whichever consumed more before failing (i.e. the deeper, more
/// specific failure), rather than discarding one arbitrarily. A
/// shorter `remaining` means more of the input was consumed before
/// this error fired, so it wins; ties keep `e1` (matches Rust's `or`,
/// which only replaces on strictly deeper progress).
///
/// This used to cost two `String.length` calls -- two `strlen`s of the
/// whole REMAINING FILE -- per pair of alternatives, and was measured as
/// quadratic in file size on the compiled backend (`parse_all_decls` over
/// 245,760 bytes: 5.91 s, of which ~3 s was this and a sibling). A
/// pointer-identity shortcut removed the common case; threading an offset
/// removes the rest: both sides are now absolute byte offsets in the
/// cursor, so the comparison is two field reads and there is nothing left
/// to shortcut.
#[partial]
def furthest_error (e1 : ParseError) (e2 : ParseError) : ParseError :=
    if I64.gt (ParseError.error_offset e2) (ParseError.error_offset e1)
    then e2
    else e1

#[partial]
pub def alt [Copy S] (a : S -> ParseResult S A) (b : S -> ParseResult S A) (input : S) : ParseResult S A :=
    alt_body (a input) b input

#[partial]
def alt_body [Copy S] (r : ParseResult S A) (b : S -> ParseResult S A) (input : S) : ParseResult S A :=
    match r {
        success rem out => success rem out,
        fail e1 => alt_second (b input) e1
    }

#[partial]
def alt_second (r : ParseResult S A) (e1 : ParseError) : ParseResult S A :=
    match r {
        success rem out => success rem out,
        fail e2 => fail (furthest_error e1 e2)
    }

// --- many0 / many1 ---

/// Zero or more `p`, accumulating in REVERSE and reversing once at the end.
///
/// The shape is load-bearing, and it is the same lesson as
/// `toolkit/position.mo`'s `line_index_go`: the obvious spelling --
/// `success rem out => List.cons out <rest of many0>` -- is NOT tail
/// recursive and CANNOT be made so, because the recursive call sits under
/// a `List.cons`. It therefore costs native stack per ITERATION, and this
/// combinator's iteration count is the number of characters in the input.
///
/// That is fine for the Monad parser, whose `many0` uses are per-token on
/// small windows, but it is fatal for the JSON reader: an LSP `didOpen`
/// request carries the entire file text as ONE JSON string, so
/// `Json.parse_string_content` calls `many0` once per character of the
/// buffer. Measured at 378,250 frames -- and `rc=-11` inside
/// `GC_clear_stack_inner` -- for the 331 KB `lang/src/module.mo`, well
/// past the 8 MB default stack. The accumulator makes the self-call the
/// whole body of one arm, which `lang/src/codegen/tco.mo` rewrites to a
/// loop with constant stack.
///
/// Equivalence with the previous spelling: same elements, same order
/// (`List.reverse` undoes the reverse accumulation), and on failure the
/// same `success input` -- note the returned remainder is the input as of
/// the call whose `p` failed, not the original, which is why the failing
/// arm here returns its own `input` rather than an outer one.
#[partial]
pub def many0 [Copy S] (p : S -> ParseResult S A) (input : S) : ParseResult S (List A) :=
    many0_go p input List.empty

#[partial]
def many0_go [Copy S] (p : S -> ParseResult S A) (input : S) (acc : List A) : ParseResult S (List A) :=
    match p input {
        success rem out => many0_go p rem (List.cons out acc),
        fail _ => success input (List.reverse acc)
    }

#[partial]
pub def many1 [Input S, Copy S] (p : S -> ParseResult S A) (input : S) : ParseResult S (List A) :=
    match many0 p input {
        success rem out => many1_nonempty rem out input,
        fail e => fail e
    }

#[partial]
def many1_nonempty [Input S] (rem : S) (out : List A) (input : S) : ParseResult S (List A) :=
    // Rebuild from the pattern binders: the success payload is typed
    // by the constructor's `A`, so mentioning the binder twice is an
    // affine use.
    match out {
        List.empty => fail (parse_error_at "expected at least one" input),
        List.cons hd tl => success rem (List.cons hd tl),
    }

// --- Extended combinators ---

#[partial]
pub def map_parse (f : A -> B) (p : S -> ParseResult S A) (input : S) : ParseResult S B :=
    map_parse_body (p input) f

#[partial]
def map_parse_body (r : ParseResult S A) (f : A -> B) : ParseResult S B :=
    match r {
        success rem out => map_parse_ok rem out f,
        fail e => map_parse_fail e
    }

#[partial]
def map_parse_ok (rem : S) (out : A) (f : A -> B) : ParseResult S B :=
    success rem (f out)

#[partial]
def map_parse_fail (e : ParseError) : ParseResult S B :=
    fail e

#[partial]
pub def bind_parse (p : S -> ParseResult S A) (f : A -> S -> ParseResult S B) (input : S) : ParseResult S B :=
    bind_parse_body (p input) f

#[partial]
def bind_parse_body (r : ParseResult S A) (f : A -> S -> ParseResult S B) : ParseResult S B :=
    match r {
        success rem out => f out rem,
        fail e => bind_parse_fail e
    }

#[partial]
def bind_parse_fail (e : ParseError) : ParseResult S B :=
    fail e

#[partial]
pub def alt_fold [Input S, Copy S] (parsers : List (S -> ParseResult S A)) (input : S) : ParseResult S A :=
    match parsers {
        List.cons p ps => alt_fold_try (p input) ps input Option.none,
        List.empty => fail (parse_error_at "alt_fold: empty list" input)
    }

/// `best` is the furthest-progressed error seen across every alternative
/// tried so far (see `furthest_error`) — threaded through the fold so
/// that when every alternative fails, the final error reported is the
/// deepest real failure among them, not whichever alternative happened
/// to be tried last.
#[partial]
def alt_fold_try [Input S, Copy S] (r : ParseResult S A) (parsers : List (S -> ParseResult S A)) (input : S) (best : Option ParseError) : ParseResult S A :=
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
def alt_fold_next [Input S, Copy S] (parsers : List (S -> ParseResult S A)) (input : S) (best : Option ParseError) : ParseResult S A :=
    match parsers {
        List.cons p ps => alt_fold_try (p input) ps input best,
        List.empty => fail (alt_fold_best_or_default best input)
    }

#[partial]
def alt_fold_best_or_default [Input S] (best : Option ParseError) (input : S) : ParseError :=
    match best {
        Option.some e => e,
        Option.none => parse_error_at "alt_fold: empty list" input
    }

#[partial]
def alt_fold_ok (rem : S) (out : A) : ParseResult S A :=
    success rem out

// --- Position-based combinators ---

#[partial]
pub def preceded_by (before : S -> ParseResult S A) (p : S -> ParseResult S B) (input : S) : ParseResult S B :=
    preceded_by_body (before input) p

#[partial]
def preceded_by_body (r : ParseResult S A) (p : S -> ParseResult S B) : ParseResult S B :=
    match r {
        success rem _ => p rem,
        fail e => preceded_by_err e
    }

#[partial]
def preceded_by_err (e : ParseError) : ParseResult S B :=
    fail e

#[partial]
pub def terminated_by (p : S -> ParseResult S A) (after : S -> ParseResult S B) (input : S) : ParseResult S A :=
    terminated_by_body (p input) after

#[partial]
def terminated_by_body (r : ParseResult S A) (after : S -> ParseResult S B) : ParseResult S A :=
    match r {
        success rem out => terminated_by_after (after rem) out,
        fail e => terminated_by_err e
    }

#[partial]
def terminated_by_after (r : ParseResult S B) (out : A) : ParseResult S A :=
    match r {
        success rem _ => terminated_by_ok rem out,
        fail e => terminated_by_err e
    }

#[partial]
def terminated_by_ok (rem : S) (out : A) : ParseResult S A :=
    success rem out

#[partial]
def terminated_by_err (e : ParseError) : ParseResult S A :=
    fail e

#[partial]
pub def delimited_by (before : S -> ParseResult S A) (p : S -> ParseResult S B) (after : S -> ParseResult S C) (input : S) : ParseResult S B :=
    delimited_by_before (before input) p after

#[partial]
def delimited_by_before (r : ParseResult S A) (p : S -> ParseResult S B) (after : S -> ParseResult S C) : ParseResult S B :=
    match r {
        success rem _ => delimited_by_body (p rem) after,
        fail e => delimited_by_err e
    }

#[partial]
def delimited_by_body (r : ParseResult S B) (after : S -> ParseResult S C) : ParseResult S B :=
    match r {
        success rem out => delimited_by_after (after rem) out,
        fail e => delimited_by_err e
    }

#[partial]
def delimited_by_after (r : ParseResult S C) (out : B) : ParseResult S B :=
    match r {
        success rem _ => delimited_by_ok rem out,
        fail e => delimited_by_err e
    }

#[partial]
def delimited_by_ok (rem : S) (out : B) : ParseResult S B :=
    success rem out

#[partial]
def delimited_by_err (e : ParseError) : ParseResult S B :=
    fail e

#[partial]
pub def separated_by [Copy S] (sep : S -> ParseResult S A) (p : S -> ParseResult S B) (input : S) : ParseResult S (List B) :=
    separated_by_body (p input) p sep input List.empty

#[partial]
def separated_by_body [Copy S] (r : ParseResult S B) (p : S -> ParseResult S B) (sep : S -> ParseResult S A) (input : S) (acc : List B) : ParseResult S (List B) :=
    match r {
        success rem out => separated_by_loop (sep rem) rem out p sep acc,
        fail e => separated_by_ok input acc
    }

#[partial]
def separated_by_loop [Copy S] (r : ParseResult S A) (rem : S) (out : B) (p : S -> ParseResult S B) (sep : S -> ParseResult S A) (acc : List B) : ParseResult S (List B) :=
    match r {
        success rem2 _ => separated_by_body (p rem2) p sep rem2 (List.cons out acc),
        fail e => separated_by_ok rem (List.cons out acc)
    }

#[partial]
def separated_by_ok (input : S) (acc : List B) : ParseResult S (List B) :=
    success input (List.reverse acc)

// --- UTF-8 codepoint-width stepping ---
//
// `String.slice`/`String.drop` are byte-oriented; stepping by a hardcoded 1
// byte per iteration — as every scanner here used to — silently returns ""
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
pub def utf8_char_width (s : String) : I64 :=
    match String.get s 0 {
        Option.some byte => utf8_char_width_of_byte byte,
        // Empty input — width is moot (every scanner checks the end
        // first), but 1 keeps this total.
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
pub def utf8_char_width_of_byte (byte : U8) : I64 :=
    if U8.lt byte 128u8 then 1
    else if U8.lt byte 192u8 then 1
    else if U8.lt byte 224u8 then 2
    else if U8.lt byte 240u8 then 3
    else 4

/// The width of the character at the cursor (its lead byte), or 1 at end.
/// The cursor-based sibling of `utf8_char_width`: a scanner that holds a
/// `Text` steps by this and slices with `Input.input_text`.
#[partial]
pub def text_char_width (input : Text) : I64 :=
    match Input.input_head input {
        Option.some b => utf8_char_width_of_byte b,
        Option.none => 1
    }

// --- take_while combinators ---
//
// Both scanners track the START cursor and the CURRENT cursor and slice the
// match once, at the boundary. The old shapes had to reconstruct "how much
// did I consume" by subtracting two `String.length`s -- two `strlen`s of the
// whole remaining file per token on the compiled backend -- because a
// suffix has no position. A `Text` cursor does, so the delta is one
// subtraction.

#[partial]
pub def take_while (pred : String -> Bool) (input : Text) : ParseResult Text String :=
    take_while_loop pred input input

// Deliberately SELF-tail-recursive: the previous shape split the loop
// into a `take_while_loop`/`take_while_check` MUTUAL tail recursion
// (check called loop, loop called check), which compiled binaries can
// not grow through -- the self-hosted backend's tail-call optimization
// (`apply_self_tco`, lang/codegen/emit.mo) rewrites only SELF-recursion
// into loops; mutual tail recursion would need LLVM `musttail`, not
// implemented. A whole-file scan then cost two real stack frames per
// input char and a ~225KB file blew the 8MB stack at ~11K chars.
#[partial]
def take_while_loop (pred : String -> Bool) (original : Text) (input : Text) : ParseResult Text String :=
    if Input.at_end input
    then take_while_done original input
    else
        let width : I64 := text_char_width input in
        let ch : String := Input.input_text width input in
        let rest : Text := Input.input_advance width input in
        if pred ch
        then take_while_loop pred original rest
        else take_while_done original input

#[partial]
def take_while_done (original : Text) (remaining : Text) : ParseResult Text String :=
    let consumed : I64 := Text.offset remaining - Text.offset original in
    success remaining (Input.input_text consumed original)

// --- Byte-wise take_while ------------------------------------------
//
// Same contract as `take_while` above, for the ASCII character classes
// (`is_space_byte`/`is_ident_char_byte`/`is_digit_byte`/... in
// `char_preds.mo`). The difference is what it costs per input character:
// `take_while` allocates a one-character string per character and calls a
// `String.beq` chain; this scans bytes (`Input.input_scan`, whose loop is
// monomorphic per cursor) and slices exactly twice, at the token boundary.
//
// Byte-wise is CORRECT for these classes precisely because they are all
// ASCII: a UTF-8 lead byte or continuation byte fails every one of them, so
// a scan stops at a character boundary rather than splitting a character.
#[partial]
pub def take_while_byte (pred : U8 -> Bool) (input : Text) : ParseResult Text String :=
    let n : I64 := Input.input_scan pred input in
    success (Input.input_advance n input) (Input.input_text n input)

// --- Optional parser ---

#[partial]
pub def opt [Copy S] (p : S -> ParseResult S A) (input : S) : ParseResult S (Option A) :=
    opt_body (p input) input

#[partial]
def opt_body [Copy S] (r : ParseResult S A) (input : S) : ParseResult S (Option A) :=
    match r {
        success rem out => opt_some rem out,
        fail e => opt_none input
    }

#[partial]
def opt_some (rem : S) (out : A) : ParseResult S (Option A) :=
    success rem (Option.some out)

#[partial]
def opt_none (input : S) : ParseResult S (Option A) :=
    success input Option.none

// --- Tests: furthest-failure-wins (alt / alt_fold) ---
//
// Offsets are absolute byte offsets, so these read the position rather than
// the remaining text.

#[test]
def test_furthest_error_picks_deeper : Bool :=
    let e1 : ParseError := ParseError.tag "x" (Text.of_string "abcd") in
    let e2 : ParseError := ParseError.custom "deep" (Text.at_offset 3) in
    I64.beq (ParseError.error_offset (furthest_error e1 e2)) 3

#[test]
def test_furthest_error_tie_keeps_first : Bool :=
    let e1 : ParseError := ParseError.tag "x" (Text.of_string "abc") in
    let e2 : ParseError := ParseError.custom "other" (Text.of_string "def") in
    String.beq "x" (match furthest_error e1 e2 { tag exp _ => exp, custom msg _ => msg })

#[partial]
def test_shallow_fail (input : Text) : ParseResult Text String :=
    fail (ParseError.tag "shallow" input)

#[partial]
def test_deep_fail (input : Text) : ParseResult Text String :=
    fail (ParseError.custom "deep failure" (Input.input_advance 3 input))

/// Both branches of `alt` fail here, but `test_deep_fail` consumed more
/// (advanced 3 bytes) before failing — the combined error must report
/// that deeper failure, not a generic "both alt failed" anchored at the
/// very start of the input.
#[test]
def test_alt_prefers_deeper_failure : Bool :=
    match alt test_shallow_fail test_deep_fail (Text.of_string "abcdef") {
        success _ _ => false,
        fail e => I64.beq (ParseError.error_offset e) 3
    }

#[test]
def test_alt_order_independent : Bool :=
    match alt test_deep_fail test_shallow_fail (Text.of_string "abcdef") {
        success _ _ => false,
        fail e => I64.beq (ParseError.error_offset e) 3
    }

#[partial]
def test_fold_fail_a (input : Text) : ParseResult Text String :=
    fail (ParseError.tag "a" input)

#[partial]
def test_fold_fail_b (input : Text) : ParseResult Text String :=
    fail (ParseError.custom "deepest" (Input.input_advance 4 input))

#[partial]
def test_fold_fail_c (input : Text) : ParseResult Text String :=
    fail (ParseError.tag "c" input)

/// Same idea as `test_alt_prefers_deeper_failure` but across an
/// `alt_fold` list of more than two alternatives, with the deepest
/// failure in the middle — confirms the running best-so-far survives
/// the whole fold, not just a pairwise comparison.
#[test]
def test_alt_fold_prefers_deepest_failure : Bool :=
    match alt_fold [test_fold_fail_a, test_fold_fail_b, test_fold_fail_c] (Text.of_string "abcdefgh") {
        success _ _ => false,
        fail e => I64.beq (ParseError.error_offset e) 4
    }

#[test]
def test_alt_fold_empty_list_still_fails : Bool :=
    match alt_fold ([] : List (Text -> ParseResult Text String)) (Text.of_string "abc") {
        success _ _ => false,
        fail _ => true
    }

// --- take_while_byte -------------------------------------------------
//
// The byte scanner's equivalence assertions: a wrong edit to a `*_byte`
// predicate would otherwise be caught only by whichever grammar test happened
// to exercise it. These run in the ordinary sweep.

#[partial]
def tw_byte_out (r : ParseResult Text String) : String :=
    match r {
        success _ out => out,
        fail _ => "<fail>"
    }

#[partial]
def tw_byte_rem (r : ParseResult Text String) : String :=
    match r {
        success rem _ => rest_text rem,
        fail _ => "<fail>"
    }

/// The remaining text under a cursor, for equality assertions.
#[partial]
def rest_text (rem : Text) : String :=
    Input.input_text (Text.remaining rem) rem

#[test]
def test_take_while_byte_consumes_run : Bool :=
    String.beq (tw_byte_out (take_while_byte is_space_byte (Text.of_string "   xy"))) "   "

#[test]
def test_take_while_byte_leaves_remainder : Bool :=
    String.beq (tw_byte_rem (take_while_byte is_space_byte (Text.of_string "   xy"))) "xy"

#[test]
def test_take_while_byte_empty_run : Bool :=
    String.beq (tw_byte_out (take_while_byte is_space_byte (Text.of_string "xy"))) ""

#[test]
def test_take_while_byte_empty_input : Bool :=
    String.beq (tw_byte_out (take_while_byte is_space_byte (Text.of_string ""))) ""

#[test]
def test_take_while_byte_whole_input : Bool :=
    String.beq (tw_byte_rem (take_while_byte is_ident_char_byte (Text.of_string "abc"))) ""

/// The correctness argument for scanning bytes rather than characters: a
/// UTF-8 lead byte (>= 0xC0) fails every ASCII predicate, so the scan
/// stops at the character boundary instead of splitting the character.
/// The em dash here is the exact shape `lang/json.mo`/`lang/toml.mo` hit
/// before their first declaration (see `utf8_char_width`'s own note).
#[test]
def test_take_while_byte_stops_at_utf8_boundary : Bool :=
    String.beq (tw_byte_out (take_while_byte is_ident_char_byte (Text.of_string "ab—cd"))) "ab"

#[test]
def test_take_while_byte_utf8_remainder_intact : Bool :=
    String.beq (tw_byte_rem (take_while_byte is_ident_char_byte (Text.of_string "ab—cd"))) "—cd"

/// Byte and string scanners must agree. This is the property
/// `bench/parser_take_while.mo` asserts at scale; asserted here too so it
/// is actually run.
#[test]
def test_take_while_byte_matches_string_scanner : Bool :=
    let src : String := "  \tfoo_bar1 baz" in
    String.beq (tw_byte_out (take_while_byte is_space_byte (Text.of_string src)))
        (tw_byte_out (take_while is_space (Text.of_string src)))

#[test]
def test_take_while_byte_matches_string_scanner_ident : Bool :=
    let src : String := "foo_bar1 baz" in
    String.beq (tw_byte_out (take_while_byte is_ident_char_byte (Text.of_string src)))
        (tw_byte_out (take_while is_ident_char (Text.of_string src)))

/// The offset a token ENDS at, and the offset the scanner starts from: the
/// two numbers that replaced a `strlen` subtraction.
#[test]
def test_take_while_offsets : Bool :=
    let input : Text := Input.input_advance 4 (Text.of_string "1234abc") in
    match take_while_byte is_ident_char_byte input {
        success rem out =>
            String.beq out "abc" && I64.beq (ParseError.error_offset (ParseError.custom "x" rem)) 7,
        fail _ => false
    }
