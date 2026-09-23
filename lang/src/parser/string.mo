/// String literal parser for the self-hosted parser
/// Extracted from parser.mo as part of Phase C

use lib::types {ParseLiteral, ParseTerm, Term, lit, pt_lit, str}
use lib::parser::core {ParseResult, custom, fail, is_empty, success, tag}
use lib::parser::combinators {tag, take_while, utf8_char_width}
use lib::parser::char_preds {is_hex_digit, is_space}
use lib::parser::number {char_to_hex_digit}

open ParseResult {fail, success}

/// Resolve a single escape character (the character right after `\`) to
/// its real value: the fixed-value half of the Rust reference's
/// `parse_escaped_char` (core/src/parser/string.rs).
///
/// The two escapes that are NOT a fixed character map live one level up,
/// in the callers, because they need the rest of the input rather than
/// just `c`: `\u{XXXX}` (`unicode_escape`, below) and `\`-whitespace
/// (`skip_escaped_whitespace`). Both are implemented here and both are
/// dispatched before this function is consulted -- `u` and a whitespace
/// character are absent from the table below, so a missed dispatch would
/// surface as `unknown escape sequence` rather than as a silent wrong
/// answer.
///
/// This function used to carry the file's record of `\u{XXXX}` as an
/// accepted gap, on the grounds that decoding hex digits into a code
/// point needed "a native bridge that doesn't exist for self-hosted
/// code". No bridge is needed and none is used: see `unicode_escape`.
/// The cost of the gap was real while it lasted -- the Rust reference
/// accepts the escape, so a `.mo` file using one checked clean under
/// `monad-rs check` and `monad-rs test` (both the host) while the
/// self-hosted parse rejected the WHOLE module, whose first symptom was a
/// self-compile dying with `call to undefined symbol(s)` naming that
/// module's defs. Cost one bootstrap cycle to find, 2026-09-13, on a
/// single `"\u{00e9}"` in a test fixture in `lang/parser/position.mo`.
/// Same shape as AGENTS.md item 40.
#[partial]
def escape_replacement (c : String) : Option String :=
	if String.beq "n" c then Option.some "\n"
	else if String.beq "r" c then Option.some "\r"
	else if String.beq "t" c then Option.some "\t"
	else if String.beq "b" c then Option.some "\b"
	else if String.beq "f" c then Option.some "\f"
	else if String.beq "\\" c then Option.some "\\"
	else if String.beq "/" c then Option.some "/"
	else if String.beq "\"" c then Option.some "\""
	else if String.beq "'" c then Option.some "'"
	else Option.none

/// `\` followed by one or more whitespace characters, which contributes
/// NOTHING to the literal's content -- the Rust reference's
/// `parse_escaped_whitespace` (core/src/parser/string.rs), Rust's line
/// continuation, so that
///
///     "a\
///      b"
///
/// is `"ab"`. The whitespace set is `nom`'s `multispace1`: exactly
/// `is_space`'s space/tab/CR/LF (`lang/parser/char_preds.mo`), so the two
/// implementations agree on which characters continue a line.
///
/// Only the STRING path has this branch. `parse_char_literal` is
/// `alt((parse_escaped_char, anychar))` with no whitespace alternative, so
/// `'\<newline>'` is a parse error in both compilers and
/// `char_literal_escape` deliberately does not grow one.
///
/// `input` is what follows the whitespace character already consumed, so
/// this consumes the REST of the run and returns what is left after it --
/// which is both the literal's remainder and the next run's start.
#[partial]
def skip_escaped_whitespace (input : String) : String :=
	if is_empty input
	then input
	else
		let width : I64 := utf8_char_width input in
		if is_space (String.slice input 0 width)
		then skip_escaped_whitespace (String.drop width input)
		else input

/// `\u{XXXX}` -- the Rust reference's `parse_unicode`, which
/// `parse_escaped_char` tries FIRST, before its fixed-value alternatives.
/// `input` is what follows the `u`: a `{`, then 1 to 6 ASCII hexadecimal
/// digits, then `}`. The digits are decoded to a code point, validated
/// exactly as `std::char::from_u32` validates it, and re-encoded as UTF-8.
///
/// No native bridge is involved, which is what the file's old record of
/// this gap assumed was necessary: `String.to_list`/`String.from_list`
/// carry raw bytes, so the encoding is arithmetic. It is done in `U32`
/// rather than `I64` for one measured reason -- `I64` has NO bitwise
/// operations at all (it is add/sub/mul/div/lt/gt/beq/neg/to_u32/to_u64/
/// to_string, and that is the whole surface), while `U32` has
/// and/or/xor/shl/shr/not. `I64.to_u32` supplies a decoded digit as a
/// `U32`.
///
/// Returns the decoded character's UTF-8 bytes as a `String`, which is
/// what both callers already want: `string_body_escape_char` appends a
/// replacement into the literal's content, and `char_literal_escape`
/// hands one to `Char.of_bytes`.
def unicode_escape (input : String) : ParseResult String :=
	match tag "{" input {
		success after_brace _ => unicode_escape_digits after_brace 0 0u32,
		fail _ => fail (ParseError.custom "expected `{` in a `\\u{...}` escape" input)
	}

/// Consume up to 6 hex digits. `acc` accumulates the code point; a
/// 7th digit must NOT be consumed -- `take_while_m_n(1, 6, ...)` stops at
/// six and the following `char('}')` then fails on the digit, which is why
/// the length test is here at the head rather than at the terminator.
#[partial]
def unicode_escape_digits (input : String) (count : I64) (acc : U32) : ParseResult String :=
	if Bool.and (I64.lt count 6) (unicode_escape_hex_at input)
	then
		let width : I64 := utf8_char_width input in
		let digit : U32 := I64.to_u32 (char_to_hex_digit (String.slice input 0 width)) in
		unicode_escape_digits (String.drop width input) (I64.add count 1)
			(U32.add (U32.mul acc 16u32) digit)
	else unicode_escape_close input count acc

/// Is the character `input` starts with an ASCII hex digit? The
/// `is_hex_digit` guard matters: `char_to_hex_digit`
/// (`lang/parser/number.mo`) is total, answering 15 for anything it does
/// not recognise, so it is only ever called behind this predicate.
#[partial]
def unicode_escape_hex_at (input : String) : Bool :=
	if is_empty input
	then false
	else
		let width : I64 := utf8_char_width input in
		is_hex_digit (String.slice input 0 width)

/// The digits are done: require `}` and at least one digit, then encode.
/// The `count == 0` test is `take_while_m_n`'s lower bound -- `\u{}` must
/// not decode as code point 0 (which would be a legal, silent, wrong
/// answer), it must fail.
#[partial]
def unicode_escape_close (input : String) (count : I64) (acc : U32) : ParseResult String :=
	if I64.beq count 0
	then fail (ParseError.custom "`\\u{...}` needs 1 to 6 hexadecimal digits" input)
	else
		match tag "}" input {
			success rest _ =>
				match unicode_escape_utf8 acc {
					Option.some decoded => success rest decoded,
					Option.none =>
						fail (ParseError.custom "`\\u{...}` is not a Unicode scalar value" input)
				},
			fail _ => fail (ParseError.custom "expected `}` ending a `\\u{...}` escape" input)
		}

/// Encode a code point as UTF-8, or `Option.none` when it is not a
/// Unicode scalar value: beyond U+10FFFF, or one of the surrogates
/// U+D800..=U+DFFF. That is `std::char::from_u32`'s acceptance set
/// exactly, so the two parsers accept and reject the same escapes.
#[partial]
def unicode_escape_utf8 (cp : U32) : Option String :=
	if U32.gt cp 0x10FFFFu32 then Option.none
	else if Bool.and (U32.gt cp 0xD7FFu32) (U32.lt cp 0xE000u32) then Option.none
	else if U32.lt cp 0x80u32
	then Option.some (String.from_list [U32.to_u8 cp])
	else if U32.lt cp 0x800u32
	then Option.some (String.from_list [
		utf8_lead (U32.shr cp 6u32) 0xC0u32,
		utf8_cont cp,
	])
	else if U32.lt cp 0x10000u32
	then Option.some (String.from_list [
		utf8_lead (U32.shr cp 12u32) 0xE0u32,
		utf8_cont (U32.shr cp 6u32),
		utf8_cont cp,
	])
	else Option.some (String.from_list [
		utf8_lead (U32.shr cp 18u32) 0xF0u32,
		utf8_cont (U32.shr cp 12u32),
		utf8_cont (U32.shr cp 6u32),
		utf8_cont cp,
	])

/// A UTF-8 leading byte: the payload bits, OR'd with the byte's `10..`/
/// `110..`/`1110..`/`11110..` prefix. `U32.to_u8` truncates to the low 8
/// bits, which is what makes the prefix the top bits of the result.
#[partial]
def utf8_lead (value : U32) (prefix : U32) : U8 :=
	U32.to_u8 (U32.or value prefix)

/// A UTF-8 continuation byte: `10xxxxxx` over the low 6 bits of `value`.
#[partial]
def utf8_cont (value : U32) : U8 :=
	U32.to_u8 (U32.or (U32.and value 0x3Fu32) 0x80u32)

/// Parse the body of a string literal (everything between the quotes,
/// the opening `"` already consumed by `string_parse`), handling
/// `\`-escapes one character at a time — the previous version
/// (`take_while is_not_quote`) stopped at the *first* raw `"`
/// regardless of whether it was escaped, so any string containing `\"`
/// truncated early instead of failing outright (the worst kind of bug:
/// invisible to a success/fail-only test). Escapes are resolved to
/// their real characters here (not left as literal backslash-letter
/// pairs), matching the Rust reference's `Literal::Str` content.
#[partial]
def string_body (input : String) : ParseResult String :=
	string_body_loop input input ""

/// Steps by `utf8_char_width` rather than a hardcoded 1 byte — a plain
/// (non-escaped) multi-byte UTF-8 character in a string literal's
/// content (an em dash, an accented letter, ...) would otherwise land
/// `String.slice`/`String.drop` mid-character and silently truncate the
/// rest of the string (see `utf8_char_width`'s own doc comment,
/// lang/parser/combinators.mo).
///
/// `run_start` tracks where the current *unescaped* run of characters
/// began (the same "original vs. shrinking remainder" trick
/// `take_while`, lang/parser/combinators.mo, uses) — the per-character
/// branch in `string_body_char` just advances `input` and recurses, it
/// does NOT touch `acc`. `acc` only grows at a run boundary (a `\` or
/// the closing `"`), via a single `String.slice` covering the whole
/// run instead of one `String.concat` per character. Escapes still
/// change content byte-for-byte, so they can't be folded into a slice
/// — but they're the exception, not the rule, so this turns the
/// dominant per-character cost from O(L^2) (one growing-copy concat
/// per char) into O(L) + O(escape count).
#[partial]
def string_body_loop (run_start : String) (input : String) (acc : String) : ParseResult String :=
	if is_empty input
	then fail (ParseError.custom "unterminated string literal" input)
	else
		let width : I64 := utf8_char_width input in
		string_body_char run_start input (String.slice input 0 width) (String.drop width input) acc

#[partial]
def string_body_char (run_start : String) (input : String) (ch : String) (rest : String) (acc : String) : ParseResult String :=
	if String.beq "\"" ch
	then success rest (String.concat acc (string_body_run_text run_start input))
	else if String.beq "\\" ch
	then string_body_escape run_start input rest acc
	else string_body_loop run_start rest acc

/// The unescaped run from `run_start` up to (not including) `input`.
def string_body_run_text (run_start : String) (input : String) : String :=
	let consumed : I64 := String.length run_start - String.length input in
	String.slice run_start 0 consumed

/// A `\` was just consumed — the next character selects the escape.
/// Correctly distinguishes `\\"` (escaped backslash, string continues,
/// then a REAL closing quote) from `\"` (escaped quote, string
/// continues past it) purely by always consuming exactly one character
/// here as "the thing being escaped" before returning to the normal
/// loop, rather than scanning for the next raw `"` first.
///
/// `before_backslash` is the loop's `input` from just before the `\`
/// was consumed — needed to close out the run ending at the `\` (see
/// `string_body_run_text`) once the escape resolves.
#[partial]
def string_body_escape (run_start : String) (before_backslash : String) (input : String) (acc : String) : ParseResult String :=
	if is_empty input
	then fail (ParseError.custom "unterminated escape sequence" input)
	else
		let width : I64 := utf8_char_width input in
		string_body_escape_char run_start before_backslash (String.slice input 0 width) (String.drop width input) acc

/// The two escapes that are not a fixed character map are dispatched here,
/// before `escape_replacement` is consulted: a whitespace character (line
/// continuation) and `u` (`\u{XXXX}`). Both need the REST of the input,
/// which is why they cannot live in that function.
#[partial]
def string_body_escape_char (run_start : String) (before_backslash : String) (ch : String) (rest : String) (acc : String) : ParseResult String :=
	if is_space ch
	then string_body_escape_append run_start before_backslash (skip_escaped_whitespace rest) "" acc
	else if String.beq "u" ch
	then
		match unicode_escape rest {
			success after decoded => string_body_escape_append run_start before_backslash after decoded acc,
			fail e => fail e
		}
	else
		match escape_replacement ch {
			Option.some replacement => string_body_escape_append run_start before_backslash rest replacement acc,
			Option.none => fail (ParseError.custom "unknown escape sequence" rest)
		}

/// Close out the run that ended at the `\`, append the escape's decoded
/// text (empty for a line continuation, which contributes nothing), and
/// resume the ordinary loop from `rest` -- which is also the next run's
/// start, since the text after an escape begins a fresh run.
#[partial]
def string_body_escape_append (run_start : String) (before_backslash : String) (rest : String) (decoded : String) (acc : String) : ParseResult String :=
	let acc2 : String := String.concat (String.concat acc (string_body_run_text run_start before_backslash)) decoded in
	string_body_loop rest rest acc2

/// Parse a string literal and return it as a Term.
#[partial]
def string_parse (input: String) : ParseResult ParseTerm :=
	match tag "\"" input {
		success rem _ =>
			match string_body rem {
				success rem2 content => success rem2 (pt_lit  (ParseLiteral.str content)),
				fail e => fail e
			},
		fail e => fail e
	}

/// Parse a Rust-style raw string literal `r"..."`, `r#"..."#`, `r##"..."##`, ...
///
/// The opener is `r`, then `n` (>= 0) `#` characters, then `"`. The body is
/// taken verbatim (no `\`-escape processing at all). The closer is the first
/// `"` in the body followed by at least `n` `#` characters: exactly `n` of
/// them are consumed as the closing delimiter and any extra `#` beyond `n`
/// are left in the remaining input (matching `rustc`'s lexer, which caps the
/// closing hash count at the opening count). A `"` followed by fewer than `n`
/// `#` is not a closer and the body continues past it.
///
/// Produces the same `Term.lit (Literal.str ...)` node an ordinary string
/// literal does, so the type checker / evaluator need no changes. Fails fast
/// (so a bare identifier `r`, `regex`, or `r#` not followed by `"` falls
/// through to the identifier parser) when the input does not begin with
/// `r"` or `r#"`.
#[partial]
def raw_string_parse (input : String) : ParseResult ParseTerm :=
	match tag "r" input {
		success after_r _ => raw_string_after_r after_r,
		fail e => fail e
	}

/// Count the leading `#` characters (the opening hash count `n`) via
/// `take_while`, then expect the opening `"`. If the remainder after the
/// hashes does not start with `"`, this is not a raw-string opener (e.g.
/// `r#x`) and we fail so the identifier parser handles the leading `r`.
#[partial]
def raw_string_after_r (input : String) : ParseResult ParseTerm :=
	match take_while (fn c => String.beq c "#") input {
		success after_hashes hashes =>
			match tag "\"" after_hashes {
				success body_start _ =>
					raw_string_body (String.length hashes) body_start body_start,
				fail e => fail e
			},
		fail e => fail e
	}

/// Scan the raw-string body (verbatim) for the closer. `orig` is the body
/// starting right after the opening `"` (kept so the final body is one
/// `String.slice` of it, avoiding any per-character accumulation — the body
/// is verbatim, so no escape resolution is needed); `input` is the shrinking
/// remainder being scanned. Steps by `utf8_char_width` so a multi-byte
/// character in the body advances correctly instead of landing mid-codepoint.
#[partial]
def raw_string_body (n : I64) (orig : String) (input : String) : ParseResult ParseTerm :=
	if is_empty input
	then fail (ParseError.custom "unterminated raw string literal" input)
	else
		let width : I64 := utf8_char_width input in
		let ch : String := String.slice input 0 width in
		if String.beq ch "\""
		then raw_string_count_hashes n 0 orig input (String.drop width input)
		else raw_string_body n orig (String.drop width input)

/// A `"` was just found at `at_quote` (a suffix of `orig`). Count the trailing
/// `#` characters, capping at `n`: as soon as `cnt` reaches `n` this is the
/// closer (the body is `orig` up to `at_quote`, the remainder is `input` after
/// the `n` consumed `#`, with any extra `#` beyond `n` left in `input`). If a
/// non-`#` (or EOF) is hit before `cnt == n`, this `"` was not a closer —
/// resume the body scan from `input` (the `"` and any `#` already counted
/// stay in the body via `orig`'s final slice).
///
/// For `n = 0`, `cnt` starts at `0 == n` so the very first call returns the
/// closer immediately — any `"` closes a zero-hash raw string.
#[partial]
def raw_string_count_hashes (n : I64) (cnt : I64) (orig : String) (at_quote : String) (input : String) : ParseResult ParseTerm :=
	if I64.beq cnt n
	then
		let consumed : I64 := String.length orig - String.length at_quote in
		success input (pt_lit  (ParseLiteral.str (String.slice orig 0 consumed)))
	else
		if is_empty input
		then fail (ParseError.custom "unterminated raw string literal" input)
		else
			let ch : String := String.slice input 0 1 in
			if String.beq ch "#"
			then raw_string_count_hashes n (I64.add cnt 1) orig at_quote (String.drop 1 input)
			else raw_string_body n orig input

/// Parse a char literal: `'x'` or `'\n'` (single character, with escape
/// support). Produces `ParseLiteral.char`, the parse-level sibling of
/// `Literal.char`.  `Char` is a stub type (AGENTS.md item 29) — this
/// gives it a literal form for parsing/parity, not runtime operations.
#[partial]
def char_literal (input : String) : ParseResult ParseTerm :=
	match tag "'" input {
		success rem _ =>
			if is_empty rem
			then fail (ParseError.custom "unterminated char literal" rem)
			else
				let width : I64 := utf8_char_width rem in
				let ch : String := String.slice rem 0 width in
				char_literal_after_char ch (String.drop width rem),
		fail e => fail e
	}

#[partial]
def char_literal_after_char (ch : String) (input : String) : ParseResult ParseTerm :=
	if String.beq ch "\\"
	then char_literal_escape input
	else char_literal_close (tag "'" input) ch

/// `\u{XXXX}` is dispatched here for the same reason it is in
/// `string_body_escape_char` (`parse_char_literal`'s `alt` reaches
/// `parse_escaped_char`, which tries `parse_unicode` first). A whitespace
/// character after the `\` is NOT dispatched: the Rust reference's char
/// literal has no escaped-whitespace branch, so both compilers reject
/// `'\<newline>'` and agreeing on that is the point.
#[partial]
def char_literal_escape (input : String) : ParseResult ParseTerm :=
	if is_empty input
	then fail (ParseError.custom "unterminated escape in char literal" input)
	else
		let width : I64 := utf8_char_width input in
		let esc : String := String.slice input 0 width in
		let rest : String := String.drop width input in
		if String.beq "u" esc
		then
			match unicode_escape rest {
				success after decoded => char_literal_close (tag "'" after) decoded,
				fail e => fail e
			}
		else
			match escape_replacement esc {
				Option.some replacement => char_literal_close (tag "'" rest) replacement,
				Option.none => fail (ParseError.custom "unknown escape sequence" input)
			}

/// `value` is the ONE codepoint `char_literal`/`char_literal_escape`
/// sliced out (by `utf8_char_width`, or an escape's replacement); its
/// UTF-8 bytes become the `Char` -- `Char`'s own declared shape
/// (`init/prelude.mo`, `of_bytes (List U8)`). No native beyond the
/// already-wired `string_to_list` is needed, and `IrLit.ir_char`
/// (`lang/core_ir.mo`) takes the result as-is.
#[partial]
def char_literal_close (r : ParseResult String) (value : String) : ParseResult ParseTerm :=
	match r {
		success rem _ => success rem (pt_lit  (ParseLiteral.char (Char.of_bytes (String.to_list value)))),
		fail e => fail e
	}
