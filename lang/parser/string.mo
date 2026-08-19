/// String literal parser for the self-hosted parser
/// Extracted from parser.mo as part of Phase C

use lang.types {Term, lit, str}
use lang.parser.core {ParseResult, custom, fail, is_empty, success, tag}
use lang.parser.combinators {tag, utf8_char_width}

open ParseResult {fail, success}

/// Resolve a single escape character (the character right after `\`) to
/// its real value. Mirrors the Rust reference's `parse_escaped_char`
/// (core/src/parser/string.rs) minus `\u{XXXX}` unicode escapes — those
/// need a hex-digits-to-codepoint native bridge that doesn't exist for
/// self-hosted code (no such native is exposed anywhere in the
/// standard library); deferred, and zero known corpus impact since no
/// `\u{}` escape appears anywhere in the current corpus.
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
	let consumed : I64 := I64.sub (String.length run_start) (String.length input) in
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

#[partial]
def string_body_escape_char (run_start : String) (before_backslash : String) (ch : String) (rest : String) (acc : String) : ParseResult String :=
	match escape_replacement ch {
		Option.some replacement =>
			let acc2 : String := String.concat (String.concat acc (string_body_run_text run_start before_backslash)) replacement in
			string_body_loop rest rest acc2,
		Option.none => fail (ParseError.custom "unknown escape sequence" rest)
	}

/// Parse a string literal and return it as a Term.
#[partial]
def string_parse (input: String) : ParseResult Term :=
	match tag "\"" input {
		success rem _ =>
			match string_body rem {
				success rem2 content => success rem2 (Term.lit (Literal.str content)),
				fail e => fail e
			},
		fail e => fail e
	}
