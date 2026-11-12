// Phase 3's highlighter gate: the table-driven lexer's classes, and the
// span bridge the view paints from.
//
// EVERY EXPECTATION IS A TOKEN LIST COUNTED BY HAND over fixtures whose
// bytes are written beside them (the toolkit suite's discipline). The
// lexer's whole contract is "fewest runs that preserve the classes", so
// the pins are the token COUNT and each token's class+text -- a lexer
// that split runs would answer a longer list and these name it.
//
// THE PALETTE IS PINNED TOO (`Highlight.style`): the view composes on top
// of these styles (a selection bg merges into them), so a style that
// drifted would surface in the view as a wrong-colored cell -- pinned
// here instead, where the class under test is the only variable.
//
// No record patterns or bare nested struct literals inside `#[test]`
// defs: `hl_*` accessor defs hold the reads, per the recorded two-host
// inference hazard (`AGENTS.md`'s "bind to an annotated local first").

use lib::highlight {LanguageConfig, Token, TokenKind}
use lib::highlight {Highlight.lex, Highlight.style, Highlight.segments,
    Highlight.config_for, Token.text_of, Token.kind_of}
use tui::types {TextStyle, TextSegment}
use tui::core {style_default}
use std::ansi {Color}
// `List.length` lives in `init/src/list.mo` (ambient and pure) as of the
// upstream move, so this import pulls the module's INSTANCES into scope
// and names nothing -- the empty brace list is the documented form.
use std::io {IO.current_time}
use std::list {}
use init::shared {Shared}

// --- Accessors: one read per binding, each used once ---

/// The token's class, as a word so a failing assertion names the case.
def hl_kind (t : Token) : String :=
    match Token.kind_of t {
        TokenKind.plain => "plain",
        TokenKind.keyword => "keyword",
        TokenKind.comment => "comment",
        TokenKind.string_lit => "string",
        TokenKind.number => "number"
    }

/// The token's text.
def hl_text (t : Token) : String := Token.text_of t

/// The whole token list as `"kind:text"` rows joined by `" | "`, so one
/// assertion failure reports the ENTIRE lex rather than one unequal pair.
#[partial]
def hl_show (toks : List Token) : String :=
    match toks {
        List.empty => "",
        List.cons one rest =>
            hl_kind one ++ ":" ++ hl_text one
                ++ (if List.is_empty rest then "" else " | " ++ hl_show rest)
    }

/// The lex of `line` under the Monad table, as the display string.
def hl_lex (line : String) : String := hl_show (Highlight.lex LanguageConfig.monad line)

/// The lex of `line` under the no-highlight table.
def hl_lex_text (line : String) : String := hl_show (Highlight.lex LanguageConfig.text line)

/// The first token of a list, or `<none>`.
def hl_first (toks : List Token) : Token :=
    match toks {
        List.cons one _ => one,
        List.empty => hl_no_token
    }

/// A stand-in token for the empty-list case, so an assertion that reads
/// the first token of an empty lex still compares a String.
def hl_no_token : Token := Token.mk "" TokenKind.plain

// ── Words: keyword vs. plain ──────────────────────────────────────────────

/// A whole word from the table is a keyword. Fixture "let": one token,
/// class keyword.
#[test]
def test_keyword_whole_word : Bool :=
    String.beq (hl_lex "let") "keyword:let"

/// An identifier is plain. Fixture "foo": one token, class plain.
#[test]
def test_identifier_is_plain : Bool :=
    String.beq (hl_lex "foo") "plain:foo"

/// THE WHOLE-WORD RULE: a word CONTAINING a keyword is not one. Fixture
/// "letter": one plain token -- a substring matcher would answer
/// keyword here, and the editor would color an ordinary word.
#[test]
def test_keyword_needs_a_whole_word : Bool :=
    String.beq (hl_lex "letter") "plain:letter"

/// `pub` and `priv` are keywords in the table even though the parser's
/// own membership test leaves them out (that file's workaround is a
/// parser fact, not a language fact; highlight.mo's table records why).
#[test]
def test_pub_and_priv_are_keywords : Bool :=
    String.beq (hl_lex "pub") "keyword:pub"
        && String.beq (hl_lex "priv") "keyword:priv"

/// Adjacent runs of different classes stay separate: the fixture
/// "letx" is ONE plain word (no keyword inside it), while "let x" is
/// three tokens (keyword, plain space, plain word).
#[test]
def test_word_then_space_then_word : Bool :=
    String.beq (hl_lex "let x") "keyword:let | plain:  | plain:x"

/// Case sensitivity is a fact about the language, and Monad's table
/// says case-sensitive: "Let" is an ordinary identifier.
#[test]
def test_monad_keywords_are_case_sensitive : Bool :=
    String.beq (hl_lex "Let") "plain:Let"

// ── Comments ──────────────────────────────────────────────────────────────

/// A comment runs to the end of the line, one token. Fixture: "x // hi"
/// is plain "x", plain " ", then one comment token " // hi" (the
/// comment STARTS at the slash, so the space before it is its own
/// plain run).
#[test]
def test_comment_runs_to_eol : Bool :=
    String.beq (hl_lex "x // hi") "plain:x | plain:  | comment:// hi"

/// A line that is ONLY a comment is one token.
#[test]
def test_whole_line_comment : Bool :=
    String.beq (hl_lex "// hi") "comment:// hi"

/// The comment prefix outranks everything inside it -- a quote in a
/// comment is comment text, not a string start.
#[test]
def test_comment_outranks_a_quote : Bool :=
    String.beq (hl_lex "// \"still comment\"") "comment:// \"still comment\""

/// An empty `line_comment` means no comments in the language: the
/// text table lexes "// hi" as punctuation and words, all plain.
#[test]
def test_text_config_has_no_comments : Bool :=
    String.beq (hl_lex_text "// hi") "plain:// | plain:  | plain:hi"

// ── Strings ───────────────────────────────────────────────────────────────

/// A string literal from quote to quote, one token, class string.
#[test]
def test_string_literal : Bool :=
    String.beq (hl_lex "\"hi\"") "string:\"hi\""

/// A backslash escape does not close the literal.
#[test]
def test_string_escape_keeps_it_open : Bool :=
    String.beq (hl_lex "\"a\\\"b\"") "string:\"a\\\"b\""

/// An unterminated literal runs to the end of the line as one string
/// token -- the line-scoped limitation's honest answer.
#[test]
def test_unterminated_string_runs_to_eol : Bool :=
    String.beq (hl_lex "\"oops") "string:\"oops"

/// A word after a closing quote is its own token.
#[test]
def test_string_then_word : Bool :=
    String.beq (hl_lex "\"a\" b") "string:\"a\" | plain:  | plain:b"

// ── Numbers ───────────────────────────────────────────────────────────────

/// A digit run is one number token; a `.` inside the run stays in it.
#[test]
def test_number : Bool :=
    String.beq (hl_lex "42") "number:42"
        && String.beq (hl_lex "3.14") "number:3.14"

/// A digit INSIDE a word does not start a number: the word scanner took
/// the run first. Fixture "x2" is one plain token.
#[test]
def test_digit_inside_a_word_is_plain : Bool :=
    String.beq (hl_lex "x2") "plain:x2"

/// THE `x-1` PIN (highlight.mo's own stated rule): a minus is an
/// operator, not a number start, so "x-1" is plain "x", plain "-",
/// number "1" -- not one number "x-1" and not a plain "x-1".
#[test]
def test_minus_is_not_a_number_start : Bool :=
    String.beq (hl_lex "x-1") "plain:x | plain:- | number:1"

// ── Adjacency and merging ─────────────────────────────────────────────────

/// Adjacent same-class bytes share one token: "ab cd" is three tokens
/// (word, space, word), and "ab// hi" is two (the word, then the
/// comment that starts right after it -- no space run between).
#[test]
def test_adjacent_word_then_comment : Bool :=
    String.beq (hl_lex "ab// hi") "plain:ab | comment:// hi"

/// Punctuation is one plain run through the last consecutive such
/// byte: "(x : I64)" lexes as plain "(", plain "x", plain " ", plain
/// ":", plain " ", plain "I64", plain ")" -- the parens and colons are
/// all plain, and the runs break only at word/string/number/comment
/// starts.
#[test]
def test_punctuation_runs : Bool :=
    String.beq (hl_lex "(x : I64)")
        "plain:( | plain:x | plain:  | plain:: | plain:  | plain:I64 | plain:)"

/// The empty line answers no tokens -- the view paints the row's
/// background itself.
#[test]
def test_empty_line : Bool :=
    I64.beq (List.length (Highlight.lex LanguageConfig.monad "")) 0

// ── Multi-byte text never splits ──────────────────────────────────────────

/// A multi-byte word is one plain token: every byte above 0x7f is a
/// word byte to the scanner, so "café" is one token and never two.
#[test]
def test_multibyte_word_is_one_token : Bool :=
    String.beq (hl_lex "café") "plain:café"

/// Prose with an astral character: one plain token, the emoji riding
/// the word run.
#[test]
def test_astral_char_stays_whole : Bool :=
    String.beq (hl_lex "a🧵b") "plain:a🧵b"

// ── The table lookup ──────────────────────────────────────────────────────

/// The known language resolves to its own table.
#[test]
def test_config_for_monad : Bool :=
    String.beq (LanguageConfig.name (Highlight.config_for "monad")) "monad"

/// An unknown language falls back to the text table -- an editor must
/// open any file, not just the ones it can color.
#[test]
def test_config_for_unknown_falls_back : Bool :=
    String.beq (LanguageConfig.name (Highlight.config_for "rust")) "text"

/// The name field, read once through a helper (the accessor rule).
def LanguageConfig.name (cfg : LanguageConfig) : String :=
    match cfg { { name, .. } => name }

// ── The palette ────────────────────────────────────────────────────────────

/// A keyword is bold blue; plain is the default style.
#[test]
def test_style_keyword_bold_blue : Bool :=
    hl_fg_is (Highlight.style TokenKind.keyword) Color.blue
        && hl_bold_is (Highlight.style TokenKind.keyword) true

#[test]
def test_style_plain_is_default : Bool :=
    Highlight.style TokenKind.plain == style_default

/// A comment is dim grey (bright_black).
#[test]
def test_style_comment_dim_grey : Bool :=
    hl_fg_is (Highlight.style TokenKind.comment) Color.bright_black

/// A string is green.
#[test]
def test_style_string_green : Bool :=
    hl_fg_is (Highlight.style TokenKind.string_lit) Color.green

/// A number is magenta.
#[test]
def test_style_number_magenta : Bool :=
    hl_fg_is (Highlight.style TokenKind.number) Color.magenta

/// The style's foreground, as a helper so the `Option.some` pattern
/// bind is used once.
def hl_fg_is (st : TextStyle) (want : Color) : Bool :=
    match st.fg {
        Option.some c => c == want,
        Option.none => false
    }

/// The style's bold flag, read through the field once.
def hl_bold_is (st : TextStyle) (want : Bool) : Bool := st.bold == want

// ── The span bridge ────────────────────────────────────────────────────────

/// The bridge: one segment per token, styled by the palette, in order.
/// Fixture "let x" (keyword, space, word) is three segments whose texts
/// concatenate back to the line.
#[test]
def test_segments_one_per_token : Bool :=
    let segs : List TextSegment := Highlight.segments (Highlight.lex LanguageConfig.monad "let x") in
    let shared : Shared (List TextSegment) := Shared.of segs in
    I64.beq (List.length (Shared.get shared)) 3
        && String.beq (hl_seg_texts_join (Shared.get shared)) "let x"

/// A keyword segment carries the keyword style; a plain one the
/// default. THE COMPOSITION BASE: the view merges selection styles INTO
/// these, so the class under test is the only thing that may vary here.
#[test]
def test_segments_carry_their_classes : Bool :=
    let segs : List TextSegment := Highlight.segments (Highlight.lex LanguageConfig.monad "let x") in
    match segs {
        List.cons first rest => hl_first_seg_is_keyword first && hl_rest_is_plain rest,
        List.empty => false
    }

/// The first segment's style is the keyword palette entry.
def hl_first_seg_is_keyword (first : TextSegment) : Bool :=
    first.style == Highlight.style TokenKind.keyword

/// The remaining segments (space, word) are default-styled.
#[partial]
def hl_rest_is_plain (rest : List TextSegment) : Bool :=
    match rest {
        List.empty => true,
        List.cons one more => one.style == style_default && hl_rest_is_plain more
    }

/// The empty token list answers the empty segment list.
#[test]
def test_segments_empty : Bool :=
    I64.beq (List.length (Highlight.segments List.empty)) 0

/// The segments' texts, concatenated -- the round-trip witness that the
/// bridge loses no bytes.
#[partial]
def hl_seg_texts_join (segs : List TextSegment) : String :=
    match segs {
        List.empty => "",
        List.cons one rest => one.text ++ hl_seg_texts_join rest
    }

// ── The lexer is linear in the line's length ─────────────────────────────

/// LEXING IS LINEAR, not quadratic. Each run used to accumulate its text by
/// `acc ++ String.from_list [b]` once per byte; `++` is a fresh
/// strlen+malloc+memcpy, so one long run cost O(len^2). Measured on the
/// built binary, a single 60 KB line (no newlines, so one enormous plain
/// run) took 3025 ms to open -- while 20 000 short lines totalling the same
/// bytes took 31 ms.
///
/// A RATIO, not a wall-clock bound: two lines 8x apart cost ~8x when linear
/// and ~64x when quadratic, so 32 separates them with noise either way.
#[test]
def test_lex_is_linear_in_the_line_length : IO Bool := do {
    let small : String := hl_ascii 8000;
    let large : String := hl_ascii 64000;
    let cfg : LanguageConfig := LanguageConfig.monad;
    let warmed : List Token := Highlight.lex cfg (hl_ascii 500);
    let t1 <- IO.current_time;
    let toks : List Token := Highlight.lex cfg small;
    let t2 <- IO.current_time;
    let big : List Token := Highlight.lex cfg large;
    let t3 <- IO.current_time;
    let ok : Bool :=
        Bool.and (hl_covers small toks) (hl_covers large big);
    let linear : Bool := hl_linear_enough (hl_elapsed t1 t2) (hl_elapsed t2 t3);
    let warm_ok : Bool := Bool.not (List.is_empty warmed);
    return (Bool.and (Bool.and ok linear) warm_ok)
}

/// The elapsed milliseconds between two readings, floored at 1 so the ratio
/// stays meaningful for a sub-millisecond measurement.
///
/// A separate def, not an inline `let ... := if ... in` inside the do-block:
/// that shape is a recorded self-hosted load failure when the same block has
/// `let ... <-` binds.
def hl_elapsed (a : I64) (b : I64) : I64 :=
    let d : I64 := b - a in
    if d < 1 then 1 else d

/// Is `big` under 32x `small`? (~8x when linear, ~64x when quadratic.)
def hl_linear_enough (small_ms : I64) (big_ms : I64) : Bool :=
    big_ms < small_ms * 32

/// Do the tokens tile the line exactly? The round-trip witness: no byte
/// lost, no byte duplicated by the accumulator.
#[partial]
def hl_covers (line : String) (toks : List Token) : Bool :=
    String.beq (hl_join toks) line

#[partial]
def hl_join (toks : List Token) : String :=
    match toks {
        List.empty => "",
        List.cons one rest => String.concat one.text (hl_join rest)
    }

/// `n` bytes of newline-free lowercase ASCII: one word run and one space
/// run, the two shapes that accumulate byte by byte.
#[terminating]
def hl_ascii (n : I64) : String :=
    if Bool.not (0 < n) then "" else String.concat "a" (hl_ascii (n - 1))
