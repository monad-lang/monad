// Ply's lexical highlighter (code-editor.md Phase 3, Decision 5).
//
// TREE-SITTER IS PHASE 9 AND GATED: `#[extern "c"]` binds at link time on
// the self-hosted compiler only, and no native loads a library at run
// time, so "load grammars as shared libraries on first use" is
// impossible. v1 highlighting is THIS: a small table-driven lexer per
// language -- keywords, line-comment prefix, string quotes and a number
// rule, all held as DATA in a `LanguageConfig`. Monad's own table comes
// first.
//
// THE LEXER IS LINE-SCOPED: a highlight query takes one line's text and
// answers the runs of styles that cover it. That is not just a
// simplification -- it is the shape the view wants (one `spans` leaf per
// visible row), and the only construct it cannot express is a string
// literal spanning lines, which Monad source does not use (every `"`
// literal in this corpus closes on its own line) and which the plan's
// Known Limitations already scope out.
//
// NO `#[derive]` HERE: this file holds function bodies, and a
// derive-bearing file must hold none (motes/tui/src/types.mo's rule).
//
// NO LOCAL IS NAMED `insert`/`select`/`prefix`/`tick`: whole-program
// constructor names that shadow same-named locals are the plan's named
// risk.

use init::shared {Shared}
use init::copy {Copy}
use tui::types {TextStyle, TextSegment}
use tui::core {style_default, mk_text_segment}
use std::ansi {Color}

// ── The table ─────────────────────────────────────────────────────────────

/// One language's lexical facts: the keywords, the line-comment prefix,
/// the string quote characters and the number rule, all data. A
/// `LanguageConfig` is what a future grammar loader would produce; today
/// the tables below are the only producers.
pub struct LanguageConfig {
    /// The config's name, the same string `Document.language` carries.
    name : String,
    /// Words highlighted as keywords when a whole word matches. Case
    /// sensitivity is a fact about the language, so it is a field too.
    keywords : List String,
    keywords_case_sensitive : Bool,
    /// The prefix that runs a comment to the end of the line, e.g.
    /// `"//"`. Empty for languages without line comments.
    line_comment : String,
    /// The quote characters that open and close a string literal on one
    /// line, e.g. `['"']`. Backslash escapes are skipped inside.
    string_quotes : List String,
    /// Whether a digit where a word could start begins a number token.
    /// Every language in the table today answers true; the field keeps
    /// the rule out of the lexer's code.
    numbers : Bool
}

/// The token classes the lexer can name, and the styles they map to.
/// The palette lives HERE and not in the view: the view composes
/// (selection backgrounds merge onto these), but "what color is a
/// keyword" is a fact about the theme, and one place names it.
pub type TokenKind {
    plain,
    keyword,
    comment,
    string_lit,
    number
}

/// The style for a token kind (the palette).
pub def Highlight.style (k : TokenKind) : TextStyle :=
    match k {
        TokenKind.plain => style_default,
        TokenKind.keyword => { style_default with fg := Option.some Color.blue, bold := true },
        TokenKind.comment => { style_default with fg := Option.some Color.bright_black },
        TokenKind.string_lit => { style_default with fg := Option.some Color.green },
        TokenKind.number => { style_default with fg := Option.some Color.magenta }
    }

/// Monad's own table. The keyword list is `lang/src/parser/keywords.mo`'s
/// `kw_list` -- `def let in use open class struct instance type fn match
/// if then else infix do return for quote with defmacro pub priv` -- with
/// `pub`/`priv` INCLUDED here even though the parser's own membership
/// test leaves them out (that file's long comment explains why: their
/// omission is a parser workaround, not a fact about the language). A
/// highlighter marking `pub` as ordinary prose would be wrong.
pub def LanguageConfig.monad : LanguageConfig :=
    { name := "monad",
        keywords := ["def", "let", "in", "use", "open", "class", "struct",
            "instance", "type", "fn", "match", "if", "then", "else",
            "infix", "do", "return", "for", "quote", "with",
            "defmacro", "pub", "priv"],
        keywords_case_sensitive := true,
        line_comment := "//",
        string_quotes := ["\""],
        numbers := true }

/// The no-highlight default: `Document.language`'s `"text"` names it.
/// Every token is plain, so the view paints one unstyled span.
pub def LanguageConfig.text : LanguageConfig :=
    { name := "text",
        keywords := List.empty,
        keywords_case_sensitive := true,
        line_comment := "",
        string_quotes := List.empty,
        numbers := false }

/// `LanguageConfig` is small immutable data, read several times per
/// lexed run, so a duplicate of the VALUE is the correct duplicate --
/// the same reasoning `model.mo` states for `EditorState` and
/// `rope.mo` for `Rope`. The instance licenses the scanner's config
/// reads without a `Shared` share at every probe.
pub instance Copy LanguageConfig {
    def copy (cfg : LanguageConfig) : Pair LanguageConfig LanguageConfig :=
        match cfg {
            { name, keywords, keywords_case_sensitive, line_comment,
                string_quotes, numbers } =>
                    let one : LanguageConfig :=
                        { name := name, keywords := copy_strs keywords,
                            keywords_case_sensitive := keywords_case_sensitive,
                            line_comment := line_comment,
                            string_quotes := copy_strs string_quotes,
                            numbers := numbers } in
                    let two : LanguageConfig :=
                        { name := name, keywords := copy_strs keywords,
                            keywords_case_sensitive := keywords_case_sensitive,
                            line_comment := line_comment,
                            string_quotes := copy_strs string_quotes,
                            numbers := numbers } in
                    Pair.pair one two
        }
}

/// Field-wise list copy, so a duplicated config owns its own list cells
/// (the same shape `model.mo`'s `copy_list` has).
#[terminating]
def copy_strs (xs : List String) : List String :=
    match xs {
        List.empty => List.empty,
        List.cons one rest => List.cons one (copy_strs rest)
    }

/// The table the view consults, by `Document.language`. Unknown names
/// fall back to `"text"` -- an editor must open any file, not just the
/// ones it can color.
pub def Highlight.config_for (lang : String) : LanguageConfig :=
    if String.beq lang "monad"
    then LanguageConfig.monad
    else LanguageConfig.text

// ── The lexer ─────────────────────────────────────────────────────────────
//
// A hand-rolled scanner over the line's BYTES (UTF-8-aware the cheap
// way: any byte above 0x7f is part of a word, so multi-byte identifiers
// and prose highlight as plain text and never split). The output is the
// fewest runs that preserve the classes: adjacent same-class bytes
// share one token.

/// One lexed run: the text and its class.
pub struct Token {
    text : String,
    kind : TokenKind
}

/// Lex one line into classed runs, fewest that preserve the classes, IN
/// LINE ORDER. The line must be the CONTENT of a row (no trailing `\n`).
///
/// Adjacent same-class runs merge, so `"ab cd"` is three tokens (word,
/// space, word) and `"ab// hi"` is two (`"ab"` plain, `"// hi"`
/// comment). Empty input answers the empty list -- the view paints the
/// row's background itself.
///
/// THE SCANNER IS FORWARD-ONLY: each arm conses its token onto the scan
/// of the REST, so the answer is already in line order and there is no
/// accumulator to reverse at the end. The first compiled test run caught
/// the shape this file shipped with -- arms consing onto the recursion
/// result (forward) under a header that promised a reversed accumulator,
/// plus a final `List.reverse` that then reversed a FORWARD list -- and
/// `#[partial]` suspends the termination/shape checks, so only execution
/// could.
#[partial]
pub def Highlight.lex (cfg : LanguageConfig) (line : String) : List Token :=
    lex_go cfg (String.to_list line)

/// The scanner. One pass over the byte list, no backtracking except the
/// one-character lookahead inside a string literal.
///
/// THE CONFIG'S READS ARE LICENSED BY ITS `Copy` INSTANCE below, the
/// same reasoning `model.mo` states for `EditorState`: a small pure data
/// record read several times per step is what the instance is for. The
/// BYTE LIST is affine with no instance (init/copy has no List), so a
/// multi-read site shares it through `Shared` -- the same rule
/// `commands.mo` states.
#[partial]
def lex_go (cfg : LanguageConfig) (bytes : List U8) : List Token :=
    match bytes {
        List.empty => List.empty,
        List.cons b rest =>
            let shared : Shared (List U8) := Shared.of bytes in
            // The line-comment prefix outranks everything: it runs to
            // the end of the line, so nothing follows it and the token
            // list ends here.
            if prefix_at cfg.line_comment (Shared.get shared)
            then List.cons
                (Token.mk (bytes_to_string (Shared.get shared)) TokenKind.comment)
                List.empty
            else if quote_list_has cfg.string_quotes b
            then lex_string cfg (Shared.get shared)
            else if Bool.and cfg.numbers (digit b)
            then lex_number cfg (Shared.get shared)
            else if word_byte b
            then lex_word cfg (Shared.get shared)
            else lex_plain cfg (Shared.get shared)
    }

/// Does `pre` start at the head of `bytes`? An empty prefix never does
/// (an empty `line_comment` means "no comments in this language").
/// Byte-wise, so no string is built per probe.
#[partial]
def prefix_at (pre : String) (bytes : List U8) : Bool :=
    let pre_bytes : List U8 := String.to_list pre in
    let shared : Shared (List U8) := Shared.of pre_bytes in
    if List.is_empty (Shared.get shared)
    then false
    else prefix_go (Shared.get shared) bytes

#[partial]
def prefix_go (pre : List U8) (bytes : List U8) : Bool :=
    match pre {
        List.empty => true,
        List.cons p rest =>
            match bytes {
                List.empty => false,
                List.cons b tail =>
                    if U8.beq p b then prefix_go rest tail else false
            }
    }

/// Is `b` one of the config's quote characters?
def quote_at (cfg : LanguageConfig) (b : U8) : Bool :=
    quote_list_has cfg.string_quotes b

/// Does the quote LIST contain this byte? THE EMPTY LIST IS THE BASE
/// CASE, and it is load-bearing: `tail_strings List.empty` is
/// `List.empty`, so a version that recursed on the tail alone would
/// call itself with the same argument forever -- and `#[partial]`
/// suspends the termination check, so only the first real test run
/// caught it (the text table's empty quote list, and the monad table's
/// list after its one quote, both reach this case on the FIRST byte
/// probed).
#[partial]
def quote_list_has (qs : List String) (b : U8) : Bool :=
    match qs {
        List.empty => false,
        List.cons one rest =>
            match String.get one 0 {
                Option.some qb =>
                    if U8.beq qb b then true else quote_list_has rest b,
                Option.none => quote_list_has rest b
            }
    }

/// The string literal from the opening quote through the closing one,
/// or to the end of the line when it never closes (the line-scoped
/// limitation: an unterminated literal reads as one string token, the
/// best a row can do). A backslash escapes the next byte, so `\"`
/// does not close.
#[partial]
def lex_string (cfg : LanguageConfig) (bytes : List U8) : List Token :=
    let shared : Shared (List U8) := Shared.of bytes in
    let r : Pair String (List U8) :=
        string_body cfg.string_quotes (byte_tail (Shared.get shared))
            (String.from_list [List.head_or (Shared.get shared) 0x20u8]) false in
    match r {
        Pair.pair text rest =>
            // The tail is the line AFTER the closing quote, and it still
            // needs lexing -- `"a" b` is three tokens (string, space,
            // word), so the scan CONTINUES here just as the number, word
            // and plain arms do. The comment is the only arm that may
            // stop early: it runs to the end of the line.
            List.cons (Token.mk text TokenKind.string_lit) (lex_go cfg rest)
    }

/// Build the literal's text: `acc` grows by one byte per step. The
/// `escaped` flag carries the backslash: an escaped quote is content,
/// not a close. The returned pair is the text and the unread tail.
/// The QUOTE LIST is a parameter, not a closure over the config: the
/// config is affine and a nested def would capture it, so the scanner
/// threads the one field it needs.
#[partial]
def string_body (quotes : List String) (bytes : List U8) (acc : String) (escaped : Bool)
    : Pair String (List U8) :=
    let shared : Shared (List String) := Shared.of quotes in
    match bytes {
        List.empty => Pair.pair acc List.empty,
        List.cons b rest =>
            if escaped
            then string_body (Shared.get shared) rest (acc ++ String.from_list [b]) false
            else if U8.beq b 92u8
            then string_body (Shared.get shared) rest (acc ++ "\\") true
            else if quote_list_has (Shared.get shared) b
            then Pair.pair (acc ++ String.from_list [b]) rest
            else string_body (Shared.get shared) rest (acc ++ String.from_list [b]) false
    }

/// The number token: digits (and `.` inside the run) through the last
/// one. A minus is an operator, not a number start -- `x-1` must not
/// mislex.
#[partial]
def lex_number (cfg : LanguageConfig) (bytes : List U8) : List Token :=
    let r : Pair String (List U8) := number_body bytes "" in
    match r {
        Pair.pair text rest =>
            List.cons (Token.mk text TokenKind.number) (lex_go cfg rest)
    }

/// Digits and `.` inside the run. The stop branch REBUILDS the cons
/// (`b` is `Copy`, `rest` is unread) instead of re-reading `bytes`,
/// which keeps the byte list single-use.
#[partial]
def number_body (bytes : List U8) (acc : String) : Pair String (List U8) :=
    match bytes {
        List.empty => Pair.pair acc List.empty,
        List.cons b rest =>
            if Bool.or (digit b) (U8.beq b 46u8)
            then number_body rest (acc ++ String.from_list [b])
            else Pair.pair acc (List.cons b rest)
    }

/// The word token: word bytes through the last one, then classified
/// (a `keywords` whole-word lookup).
#[partial]
def lex_word (cfg : LanguageConfig) (bytes : List U8) : List Token :=
    let r : Pair String (List U8) := word_body bytes "" in
    match r {
        Pair.pair text rest =>
            List.cons (word_token cfg text) (lex_go cfg rest)
    }

/// Classify and build one word token. The text is read twice (the
/// keyword lookup and the token), and the earlier inline shape warned
/// on the self-hosted side, so the def exists to share it once.
def word_token (cfg : LanguageConfig) (text : String) : Token :=
    let shared : Shared String := Shared.of text in
    let k : TokenKind :=
        if is_keyword cfg (Shared.get shared) then TokenKind.keyword else TokenKind.plain in
    Token.mk (Shared.get shared) k

/// Word bytes: letters, digits, underscore and everything above 0x7f
/// (a UTF-8 lead or continuation byte -- never split).
#[partial]
def word_body (bytes : List U8) (acc : String) : Pair String (List U8) :=
    match bytes {
        List.empty => Pair.pair acc List.empty,
        List.cons b rest =>
            if word_byte b
            then word_body rest (acc ++ String.from_list [b])
            else Pair.pair acc (List.cons b rest)
    }

/// The plain run: bytes that are not the start of any other class,
/// through the last consecutive such byte (spaces, punctuation).
#[partial]
def lex_plain (cfg : LanguageConfig) (bytes : List U8) : List Token :=
    let r : Pair String (List U8) := plain_body cfg bytes "" in
    match r {
        Pair.pair text rest =>
            List.cons (Token.mk text TokenKind.plain) (lex_go cfg rest)
    }

/// Plain bytes: stops at a comment prefix, a quote, a digit, a word
/// byte, the end, or a byte of a DIFFERENT plain kind than the run's
/// head. The byte list is probed (prefix) and returned (stop), so it is
/// shared; the config reads are Copy-licensed.
///
/// PLAIN KINDS: a space run and a punctuation run never merge, and
/// punctuation bytes merge only with themselves -- "//" is one token
/// but ": " is two. `plain_kind` names the byte's kind, and the run
/// continues only while the next byte's kind equals the head's.
#[partial]
def plain_body (cfg : LanguageConfig) (bytes : List U8) (acc : String) : Pair String (List U8) :=
    let shared : Shared (List U8) := Shared.of bytes in
    match bytes {
        List.empty => Pair.pair acc List.empty,
        List.cons b rest =>
            if Bool.or
                (Bool.or (prefix_at cfg.line_comment (Shared.get shared)) (quote_at cfg b))
                (Bool.or (Bool.and cfg.numbers (digit b)) (word_byte b))
            then Pair.pair acc (List.cons b rest)
            else plain_run_on cfg (Shared.get shared) b rest acc
    }

/// The run's head byte `b` is plain (not a class start): continue while
/// the next byte is the SAME KIND -- both spaces, or the same
/// punctuation character -- and stop at any other byte.
#[partial]
def plain_run_on (cfg : LanguageConfig) (bytes : List U8) (head : U8) (tail : List U8)
    (acc : String) : Pair String (List U8) :=
    // The tail is read twice (the stop's return, the run's recursion),
    // so it shares one handle -- a `List` is deliberately not `Copy`.
    let shared : Shared (List U8) := Shared.of tail in
    match (Shared.get shared) {
        List.empty => Pair.pair (acc ++ String.from_list [head]) List.empty,
        List.cons b rest =>
            if Bool.not (plain_same_kind head b)
            then Pair.pair (acc ++ String.from_list [head]) (Shared.get shared)
            else plain_body cfg (Shared.get shared) (acc ++ String.from_list [head])
    }

/// Two plain bytes are the same kind: both spaces, or the same byte.
/// Spaces merge into one run ("  " is one token); a punctuation
/// character merges only with itself ("//" is one token, ": " is two).
def plain_same_kind (a : U8) (b : U8) : Bool :=
    Bool.or (U8.beq a b) (Bool.and (space_byte a) (space_byte b))

/// A space byte (0x20). Tab and the other controls are plain bytes of
/// their own kind, like punctuation.
def space_byte (b : U8) : Bool := U8.beq b 32u8

/// Classify a word: whole-word membership in the keyword list, honoring
/// the config's case sensitivity.
def is_keyword (cfg : LanguageConfig) (word : String) : Bool :=
    let probe : String :=
        if cfg.keywords_case_sensitive then word else String.to_lowercase word in
    keyword_member cfg.keywords probe

#[partial]
def keyword_member (kws : List String) (probe : String) : Bool :=
    match kws {
        List.empty => false,
        List.cons one rest =>
            if String.beq one probe then true else keyword_member rest probe
    }

/// A digit: `0x30..=0x39`.
def digit (b : U8) : Bool := U8.gt b 47u8 && Bool.not (U8.gt b 57u8)

/// A word byte: ASCII letters, digits, underscore, or any byte above
/// 0x7f (a UTF-8 lead or continuation byte -- never split). DIGITS ARE
/// WORD BYTES: `x2` is one word, not a word followed by a number -- the
/// word scanner takes a run first, so a digit INSIDE a word never starts
/// a number (`test_digit_inside_a_word_is_plain`'s pin). A digit where a
/// word could START still begins a number, because `lex_go` probes
/// `digit` before `word_byte`.
def word_byte (b : U8) : Bool :=
    Bool.or
        (Bool.or (Bool.or (letter b) (digit b)) (U8.beq b 95u8))
        (U8.gt b 127u8)

/// ASCII letters, either case.
def letter (b : U8) : Bool :=
    Bool.or
        (Bool.and (U8.gt b 64u8) (Bool.not (U8.gt b 90u8)))
        (Bool.and (U8.gt b 96u8) (Bool.not (U8.gt b 122u8)))

/// The head of a string list, or `""` when empty.
def head_string (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons one _ => one
    }

/// A string list without its first cell.
#[partial]
def tail_strings (xs : List String) : List String :=
    match xs {
        List.empty => List.empty,
        List.cons _ rest => rest
    }

/// One token, built here (not a struct literal at the call site) so the
/// derive-free rule needs no exception and the two-host inference
/// hazard stays out of the hot path.
pub def Token.mk (text : String) (kind : TokenKind) : Token :=
    { text := text, kind := kind }

/// The token's text.
pub def Token.text_of (t : Token) : String :=
    match t { { text, .. } => text }

/// The token's class.
pub def Token.kind_of (t : Token) : TokenKind :=
    match t { { kind, .. } => kind }

/// The bytes of a byte list as a String. The one place the lexer pays
/// a list-to-string conversion; the line is already flat when the view
/// calls, and the runs it builds are short.
def bytes_to_string (bytes : List U8) : String := String.from_list bytes

/// The head of a byte list, or `fallback` when empty.
def List.head_or (xs : List U8) (fallback : U8) : U8 :=
    match xs {
        List.empty => fallback,
        List.cons b _ => b
    }

/// The list without its first cell. `List.drop` is not in `std`'s list
/// surface (the plan's "no invented APIs" rule), so the scanner's one
/// use has its own two-line def.
#[partial]
def byte_tail (xs : List U8) : List U8 :=
    match xs {
        List.empty => List.empty,
        List.cons _ rest => rest
    }

// ── The span bridge ────────────────────────────────────────────────────────
//
// The view speaks `TextSegment`s (tui's `spans` leaf), the lexer speaks
// `Token`s. This is the one place the two vocabularies meet: a token list
// becomes the segment list the view paints, each token carrying the
// palette's style for its class. The view then composes ON TOP of these
// segments (a selection bg merges into a keyword's style, the primary
// head reverses one cell) -- `Highlight.style` is the base layer, never
// the final word.

/// The token list as the `TextSegment`s the `spans` leaf paints, in
/// token order: one segment per token, each styled by the palette.
///
/// The tokens' texts CONCATENATE to the lexed line, so the segments tile
/// the row with no gaps; the renderer clips whatever runs past the
/// area's width. An empty token list (the empty line) answers an empty
/// segment list -- the row paints its background and nothing else.
#[partial]
pub def Highlight.segments (toks : List Token) : List TextSegment :=
    Highlight.segments_go toks List.empty

#[partial]
def Highlight.segments_go (toks : List Token) (acc : List TextSegment) : List TextSegment :=
    match toks {
        List.empty => List.reverse acc,
        List.cons one rest =>
            let seg : TextSegment :=
                mk_text_segment (Token.text_of one) (Highlight.style (Token.kind_of one)) in
            Highlight.segments_go rest (List.cons seg acc)
    }
