/// A lossless, policy-free tokenizer for Monad source.
///
/// The compiler's parser has no token type: it consumes raw source text with
/// combinators and discards whitespace and comments. A formatter cannot use
/// that surface -- comments would vanish and infix expressions would be
/// reprinted in prefix form (`a + b` parses to `app (app (+) a) b`) -- so this
/// module builds the missing concrete token stream instead.
///
/// It carries no formatting policy. `kind` is a lexical category, `text` is
/// the source slice verbatim, and `gap` records the trivia before the token.
/// That makes it reusable by anything that needs Monad tokens (syntax
/// highlighting, a linter, import organization), while `rules`/`render` hold
/// everything that is specifically about layout.
///
/// ## Cost model
///
/// Every scanner threads the remaining SUFFIX and peeks at byte 0. That is not
/// a style choice: `String.get s i` is O(1) only at `i == 0` on the compiled
/// backend (any other index pays a `strlen` for its bounds check), and
/// `String.is_empty` is defined in terms of `String.length` (`strlen`). A
/// per-byte scan using absolute indices is therefore O(n^2). Dropping one byte
/// from a suffix is O(1), so each scanner is linear. The same reason is
/// documented in `motes/markdown/src/scan.mo`.
///
/// ## Lexical rules
///
/// They mirror the self-hosted parser's scanners:
/// - whitespace: `is_space_byte` (`motes/parsec/src/char_preds.mo`);
/// - identifiers are ASCII (`is_ident_char_byte`), keywords are just words;
/// - comments: `//` to end of line, `/* ... */` to the first `*/` (not
///   nested), unterminated block comments run to EOF (`lang/src/parser.mo`'s
///   `skip_docstrings`);
/// - strings: `"..."` with backslash escapes and raw newlines, `'...'` chars,
///   and `r"..."`/`r#"..."#` raw strings whose closing hash count is capped at
///   the opening count (`lang/src/parser/string.mo`);
/// - numbers: hex or decimal digits/underscores, then -- matching
///   `numeric_literal_try_dot` -- a `.` after decimal digits is consumed with
///   any following fraction digits (zero or more), then a known suffix;
/// - operators: a maximal run of `+&|=<>*/-!.@` (`lang/src/parser/op_table.mo`),
///   with `:`, `::`, `:=`, `#`, `#[`, `#![`, `%`, `?`, `\` and the `ꟛ` lambda
///   handled as their own tokens.
///
/// Two facts matter to every consumer: token text is never rewritten, and the
/// 0-vs-positive gap relation is recorded, because the parser keys the negative
/// literal (`-1` vs `- 1`), macro suffixes (`name!`), multiplicities (`!x`,
/// `%x`, `?x`), dict hints (`#Named`), and dotted names on tightness.

use parsec::char_preds {
    is_digit_byte, is_digit_or_underscore_byte, is_ident_char_byte, is_space_byte,
}

pub type TokKind {
    /// Identifiers and keywords. The lexer does not know the keyword list:
    /// no layout rule needs it.
    word,
    /// Decimal/hex digits, optional fraction, optional suffix.
    number,
    /// Ordinary strings, raw strings, and char literals (the text says which).
    string,
    /// `// ...` or `/* ... */`.
    comment,
    /// `(` `[` `{`
    opener,
    /// `)` `]` `}`
    closer,
    /// `,` `;`
    sep,
    /// A maximal operator run: `+ - * / = < > | & ! . @`, including `->`,
    /// `=>`, `<-`, `..`, `!=` and friends.
    op,
    /// `:`, `::`, `:=`, `#`, `#[`, `#![`, `%`, `?`, `\`, and `ꟛ`.
    punct,
}

/// The trivia before a token. `newlines` counts line breaks; `spaces` counts
/// every whitespace byte in the run (so it is nonzero exactly when there was
/// whitespace), and `indent` is the whitespace width after the last newline
/// (a tab counts as one unit here). Only the *presence* of whitespace is
/// semantically significant to the parser; the counts exist so the renderer
/// can preserve line breaks and re-indent.
pub struct Gap {
    newlines : I64,
    spaces : I64,
    indent : I64,
}

pub struct Token {
    kind : TokKind,
    text : String,
    gap : Gap,
}

pub struct LexError {
    offset : I64,
    message : String,
}

/// A token's kind and length in bytes. Text is `String.slice s 0 len`.
struct Scan {
    kind : TokKind,
    len : I64,
}

// ---------------------------------------------------------------------------
// Suffix helpers
// ---------------------------------------------------------------------------

/// Byte 0 of the suffix, or NUL at end of input.
def head (s : String) : U8 :=
    match String.get s 0 {
        Option.some b => b,
        Option.none => 0u8,
    }

def head_is (s : String) (b : U8) : Bool :=
    U8.beq (head s) b

/// End of input. Deliberately not `String.is_empty`: that is `length == 0`,
/// i.e. a `strlen`, and this is called once per byte.
def at_end (s : String) : Bool :=
    match String.get s 0 {
        Option.some _ => false,
        Option.none => true,
    }

/// Drop one ASCII byte. Safe only when the head is known to be ASCII (all
/// structural characters and runs are).
def tail (s : String) : String :=
    String.drop 1 s

/// Width of the character at the head, 0 at end of input. `String.drop` is
/// byte-oriented and returns "" when the cut lands mid-character (AGENTS.md's
/// `String.slice`/`drop` note), so arbitrary-text scanners must advance by a
/// whole character rather than one byte.
def width_at (s : String) : I64 :=
    if at_end s then 0 else utf8_width (head s)

def has_prefix (prefix : String) (s : String) : Bool :=
    String.starts_with prefix s

/// `+ & = | < > * / - ! . @` -- `lang/src/parser/op_table.mo`'s `op_chars`.
def is_op_byte (b : U8) : Bool :=
    U8.beq b 43u8 || U8.beq b 38u8 || U8.beq b 61u8 || U8.beq b 124u8 ||
    U8.beq b 60u8 || U8.beq b 62u8 || U8.beq b 42u8 || U8.beq b 47u8 ||
    U8.beq b 45u8 || U8.beq b 33u8 || U8.beq b 46u8 || U8.beq b 64u8

/// `0`-`9`, `A`-`F`, `a`-`f`. `is_hex_digit_byte` is not `pub` in parsec.
def is_hex_byte (b : U8) : Bool :=
    is_digit_byte b ||
    (U8.gt b 64u8 && Bool.not (U8.gt b 70u8)) ||
    (U8.gt b 96u8 && Bool.not (U8.gt b 102u8))

def is_ident_start_byte (b : U8) : Bool :=
    is_ident_char_byte b && Bool.not (is_digit_byte b)

/// Width in bytes of the UTF-8 character starting with `b` (only used for
/// char-literal contents; valid input is assumed, and a malformed lead byte
/// is reported as width 1).
def utf8_width (b : U8) : I64 :=
    if U8.gt b 239u8 then 4
    else if U8.gt b 223u8 then 3
    else if U8.gt b 191u8 then 2
    else 1

def ok_scan (kind : TokKind) (len : I64) : Result LexError Scan :=
    let s : Scan := { kind := kind, len := len } in
    Result.ok s

def err_len (offset : I64) (message : String) : Result LexError I64 :=
    let e : LexError := { offset := offset, message := message } in
    Result.err e

def err_scan (offset : I64) (message : String) : Result LexError Scan :=
    let e : LexError := { offset := offset, message := message } in
    Result.err e

// ---------------------------------------------------------------------------
// Run lengths
// ---------------------------------------------------------------------------

#[partial]
def line_comment_len (s : String) (n : I64) : I64 :=
    if at_end s then n
    else if head_is s 10u8 then n
    else
        let w : I64 := width_at s in
        line_comment_len (String.drop w s) (I64.add n w)

/// First `*/`, or EOF when unterminated (the parser consumes to EOF).
#[partial]
def block_comment_len (s : String) (n : I64) : I64 :=
    if at_end s then n
    else if has_prefix "*/" s then I64.add n 2
    else
        let w : I64 := width_at s in
        block_comment_len (String.drop w s) (I64.add n w)

#[partial]
def ident_run (s : String) (n : I64) : I64 :=
    if at_end s then n
    else if is_ident_char_byte (head s) then ident_run (tail s) (I64.add n 1)
    else n

#[partial]
def op_run (s : String) (n : I64) : I64 :=
    if at_end s then n
    else if is_op_byte (head s) then op_run (tail s) (I64.add n 1)
    else n

#[partial]
def decimal_run (s : String) (n : I64) : I64 :=
    if at_end s then n
    else if is_digit_or_underscore_byte (head s) then decimal_run (tail s) (I64.add n 1)
    else n

#[partial]
def fraction_run (s : String) (n : I64) : I64 :=
    if at_end s then n
    else if is_digit_byte (head s) then fraction_run (tail s) (I64.add n 1)
    else n

#[partial]
def hex_run (s : String) (n : I64) : I64 :=
    if at_end s then n
    else if is_hex_byte (head s) then hex_run (tail s) (I64.add n 1)
    else n

#[partial]
def skip_hashes (s : String) (n : I64) : I64 :=
    if at_end s then n
    else if head_is s 35u8 then skip_hashes (tail s) (I64.add n 1)
    else n

#[partial]
def hashes_capped (s : String) (count : I64) (n : I64) : I64 :=
    if I64.beq count n then count
    else if at_end s then count
    else if head_is s 35u8 then hashes_capped (tail s) (I64.add count 1) n
    else count

// ---------------------------------------------------------------------------
// String, char, raw-string, number lengths
// ---------------------------------------------------------------------------

/// `s` is the byte after the opening `"`; `pos` counts consumed bytes.
#[partial]
def string_len (s : String) (pos : I64) : Result LexError I64 :=
    if at_end s then err_len pos "unterminated string literal"
    else if head_is s 92u8 then
        let after := tail s in
        if at_end after then err_len (I64.add pos 1) "unterminated string literal"
        else
            let w : I64 := width_at after in
            string_len (String.drop w after) (I64.add pos (I64.add 1 w))
    else if head_is s 34u8 then Result.ok (I64.add pos 1)
    else
        let w : I64 := width_at s in
        string_len (String.drop w s) (I64.add pos w)

/// `s` is the byte after the opening `'`; `pos` counts consumed bytes.
#[partial]
def char_len (s : String) (pos : I64) : Result LexError I64 :=
    if at_end s then err_len pos "unterminated char literal"
    else if head_is s 92u8 then char_escape_len (tail s) (I64.add pos 1)
    else
        let width : I64 := utf8_width (head s) in
        let after : String := String.drop width s in
        if head_is after 39u8 then Result.ok (I64.add pos (I64.add width 1))
        else err_len pos "unterminated char literal"

/// `s` is the byte after the backslash; `pos` includes the backslash.
#[partial]
def char_escape_len (s : String) (pos : I64) : Result LexError I64 :=
    if at_end s then err_len pos "unterminated char literal"
    else if head_is s 117u8 then
        // `\u{...}`: find the closing brace, then the quote.
        match find_byte (tail s) 125u8 0 {
            Option.none => err_len pos "unterminated unicode escape",
            Option.some at =>
                let close : String := String.drop at (tail s) in
                if head_is close 125u8 && head_is (tail close) 39u8
                then Result.ok (I64.add pos (I64.add at 3))
                else err_len (I64.add pos (I64.add at 1)) "expected closing quote after unicode escape",
        }
    else if head_is (tail s) 39u8 then Result.ok (I64.add pos 2)
    else err_len pos "unterminated char literal"

#[partial]
def find_byte (s : String) (want : U8) (at : I64) : Option I64 :=
    if at_end s then Option.none
    else if head_is s want then Option.some at
    else
        let w : I64 := width_at s in
        find_byte (String.drop w s) want (I64.add at w)

/// `s` is the raw string's body; `n` is the opening hash count; `pos` counts
/// the `r`, hashes, and opening quote already consumed.
#[partial]
def raw_body_len (s : String) (n : I64) (pos : I64) : Result LexError I64 :=
    if at_end s then err_len pos "unterminated raw string literal"
    else if head_is s 34u8 then
        let seen : I64 := hashes_capped (tail s) 0 n in
        if I64.beq seen n then Result.ok (I64.add (I64.add pos 1) n)
        else raw_body_len (String.drop (I64.add 1 seen) s) n (I64.add pos (I64.add 1 seen))
    else
        let w : I64 := width_at s in
        raw_body_len (String.drop w s) n (I64.add pos w)

def int_suffix_len (rest : String) : I64 :=
    if has_prefix "i8" rest then 2
    else if has_prefix "i16" rest then 3
    else if has_prefix "i32" rest then 3
    else if has_prefix "i64" rest then 3
    else if has_prefix "u8" rest then 2
    else if has_prefix "u16" rest then 3
    else if has_prefix "u32" rest then 3
    else if has_prefix "u64" rest then 3
    else 0

def float_suffix_len (rest : String) : I64 :=
    if has_prefix "f32" rest then 3
    else if has_prefix "f64" rest then 3
    else 0

/// `s` starts at a digit. The shape mirrors `numeric_literal`.
def scan_number (s : String) : Result LexError Scan :=
    let one : String := String.drop 1 s in
    if head_is s 48u8 && (head_is one 120u8 || head_is one 88u8) then
        let digits : I64 := hex_run (String.drop 2 s) 0 in
        let base : I64 := I64.add 2 digits in
        ok_scan TokKind.number (I64.add base (int_suffix_len (String.drop base s)))
    else
        let digits : I64 := decimal_run s 0 in
        let after_int : String := String.drop digits s in
        if head_is after_int 46u8 then
            let frac : I64 := fraction_run (tail after_int) 0 in
            let base : I64 := I64.add digits (I64.add 1 frac) in
            ok_scan TokKind.number (I64.add base (float_suffix_len (String.drop base s)))
        else
            ok_scan TokKind.number (I64.add digits (int_suffix_len after_int))

// ---------------------------------------------------------------------------
// Token dispatch
// ---------------------------------------------------------------------------

/// `s` starts at `r`. A raw string is `r` + zero or more `#` + `"`.
def scan_r_word (s : String) : Result LexError Scan :=
    let after_r : String := tail s in
    let n : I64 := skip_hashes after_r 0 in
    let after_hashes : String := String.drop n after_r in
    if head_is after_hashes 34u8 then
        match raw_body_len (tail after_hashes) n (I64.add n 2) {
            Result.err e => Result.err e,
            Result.ok len => ok_scan TokKind.string len,
        }
    else ok_scan TokKind.word (I64.add 1 (ident_run after_r 0))

def scan_string (s : String) : Result LexError Scan :=
    match string_len (tail s) 1 {
        Result.err e => Result.err e,
        Result.ok len => ok_scan TokKind.string len,
    }

def scan_char (s : String) : Result LexError Scan :=
    match char_len (tail s) 1 {
        Result.err e => Result.err e,
        Result.ok len => ok_scan TokKind.string len,
    }

def scan_colon (s : String) : Result LexError Scan :=
    if has_prefix "::" s || has_prefix ":=" s
    then ok_scan TokKind.punct 2
    else ok_scan TokKind.punct 1

def scan_hash (s : String) : Result LexError Scan :=
    if has_prefix "#![" s then ok_scan TokKind.punct 3
    else if has_prefix "#[" s then ok_scan TokKind.punct 2
    else ok_scan TokKind.punct 1

#[partial]
def scan_token (s : String) : Result LexError Scan :=
    if has_prefix "//" s then
        ok_scan TokKind.comment (line_comment_len (String.drop 2 s) 2)
    else if has_prefix "/*" s then
        ok_scan TokKind.comment (block_comment_len (String.drop 2 s) 2)
    else if head_is s 34u8 then scan_string s
    else if head_is s 39u8 then scan_char s
    else if head_is s 114u8 then scan_r_word s
    else if is_digit_byte (head s) then scan_number s
    else if is_ident_start_byte (head s) then ok_scan TokKind.word (ident_run s 0)
    else if head_is s 40u8 || head_is s 91u8 || head_is s 123u8 then ok_scan TokKind.opener 1
    else if head_is s 41u8 || head_is s 93u8 || head_is s 125u8 then ok_scan TokKind.closer 1
    else if head_is s 44u8 || head_is s 59u8 then ok_scan TokKind.sep 1
    else if head_is s 58u8 then scan_colon s
    else if head_is s 35u8 then scan_hash s
    else if head_is s 37u8 || head_is s 63u8 || head_is s 92u8 then ok_scan TokKind.punct 1
    else if has_prefix "ꟛ" s then ok_scan TokKind.punct 3
    else if is_op_byte (head s) then ok_scan TokKind.op (op_run s 0)
    else err_scan 0 ("unexpected character " ++ U8.to_string (head s))

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

pub def Lex.kind_tag (k : TokKind) : I64 :=
    match k {
        TokKind.word => 0,
        TokKind.number => 1,
        TokKind.string => 2,
        TokKind.comment => 3,
        TokKind.opener => 4,
        TokKind.closer => 5,
        TokKind.sep => 6,
        TokKind.op => 7,
        TokKind.punct => 8,
    }

/// Drop trailing spaces/tabs/`\r` from a line comment, leaving its text
/// otherwise verbatim.
#[partial]
def trim_ws_end (s : String) (end : I64) : I64 :=
    if I64.gt end 0 then
        let b : U8 := match String.get s (I64.sub end 1) {
            Option.some x => x,
            Option.none => 0u8,
        } in
        if U8.beq b 32u8 || U8.beq b 9u8 || U8.beq b 13u8
        then trim_ws_end s (I64.sub end 1)
        else end
    else 0

#[partial]
def lex_loop
    (rest : String) (offset : I64)
    (newlines : I64) (spaces : I64) (indent : I64)
    (acc : List Token) : Result LexError (List Token) :=
    if at_end rest then Result.ok (List.reverse acc)
    else
        let b : U8 := head rest in
        if is_space_byte b then
            if U8.beq b 10u8
            then lex_loop (tail rest) (I64.add offset 1)
                (I64.add newlines 1) (I64.add spaces 1) 0 acc
            else lex_loop (tail rest) (I64.add offset 1)
                newlines (I64.add spaces 1) (I64.add indent 1) acc
        else
            match scan_token rest {
                Result.err e =>
                    let abs : LexError := {
                        offset := I64.add offset e.offset,
                        message := e.message,
                    } in
                    Result.err abs,
                Result.ok scan =>
                    let raw : String := String.slice rest 0 scan.len in
                    let text : String :=
                        if I64.beq (Lex.kind_tag scan.kind) 3 && has_prefix "//" raw
                        then String.slice raw 0 (trim_ws_end raw (String.length raw))
                        else raw in
                    let gap : Gap := { newlines := newlines, spaces := spaces, indent := indent } in
                    let token : Token := { kind := scan.kind, text := text, gap := gap } in
                    lex_loop (String.drop scan.len rest) (I64.add offset scan.len)
                        0 0 0 (List.cons token acc),
            }

pub def Lex.lex (src : String) : Result LexError (List Token) :=
    lex_loop src 0 0 0 0 List.empty

/// Same lexical unit: same category and same verbatim text. Line-comment text
/// is already right-trimmed by the lexer, so this is an exact comparison.
pub def Lex.same_token (a : Token) (b : Token) : Bool :=
    match a {
        { kind := kind_a, text := text_a, .. } =>
            match b {
                { kind := kind_b, text := text_b, .. } =>
                    I64.beq (Lex.kind_tag kind_a) (Lex.kind_tag kind_b) &&
                    String.beq text_a text_b,
            },
    }

/// Was there no whitespace before this token?
pub def Lex.gap_tight (g : Gap) : Bool :=
    match g {
        { newlines, spaces, .. } =>
            I64.beq newlines 0 && I64.beq spaces 0,
    }

#[partial]
def lines_loop
    (line_start : String) (rest : String) (consumed : I64) (last_cr : Bool)
    (acc : List String) : List String :=
    if at_end rest then
        if I64.beq consumed 0 then List.reverse acc
        else
            let n : I64 := if last_cr then I64.sub consumed 1 else consumed in
            List.reverse (List.cons (String.slice line_start 0 n) acc)
    else if head_is rest 10u8 then
        let n : I64 := if last_cr then I64.sub consumed 1 else consumed in
        let line : String := String.slice line_start 0 n in
        lines_loop (tail rest) (tail rest) 0 false (List.cons line acc)
    else
        // Arbitrary text: step by a whole character, not a byte.
        let w : I64 := width_at rest in
        lines_loop line_start (String.drop w rest) (I64.add consumed w)
            (head_is rest 13u8) acc

/// Split into lines without their terminators. A trailing newline does not
/// produce a final empty line. CRLF loses its `\r`.
pub def Lex.lines (s : String) : List String :=
    lines_loop s s 0 false List.empty
