/// Syntax highlighting over the lossless tokenizer.
///
/// `Highlight.spans` cuts Monad source into classified spans whose texts
/// concatenate back to the input exactly; consumers turn spans into markup
/// (`acorn`'s book pages, `try_ui`'s editor overlay). Nothing here depends on
/// the compiler, so it stays usable from wasm.
///
/// Whitespace is copied from the source, not rebuilt from `Gap` counts (a
/// tab counts as one there). The token texts are the source's own slices; a
/// line comment's trailing blanks, which the lexer trims, fall into the next
/// whitespace span.
use std::list {List.any}
use parsec::char_preds {is_space_byte}
use lib::lexer {LexError, TokKind, Token, Lex.kind_tag, Lex.lex}

/// A span's class. `plain` covers whitespace, punctuation, operators and
/// ordinary identifiers.
pub type HlClass {
    plain,
    /// A reserved keyword (`def`, `match`, `pub`, ...).
    kw,
    /// The name a `def`/`defmacro` introduces.
    fn_name,
    /// A capitalised identifier, or `Type`/`Pred`/`Sort`.
    type_name,
    num,
    str,
    comment,
    /// An attribute, `#[` through its `]`. Not named `attr`: `Html.Attr.attr`
    /// (arity 2) would share the bare name in any program linking both motes
    /// (see `TokKind.str_lit` in `lexer.mo`).
    attribute,
}

pub struct Span {
    cls : HlClass,
    text : String,
}

/// The CSS class for a span (`""` for plain), matching the landing page's
/// hand-written `kw|fn|type|num|comment` classes.
pub def Highlight.css_class (c : HlClass) : String :=
    match c {
        HlClass.plain => "",
        HlClass.kw => "kw",
        HlClass.fn_name => "fn",
        HlClass.type_name => "type",
        HlClass.num => "num",
        HlClass.str => "str",
        HlClass.comment => "comment",
        HlClass.attribute => "attr",
    }

/// The reserved keywords (`RESERVED_KEYWORDS`, `rust/core/src/parser.rs`).
pub def Highlight.is_keyword (w : String) : Bool :=
    List.any (fn (k : String) => String.beq k w)
        ["def", "defmacro", "let", "in", "use", "open", "class", "struct", "instance", "type", "fn",
            "match", "if", "then", "else", "infix", "return", "for", "do", "quote", "with", "pub", "priv"]

def is_upper_byte (b : U8) : Bool :=
    U8.gt b 64u8 && U8.lt b 91u8

def starts_upper (w : String) : Bool :=
    match String.get w 0 {
        Option.some b => is_upper_byte b,
        Option.none => false,
    }

/// What the previous tokens make of the next one.
struct State {
    /// The previous token was `def`/`defmacro`.
    after_def : Bool,
    /// Inside `#[ ... ]`.
    in_attr : Bool,
}

def word_class (st : State) (w : String) : HlClass :=
    if st.in_attr then HlClass.attribute
    else if Highlight.is_keyword w then HlClass.kw
    else if st.after_def then HlClass.fn_name
    else if starts_upper w then HlClass.type_name
    else HlClass.plain

instance Copy State {
    def copy (s : State) : Pair State State := Pair.pair s s
}

def token_class (st : State) (tag : I64) (text : String) : HlClass :=
    if I64.beq tag (Lex.kind_tag TokKind.word) then word_class st text
    else if st.in_attr then HlClass.attribute
    else if I64.beq tag (Lex.kind_tag TokKind.number) then HlClass.num
    else if I64.beq tag (Lex.kind_tag TokKind.str_lit) then HlClass.str
    else if I64.beq tag (Lex.kind_tag TokKind.comment) then HlClass.comment
    else if I64.beq tag (Lex.kind_tag TokKind.punct) && String.starts_with "#" text && String.ends_with text "[" then HlClass.attribute
    else HlClass.plain

def next_state (st : State) (tag : I64) (text : String) : State :=
    let opens_attr : Bool := I64.beq tag (Lex.kind_tag TokKind.punct) && String.ends_with text "[" in
    let closes_attr : Bool := I64.beq tag (Lex.kind_tag TokKind.closer) && String.beq text "]" in
    let is_def : Bool := I64.beq tag (Lex.kind_tag TokKind.word) && (String.beq text "def" || String.beq text "defmacro") in
    { after_def := is_def, in_attr := (st.in_attr || opens_attr) && Bool.not closes_attr }

/// The number of leading whitespace bytes, scanning the suffix (O(gap)).
#[terminating]
def space_len (s : String) (n : I64) : I64 :=
    match String.get s 0 {
        Option.some b => if is_space_byte b then space_len (String.drop 1 s) (n + 1) else n,
        Option.none => n,
    }

def plain_span (text : String) : Span :=
    { cls := HlClass.plain, text := text }

/// Whitespace before the next token, when there is any.
def gap_spans (rest : String) (n : I64) : List Span :=
    if n > 0 then [plain_span (String.slice rest 0 n)] else List.empty

/// Walk the tokens against the source suffix they came from.
def spans_loop (st : State) (rest : String) (tokens : List Token) (acc : List Span) : List Span :=
    match tokens {
        List.empty =>
            List.reverse (if String.is_empty rest then acc else List.cons (plain_span rest) acc),
        List.cons t more => token_spans st rest t more acc,
    }

// Part of the `spans_loop` cycle; `more` shrinks on every turn.
#[terminating]
def token_spans (st : State) (rest : String) (t : Token) (more : List Token) (acc : List Span) : List Span :=
    match t {
        { kind, text, .. } => text_spans st rest (Lex.kind_tag kind) text more acc,
    }

// Mutual recursion with `spans_loop` on the strictly shorter `more`.
#[terminating]
def text_spans (st : State) (rest : String) (tag : I64) (text : String) (more : List Token) (acc : List Span) : List Span :=
    let gap : I64 := space_len rest 0 in
    let span : Span := { cls := token_class st tag text, text := text } in
    spans_loop (next_state st tag text) (String.drop (String.length text) (String.drop gap rest)) more
        (List.cons span (List.append (gap_spans rest gap) acc))

/// Classified spans of `src`; their texts concatenate to `src`. Source the
/// lexer rejects (a half-typed buffer, an `ignore` fragment) is one plain
/// span: highlighting never fails a page.
pub def Highlight.spans (src : String) : List Span :=
    match Lex.lex src {
        Result.ok tokens => spans_loop { after_def := false, in_attr := false } src tokens List.empty,
        Result.err _ => [plain_span src],
    }
