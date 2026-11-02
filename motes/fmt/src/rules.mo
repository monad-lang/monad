/// The formatter's layout policy, kept in one module so a new construct is a
/// table entry rather than an edit spread through the renderer.
///
/// There are two independent tables:
///
/// - **Tight pairs** are pairs whose 0-vs-positive whitespace relation the
///   parser observes. That relation is preserved verbatim, never canonicalized:
///   `-1` must stay a negative literal while `- 1` stays subtraction; `name!`,
///   `!x`/`%x`/`?x`, `#Named`, `::`, and `x.y` (dotted name/field access, as
///   opposed to the infix `.` operator) likewise key on adjacency.
/// - **Spacing** decides the width (0 or 1) between all other tokens on the
///   same line. It may tighten a pair the source separated (e.g. `f ( x )` ->
///   `f (x)`) because none of the tokens involved are operator characters, so
///   the parser cannot read a different token stream.
///
/// Line breaks are never decided here: the renderer preserves the author's.

use lib::lexer {Lex.gap_tight, Lex.kind_tag, Lex.same_token, TokKind, Token}

def kind_is (t : Token) (k : TokKind) : Bool :=
    I64.beq (Lex.kind_tag t.kind) (Lex.kind_tag k)

pub def Rules.is_sep (t : Token) : Bool := kind_is t TokKind.sep

pub def Rules.is_opener (t : Token) : Bool := kind_is t TokKind.opener

pub def Rules.is_closer (t : Token) : Bool := kind_is t TokKind.closer

pub def Rules.is_line_comment (t : Token) : Bool :=
    kind_is t TokKind.comment && String.starts_with "//" t.text

pub def Rules.is_block_comment (t : Token) : Bool :=
    kind_is t TokKind.comment && String.starts_with "/*" t.text

def is_bracket_open (t : Token) : Bool :=
    String.beq t.text "(" || String.beq t.text "["

def is_bracket_close (t : Token) : Bool :=
    String.beq t.text ")" || String.beq t.text "]"

def is_brace_close (t : Token) : Bool :=
    String.beq t.text "}"

/// The sigils the parser requires to touch their neighbour: macro name suffix,
/// the three multiplicity prefixes, the dict-hint marker, and the two lambda
/// spellings.
def is_sigil (s : String) : Bool :=
    String.beq s "!" || String.beq s "%" || String.beq s "?" || String.beq s "#" ||
    String.beq s "\\" || String.beq s "ꟛ"

/// Does the parser observe whether these two tokens touch?
pub def Rules.tight_pair (prev : Token) (cur : Token) : Bool :=
    (String.beq prev.text "-" && I64.beq (Lex.kind_tag cur.kind) (Lex.kind_tag TokKind.number)) ||
    String.beq prev.text "." || String.beq cur.text "." ||
    String.beq prev.text "::" || String.beq cur.text "::" ||
    is_sigil prev.text || is_sigil cur.text

/// The closer that matches an opener, used by the renderer's alignment stack.
pub def Rules.matching_closer (open_text : String) : String :=
    if String.beq open_text "(" then ")"
    else if String.beq open_text "[" then "]"
    else "}"

/// Spaces (0 or 1) between two non-tight tokens on the same line.
pub def Rules.space_between (prev : Token) (cur : Token) : I64 :=
    if Rules.is_sep cur then 0
    else if is_bracket_close cur then 0
    else if is_bracket_open prev then 0
    else if is_brace_close cur then
        if String.beq prev.text "{" || Rules.is_sep prev then 0 else 1
    else if String.beq prev.text "#[" || String.beq prev.text "#![" then 0
    else 1

/// Do two token streams describe the same program as far as whitespace is
/// concerned: same kind and text for every token, and the same 0-vs-positive
/// relation at every tight pair.
#[partial]
pub def Rules.tokens_match (a : List Token) (b : List Token) : Bool :=
    tokens_match_from Option.none a b

#[partial]
def tokens_match_from (prev : Option Token) (a : List Token) (b : List Token) : Bool :=
    match a {
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false,
        },
        List.cons x xs => match b {
            List.empty => false,
            List.cons y ys =>
                let tight : Bool := match prev {
                    Option.some p => Rules.tight_pair p x,
                    Option.none => false,
                } in
                let gap_ok : Bool :=
                    if tight
                    then if Lex.gap_tight x.gap
                        then Lex.gap_tight y.gap
                        else Bool.not (Lex.gap_tight y.gap)
                    else true in
                Lex.same_token x y && gap_ok &&
                    tokens_match_from (Option.some x) xs ys,
        },
    }
