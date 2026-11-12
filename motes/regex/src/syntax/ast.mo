/// The regex abstract syntax tree: what the pattern says, with spans,
/// before flags are resolved (that is `hir.mo`'s job).
///
/// `RxAst.render` prints a compact S-expression; the parser's golden tests
/// compare against it.
use lib::error {RegexSpan}
use std::list {List.intercalate}

/// The inline / builder flags.
pub type RxFlag {
    case_insensitive,
    multi_line,
    dot_matches_new_line,
    swap_greed,
    ignore_whitespace,
    unicode,
}

/// One flag set on (`true`) or cleared (`false`), as written in `(?i-s)`.
pub struct RxFlagItem {
    flag : RxFlag,
    on : Bool,
}

pub type RxAssert {
    /// `^`: start of text, or of a line under `m`.
    start_line,
    /// `$`: end of text, or of a line under `m`.
    end_line,
    /// `\A`
    start_text,
    /// `\z`
    end_text,
    /// `\b`
    word_boundary,
    /// `\B`
    not_word_boundary,
}

/// `\d`, `\s`, `\w`.
pub type RxPerl {
    digit,
    space,
    word,
}

pub type RxSetOp {
    /// `&&`
    intersection,
    /// `--`
    difference,
    /// `~~`
    symmetric_difference,
}

/// One item of a bracketed class.
pub type RxClassItem {
    /// A single scalar (or byte, under `(?-u)`).
    lit (cp : I64),
    range (lo : I64) (hi : I64),
    /// `[:alpha:]`, `[:^alpha:]`.
    ascii (name : String) (negated : Bool),
    perl (kind : RxPerl) (negated : Bool),
    /// `\p{..}` / `\RxP{..}`.
    unicode (name : String) (negated : Bool),
    /// A nested `[...]`.
    bracket (negated : Bool) (set : RxClassSet),
}

/// A class body: a union of items, or a set operation. The operators are
/// left-associative and bind looser than juxtaposition, as in Rust's
/// `regex`: `[a-z&&[^aeiou]--x]` is `([a-z] && [^aeiou]) -- [x]`.
pub type RxClassSet {
    items (list : List RxClassItem),
    op (kind : RxSetOp) (lhs : RxClassSet) (rhs : RxClassSet),
}

pub type RxGroupKind {
    /// `( )`, with its 1-based capture index.
    capture (index : I64),
    /// `(?RxP<name> )` / `(?<name> )`.
    named (name : String) (index : I64),
    /// `(?: )` or `(?flags: )`.
    non_capture (flags : List RxFlagItem),
}

pub type RxAst {
    /// The empty regex (`` or one side of `a|`).
    empty (span : RegexSpan),
    /// A scalar value; under `(?-u)` an `\xNN` escape is a byte.
    literal (span : RegexSpan) (cp : I64),
    /// `.`
    dot (span : RegexSpan),
    assertion (span : RegexSpan) (kind : RxAssert),
    /// `\d \s \w` and their negations outside a bracket.
    perl (span : RegexSpan) (kind : RxPerl) (negated : Bool),
    /// `\pL`, `\p{Greek}`, `\RxP{..}` outside a bracket.
    unicode_class (span : RegexSpan) (name : String) (negated : Bool),
    bracket (span : RegexSpan) (negated : Bool) (set : RxClassSet),
    /// `max` is `none` for an unbounded repetition.
    repetition (span : RegexSpan) (min : I64) (max : Option I64) (greedy : Bool) (sub : RxAst),
    group (span : RegexSpan) (kind : RxGroupKind) (sub : RxAst),
    /// A standalone `(?flags)`: applies to the rest of the enclosing group.
    set_flags (span : RegexSpan) (flags : List RxFlagItem),
    concat (span : RegexSpan) (items : List RxAst),
    alternation (span : RegexSpan) (items : List RxAst),
}

pub def RxAst.span (a : RxAst) : RegexSpan :=
    match a {
        RxAst.empty sp => sp,
        RxAst.literal sp _ => sp,
        RxAst.dot sp => sp,
        RxAst.assertion sp _ => sp,
        RxAst.perl sp _ _ => sp,
        RxAst.unicode_class sp _ _ => sp,
        RxAst.bracket sp _ _ => sp,
        RxAst.repetition sp _ _ _ _ => sp,
        RxAst.group sp _ _ => sp,
        RxAst.set_flags sp _ => sp,
        RxAst.concat sp _ => sp,
        RxAst.alternation sp _ => sp,
    }

// ─── Rendering (golden tests) ───

def neg_mark (negated : Bool) : String := if negated then "^" else ""

def RxFlag.letter (f : RxFlag) : String :=
    match f {
        RxFlag.case_insensitive => "i",
        RxFlag.multi_line => "m",
        RxFlag.dot_matches_new_line => "s",
        RxFlag.swap_greed => "U",
        RxFlag.ignore_whitespace => "x",
        RxFlag.unicode => "u",
    }

def render_flag (f : RxFlagItem) : String :=
    if f.on then RxFlag.letter f.flag else String.concat "-" (RxFlag.letter f.flag)

def render_flags (fs : List RxFlagItem) : String :=
    String.concat_list (List.map render_flag fs)

def RxAssert.name (k : RxAssert) : String :=
    match k {
        RxAssert.start_line => "^",
        RxAssert.end_line => "$",
        RxAssert.start_text => "\\A",
        RxAssert.end_text => "\\z",
        RxAssert.word_boundary => "\\b",
        RxAssert.not_word_boundary => "\\B",
    }

pub def RxPerl.name (k : RxPerl) : String :=
    match k {
        RxPerl.digit => "d",
        RxPerl.space => "s",
        RxPerl.word => "w",
    }

def RxSetOp.name (k : RxSetOp) : String :=
    match k {
        RxSetOp.intersection => "&&",
        RxSetOp.difference => "--",
        RxSetOp.symmetric_difference => "~~",
    }

def render_item (it : RxClassItem) : String :=
    match it {
        RxClassItem.lit cp => I64.to_string cp,
        RxClassItem.range lo hi => String.concat_list [I64.to_string lo, "-", I64.to_string hi],
        RxClassItem.ascii name negated => String.concat_list ["[:", neg_mark negated, name, ":]"],
        RxClassItem.perl kind negated => String.concat_list ["\\", neg_mark negated, RxPerl.name kind],
        RxClassItem.unicode name negated => String.concat_list ["\\p{", neg_mark negated, name, "}"],
        RxClassItem.bracket negated set => String.concat_list ["[", neg_mark negated, render_set set, "]"],
    }

pub def render_set (s : RxClassSet) : String :=
    match s {
        RxClassSet.items list => List.intercalate " " (List.map render_item list),
        RxClassSet.op kind lhs rhs =>
            String.concat_list ["(", render_set lhs, " ", RxSetOp.name kind, " ", render_set rhs, ")"],
    }

def render_max (max : Option I64) : String :=
    match max {
        Option.some m => I64.to_string m,
        Option.none => "inf",
    }

def render_group_kind (k : RxGroupKind) : String :=
    match k {
        RxGroupKind.capture i => String.concat "cap " (I64.to_string i),
        RxGroupKind.named name i => String.concat_list ["cap ", I64.to_string i, " ", name],
        RxGroupKind.non_capture fs => String.concat "nc " (render_flags fs),
    }

/// `(lit 97)`, `(cat (lit 97) (rep 0 inf greedy dot))`, ...
pub def RxAst.render (a : RxAst) : String :=
    match a {
        RxAst.empty _ => "empty",
        RxAst.literal _ cp => String.concat_list ["(lit ", I64.to_string cp, ")"],
        RxAst.dot _ => "dot",
        RxAst.assertion _ k => String.concat_list ["(assert ", RxAssert.name k, ")"],
        RxAst.perl _ k negated => String.concat_list ["(perl ", neg_mark negated, RxPerl.name k, ")"],
        RxAst.unicode_class _ name negated => String.concat_list ["(prop ", neg_mark negated, name, ")"],
        RxAst.bracket _ negated set => String.concat_list ["(class ", neg_mark negated, "[", render_set set, "])"],
        RxAst.repetition _ min max greedy sub =>
            String.concat_list ["(rep ", I64.to_string min, " ", render_max max,
                if greedy then " " else " lazy ", RxAst.render sub, ")"],
        RxAst.group _ k sub => String.concat_list ["(group ", render_group_kind k, " ", RxAst.render sub, ")"],
        RxAst.set_flags _ fs => String.concat_list ["(flags ", render_flags fs, ")"],
        RxAst.concat _ items => String.concat_list ["(cat ", List.intercalate " " (List.map RxAst.render items), ")"],
        RxAst.alternation _ items => String.concat_list ["(alt ", List.intercalate " " (List.map RxAst.render items), ")"],
    }
