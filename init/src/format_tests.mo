/// Parser/padding tests for `init/src/format.mo`.
///
/// These call `Format.parse` and the padding helpers DIRECTLY — no `fmt!`
/// — so they are checkable and runnable by any host, including one that
/// cannot expand a term macro yet. The macro's own end-to-end behaviour is
/// pinned by `slow_tests/src/fmt_macro_tests.mo` and by the Rust host's
/// `eval::format_test`.
use init::format {Format.apply_align, Format.parse, FormatAlign, FormatPiece}

def literal_is (p : FormatPiece) (expected : String) : Bool :=
    match p {
        FormatPiece.literal text => String.beq text expected,
        FormatPiece.hole _ _ => false,
    }

def align_is_left (a : FormatAlign) : Bool :=
    match a { FormatAlign.left => true, FormatAlign.right _ => false, FormatAlign.centre _ => false }

def align_is_right (a : FormatAlign) (expected : I64) : Bool :=
    match a { FormatAlign.right w => I64.beq w expected, FormatAlign.left => false, FormatAlign.centre _ => false }

def hole_is_left (p : FormatPiece) (name : String) : Bool :=
    match p {
        FormatPiece.hole n a => String.beq n name && align_is_left a,
        FormatPiece.literal _ => false,
    }

def hole_is_right (p : FormatPiece) (name : String) (width : I64) : Bool :=
    match p {
        FormatPiece.hole n a => String.beq n name && align_is_right a width,
        FormatPiece.literal _ => false,
    }

def rest_is_empty (pieces : List FormatPiece) : Bool :=
    match pieces { empty => true, cons _ _ => false }

/// Concatenate every LITERAL piece's text; a hole marks itself so a test
/// using this can prove there was none. Adjacent literals are separate
/// pieces (`"{{x}}"` parses as `"{"`, `"x"`, `"}"`), so tests about the
/// reconstructed text use this rather than a piece-count.
def literals_text (pieces : List FormatPiece) : String :=
    match pieces {
        empty => "",
        cons p rest => match p {
            FormatPiece.literal text => String.concat text (literals_text rest),
            FormatPiece.hole _ _ => "<hole>",
        },
    }

/// `"plain"` — one literal piece, no holes.
#[test]
def test_parse_literal_only : Bool :=
    match Format.parse "plain" {
        err _ => false,
        ok pieces => match pieces {
            cons p rest => literal_is p "plain" && rest_is_empty rest,
            empty => false,
        },
    }

/// `"<{word}>"` — literal, hole, literal; the hole names `word` and has
/// no alignment.
#[test]
def test_parse_named_hole : Bool :=
    match Format.parse "<{word}>" {
        err _ => false,
        ok pieces => match pieces {
            cons first rest => match rest {
                cons middle rest2 => match rest2 {
                    cons last tail =>
                        literal_is first "<" && hole_is_left middle "word"
                            && literal_is last ">" && rest_is_empty tail,
                    empty => false,
                },
                empty => false,
            },
            empty => false,
        },
    }

/// `"{n:>6}"` carries a right alignment and width 6.
#[test]
def test_parse_alignment_and_width : Bool :=
    match Format.parse "{n:>6}" {
        err _ => false,
        ok pieces => match pieces {
            cons p rest => hole_is_right p "n" 6 && rest_is_empty rest,
            empty => false,
        },
    }

/// `{{`/`}}` are literal braces, not holes.
#[test]
def test_parse_brace_escapes : Bool :=
    match Format.parse "{{x}}" {
        err _ => false,
        ok pieces => String.beq (literals_text pieces) "{x}",
    }

/// An unclosed hole is an error naming the offset.
#[test]
def test_parse_rejects_an_unclosed_hole : Bool :=
    match Format.parse "oops {name" {
        ok _ => false,
        err message => String.contains message "unclosed",
    }

/// An unknown specifier is an error naming the spec.
#[test]
def test_parse_rejects_an_unknown_spec : Bool :=
    match Format.parse "{n:x}" {
        ok _ => false,
        err message => String.contains message "unknown format spec",
    }

/// `{}` has nothing to refer to (there is no positional argument), so it
/// is rejected at parse time instead of emitting `e_var ""`.
#[test]
def test_parse_rejects_an_unnamed_hole : Bool :=
    match Format.parse "{}" {
        ok _ => false,
        err message => String.contains message "must name a variable",
    }

/// The same for `{:>4}`: a width does not supply a name either.
#[test]
def test_parse_rejects_a_width_without_a_name : Bool :=
    match Format.parse "{:>4}" {
        ok _ => false,
        err message => String.contains message "must name a variable",
    }

/// A width is a MINIMUM: padding never truncates.
#[test]
def test_apply_align_pads_and_never_truncates : Bool :=
    String.beq (Format.apply_align (FormatAlign.right 4) "ab") "  ab"
        && String.beq (Format.apply_align (FormatAlign.right 1) "ab") "ab"
        && String.beq (Format.apply_align FormatAlign.left "ab") "ab"
        && String.beq (Format.apply_align (FormatAlign.centre 4) "ab") " ab "
