/// End-to-end `fmt!` tests.
///
/// These need a compiler whose term-macro expansion (a) unwraps a
/// `quote`-bodied macro, (b) resolves a macro defined in another module
/// (`use init::format {fmt}`), and (c) evaluates the term-position `meta!`
/// intrinsic. That is THIS tree's self-hosted compiler; an older installed
/// nightly predates all three and cannot compile this file. See
/// `plans/implementations/format-strings.md`.
use init::format {fmt}

/// No holes: the literal is the whole result.
#[test]
def test_fmt_literal : Bool :=
    String.beq (fmt! "plain") "plain"

/// One hole, naming an in-scope variable.
#[test]
def test_fmt_hole : Bool :=
    let word : String := "yo" in
    String.beq (fmt! "<{word}>") "<yo>"

/// `:>N` is a right-aligned MINIMUM width.
#[test]
def test_fmt_width : Bool :=
    let n : I64 := 7 in
    String.beq (fmt! "{n:>4}") "   7"

/// A value already wider than the width is not truncated.
#[test]
def test_fmt_width_never_truncates : Bool :=
    let n : I64 := 12345 in
    String.beq (fmt! "{n:>2}") "12345"

/// `{{`/`}}` are literal braces, not holes.
#[test]
def test_fmt_brace_escape : Bool :=
    String.beq (fmt! "{{x}}") "{x}"

/// Literal text and several holes compose into one result.
#[test]
def test_fmt_mixed : Bool :=
    let name : String := "Ada" in
    let n : I64 := 7 in
    String.beq (fmt! "hi {name}, you are {n:>4}") "hi Ada, you are    7"

/// A `Bool` hole resolves through the format module's `ToString Bool`
/// instance (the blanket `[ToString A] FmtDisplay A` bridge).
#[test]
def test_fmt_bool : Bool :=
    let flag : Bool := true in
    String.beq (fmt! "{flag}") "true"
