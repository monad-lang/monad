// Char literals: `'M'`, `'\n'`, `'λ'`
//
// A `'c'` literal carries a `Char` -- ONE Unicode codepoint, mirroring the
// Rust reference's `Literal::Char`. `Char` is declared `of_bytes (List U8)`
// (`init/prelude.mo`) and holds that codepoint's UTF-8 bytes, so multi-byte
// characters round-trip intact.
//
// The same `\`-escapes string literals accept work here: `\n`, `\t`, `\\`,
// `\'`, `\"`, `\r`, `\b`, `\f`. (`\u{...}` is NOT supported -- write the
// character itself, as `lambda` does below.)
//
// IMPORTANT -- `Char` is a stub type. It has no operations at all: no
// `Char.*` functions, no `BEq`, no `ToString`. So a `Char` can be written,
// typed, passed around and stored, but nothing can inspect or compare one
// yet. That is why this example asserts on the literals' TYPE rather than
// their value. See AGENTS.md's `Char` item before reaching for it.
//
// Usage: monad test examples/char_literals.mo

/// A plain ASCII character.
def letter : Char := 'M'

/// An escape -- resolved to the real control character, not left as the
/// two-character sequence `\` `n`.
def newline : Char := '\n'

/// An escaped single quote, which would otherwise close the literal.
def single_quote : Char := '\''

/// A multi-byte codepoint, written directly.
def lambda : Char := 'λ'

/// `Char` has no operations, so the most a test can do is confirm the
/// literals type-check as `Char` and can be threaded through ordinary code.
def identity_char (c : Char) : Char := c

#[test]
def test_char_literals_typecheck : Bool :=
    // Each of these is a `Char` by its own declared signature above; passing
    // them through a `Char -> Char` function is the strongest observation
    // available without any `Char` operation to call.
    match Option.some (identity_char letter) {
        Option.some _ => true,
        Option.none => false,
    }

#[test]
def test_char_escapes_and_multibyte_typecheck : Bool :=
    match Option.some [identity_char newline, identity_char single_quote, identity_char lambda] {
        Option.some _ => true,
        Option.none => false,
    }
