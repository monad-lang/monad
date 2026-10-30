/// The byte-level vocabulary the protocol modules share: the ASCII control
/// bytes both framings care about, and the UTF-8 shape tests that position
/// conversion needs.
///
/// It is a module of its own rather than a section of one of its two users,
/// because both of them need ALL of it and neither owns it. `framing` needs
/// `\r` and `\n` to find where a header ends; `position` needs `\n` and the
/// two encoding predicates to find where a line ends and how wide a character
/// is. Putting the constants in `framing` would make line splitting depend on
/// the frame reader, which is backwards.
///
/// THE THREE COUNTS A STRING HAS ARE NOT THE SAME COUNT, and that is the fact
/// these predicates exist to keep straight. A character is one code point, but
/// it is one to four BYTES in UTF-8 and one to two UTF-16 CODE UNITS, and it is
/// one COLUMN if you count the way `lang`'s `Location.column` does. Every one
/// of the three is needed by something in this toolkit, and each of the three
/// shortcuts between them is wrong on a different input -- see `position`'s
/// module doc, which is where that gets pinned.
///
/// Every predicate is written with `U8.gt` and a negation rather than with the
/// range's lower bound directly, because `U8.gt` is `pub`
/// (`init/src/number.mo:268`) and `U8.lt` is not. Reaching for the non-`pub`
/// name would draw a `cross_mote_package_private` warning on every check of
/// every consumer, so the bound each predicate really means is spelled out in
/// its doc comment instead of in its code.

/// `\r`. Part of a header terminator in `framing`, part of a line terminator in
/// `position` -- the same byte wearing two hats, which is why it lives here.
pub def byte_cr : U8 := 13u8

/// `\n`. The message delimiter in MCP's framing and the line delimiter
/// everywhere else.
pub def byte_lf : U8 := 10u8

/// The space that may surround a header's value.
pub def byte_space : U8 := 32u8

/// The largest byte that is still ASCII (`0x7f`), i.e. `DEL`.
pub def byte_ascii_max : U8 := 127u8

/// Does this byte stand alone, i.e. is it ASCII?
///
/// `U8.gt b 127u8` negated: `b <= 0x7f`.
pub def is_ascii_byte (b : U8) : Bool :=
  Bool.not (U8.gt b byte_ascii_max)

/// Is `b` a UTF-8 continuation byte, `0b10xxxxxx`?
///
/// `0x80 <= b <= 0xbf`, written as "greater than `0x7f` and not greater than
/// `0xbf`". This is the rule `String.trailing_chars` counts by on BOTH runtimes
/// -- `rust/core/src/core_native.rs` and `runtime/src/runtime.c` each test
/// `(b & 0xC0) != 0x80` -- and the rule `lang/parser/position.mo`'s
/// `is_utf8_continuation_byte` states (`lang/parser/position.mo:108`), which is
/// where this formulation is copied from. It is copied rather than imported
/// because that module is not `pub` and `lang` is not a dependency of this
/// mote; a `pub` re-export would put the whole compiler in every consumer's
/// closure for one three-byte test.
///
/// A byte that is NOT a continuation byte is either ASCII or a lead byte, which
/// is the property both callers actually want: it is the test for "a character
/// starts here".
#[partial]
pub def is_continuation_byte (b : U8) : Bool :=
  U8.gt b 127u8 && Bool.not (U8.gt b 191u8)

/// Is `b` the lead byte of a FOUR-byte UTF-8 sequence, `0b11110xxx`?
///
/// `0xf0 <= b <= 0xf7`, written as "greater than `0xef`". Only these sequences
/// encode a code point above `U+FFFF`, which is exactly the set that needs a
/// surrogate PAIR and so counts as two UTF-16 code units rather than one. That
/// is the whole reason this predicate exists: it is the only place the byte
/// encoding tells you the unit count is not one.
///
/// Bytes `0xf5`-`0xf7` are not valid UTF-8 lead bytes, and the test reports
/// them as four-byte leads anyway. That is deliberate: this is a COUNTING
/// predicate, not a validator, and the count it produces for malformed input is
/// no more wrong than any other answer would be. Nothing here rejects a
/// malformed sequence, so nothing here needs to agree with a validator about
/// one.
#[partial]
pub def is_four_byte_lead (b : U8) : Bool :=
  U8.gt b 239u8

/// UTF-16 code units this byte contributes: 0 for a continuation byte, 2 for
/// the lead of a four-byte sequence, 1 otherwise.
///
/// Adding this over a character's bytes gives 2 for an astral character and 1
/// for everything else, which is the UTF-16 rule stated in one line. Note what
/// it does NOT do: it never looks at the continuation bytes' own values, so a
/// truncated or over-long sequence is miscounted rather than rejected. That is
/// the right trade for a position encoder, which runs on every diagnostic and
/// must not have opinions about text it is only counting.
#[partial]
pub def utf16_units_of_byte (b : U8) : I64 :=
  if is_continuation_byte b
  then 0
  else if is_four_byte_lead b then 2 else 1
