/// String/byte helpers for the `http` mote — Layer 0, pure Monad.
///
/// Ships the small byte-level primitives the URI parser and percent-encoding
/// need: a `split_on`, byte predicates, hex (de)coding, and list-slicing
/// helpers. The stdlib has no `String.split_on` native, so it lives here.
/// `Strings` is an empty namespace type (never constructed) so the helpers
/// resolve cross-module the same way `Headers.*` does.

use std::base64 {B64.decode_std, B64Error.to_string}

type Strings {}

// ── split_on ────────────────────────────────────────────────────────────

pub def Strings.split_on (delim : String) (s : String) : List String :=
  Strings.split_on_bytes (String.to_list delim) (String.to_list s)

def Strings.split_on_bytes (delim : List U8) (input : List U8) : List String :=
  match delim {
    List.empty => List.singleton (String.from_list input),
    List.cons _ _ => Strings.split_on_go delim input List.empty
  }

#[terminating]
def Strings.split_on_go (delim : List U8) (input : List U8) (acc : List U8) : List String :=
  match input {
    List.empty => List.singleton (String.from_list (List.reverse acc)),
    List.cons x rest =>
      if Strings.list_starts_with delim input
      then List.cons (String.from_list (List.reverse acc)) (Strings.split_on_go delim (Strings.list_drop_prefix delim input) List.empty)
      else Strings.split_on_go delim rest (List.cons x acc)
  }

// ── list slicing ───────────────────────────────────────────────────────

pub def Strings.list_starts_with (prefix : List U8) (xs : List U8) : Bool :=
  match prefix {
    List.empty => true,
    List.cons p ps =>
      match xs {
        List.empty => false,
        List.cons x xs2 =>
          if U8.beq p x
          then Strings.list_starts_with ps xs2
          else false
      }
  }

pub def Strings.list_drop_prefix (prefix : List U8) (xs : List U8) : List U8 :=
  match prefix {
    List.empty => xs,
    List.cons _ ps =>
      match xs {
        List.empty => List.empty,
        List.cons _ xs2 => Strings.list_drop_prefix ps xs2
      }
  }

#[terminating]
pub def Strings.drop_bytes (n : I64) (xs : List U8) : List U8 :=
  if I64.beq n 0
  then xs
  else
    match xs {
      List.empty => List.empty,
      List.cons _ rest => Strings.drop_bytes (I64.sub n 1) rest
    }

pub def Strings.split_at_byte (c : U8) (bytes : List U8) : Pair (List U8) (List U8) :=
  Strings.split_at_byte_go c bytes List.empty

def Strings.split_at_byte_go (c : U8) (bytes : List U8) (acc : List U8) : Pair (List U8) (List U8) :=
  match bytes {
    List.empty => Pair.pair (List.reverse acc) List.empty,
    List.cons x rest =>
      if U8.beq x c
      then Pair.pair (List.reverse acc) rest
      else Strings.split_at_byte_go c rest (List.cons x acc)
  }

def Strings.split_at_byte_opt (c : U8) (bytes : List U8) : Option (Pair (List U8) (List U8)) :=
  Strings.split_at_byte_opt_go c bytes List.empty

def Strings.split_at_byte_opt_go (c : U8) (bytes : List U8) (acc : List U8) : Option (Pair (List U8) (List U8)) :=
  match bytes {
    List.empty => Option.none,
    List.cons x rest =>
      if U8.beq x c
      then Option.some (Pair.pair (List.reverse acc) rest)
      else Strings.split_at_byte_opt_go c rest (List.cons x acc)
  }

def Strings.option_from (bs : List U8) : Option String :=
  match bs {
    List.empty => Option.none,
    List.cons _ _ => Option.some (String.from_list bs)
  }

// ── byte predicates ────────────────────────────────────────────────────

def Strings.is_upper_alpha (b : U8) : Bool :=
  if U8.lt b 65u8 then false
  else U8.lt b 91u8

def Strings.is_lower_alpha (b : U8) : Bool :=
  if U8.lt b 97u8 then false
  else U8.lt b 123u8

def Strings.is_alpha (b : U8) : Bool :=
  if Strings.is_upper_alpha b then true
  else Strings.is_lower_alpha b

def Strings.is_digit (b : U8) : Bool :=
  if U8.lt b 48u8 then false
  else U8.lt b 58u8

def Strings.is_alnum (b : U8) : Bool :=
  if Strings.is_alpha b then true
  else Strings.is_digit b

/// RFC 3986 unreserved: ALPHA / DIGIT / "-" / "." / "_" / "~"
def Strings.is_unreserved (b : U8) : Bool :=
  if Strings.is_alnum b then true
  else if U8.beq b 45u8 then true
  else if U8.beq b 46u8 then true
  else if U8.beq b 95u8 then true
  else U8.beq b 126u8

def Strings.is_scheme_char (b : U8) : Bool :=
  if Strings.is_alnum b then true
  else if U8.beq b 43u8 then true
  else if U8.beq b 45u8 then true
  else U8.beq b 46u8

def Strings.is_valid_scheme (bytes : List U8) : Bool :=
  match bytes {
    List.empty => false,
    List.cons first rest =>
      if Strings.is_alpha first
      then Strings.is_valid_scheme_rest rest
      else false
  }

def Strings.is_valid_scheme_rest (bytes : List U8) : Bool :=
  match bytes {
    List.empty => true,
    List.cons b rest =>
      if Strings.is_scheme_char b
      then Strings.is_valid_scheme_rest rest
      else false
  }

// ── hex ─────────────────────────────────────────────────────────────────

def Strings.hex_char_of_nibble (n : U8) : U8 :=
  if U8.lt n 10u8 then U8.add n 48u8 else U8.add n 55u8

def Strings.hex_value (c : U8) : Option U8 :=
  if U8.lt c 48u8 then Option.none
  else if U8.lt c 58u8 then Option.some (U8.sub c 48u8)
  else if U8.lt c 65u8 then Option.none
  else if U8.lt c 71u8 then Option.some (U8.sub c 55u8)
  else if U8.lt c 97u8 then Option.none
  else if U8.lt c 103u8 then Option.some (U8.sub c 87u8)
  else Option.none

/// A hex nibble (0..15, what `hex_value` yields) as an `I64`. Spelled out
/// digit by digit like `i64_of_digit` -- no U8→I64 conversion exists.
def Strings.i64_of_nibble (v : U8) : I64 :=
  if v == 0u8 then 0i64
  else if v == 1u8 then 1i64
  else if v == 2u8 then 2i64
  else if v == 3u8 then 3i64
  else if v == 4u8 then 4i64
  else if v == 5u8 then 5i64
  else if v == 6u8 then 6i64
  else if v == 7u8 then 7i64
  else if v == 8u8 then 8i64
  else if v == 9u8 then 9i64
  else if v == 10u8 then 10i64
  else if v == 11u8 then 11i64
  else if v == 12u8 then 12i64
  else if v == 13u8 then 13i64
  else if v == 14u8 then 14i64
  else 15i64

def Strings.decode_hex_pair (h1 : U8) (h2 : U8) : Result String U8 :=
  match Strings.hex_value h1 {
    Option.none => Result.err "invalid hex digit",
    Option.some v1 =>
      match Strings.hex_value h2 {
        Option.none => Result.err "invalid hex digit",
        Option.some v2 => Result.ok (U8.add (U8.mul v1 16u8) v2)
      }
  }

// ── base64 ──────────────────────────────────────────────────────────────
// RFC 4648 §4 decoding, for `Middleware.auth_basic`: the HTTP Basic
// credential is base64 (RFC 7617), so a predicate that claims to see the
// decoded "user:pass" has to actually decode it.
//
// The decoder is `std::base64`'s: strict about characters, padding
// placement and canonical trailing bits. Its one difference from the
// local decoder this replaced is that an unpadded final group (`YQ` as
// well as `YQ==`) is accepted. A malformed credential is a rejection,
// not a best-effort guess.

/// Decode a whole standard-alphabet base64 string to the bytes it encodes.
/// `std`'s reasons are rendered here: this module's seam reports text.
pub def Strings.base64_decode (s : String) : Result String (List U8) :=
  match B64.decode_std s {
    Result.ok bs => Result.ok bs,
    Result.err e => Result.err (B64Error.to_string e)
  }

/// Map an ASCII digit byte ('0'..'9') to a U16, or none for non-digits.
/// The stdlib has no U8→U16 conversion, so the 10 cases are explicit.
def Strings.u16_of_digit (d : U8) : Option U16 :=
  if U8.beq d 48u8 then Option.some 0u16
  else if U8.beq d 49u8 then Option.some 1u16
  else if U8.beq d 50u8 then Option.some 2u16
  else if U8.beq d 51u8 then Option.some 3u16
  else if U8.beq d 52u8 then Option.some 4u16
  else if U8.beq d 53u8 then Option.some 5u16
  else if U8.beq d 54u8 then Option.some 6u16
  else if U8.beq d 55u8 then Option.some 7u16
  else if U8.beq d 56u8 then Option.some 8u16
  else if U8.beq d 57u8 then Option.some 9u16
  else Option.none

// ── bounded decimal parsing ─────────────────────────────────────────────
//
// `u16_of_digit` gives a digit's value; these turn a digit run into a number,
// and they are the only place a byte list becomes a `U16` or an `I64`. Both
// bound the value BEFORE multiplying, so no intermediate ever leaves the
// target range. An unbounded `U16.mul acc 10u16` truncates silently instead --
// `"70000"` accumulated to `4464`, which is how an out-of-range port became a
// plausible wrong one rather than an error.

/// Would `acc * 10 + digit` exceed 65535?
///
/// Checked before multiplying, so `acc` itself never leaves `U16` range:
/// `acc <= 6552` always fits, and `acc == 6553` fits only while the next digit
/// is at most 5. The largest intermediate is `6553 * 10 + 9 = 65539`, which is
/// why this is safe even though the comparison happens in `U16`.
def Strings.u16_overflows (acc : U16) (digit : U16) : Bool :=
  if U16.gt acc 6553u16
  then true
  else if U16.beq acc 6553u16
  then U16.gt digit 5u16
  else false

/// Parse a run of decimal digits into a `U16`. Fails on an empty run, on a
/// non-digit, and on any value above 65535. `label` names the field so each
/// caller keeps its own wording ("port", "status").
def Strings.parse_u16_bounded (label : String) (bytes : List U8) : Result String U16 :=
  match bytes {
    List.empty => Result.err (String.concat label " is empty"),
    List.cons _ _ => Strings.parse_u16_bounded_go label bytes 0u16
  }

#[terminating]
def Strings.parse_u16_bounded_go (label : String) (bytes : List U8) (acc : U16) : Result String U16 :=
  match bytes {
    List.empty => Result.ok acc,
    List.cons d rest =>
      match Strings.u16_of_digit d {
        Option.none => Result.err (String.concat "invalid " (String.concat label " digit")),
        Option.some v =>
          if Strings.u16_overflows acc v
          then Result.err (String.concat label " out of range")
          else Strings.parse_u16_bounded_go label rest (U16.add (U16.mul acc 10u16) v)
      }
  }

/// Map an ASCII digit byte ('0'..'9') to I64 (no U8→I64 conversion exists).
def Strings.i64_of_digit (d : U8) : Option I64 :=
  if U8.beq d 48u8 then Option.some 0i64
  else if U8.beq d 49u8 then Option.some 1i64
  else if U8.beq d 50u8 then Option.some 2i64
  else if U8.beq d 51u8 then Option.some 3i64
  else if U8.beq d 52u8 then Option.some 4i64
  else if U8.beq d 53u8 then Option.some 5i64
  else if U8.beq d 54u8 then Option.some 6i64
  else if U8.beq d 55u8 then Option.some 7i64
  else if U8.beq d 56u8 then Option.some 8i64
  else if U8.beq d 57u8 then Option.some 9i64
  else Option.none

/// Would `acc * 10 + digit` exceed 9223372036854775807? The same pre-multiply
/// discipline as `u16_overflows`, against `I64.max`.
def Strings.i64_overflows (acc : I64) (digit : I64) : Bool :=
  if I64.gt acc 922337203685477580i64
  then true
  else if I64.beq acc 922337203685477580i64
  then I64.gt digit 7i64
  else false

/// Parse a trimmed run of decimal digits into an `I64`. `Option.none` on an
/// empty run, on a non-digit, and on a value that would leave `I64` range --
/// so an absurd `Content-Length` is rejected rather than wrapping into a
/// plausible small one.
pub def Strings.parse_i64 (s : String) : Option I64 :=
  let bytes := String.to_list (String.trim s) in
  if List.is_empty bytes
  then Option.none
  else Strings.parse_i64_go bytes 0i64

#[terminating]
def Strings.parse_i64_go (bytes : List U8) (acc : I64) : Option I64 :=
  match bytes {
    List.empty => Option.some acc,
    List.cons d rest =>
      match Strings.i64_of_digit d {
        Option.none => Option.none,
        Option.some v =>
          if Strings.i64_overflows acc v
          then Option.none
          else Strings.parse_i64_go rest (I64.add (I64.mul acc 10i64) v)
      }
  }

/// Constant-time-ish equality: compares every byte of equal-length strings
/// without the early exit `String.beq` takes. Lengths are not hidden. Use
/// this for CSRF tokens and other secret comparisons.
pub def Strings.ct_eq (a : String) (b : String) : Bool :=
  if Bool.not (I64.beq (String.length a) (String.length b))
  then false
  else Strings.ct_eq_go (String.to_list a) (String.to_list b) true

#[terminating]
def Strings.ct_eq_go (a : List U8) (b : List U8) (same : Bool) : Bool :=
  match a {
    List.empty => same,
    List.cons x xs =>
      match b {
        List.empty => false,
        List.cons y ys => Strings.ct_eq_go xs ys (Bool.and same (U8.beq x y))
      }
  }
