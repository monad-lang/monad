/// Base64 decoding tests — `Strings.base64_decode`, which is what
/// `Middleware.auth_basic` uses to see the RFC 7617 credential as
/// `user:pass` rather than as encoded text.
///
/// The decoder is strict, so the negative cases matter as much as the
/// positive ones: a credential that is not valid base64 must be
/// rejected, not decoded as far as it can be.

use http::strings {
  Strings.base64_decode, Strings.parse_i64, Strings.parse_u16_bounded,
}

/// True when the decode succeeded and yields exactly `want`.
def decoded_is (got : Result String (List U8)) (want : String) : Bool :=
  match got {
    Result.err _ => false,
    Result.ok bytes => String.from_list bytes == want
  }

/// True when the decode failed.
def decode_fails (got : Result String (List U8)) : Bool :=
  match got {
    Result.err _ => true,
    Result.ok _ => false
  }

// ── decoding ───────────────────────────────────────────────────────────

/// No padding: 12 characters of credential.
#[test]
def test_base64_plain : Bool :=
  decoded_is (Strings.base64_decode "YWRtaW46c2VjcmV0") "admin:secret"

/// No padding, a different length.
#[test]
def test_base64_user_pass : Bool :=
  decoded_is (Strings.base64_decode "dXNlcjpwYXNz") "user:pass"

/// One `=`: a single leftover byte.
#[test]
def test_base64_one_pad : Bool :=
  decoded_is (Strings.base64_decode "YQ==") "a"

/// Two `=`: two leftover bytes.
#[test]
def test_base64_two_pad : Bool :=
  decoded_is (Strings.base64_decode "YWI=") "ab"

/// The last two characters of the standard alphabet: `Pz8/` is "???"
/// and `by9+` is "o/~", so both `/` and `+` are exercised.
#[test]
def test_base64_slash_and_plus : Bool :=
  Bool.and (decoded_is (Strings.base64_decode "Pz8/") "???")
    (decoded_is (Strings.base64_decode "by9+") "o/~")

/// The empty string decodes to no bytes.
#[test]
def test_base64_empty : Bool :=
  decoded_is (Strings.base64_decode "") ""

/// The std decoder accepts an untruncated final group without padding; the
/// local decoder this replaced required a multiple of four characters.
#[test]
def test_base64_unpadded_tail : Bool :=
  decoded_is (Strings.base64_decode "YQ") "a"

// ── rejection ──────────────────────────────────────────────────────────

/// A length that is not a whole number of 4-character groups.
#[test]
def test_base64_bad_length : Bool :=
  Bool.and (decode_fails (Strings.base64_decode "YQ="))
    (decode_fails (Strings.base64_decode "YWRtaW46c2VjcmV0="))

/// A character from outside the alphabet (here `!` and a space).
#[test]
def test_base64_bad_char : Bool :=
  Bool.and (decode_fails (Strings.base64_decode "!!!!"))
    (decode_fails (Strings.base64_decode "YQ =="))

/// Padding in the middle, and padding followed by more data.
#[test]
def test_base64_padding_only_at_the_end : Bool :=
  Bool.and (decode_fails (Strings.base64_decode "YQ==YQ=="))
    (decode_fails (Strings.base64_decode "YWI=X"))

/// `YR==` and `YWI=` carry non-zero bits in the last character that the
/// padding discards. `YQ==`/`YWI=` are the canonical spellings of the
/// same bytes, and only those are accepted.
#[test]
def test_base64_non_canonical_padding : Bool :=
  Bool.and (decode_fails (Strings.base64_decode "YR=="))
    (decode_fails (Strings.base64_decode "YWJ="))

/// `=` alone (or as a group of its own) is never an encoding of anything.
#[test]
def test_base64_padding_alone : Bool :=
  decode_fails (Strings.base64_decode "====")

// ── bounded decimal parsing ────────────────────────────────────────────
//
// `parse_u16_bounded`/`parse_i64` are the only place a digit run becomes a
// number. The bound is what turns an out-of-range value into an error instead
// of a truncated one that looks plausible: an unbounded `U16` accumulation
// turned the port `70000` into `4464`, and an unbounded `I64` accumulation
// would turn an absurd `Content-Length` into a small positive one.

/// True when a bounded parse succeeded with exactly `want`.
def st_u16_is (got : Result String U16) (want : U16) : Bool :=
  match got {
    Result.err _ => false,
    Result.ok v => U16.beq v want
  }

/// True when a bounded parse failed.
def st_u16_fails (got : Result String U16) : Bool :=
  match got {
    Result.err _ => true,
    Result.ok _ => false
  }

/// True when an `I64` parse succeeded with exactly `want`.
def st_i64_is (got : Option I64) (want : I64) : Bool :=
  match got {
    Option.none => false,
    Option.some v => I64.beq v want
  }

/// True when an `I64` parse failed.
def st_i64_fails (got : Option I64) : Bool :=
  match got {
    Option.none => true,
    Option.some _ => false
  }

#[test]
def test_u16_simple : Bool :=
  st_u16_is (Strings.parse_u16_bounded "port" (String.to_list "8080")) 8080u16

#[test]
def test_u16_zero : Bool :=
  st_u16_is (Strings.parse_u16_bounded "port" (String.to_list "0")) 0u16

/// 65535 is the last representable value, so it must parse.
#[test]
def test_u16_max_ok : Bool :=
  st_u16_is (Strings.parse_u16_bounded "port" (String.to_list "65535")) 65535u16

/// 65536 is the first value past the range: it must fail, not wrap to 0.
#[test]
def test_u16_over_max_fails : Bool :=
  st_u16_fails (Strings.parse_u16_bounded "port" (String.to_list "65536"))

/// The motivating case. `70000 mod 65536` is `4464`, which is a usable-looking
/// port, so truncation here is silent where an error is not.
#[test]
def test_u16_truncating_value_fails : Bool :=
  st_u16_fails (Strings.parse_u16_bounded "port" (String.to_list "70000"))

/// A run long enough to wrap repeatedly still fails, rather than landing on
/// whatever the accumulated `U16` happens to hold.
#[test]
def test_u16_long_digit_run_fails : Bool :=
  st_u16_fails (Strings.parse_u16_bounded "port" (String.to_list "99999999999999999999"))

#[test]
def test_u16_empty_fails : Bool :=
  st_u16_fails (Strings.parse_u16_bounded "port" List.empty)

#[test]
def test_u16_non_digit_fails : Bool :=
  st_u16_fails (Strings.parse_u16_bounded "port" (String.to_list "80a0"))

#[test]
def test_i64_simple : Bool :=
  st_i64_is (Strings.parse_i64 "1234") 1234i64

#[test]
def test_i64_zero : Bool :=
  st_i64_is (Strings.parse_i64 "0") 0i64

/// Header values carry surrounding whitespace.
#[test]
def test_i64_trims : Bool :=
  st_i64_is (Strings.parse_i64 " 42 ") 42i64

#[test]
def test_i64_max_ok : Bool :=
  st_i64_is (Strings.parse_i64 "9223372036854775807") 9223372036854775807i64

/// One past `I64.max`.
#[test]
def test_i64_over_max_fails : Bool :=
  st_i64_fails (Strings.parse_i64 "9223372036854775808")

#[test]
def test_i64_long_digit_run_fails : Bool :=
  st_i64_fails (Strings.parse_i64 "999999999999999999999999999999")

#[test]
def test_i64_empty_fails : Bool :=
  st_i64_fails (Strings.parse_i64 "")

#[test]
def test_i64_non_digit_fails : Bool :=
  st_i64_fails (Strings.parse_i64 "12x4")

/// A length is non-negative, and `-` is not a digit, so a signed value is
/// rejected rather than parsed as a negative length.
#[test]
def test_i64_negative_fails : Bool :=
  st_i64_fails (Strings.parse_i64 "-5")
