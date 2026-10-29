/// Codec vectors and strict-decoding rejections for `std::base64`
/// (formerly `motes/crypto`'s `b64.mo`).
///
/// RFC 4648 §10 standard vectors, the URL-alphabet forms, and the strict
/// decode rejections. Pure (`Bool`), so both hosts run them.

use std::base64 {
  B64.encode_std, B64.decode_std, B64Error, B64Error.to_string,
  B64Url.encode, B64Url.decode,
}

// `BEq (List A)` lives here, not in the ambient prelude; the empty brace
// list pulls the module (and its instances) into scope.
use std::list {}

// ── helpers ─────────────────────────────────────────────────────────────

def decoded_text (r : Result B64Error (List U8)) (expected : String) : Bool :=
  match r {
    Result.ok bs => bs == String.to_list expected,
    Result.err _ => false
  }

def decoded_bytes (r : Result B64Error (List U8)) (expected : List U8) : Bool :=
  match r {
    Result.ok bs => bs == expected,
    Result.err _ => false
  }

def rejected_with (r : Result B64Error (List U8)) (msg : String) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => B64Error.to_string e == msg
  }

/// `0xfb 0xff` exercises both alphabet-specific characters: `+`/`/` in the
/// standard alphabet, `-`/`_` in the URL one.
def edge_bytes : List U8 := [0xfbu8, 0xffu8]

def one_zero_byte : List U8 := [0u8]

// ── standard base64 (RFC 4648 §10) ──────────────────────────────────────

#[test]
def test_b64_std_rfc4648_encode : Bool :=
  B64.encode_std (String.to_list "") == ""
  && B64.encode_std (String.to_list "f") == "Zg=="
  && B64.encode_std (String.to_list "fo") == "Zm8="
  && B64.encode_std (String.to_list "foo") == "Zm9v"
  && B64.encode_std (String.to_list "foob") == "Zm9vYg=="
  && B64.encode_std (String.to_list "fooba") == "Zm9vYmE="
  && B64.encode_std (String.to_list "foobar") == "Zm9vYmFy"

#[test]
def test_b64_std_rfc4648_decode : Bool :=
  decoded_text (B64.decode_std "") ""
  && decoded_text (B64.decode_std "Zg==") "f"
  && decoded_text (B64.decode_std "Zm8=") "fo"
  && decoded_text (B64.decode_std "Zm9v") "foo"
  && decoded_text (B64.decode_std "Zm9vYg==") "foob"
  && decoded_text (B64.decode_std "Zm9vYmE=") "fooba"
  && decoded_text (B64.decode_std "Zm9vYmFy") "foobar"

#[test]
def test_b64_std_accepted_unpadded : Bool :=
  decoded_text (B64.decode_std "Zg") "f"
  && decoded_text (B64.decode_std "Zm8") "fo"
  && decoded_text (B64.decode_std "Zm9vYg") "foob"

#[test]
def test_b64_std_alphabet_edge : Bool :=
  B64.encode_std edge_bytes == "+/8="
  && decoded_bytes (B64.decode_std "+/8=") edge_bytes

// ── base64url (RFC 4648 §5) ─────────────────────────────────────────────

#[test]
def test_b64url_encode_is_unpadded : Bool :=
  B64Url.encode (String.to_list "") == ""
  && B64Url.encode (String.to_list "f") == "Zg"
  && B64Url.encode (String.to_list "fo") == "Zm8"
  && B64Url.encode (String.to_list "foo") == "Zm9v"
  && B64Url.encode (String.to_list "foob") == "Zm9vYg"
  && B64Url.encode (String.to_list "fooba") == "Zm9vYmE"
  && B64Url.encode (String.to_list "foobar") == "Zm9vYmFy"

#[test]
def test_b64url_decode : Bool :=
  decoded_text (B64Url.decode "Zg") "f"
  && decoded_text (B64Url.decode "Zm8") "fo"
  && decoded_text (B64Url.decode "Zm9vYmFy") "foobar"
  && decoded_bytes (B64Url.decode "-_8") edge_bytes
  && B64Url.encode edge_bytes == "-_8"

#[test]
def test_b64url_roundtrip : Bool :=
  decoded_bytes (B64Url.decode (B64Url.encode edge_bytes)) edge_bytes
  && decoded_bytes (B64Url.decode (B64Url.encode one_zero_byte)) one_zero_byte

// ── strict decoding ─────────────────────────────────────────────────────

#[test]
def test_b64_rejects_short_group : Bool :=
  rejected_with (B64.decode_std "Z") "base64: length is not a multiple of 4"

#[test]
def test_b64_rejects_bad_character : Bool :=
  rejected_with (B64.decode_std "Zm9!") "base64: invalid character"
  && rejected_with (B64.decode_std "!m9v") "base64: invalid character"

#[test]
def test_b64_rejects_data_after_padding : Bool :=
  rejected_with (B64.decode_std "Zg==A") "base64: data after the padding"

#[test]
def test_b64_rejects_bad_padding : Bool :=
  rejected_with (B64.decode_std "Zg=") "base64: invalid padding"
  && rejected_with (B64.decode_std "Z=g=") "base64: invalid padding"
  && rejected_with (B64.decode_std "=Zg=") "base64: invalid padding"

#[test]
def test_b64_rejects_non_canonical_bits : Bool :=
  rejected_with (B64.decode_std "Zh") "base64: non-canonical padding bits"
  && rejected_with (B64.decode_std "Zm9=") "base64: non-canonical padding bits"

#[test]
def test_b64url_rejects_std_alphabet : Bool :=
  rejected_with (B64Url.decode "+/8") "base64: invalid character"
  && rejected_with (B64.decode_std "-_8") "base64: invalid character"

/// The variant itself, not just its text: a collapse of two reasons into
/// one message would still pass the rows above.
def rejected_bad_length (r : Result B64Error (List U8)) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => match e { B64Error.bad_length => true, _ => false }
  }

def rejected_invalid_char (r : Result B64Error (List U8)) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => match e { B64Error.invalid_char => true, _ => false }
  }

def rejected_after_padding (r : Result B64Error (List U8)) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => match e { B64Error.data_after_padding => true, _ => false }
  }

def rejected_non_canonical (r : Result B64Error (List U8)) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => match e { B64Error.non_canonical_bits => true, _ => false }
  }

def rejected_invalid_padding (r : Result B64Error (List U8)) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => match e { B64Error.invalid_padding => true, _ => false }
  }

#[test]
def test_b64_error_variants : Bool :=
  rejected_bad_length (B64.decode_std "Z")
  && rejected_invalid_char (B64.decode_std "Zm9!")
  && rejected_after_padding (B64.decode_std "Zg==A")
  && rejected_non_canonical (B64.decode_std "Zh")
  && rejected_invalid_padding (B64.decode_std "Zg=")
