/// Phase 0 vectors for `motes/crypto`: RFC 4648 §10, the URL-alphabet
/// forms, strict-decoding rejections, hex, and constant-time equality.
///
/// Pure (`Bool`) so the whole file runs on the Rust host and the compiled
/// backend alike.

use crypto::b64 {B64.encode_std, B64.decode_std, B64Url.encode, B64Url.decode}
use crypto::hex {Hex.encode, Hex.decode}
use crypto::ct {Ct.eq}

// `BEq (List A)` lives here, not in the ambient prelude; the empty brace
// list pulls the module (and its instances) into scope.
use std::list {}

// ── helpers ─────────────────────────────────────────────────────────────

def decoded_text (r : Result String (List U8)) (expected : String) : Bool :=
  match r {
    Result.ok bs => bs == String.to_list expected,
    Result.err _ => false
  }

def decoded_bytes (r : Result String (List U8)) (expected : List U8) : Bool :=
  match r {
    Result.ok bs => bs == expected,
    Result.err _ => false
  }

def rejected_with (r : Result String (List U8)) (msg : String) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => e == msg
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

// ── hex ─────────────────────────────────────────────────────────────────

#[test]
def test_hex_encode : Bool :=
  Hex.encode (String.to_list "foobar") == "666f6f626172"
  && Hex.encode one_zero_byte == "00"
  && Hex.encode edge_bytes == "fbff"
  && Hex.encode List.empty == ""

#[test]
def test_hex_decode : Bool :=
  decoded_text (Hex.decode "666f6f626172") "foobar"
  && decoded_text (Hex.decode "666F6F626172") "foobar"
  && decoded_bytes (Hex.decode "00") one_zero_byte
  && decoded_bytes (Hex.decode "") List.empty
  && decoded_bytes (Hex.decode (Hex.encode edge_bytes)) edge_bytes

#[test]
def test_hex_rejects_bad_input : Bool :=
  rejected_with (Hex.decode "abc") "hex: odd length"
  && rejected_with (Hex.decode "zz") "hex: invalid character"
  && rejected_with (Hex.decode "0g") "hex: invalid character"

// ── constant-time equality ──────────────────────────────────────────────

#[test]
def test_ct_eq : Bool :=
  Ct.eq (String.to_list "abc") (String.to_list "abc")
  && Bool.not (Ct.eq (String.to_list "abc") (String.to_list "abd"))
  && Bool.not (Ct.eq (String.to_list "abc") (String.to_list "zbc"))
  && Bool.not (Ct.eq (String.to_list "abc") (String.to_list "ab"))
  && Bool.not (Ct.eq (String.to_list "abc") (String.to_list "abcd"))
  && Ct.eq List.empty List.empty
  && Bool.not (Ct.eq List.empty one_zero_byte)
