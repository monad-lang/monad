/// RFC 4231 HMAC-SHA-256 vectors, including the long-key cases. Pure, so
/// both hosts run them.

use std::hex {Hex.decode, Hex.encode}
use crypto::hmac {Hmac.sha256}

def hex (s : String) : List U8 :=
  match Hex.decode s {
    Result.ok bs => bs,
    Result.err _ => List.empty
  }

def hex_of (bs : List U8) : String :=
  Hex.encode bs

#[terminating]
def repeat_byte (n : I64) (b : U8) : List U8 :=
  if I64.beq n 0i64 then List.empty else List.cons b (repeat_byte (I64.sub n 1i64) b)

#[terminating]
def first_n (n : I64) (xs : List U8) : List U8 :=
  if I64.beq n 0i64 then List.empty
  else match xs {
    List.empty => List.empty,
    List.cons x rest => List.cons x (first_n (I64.sub n 1i64) rest)
  }

#[test]
def test_hmac_rfc4231_case1 : Bool :=
  hex_of (Hmac.sha256 (repeat_byte 20i64 11u8) (String.to_list "Hi There"))
    == "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"

#[test]
def test_hmac_rfc4231_case2 : Bool :=
  hex_of (Hmac.sha256 (String.to_list "Jefe")
    (String.to_list "what do ya want for nothing?"))
    == "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"

#[test]
def test_hmac_rfc4231_case3 : Bool :=
  hex_of (Hmac.sha256 (repeat_byte 20i64 170u8) (repeat_byte 50i64 221u8))
    == "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"

#[test]
def test_hmac_rfc4231_case4 : Bool :=
  hex_of (Hmac.sha256 (hex "0102030405060708090a0b0c0d0e0f10111213141516171819")
    (repeat_byte 50i64 205u8))
    == "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b"

#[test]
def test_hmac_rfc4231_case5_truncated : Bool :=
  let mac := Hmac.sha256 (repeat_byte 20i64 12u8)
    (String.to_list "Test With Truncation") in
  hex_of (first_n 16i64 mac) == "a3b6167473100ee06e0c796c2955552b"

#[test]
def test_hmac_rfc4231_case6_long_key : Bool :=
  hex_of (Hmac.sha256 (repeat_byte 131i64 170u8)
    (String.to_list "Test Using Larger Than Block-Size Key - Hash Key First"))
    == "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"

#[test]
def test_hmac_rfc4231_case7_long_key_and_data : Bool :=
  hex_of (Hmac.sha256 (repeat_byte 131i64 170u8)
    (String.to_list "This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm."))
    == "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"
