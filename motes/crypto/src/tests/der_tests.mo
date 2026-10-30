/// DER encoding tests for `motes/crypto`.
///
/// The RFC 7515 §A.3 signature is the real-world case: its `r` has the top
/// bit clear and its `s` has it set, so the encoded form needs exactly one
/// sign byte. Pure (`Bool`), so both hosts run it.

use std::list {List.length}
use crypto::der {Der.ecdsa_raw_to_der, Der.integer}

/// The RFC 7515 §A.3 P-256 signature, as its 64 raw `R || S` bytes.
def rfc_a3_r : List U8 := [
  14u8, 209u8, 33u8, 83u8, 121u8, 99u8, 108u8, 72u8, 60u8, 47u8, 127u8,
  21u8, 88u8, 7u8, 212u8, 2u8, 163u8, 178u8, 40u8, 3u8, 58u8, 249u8,
  124u8, 126u8, 23u8, 129u8, 154u8, 195u8, 22u8, 158u8, 166u8, 101u8
]

def rfc_a3_s : List U8 := [
  197u8, 10u8, 7u8, 211u8, 140u8, 60u8, 112u8, 229u8, 216u8, 241u8,
  45u8, 175u8, 8u8, 74u8, 84u8, 128u8, 166u8, 101u8, 144u8, 197u8,
  242u8, 147u8, 80u8, 154u8, 143u8, 63u8, 127u8, 138u8, 131u8, 163u8,
  84u8, 213u8
]

def rfc_a3_raw : List U8 := List.append rfc_a3_r rfc_a3_s

def byte_at (i : I64) (xs : List U8) : U8 :=
  match xs {
    List.empty => 0u8,
    List.cons x rest =>
      if I64.beq i 0i64 then x else byte_at (I64.sub i 1i64) rest
  }

#[terminating]
def repeat_byte (n : I64) (b : U8) : List U8 :=
  if I64.beq n 0i64 then List.empty else List.cons b (repeat_byte (I64.sub n 1i64) b)

def der_of (raw : List U8) : Option (List U8) :=
  match Der.ecdsa_raw_to_der raw {
    Result.ok bs => Option.some bs,
    Result.err _ => Option.none
  }

def der_error (raw : List U8) : Bool :=
  match Der.ecdsa_raw_to_der raw {
    Result.ok _ => false,
    Result.err _ => true
  }

#[test]
def test_der_wrong_length_rejected : Bool :=
  der_error (repeat_byte 63i64 0u8)
  && der_error (repeat_byte 65i64 0u8)
  && der_error List.empty

#[test]
def test_der_zero_components : Bool :=
  match der_of (repeat_byte 64i64 0u8) {
    Option.none => false,
    Option.some bs =>
      // SEQUENCE { INTEGER 0, INTEGER 0 }
      bs == [48u8, 6u8, 2u8, 1u8, 0u8, 2u8, 1u8, 0u8]
  }

#[test]
def test_der_high_bit_gets_sign_byte : Bool :=
  match der_of (repeat_byte 64i64 128u8) {
    Option.none => false,
    Option.some bs =>
      // Each INTEGER is 0x02 0x21 0x00 followed by its 32 bytes.
      I64.beq (List.length bs) 72i64
        && U8.beq (byte_at 0i64 bs) 48u8
        && U8.beq (byte_at 1i64 bs) 70u8
        && U8.beq (byte_at 2i64 bs) 2u8
        && U8.beq (byte_at 3i64 bs) 33u8
        && U8.beq (byte_at 4i64 bs) 0u8
        && U8.beq (byte_at 37i64 bs) 2u8
        && U8.beq (byte_at 38i64 bs) 33u8
        && U8.beq (byte_at 39i64 bs) 0u8
  }

#[test]
def test_der_strips_redundant_leading_zeros : Bool :=
  // r = 30 bytes of 0x01 after two zero bytes; s = 32 bytes of 0x7f.
  let r := List.append [0u8, 0u8] (repeat_byte 30i64 1u8) in
  let raw := List.append r (repeat_byte 32i64 127u8) in
  match der_of raw {
    Option.none => false,
    Option.some bs =>
      // INTEGER r is 2 + 30 bytes; INTEGER s is 2 + 32 bytes.
      I64.beq (List.length bs) 68i64
        && U8.beq (byte_at 2i64 bs) 2u8
        && U8.beq (byte_at 3i64 bs) 30u8
        && U8.beq (byte_at 34i64 bs) 2u8
        && U8.beq (byte_at 35i64 bs) 32u8
  }

#[test]
def test_der_rfc7515_a3_vector : Bool :=
  match der_of rfc_a3_raw {
    Option.none => false,
    Option.some bs =>
      // r: 0x02 0x20 + 32 bytes; s: 0x02 0x21 0x00 + 32 bytes.
      I64.beq (List.length bs) 71i64
        && U8.beq (byte_at 0i64 bs) 48u8
        && U8.beq (byte_at 1i64 bs) 69u8
        && U8.beq (byte_at 2i64 bs) 2u8
        && U8.beq (byte_at 3i64 bs) 32u8
        && U8.beq (byte_at 4i64 bs) 14u8
        && U8.beq (byte_at 36i64 bs) 2u8
        && U8.beq (byte_at 37i64 bs) 33u8
        && U8.beq (byte_at 38i64 bs) 0u8
        && U8.beq (byte_at 39i64 bs) 197u8
  }

#[test]
def test_der_integer_all_zero_is_one_byte : Bool :=
  Der.integer (repeat_byte 8i64 0u8) == [2u8, 1u8, 0u8]
