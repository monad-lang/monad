/// Minimal DER encoding for ECDSA signatures in JWS form.
///
/// A JWS ES256 signature is `R || S`, 32 bytes each (RFC 7515 §A.3).
/// OpenSSL's `EVP_DigestVerify` expects `SEQUENCE { INTEGER r, INTEGER s }`
/// in DER, so this is the one conversion `motes/crypto` needs. It is pure,
/// so its cases run on both hosts; only `Pubkey.verify` is compiled-only.

use std::list {List.length}

/// The fixed half-width of a P-256 ECDSA component, in bytes.
def Der.component_bytes : I64 := 32i64

/// DER tag values. Lengths here are always under 128, so the short form is
/// the only one this encoder emits.
def Der.tag_integer : U8 := 2u8
def Der.tag_sequence : U8 := 48u8

/// A high bit on the first content byte would read as a negative INTEGER,
/// so canonical DER prefixes a zero byte. 0x80 is that boundary.
def Der.negative_boundary : U8 := 128u8

def Der.take (n : I64) (xs : List U8) : List U8 :=
  match xs {
    List.empty => List.empty,
    List.cons x rest =>
      if I64.beq n 0i64 then List.empty
      else List.cons x (Der.take (I64.sub n 1i64) rest)
  }

def Der.drop (n : I64) (xs : List U8) : List U8 :=
  match xs {
    List.empty => List.empty,
    List.cons _ rest =>
      if I64.beq n 0i64 then xs
      else Der.drop (I64.sub n 1i64) rest
  }

/// Drop leading zero bytes; an all-zero component becomes the empty list and
/// is normalized to a single zero byte by `Der.integer_body`.
pub def Der.strip_leading_zeros (xs : List U8) : List U8 :=
  match xs {
    List.empty => List.empty,
    List.cons x rest =>
      if U8.beq x 0u8 then Der.strip_leading_zeros rest else xs
  }

/// The content octets of a DER INTEGER: minimal (no redundant leading
/// zeros), with one zero byte prepended when the top bit is set.
def Der.integer_body (bytes : List U8) : List U8 :=
  let trimmed := Der.strip_leading_zeros bytes in
  match trimmed {
    List.empty => [0u8],
    List.cons x _ =>
      if U8.lt x Der.negative_boundary then trimmed
      else List.cons 0u8 trimmed
  }

/// One-byte length, then the content.
def Der.tlv (tag : U8) (content : List U8) : List U8 :=
  let n : U32 := I64.to_u32 (List.length content) in
  List.cons tag (List.cons (U32.to_u8 n) content)

/// Package-private: the one-byte length form is a precondition of
/// `Der.ecdsa_raw_to_der` (a P-256 component is at most 33 bytes), not a
/// general DER encoder. Keep the API surface at the checked entry point.
def Der.integer (bytes : List U8) : List U8 :=
  Der.tlv Der.tag_integer (Der.integer_body bytes)

def Der.sequence (content : List U8) : List U8 :=
  Der.tlv Der.tag_sequence content

pub def Der.ecdsa_raw_to_der (raw : List U8) : Result String (List U8) :=
  if Bool.not (I64.beq (List.length raw) 64i64)
  then Result.err "der: ECDSA signature must be 64 bytes"
  else
    let r := Der.take Der.component_bytes raw in
    let s := Der.drop Der.component_bytes raw in
    let body := List.append (Der.integer r) (Der.integer s) in
    Result.ok (Der.sequence body)
