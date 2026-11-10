/// HMAC-SHA-256 (RFC 2104 / FIPS 198-1).
///
/// Pure, so the RFC 4231 vectors run on both hosts. A key longer than the
/// 64-byte block is hashed first; the key is then zero-filled to the block
/// size and XORed with the inner and outer pads. This module only computes;
/// comparing two MACs is `Ct.eq` (motes/crypto/src/ct.mo).

use std::list {}
use std::sha256 {Sha256.hash_bytes}

def Hmac.block_bytes : I64 := 64i64

/// 0x36 and 0x5c, the RFC 2104 inner and outer pad bytes.
def Hmac.ipad_byte : U8 := 54u8
def Hmac.opad_byte : U8 := 92u8
def Hmac.zero_byte : U8 := 0u8

def Hmac.xor_byte (a b : U8) : U8 :=
    U32.to_u8 (U32.xor (U8.to_u32 a) (U8.to_u32 b))

#[terminating]
def Hmac.xor_each (xs : List U8) (pad : U8) : List U8 :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons (Hmac.xor_byte x pad) (Hmac.xor_each rest pad)
    }

/// Hash an over-long key, then zero-fill to the block size.
#[terminating]
def Hmac.pad_key (key : List U8) : List U8 :=
    if I64.gt (List.length key) Hmac.block_bytes
    then Hmac.pad_key (Sha256.hash_bytes key)
    else Hmac.fill_key key

#[terminating]
def Hmac.fill_key (key : List U8) : List U8 :=
    if I64.lt (List.length key) Hmac.block_bytes
    then Hmac.fill_key (List.append key [Hmac.zero_byte])
    else key

pub def Hmac.sha256 (key : List U8) (msg : List U8) : List U8 :=
    let padded := Hmac.pad_key key in
    let inner := Sha256.hash_bytes
        (List.append (Hmac.xor_each padded Hmac.ipad_byte) msg) in
    Sha256.hash_bytes (List.append (Hmac.xor_each padded Hmac.opad_byte) inner)
