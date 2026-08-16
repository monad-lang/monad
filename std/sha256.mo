/// SHA-256 (FIPS 180-4).
///
/// Public API: `Sha256.hash : String -> String` (lowercase 64-hex-char
/// digest). Also exposes `Sha256.hash_bytes : List U8 -> List U8` (raw
/// 32-byte digest) for anyone who wants the digest bytes directly rather
/// than hex text.
///
/// Assumption: only the low 32 bits of the bit-length are encoded in the
/// padding footer (the high 32 bits are hardcoded to zero) — correct for
/// any message under 2^32 bits (~512 MiB), which is far beyond what this
/// tree-walking-successor interpreter can hash in reasonable time anyway.

use std.list {length}

// ── State ──

struct Sha256State {
  a : U32, b : U32, c : U32, d : U32,
  e : U32, f : U32, g : U32, h : U32
}

// ── Constants (FIPS 180-4) ──

def Sha256.h0 : List U32 :=
  [ 0x6a09e667u32,
    0xbb67ae85u32,
    0x3c6ef372u32,
    0xa54ff53au32,
    0x510e527fu32,
    0x9b05688cu32,
    0x1f83d9abu32,
    0x5be0cd19u32
  ]

def Sha256.initial_state : Sha256State :=
  { a := 0x6a09e667u32, b := 0xbb67ae85u32, c := 0x3c6ef372u32, d := 0xa54ff53au32,
    e := 0x510e527fu32, f := 0x9b05688cu32, g := 0x1f83d9abu32, h := 0x5be0cd19u32 }

def Sha256.k : List U32 :=
  [
    0x428a2f98u32,
    0x71374491u32,
    0xb5c0fbcfu32,
    0xe9b5dba5u32,
    0x3956c25bu32,
    0x59f111f1u32,
    0x923f82a4u32,
    0xab1c5ed5u32,
    0xd807aa98u32,
    0x12835b01u32,
    0x243185beu32,
    0x550c7dc3u32,
    0x72be5d74u32,
    0x80deb1feu32,
    0x9bdc06a7u32,
    0xc19bf174u32,
    0xe49b69c1u32,
    0xefbe4786u32,
    0x0fc19dc6u32,
    0x240ca1ccu32,
    0x2de92c6fu32,
    0x4a7484aau32,
    0x5cb0a9dcu32,
    0x76f988dau32,
    0x983e5152u32,
    0xa831c66du32,
    0xb00327c8u32,
    0xbf597fc7u32,
    0xc6e00bf3u32,
    0xd5a79147u32,
    0x06ca6351u32,
    0x14292967u32,
    0x27b70a85u32,
    0x2e1b2138u32,
    0x4d2c6dfcu32,
    0x53380d13u32,
    0x650a7354u32,
    0x766a0abbu32,
    0x81c2c92eu32,
    0x92722c85u32,
    0xa2bfe8a1u32,
    0xa81a664bu32,
    0xc24b8b70u32,
    0xc76c51a3u32,
    0xd192e819u32,
    0xd6990624u32,
    0xf40e3585u32,
    0x106aa070u32,
    0x19a4c116u32,
    0x1e376c08u32,
    0x2748774cu32,
    0x34b0bcb5u32,
    0x391c0cb3u32,
    0x4ed8aa4au32,
    0x5b9cca4fu32,
    0x682e6ff3u32,
    0x748f82eeu32,
    0x78a5636fu32,
    0x84c87814u32,
    0x8cc70208u32,
    0x90befffau32,
    0xa4506cebu32,
    0xbef9a3f7u32,
    0xc67178f2u32
  ]

// ── Byte <-> word packing (big-endian) ──

def Sha256.pack_word (b0 b1 b2 b3 : U8) : U32 :=
  U32.or (U32.or (U32.shl (U8.to_u32 b0) 24u32) (U32.shl (U8.to_u32 b1) 16u32))
         (U32.or (U32.shl (U8.to_u32 b2) 8u32) (U8.to_u32 b3))

// Structural recursion on `bytes` (shrinks by 4 each call). Nested
// constructor patterns like `cons a (cons b c)` aren't supported by the
// parser, so each byte is peeled off via its own nested `match` instead
// of one deep pattern.
def Sha256.pack_words (bytes : List U8) : List U32 :=
  match bytes {
    empty => List.empty,
    cons b0 rest0 => match rest0 {
      empty => List.empty,
      cons b1 rest1 => match rest1 {
        empty => List.empty,
        cons b2 rest2 => match rest2 {
          empty => List.empty,
          cons b3 rest3 =>
            List.cons (Sha256.pack_word b0 b1 b2 b3) (Sha256.pack_words rest3)
        }
      }
    }
  }

def Sha256.unpack_word (w : U32) : List U8 :=
  [ U32.to_u8 (U32.shr w 24u32), U32.to_u8 (U32.shr w 16u32),
    U32.to_u8 (U32.shr w 8u32), U32.to_u8 w ]

// ── Padding ──

// smallest k >= 0 with (msg_len_bytes + 1 + k) mod 64 == 56
def Sha256.pad_zeros_needed (msg_len_bytes : I64) : I64 :=
  let total := I64.add msg_len_bytes 1 in
  let rem := I64.sub total (I64.mul 64 (I64.div total 64)) in
  if I64.lt rem 57 then I64.sub 56 rem else I64.sub 120 rem

#[terminating] // decreasing I64 counter, same idiom as String.repeat
def Sha256.zero_bytes (n : I64) : List U8 :=
  if I64.beq n 0 then List.empty
  else List.cons 0u8 (Sha256.zero_bytes (I64.sub n 1))

def Sha256.pad (bytes : List U8) (msg_len_bytes : I64) : List U8 :=
  let bit_len := I64.mul msg_len_bytes 8 in
  let marked := List.append bytes (List.singleton 128u8) in // 0x80
  let zeros := Sha256.zero_bytes (Sha256.pad_zeros_needed msg_len_bytes) in
  let len_hi := Sha256.unpack_word 0u32 in // high 32 bits of bit-length: see module doc
  let len_lo := Sha256.unpack_word (I64.to_u32 bit_len) in
  List.append marked (List.append zeros (List.append len_hi len_lo))

// ── Message schedule (W[0..63]) ──

def Sha256.sigma0 (x : U32) : U32 :=
  U32.xor (U32.xor (U32.rotr x 7u32) (U32.rotr x 18u32)) (U32.shr x 3u32)

def Sha256.sigma1 (x : U32) : U32 :=
  U32.xor (U32.xor (U32.rotr x 17u32) (U32.rotr x 19u32)) (U32.shr x 10u32)

def Sha256.at_or_zero (l : List U32) (i : I64) : U32 :=
  Option.get_or_default 0u32 (List.get i l)

// `rev_words` holds the schedule words produced so far, most-recent
// first (cons-accumulator, same idiom as List.reverse_append). For the
// next word: sigma1(rev[1]) + rev[6] + sigma0(rev[14]) + rev[15].
#[terminating] // decreasing I64 counter over a 2-list-lookback window
def Sha256.expand_loop (rev_words : List U32) (remaining : I64) : List U32 :=
  if I64.beq remaining 0 then rev_words
  else
    let w2 := Sha256.at_or_zero rev_words 1 in
    let w7 := Sha256.at_or_zero rev_words 6 in
    let w15 := Sha256.at_or_zero rev_words 14 in
    let w16 := Sha256.at_or_zero rev_words 15 in
    let new_w := U32.add (U32.add (Sha256.sigma1 w2) w7) (U32.add (Sha256.sigma0 w15) w16) in
    Sha256.expand_loop (List.cons new_w rev_words) (I64.sub remaining 1)

def Sha256.schedule (block16 : List U32) : List U32 :=
  List.reverse (Sha256.expand_loop (List.reverse block16) 48)

// ── Compression ──

def Sha256.ch (x y z : U32) : U32 := U32.xor (U32.and x y) (U32.and (U32.not x) z)
def Sha256.maj (x y z : U32) : U32 := U32.xor (U32.xor (U32.and x y) (U32.and x z)) (U32.and y z)
def Sha256.big_sigma0 (x : U32) : U32 := U32.xor (U32.xor (U32.rotr x 2u32) (U32.rotr x 13u32)) (U32.rotr x 22u32)
def Sha256.big_sigma1 (x : U32) : U32 := U32.xor (U32.xor (U32.rotr x 6u32) (U32.rotr x 11u32)) (U32.rotr x 25u32)

// Structural recursion pairing the K/W lists (each call strictly
// shorter) — one round per (k, w) pair.
def Sha256.compress_rounds (ks ws : List U32) (s : Sha256State) : Sha256State :=
  match ks {
    empty => s,
    cons k ks_rest => match ws {
      empty => s,
      cons w ws_rest => match s {
        mk a b c d e f g h =>
          let t1 := U32.add (U32.add (U32.add (U32.add h (Sha256.big_sigma1 e)) (Sha256.ch e f g)) k) w in
          let t2 := U32.add (Sha256.big_sigma0 a) (Sha256.maj a b c) in
          Sha256.compress_rounds ks_rest ws_rest
            { a := U32.add t1 t2, b := a, c := b, d := c,
              e := U32.add d t1, f := e, g := f, h := g }
      }
    }
  }

def Sha256.compress_block (s : Sha256State) (block64 : List U8) : Sha256State :=
  let w := Sha256.schedule (Sha256.pack_words block64) in
  let r := Sha256.compress_rounds Sha256.k w s in
  match s { mk a0 b0 c0 d0 e0 f0 g0 h0 =>
    match r { mk a b c d e f g h =>
      { a := U32.add a0 a, b := U32.add b0 b, c := U32.add c0 c, d := U32.add d0 d,
        e := U32.add e0 e, f := U32.add f0 f, g := U32.add g0 g, h := U32.add h0 h }
    }
  }

// ── Block splitting + top-level API ──

#[terminating]
def Sha256.take_n (n : I64) (bytes : List U8) : List U8 :=
  if I64.beq n 0 then List.empty
  else match bytes {
    empty => List.empty,
    cons b rest => List.cons b (Sha256.take_n (I64.sub n 1) rest)
  }

#[terminating]
def Sha256.drop_n (n : I64) (bytes : List U8) : List U8 :=
  if I64.beq n 0 then bytes
  else match bytes {
    empty => List.empty,
    cons _ rest => Sha256.drop_n (I64.sub n 1) rest
  }

#[terminating] // list shrinks by 64 each call via a helper, not a
                // directly-matched sub-term
def Sha256.process_blocks (s : Sha256State) (padded : List U8) : Sha256State :=
  match padded {
    empty => s,
    cons _ _ =>
      Sha256.process_blocks
        (Sha256.compress_block s (Sha256.take_n 64 padded))
        (Sha256.drop_n 64 padded)
  }

def Sha256.hash_bytes (bytes : List U8) : List U8 :=
  let padded := Sha256.pad bytes (List.length bytes) in
  let final := Sha256.process_blocks Sha256.initial_state padded in
  match final { mk a b c d e f g h =>
    List.flatten [Sha256.unpack_word a, Sha256.unpack_word b, Sha256.unpack_word c, Sha256.unpack_word d,
                   Sha256.unpack_word e, Sha256.unpack_word f, Sha256.unpack_word g, Sha256.unpack_word h]
  }

// Hex encode without any new native: nibble -> ASCII via arithmetic.
def Sha256.hex_char_of_nibble (n : U8) : U8 :=
  if U8.lt n 10u8 then U8.add n 48u8 else U8.add n 87u8

def Sha256.hex_bytes_of_byte (b : U8) : List U8 :=
  let hi := U8.div b 16u8 in
  let lo := U8.sub b (U8.mul hi 16u8) in
  [Sha256.hex_char_of_nibble hi, Sha256.hex_char_of_nibble lo]

def Sha256.hex_of_bytes (bytes : List U8) : List U8 :=
  match bytes {
    empty => List.empty,
    cons b rest => List.append (Sha256.hex_bytes_of_byte b) (Sha256.hex_of_bytes rest)
  }

// Digest bytes aren't valid UTF-8 in general, so hex-encode to ASCII
// (always valid UTF-8) before the only String.from_list call.
def Sha256.hash (s : String) : String :=
  String.from_list (Sha256.hex_of_bytes (Sha256.hash_bytes (String.to_list s)))
