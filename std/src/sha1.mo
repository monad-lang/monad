/// SHA-1 (FIPS 180-4).
///
/// Public API: `Sha1.hash : String -> String` (lowercase 40-hex-char
/// digest) and `Sha1.hash_bytes : List U8 -> List U8` (raw 20-byte digest).
///
/// SHA-1 is broken for collision resistance. It is here because protocols
/// still name it — the WebSocket handshake's `Sec-WebSocket-Accept`
/// (RFC 6455 §4.2.2) is the reason it exists — never for integrity or
/// authentication. Use `std::sha256` for anything security-relevant.
///
/// The byte packing, padding and block splitting are SHA-256's (the two
/// share the 512-bit block, the big-endian word order and the length
/// footer, including its under-2^32-bits assumption); only the schedule and
/// the compression rounds differ.

use std::sha256 {}

// ── State ──

struct Sha1State { a : U32, b : U32, c : U32, d : U32, e : U32 }

/// Five 32-bit registers; duplicating the state is a register copy.
pub instance Copy Sha1State {
    def copy (s : Sha1State) : Pair Sha1State Sha1State := Pair.pair s s
}

def Sha1.initial_state : Sha1State :=
    { a := 0x67452301u32, b := 0xefcdab89u32, c := 0x98badcfeu32, d := 0x10325476u32,
        e := 0xc3d2e1f0u32 }

/// Left-rotate by `n` (1..31) as a right-rotate by `32 - n`.
def Sha1.rotl (x : U32) (n : U32) : U32 := U32.rotr x (U32.sub 32u32 n)

// ── Message schedule (W[0..79]) ──

// `rev_words` holds the words so far, most-recent first. For the next word:
// rotl1(rev[2] ^ rev[7] ^ rev[13] ^ rev[15]) — W[t-3], W[t-8], W[t-14], W[t-16].
#[terminating] // decreasing I64 counter, same idiom as Sha256.expand_loop
def Sha1.expand_loop (rev_words : Shared (List U32)) (remaining : I64) : List U32 :=
    if I64.beq remaining 0 then Shared.get rev_words
    else
        let w3 := Sha256.at_or_zero (Shared.get rev_words) 2 in
        let w8 := Sha256.at_or_zero (Shared.get rev_words) 7 in
        let w14 := Sha256.at_or_zero (Shared.get rev_words) 13 in
        let w16 := Sha256.at_or_zero (Shared.get rev_words) 15 in
        let new_w := Sha1.rotl (U32.xor (U32.xor w3 w8) (U32.xor w14 w16)) 1u32 in
        Sha1.expand_loop (Shared.of (List.cons new_w (Shared.get rev_words))) (remaining - 1)

def Sha1.schedule (block16 : List U32) : List U32 :=
    List.reverse (Sha1.expand_loop (Shared.of (List.reverse block16)) 64)

// ── Compression ──

/// The round function and constant for round `t` (0..79).
def Sha1.f (t : I64) (b c d : U32) : U32 :=
    if I64.lt t 20 then U32.or (U32.and b c) (U32.and (U32.not b) d)
    else if I64.lt t 40 then U32.xor (U32.xor b c) d
    else if I64.lt t 60 then U32.or (U32.or (U32.and b c) (U32.and b d)) (U32.and c d)
    else U32.xor (U32.xor b c) d

def Sha1.k (t : I64) : U32 :=
    if I64.lt t 20 then 0x5a827999u32
    else if I64.lt t 40 then 0x6ed9eba1u32
    else if I64.lt t 60 then 0x8f1bbcdcu32
    else 0xca62c1d6u32

// Structural recursion on the schedule — one round per word.
def Sha1.compress_rounds (t : I64) (ws : List U32) (s : Sha1State) : Sha1State :=
    match ws {
        empty => s,
        cons w rest => match s {
            { a, b, c, d, e } =>
                let tmp := U32.add (U32.add (U32.add (Sha1.rotl a 5u32) (Sha1.f t b c d))
                    (U32.add e (Sha1.k t))) w in
                Sha1.compress_rounds (t + 1) rest
                    { a := tmp, b := a, c := Sha1.rotl b 30u32, d := c, e := d }
        }
    }

def Sha1.compress_block (s : Sha1State) (block64 : List U8) : Sha1State :=
    let w := Sha1.schedule (Sha256.pack_words block64) in
    let r := Sha1.compress_rounds 0 w s in
    match s { { a := a0, b := b0, c := c0, d := d0, e := e0 } =>
        match r { { a, b, c, d, e } =>
            { a := U32.add a0 a, b := U32.add b0 b, c := U32.add c0 c, d := U32.add d0 d,
                e := U32.add e0 e }
        }
    }

#[terminating] // the list shrinks by 64 each call via a helper
def Sha1.process_blocks (s : Sha1State) (padded : Shared (List U8)) : Sha1State :=
    match Shared.get padded {
        empty => s,
        cons _ _ =>
            Sha1.process_blocks
                (Sha1.compress_block s (Sha256.take_n 64 (Shared.get padded)))
                (Shared.of (Sha256.drop_n 64 (Shared.get padded)))
    }

/// The raw 20-byte digest.
pub def Sha1.hash_bytes (bytes : List U8) : List U8 :=
    let padded := Sha256.pad (Shared.of bytes) in
    let final := Sha1.process_blocks Sha1.initial_state (Shared.of padded) in
    match final { { a, b, c, d, e } =>
        List.flatten [Sha256.unpack_word a, Sha256.unpack_word b, Sha256.unpack_word c,
            Sha256.unpack_word d, Sha256.unpack_word e]
    }

/// The lowercase hex digest of a string's UTF-8 bytes.
pub def Sha1.hash (s : String) : String :=
    String.from_list (Sha256.hex_of_bytes (Sha1.hash_bytes (String.to_list s)))
