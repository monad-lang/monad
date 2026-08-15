/// Correctness tests for std/sha256.mo — asserts against known-correct
/// SHA-256 digests (FIPS 180-4 example vectors, plus a couple of
/// additional ones). Every digest below was independently confirmed with
/// a real `sha256sum` run during development, not taken from memory.

use std.sha256 {}

// ── Primitive unit tests ──
// Isolates a failure to "native op" vs. "algorithm composition" first.

#[test]
def test_u32_rotr : Bool :=
  U32.rotr 1u32 1u32 == 2147483648u32

#[test]
def test_u32_shr : Bool :=
  U32.shr 1u32 1u32 == 0u32

#[test]
def test_u32_shl : Bool :=
  U32.shl 1u32 31u32 == 2147483648u32

#[test]
def test_u32_and : Bool :=
  U32.and 4294967295u32 0u32 == 0u32

#[test]
def test_u32_or : Bool :=
  U32.or 0u32 4294901760u32 == 4294901760u32 // 0xFFFF0000

#[test]
def test_u32_xor : Bool :=
  U32.xor 4294967295u32 4294967295u32 == 0u32

#[test]
def test_u32_not : Bool :=
  U32.not 0u32 == 4294967295u32

#[test]
def test_u32_add_wraps : Bool :=
  U32.add 4000000000u32 4000000000u32 == 3705032704u32

#[test]
def test_hex_bytes_of_byte_ff : Bool :=
  Sha256.hex_bytes_of_byte 255u8 == [102u8, 102u8] // "ff"

#[test]
def test_hex_bytes_of_byte_00 : Bool :=
  Sha256.hex_bytes_of_byte 0u8 == [48u8, 48u8] // "00"

// ── Test vectors ──

#[test]
def test_sha256_empty : Bool :=
  Sha256.hash "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

#[test]
def test_sha256_abc : Bool :=
  Sha256.hash "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

// 448-bit boundary: forces padding to spill into a second block
#[test]
def test_sha256_448_boundary : Bool :=
  Sha256.hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
    == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

// genuinely >= 2 full 64-byte blocks
#[test]
def test_sha256_two_block : Bool :=
  Sha256.hash "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
    == "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"

#[test]
def test_sha256_quick_fox : Bool :=
  Sha256.hash "The quick brown fox jumps over the lazy dog"
    == "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592"
