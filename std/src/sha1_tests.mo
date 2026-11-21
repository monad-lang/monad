/// Correctness tests for std/sha1.mo — FIPS 180-4 / RFC 3174 vectors, the
/// 2-block boundary, and the RFC 6455 §1.3 handshake value SHA-1 exists in
/// the tree for. Digests confirmed with `sha1sum`.

use std::sha1 {Sha1.hash, Sha1.hash_bytes}
use std::base64 {B64.encode_std}
use std::list {}

#[test]
def test_sha1_empty : Bool :=
    Sha1.hash "" == "da39a3ee5e6b4b0d3255bfef95601890afd80709"

#[test]
def test_sha1_abc : Bool :=
    Sha1.hash "abc" == "a9993e364706816aba3e25717850c26c9cd0d89d"

// 448 bits: the padding needs a second block.
#[test]
def test_sha1_two_blocks : Bool :=
    Sha1.hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
        == "84983e441c3bd26ebaae4aa1f95129e5e54670f1"

#[test]
def test_sha1_fox : Bool :=
    Sha1.hash "The quick brown fox jumps over the lazy dog"
        == "2fd4e1c67a2d28fced849ee1bb76e7391b93eb12"

// 64 bytes exactly: a whole block of message plus a whole padding block.
#[test]
def test_sha1_one_full_block : Bool :=
    Sha1.hash "0123456701234567012345670123456701234567012345670123456701234567"
        == "e0c094e867ef46c350ef54a7f59dd60bed92ae83"

#[test]
def test_sha1_digest_length : Bool :=
    List.length (Sha1.hash_bytes (String.to_list "x")) == 20

// RFC 6455 §1.3: key "dGhlIHNhbXBsZSBub25jZQ==" accepts as
// "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=".
#[test]
def test_sha1_websocket_accept : Bool :=
    B64.encode_std (Sha1.hash_bytes
        (String.to_list "dGhlIHNhbXBsZSBub25jZQ==258EAFA5-E914-47DA-95CA-C5AB0DC85B11"))
        == "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="
