/// A CSPRNG over OpenSSL's `RAND_bytes`, and the base64url token shape
/// PKCE verifiers, OAuth `state`/`nonce`, and session ids need.
///
/// Compiled backend only: `ByteBuf.ptr` exists only there, so the Rust
/// interpreter cannot run these. Tests that force them are gated by
/// `MONAD_CRYPTO_FFI_TESTS` (see `tests/ffi_tests.mo`).
///
/// The buffer is allocated here, filled in place, read back through
/// `ByteBuf.to_list` with its own length, and freed on every path — the
/// FFI boundary never sees foreign memory or a caller-supplied length.

use std::bytebuf {ByteBuf, ByteBuf.alloc, ByteBuf.free, ByteBuf.ptr, ByteBuf.to_list}
use lib::b64 {B64Url.encode}
use lib::ffi {RAND_bytes}

/// Upper bound on a single draw. Tokens are 32 bytes; the cap only stops a
/// caller from asking for an allocation no consumer could use.
def Random.max_bytes : I64 := 1048576

def Random.clamp (n : I64) : I64 :=
  if I64.lt n 0i64 then 0i64
  else if I64.gt n Random.max_bytes then Random.max_bytes
  else n

/// `n` cryptographically secure bytes. `n <= 0` is the empty list, with no
/// FFI call at all.
pub def Random.bytes (n : I64) : IO (Result String (List U8)) := do {
  let count := Random.clamp n;
  if I64.lt count 1i64
  then return (Result.ok List.empty)
  else Random.draw count
}

def Random.draw (count : I64) : IO (Result String (List U8)) := do {
  let buf <- ByteBuf.alloc count;
  let rc <- IO.mk (RAND_bytes (ByteBuf.ptr buf) (I64.to_i32 count));
  if I64.beq (I32.to_i64 rc) 1i64
  then Random.draw_ok buf count
  else Random.draw_failed buf
}

def Random.draw_ok (buf : ByteBuf) (count : I64) : IO (Result String (List U8)) := do {
  let xs <- ByteBuf.to_list buf count;
  let _ <- ByteBuf.free buf;
  return (Result.ok xs)
}

/// Never read a buffer `RAND_bytes` declined to fill.
def Random.draw_failed (buf : ByteBuf) : IO (Result String (List U8)) := do {
  let _ <- ByteBuf.free buf;
  return (Result.err "rng_failed")
}

/// `Random.bytes n` as an unpadded base64url string: the token format
/// RFC 7636 and OAuth 2.1 use. 32 bytes yields 43 characters.
pub def Random.token (n : I64) : IO (Result String String) := do {
  let r <- Random.bytes n;
  return (match r {
    Result.ok bs => Result.ok (B64Url.encode bs),
    Result.err e => Result.err e,
  })
}
