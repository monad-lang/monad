/// The OpenSSL `RAND_bytes` implementation of `std::random`'s `Random`
/// class.
///
/// The class and `Random.token` live in `std`; this mote supplies the only
/// OS-backed source. `CryptoRandom` is a marker type: the value carries no
/// state because the entropy comes from the OS through OpenSSL. A seeded
/// or software generator would keep its state in its own type and the
/// class would pick that instance up unchanged.
///
/// Compiled backend only: `ByteBuf.ptr` exists only there, so the Rust
/// interpreter cannot run these. Tests that force them are gated by
/// `MONAD_CRYPTO_FFI_TESTS` (see `tests/ffi_tests.mo`).
///
/// The buffer is allocated here, filled in place, read back through
/// `ByteBuf.to_list` with its own length, and freed on every path — the
/// FFI boundary never sees foreign memory or a caller-supplied length.

use std::bytebuf {ByteBuf, ByteBuf.alloc, ByteBuf.free, ByteBuf.ptr, ByteBuf.to_list}
use std::random {Random, RandomError}
use lib::ffi {RAND_bytes}

/// The OpenSSL random-byte source. Stateless: the value names the OS RNG.
pub type CryptoRandom { crypto_random }

/// The source value. A zero-argument def, so each use constructs a fresh
/// value: a caller may draw more than once without an affine complaint,
/// and call sites read `Random.token CryptoRandom.new 32i64`.
pub def CryptoRandom.new : CryptoRandom := CryptoRandom.crypto_random

/// Upper bound on a single draw. Tokens are 32 bytes; the cap only stops a
/// caller from asking for an allocation no consumer could use.
priv def random_max_bytes : I64 := 1048576

priv def random_clamp (n : I64) : I64 :=
  if I64.lt n 0i64 then 0i64
  else if I64.gt n random_max_bytes then random_max_bytes
  else n

priv def random_draw (count : I64) : IO (Result RandomError (List U8)) := do {
  let buf <- ByteBuf.alloc count;
  let rc <- IO.mk (RAND_bytes (ByteBuf.ptr buf) (I64.to_i32 count));
  if I64.beq (I32.to_i64 rc) 1i64
  then random_draw_ok buf count
  else random_draw_failed buf
}

priv def random_draw_ok (buf : ByteBuf) (count : I64) : IO (Result RandomError (List U8)) := do {
  let xs <- ByteBuf.to_list buf count;
  let _ <- ByteBuf.free buf;
  return (Result.ok xs)
}

/// Never read a buffer `RAND_bytes` declined to fill.
priv def random_draw_failed (buf : ByteBuf) : IO (Result RandomError (List U8)) := do {
  let _ <- ByteBuf.free buf;
  return (Result.err (RandomError.of "openssl RAND_bytes returned 0"))
}

pub instance Random CryptoRandom {
  def bytes (r : CryptoRandom) (n : I64) : IO (Result RandomError (List U8)) := do {
    let count := random_clamp n;
    if I64.lt count 1i64
    then return (Result.ok List.empty)
    else random_draw count
  }
}
