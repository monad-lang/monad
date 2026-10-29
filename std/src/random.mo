/// A random-byte source as a class, so code that needs entropy names a
/// source value rather than reaching for a fixed module of IO functions.
///
/// The shape follows `class Stream S` (`std/src/stream.mo`): the class
/// parameter is a handle and the method is effectful. A source may be
/// stateless — a marker type naming an OS RNG, such as `motes/crypto`'s
/// `CryptoRandom` over OpenSSL `RAND_bytes` — or carry state (a seeded
/// generator, a per-request RNG), which is why the class takes a value.
///
/// Tests define their own source type and instance, so entropy-dependent
/// code is testable without touching the OS (see `std/random_tests.mo`).

use std::base64 {B64Url.encode}

/// Why a source produced no bytes: the source's own failure text, which is
/// only ever a fixed phrase, never data it was asked to generate.
pub struct RandomError {
  detail : String
}

/// A source's failure. The detail is the source's own diagnostic.
pub def RandomError.of (detail : String) : RandomError :=
  { detail := detail }

pub def RandomError.to_string (e : RandomError) : String :=
  String.concat "random: " e.detail

/// A source of random bytes. `n <= 0` should yield the empty list, not an
/// error, so callers can use one code path.
pub class Random R {
  def bytes (r : R) (n : I64) : IO (Result RandomError (List U8))
}

/// `Random.bytes r n` as an unpadded base64url string: the token format
/// RFC 7636 and OAuth 2.1 use. 32 bytes yields 43 characters.
pub def Random.token [Random R] (r : R) (n : I64) : IO (Result RandomError String) := do {
  let res <- Random.bytes r n;
  return (match res {
    Result.ok bs => Result.ok (B64Url.encode bs),
    Result.err e => Result.err e,
  })
}
