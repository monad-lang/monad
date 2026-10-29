/// Tests for `std::random`'s `Random` class and `Random.token`.
///
/// The point is the instance itself: this file defines the only `Random`
/// instance it loads (`Random TestRng`), over a deterministic local
/// source, so both hosts run it and no OS entropy is involved. A consumer
/// that loads a different instance gets that one — resolution is
/// per-carrier.

use std::list {}
use std::random {Random, Random.token, RandomError}

type TestRng { test_rng }

/// `n` copies of one byte, in order.
#[terminating]
def test_fill (n : I64) (acc : List U8) : List U8 :=
  if I64.lt n 1i64 then acc else test_fill (I64.sub n 1i64) (List.cons 0x66u8 acc)

pub instance Random TestRng {
  def bytes (r : TestRng) (n : I64) : IO (Result RandomError (List U8)) :=
    IO.pure (Result.ok (test_fill n List.empty))
}

def three_fs : List U8 := [0x66u8, 0x66u8, 0x66u8]

#[test]
def test_random_bytes_uses_the_local_instance : IO Bool := do {
  let res <- Random.bytes TestRng.test_rng 3i64;
  return (match res {
    Result.ok bs => bs == three_fs,
    Result.err _ => false,
  })
}

#[test]
def test_random_token_is_base64url : IO Bool := do {
  let res <- Random.token TestRng.test_rng 4i64;
  return (match res {
    Result.ok t => t == "ZmZmZg",
    Result.err _ => false,
  })
}
