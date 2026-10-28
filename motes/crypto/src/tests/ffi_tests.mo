/// CSPRNG tests.
///
/// `Random.*` needs `ByteBuf.ptr`, which exists only in the compiled
/// backend, so anything that forces the FFI is gated by
/// `MONAD_CRYPTO_FFI_TESTS=1` and returns `true` when the variable is
/// unset. The two `n <= 0` tests are ungated: they return before the
/// allocation and prove the short-circuit.

use std::io {IO.get_env}
use std::list {List.any, List.length}
use crypto::b64 {B64Url.decode}
use crypto::ct {Ct.eq}
use crypto::random {Random.bytes, Random.token}

def ffi_enabled : IO Bool := do {
  let v <- IO.get_env "MONAD_CRYPTO_FFI_TESTS";
  return (match v {
    Option.some s => s == "1",
    Option.none => false,
  })
}

def has_nonzero (bs : List U8) : Bool :=
  List.any (fn (b : U8) => Bool.not (U8.beq b 0u8)) bs

def differ (a : Result String (List U8)) (b : Result String (List U8)) : Bool :=
  match a {
    Result.err _ => false,
    Result.ok x => match b {
      Result.err _ => false,
      Result.ok y => Bool.not (Ct.eq x y)
    }
  }

def token_is_32_bytes (r : Result String String) : Bool :=
  match r {
    Result.err _ => false,
    Result.ok traw =>
      let tok : String := traw in
      if I64.beq (String.length tok) 43i64
      then match B64Url.decode tok {
        Result.ok bs => I64.beq (List.length bs) 32i64,
        Result.err _ => false
      }
      else false
  }

#[test]
def test_random_zero_bytes : IO Bool := do {
  let r <- Random.bytes 0i64;
  return (match r {
    Result.ok bs => bs == List.empty,
    Result.err _ => false,
  })
}

#[test]
def test_random_negative_bytes : IO Bool := do {
  let r <- Random.bytes (I64.sub 0i64 5i64);
  return (match r {
    Result.ok bs => bs == List.empty,
    Result.err _ => false,
  })
}

#[test]
def test_random_32_bytes : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- Random.bytes 32i64;
    return (match r {
      Result.ok bs => I64.beq (List.length bs) 32i64,
      Result.err _ => false,
    })
  }
  else return true
}

#[test]
def test_random_not_all_zero : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- Random.bytes 32i64;
    return (match r {
      Result.ok bs => has_nonzero bs,
      Result.err _ => false,
    })
  }
  else return true
}

#[test]
def test_random_two_draws_differ : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r1 <- Random.bytes 32i64;
    let r2 <- Random.bytes 32i64;
    return (differ r1 r2)
  }
  else return true
}

#[test]
def test_random_token_is_base64url : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- Random.token 32i64;
    return (token_is_32_bytes r)
  }
  else return true
}
