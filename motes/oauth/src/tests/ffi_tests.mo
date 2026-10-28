/// CSPRNG-backed tests.
///
/// `Pkce.verifier` and `OauthStateStore.begin` draw from `Random`, which
/// needs `ByteBuf.ptr` and is compiled-only. Gated by
/// `MONAD_OAUTH_FFI_TESTS=1`; each row returns `true` when the variable is
/// unset so the suite stays green on the Rust host.

use std::io {IO.get_env}
use std::list {List.length}
use crypto::b64 {B64Url.decode}
use oauth::pkce {Pkce.valid_verifier, Pkce.verifier}
use oauth::errors {OauthError}
use oauth::state {OauthStateStore.begin, OauthStateStore.new, PendingAuth}

def ffi_enabled : IO Bool := do {
  let v <- IO.get_env "MONAD_OAUTH_FFI_TESTS";
  return (match v {
    Option.some s => s == "1",
    Option.none => false,
  })
}

def verifier_ok (r : Result String String) : Bool :=
  match r {
    Result.err _ => false,
    Result.ok vraw =>
      let v : String := vraw in
      I64.beq (String.length v) 43i64
        && Pkce.valid_verifier v
        && (match B64Url.decode v {
          Result.ok bs => I64.beq (List.length bs) 32i64,
          Result.err _ => false
        })
  }

def state_of (r : Result OauthError PendingAuth) : String :=
  match r {
    Result.ok p => p.state,
    Result.err _ => "",
  }

#[test]
def test_pkce_verifier_shape : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- Pkce.verifier;
    return (verifier_ok r)
  }
  else return true
}

#[test]
def test_state_begin_generates_distinct_tokens : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let st <- OauthStateStore.new 600i64 4i64;
    let r1 <- OauthStateStore.begin st "https://app.example/callback" Option.none;
    let r2 <- OauthStateStore.begin st "https://app.example/callback" Option.none;
    let s1 := state_of r1;
    let s2 := state_of r2;
    return (Bool.not (String.is_empty s1)
      && Bool.not (String.is_empty s2)
      && Bool.not (s1 == s2))
  }
  else return true
}
