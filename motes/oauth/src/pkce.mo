/// PKCE (RFC 7636), S256 only.
///
/// `plain` is deliberately absent: OAuth 2.1 requires S256, and a
/// `plain` branch would only exist to be misconfigured into.
///
/// The challenge is `base64url(SHA-256(verifier))`; the verifier is 32
/// CSPRNG bytes rendered as unpadded base64url, which is 43 characters —
/// inside RFC 7636's 43..128 unreserved-character range.

use std::list {List.all}
use std::sha256 {Sha256.hash_bytes}
use crypto::b64 {B64Url.encode}
use crypto::random {Random.token}
use moose::form {Form.is_unreserved}

pub def Pkce.method : String := "S256"

pub def Pkce.challenge (verifier : String) : String :=
  B64Url.encode (Sha256.hash_bytes (String.to_list verifier))

/// A fresh verifier, or the RNG failure.
pub def Pkce.verifier : IO (Result String String) :=
  Random.token 32i64

/// RFC 7636 §4.1: 43 to 128 characters, all unreserved.
pub def Pkce.valid_verifier (verifier : String) : Bool :=
  let n := String.length verifier in
  I64.lt 42i64 n
    && I64.lt n 129i64
    && List.all (fn (b : U8) => Form.is_unreserved b) (String.to_list verifier)
