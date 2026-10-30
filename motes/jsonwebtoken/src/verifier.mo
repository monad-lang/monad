/// The injectable signature verifier.
///
/// `JwtVerifier.real` calls `motes/crypto`'s OpenSSL implementation, so it
/// only works on the compiled backend. `JwtVerifier.fake` lets the parse,
/// JWKS, and claim rules run on the Rust host (and lets a test prove the
/// verification-before-claims order). Callers use `JwtVerifier.run` rather
/// than calling the record's function field directly, following
/// `OauthHttp.send_get` in `motes/oauth`.

use crypto::types {CryptoSigAlg, CryptoPublicKey}
use crypto::pubkey {Pubkey.verify}
use lib::errors {JwtError}

pub struct JwtVerifier {
  check : CryptoSigAlg -> CryptoPublicKey -> List U8 -> List U8
    -> IO (Result JwtError Bool)
}

pub def JwtVerifier.run
  (v : JwtVerifier) (alg : CryptoSigAlg) (key : CryptoPublicKey)
  (msg : List U8) (sig : List U8)
  : IO (Result JwtError Bool) :=
  match v {
    { check, .. } => check alg key msg sig
  }

/// A verifier that accepts or rejects every signature. Only for tests and
/// for exercising the claim layer without a crypto backend.
pub def JwtVerifier.fake (accept : Bool) : JwtVerifier :=
  let v : JwtVerifier := {
    check := fn (_alg : CryptoSigAlg) (_key : CryptoPublicKey)
                  (_msg : List U8) (_sig : List U8) =>
      IO.pure (Result.ok accept)
  } in
  v

def JwtVerifier.real_check
  (alg : CryptoSigAlg) (key : CryptoPublicKey) (msg : List U8) (sig : List U8)
  : IO (Result JwtError Bool) := do {
  let r <- Pubkey.verify alg key msg sig;
  return (match r {
    Result.err detail => Result.err (JwtError.verification_failed detail),
    Result.ok ok => Result.ok ok
  })
}

pub def JwtVerifier.real : JwtVerifier :=
  let v : JwtVerifier := { check := JwtVerifier.real_check } in
  v
