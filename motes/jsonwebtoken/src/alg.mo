/// JWS `alg` spellings, in one place.
///
/// `CryptoSigAlg` is the crypto mote's type; the wire names are JOSE's.
/// Keeping the mapping here means `Jwt.parse` and JWKS selection cannot
/// disagree about what "RS256" means.

use crypto::types {CryptoSigAlg}

pub def Alg.name (a : CryptoSigAlg) : String :=
  match a {
    CryptoSigAlg.rs256 => "RS256",
    CryptoSigAlg.es256 => "ES256",
    CryptoSigAlg.eddsa => "EdDSA"
  }

/// The allowlist is exactly the three algorithms `crypto` can verify.
/// `none` and every `HS*` are absent by construction.
pub def Alg.parse (s : String) : Option CryptoSigAlg :=
  if s == "RS256" then Option.some CryptoSigAlg.rs256
  else if s == "ES256" then Option.some CryptoSigAlg.es256
  else if s == "EdDSA" then Option.some CryptoSigAlg.eddsa
  else Option.none
