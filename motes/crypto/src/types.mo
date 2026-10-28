/// Signature algorithms and public-key shapes this mote will verify.
///
/// Phase 0-1 has no verification: `Pubkey.verify` is Phase 3 of
/// `plans/library-ideas/crypto-primitives.md`. These types exist now
/// because `motes/oauth`'s verifier signature names them, and because a
/// JWK parses into exactly this shape.

pub type CryptoSigAlg {
  rs256,
  es256,
  eddsa
}

/// A verification key, as a JWK would carry it: RSA modulus and exponent,
/// P-256 affine coordinates, or a raw Ed25519 public key.
pub type CryptoPublicKey {
  rsa (modulus : List U8) (exponent : List U8),
  ec_p256 (x : List U8) (y : List U8),
  ed25519 (raw : List U8)
}
