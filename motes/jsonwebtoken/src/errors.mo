/// The jsonwebtoken mote's error type.
///
/// One variant per failure, so a caller can branch on the reason.
/// `JwtError.to_string` is the ONE render point. No message includes a
/// token, a signature, key material, or a claim value other than the claim
/// NAME.

pub type JwtError {
  // ── compact serialization ─────────────────────────────────────────────
  jwt_malformed,
  jwt_invalid_base64 (part : String),
  jwt_invalid_json (part : String),
  jwt_not_object (part : String),
  jwt_missing_alg,
  jwt_alg_unsupported (alg : String),
  jwt_crit_unsupported,
  jwt_bad_kid,
  jwt_empty_signature,

  // ── JWKS ──────────────────────────────────────────────────────────────
  jwks_invalid_document,
  jwks_missing_keys,
  jwks_key_invalid (field : String),
  jwks_unsupported_kty (kty : String),
  jwks_private_key,
  jwks_weak_rsa,
  jwks_unknown_kid,
  jwks_ambiguous_kid,
  jwks_missing_kid,
  jwks_no_compatible_key,

  // ── claims ────────────────────────────────────────────────────────────
  claims_missing (name : String),
  claims_invalid (name : String),
  claims_issuer_mismatch,
  claims_audience_mismatch,
  claims_azp_mismatch,
  claims_azp_missing,
  claims_expired,
  claims_not_yet_valid,
  claims_issued_in_future,
  claims_nonce_mismatch,
  claims_subject_empty,
  claims_roles_invalid,

  // ── verification boundary ─────────────────────────────────────────────
  /// The crypto backend could not render a verdict (as opposed to
  /// `signature_invalid`, which is a well-formed key rejecting a signature).
  verification_failed (detail : String),
  signature_invalid
}

pub def JwtError.to_string (e : JwtError) : String :=
  match e {
    JwtError.jwt_malformed =>
      "jwt: expected three dot-separated segments",
    JwtError.jwt_invalid_base64 part =>
      String.concat "jwt: invalid base64url in " part,
    JwtError.jwt_invalid_json part =>
      String.concat "jwt: invalid JSON in " part,
    JwtError.jwt_not_object part =>
      String.concat "jwt: " (String.concat part " is not a JSON object"),
    JwtError.jwt_missing_alg => "jwt: header has no alg",
    JwtError.jwt_alg_unsupported alg =>
      String.concat "jwt: unsupported alg " alg,
    JwtError.jwt_crit_unsupported =>
      "jwt: unsupported critical header",
    JwtError.jwt_bad_kid =>
      "jwt: header kid is not a non-empty string",
    JwtError.jwt_empty_signature => "jwt: signature is empty",

    JwtError.jwks_invalid_document => "jwks: not a JSON object",
    JwtError.jwks_missing_keys => "jwks: no keys",
    JwtError.jwks_key_invalid field =>
      String.concat "jwks: invalid " field,
    JwtError.jwks_unsupported_kty kty =>
      String.concat "jwks: unsupported kty " kty,
    JwtError.jwks_private_key => "jwks: key contains private material",
    JwtError.jwks_weak_rsa => "jwks: weak RSA key",
    JwtError.jwks_unknown_kid => "jwks: no key for the token's kid",
    JwtError.jwks_ambiguous_kid =>
      "jwks: more than one key for the token's kid",
    JwtError.jwks_missing_kid =>
      "jwks: token has no kid and the JWKS is not unambiguous",
    JwtError.jwks_no_compatible_key =>
      "jwks: no key for the token's algorithm",

    JwtError.claims_missing name =>
      String.concat "claims: missing " name,
    JwtError.claims_invalid name =>
      String.concat "claims: invalid " name,
    JwtError.claims_issuer_mismatch => "claims: issuer mismatch",
    JwtError.claims_audience_mismatch => "claims: audience mismatch",
    JwtError.claims_azp_mismatch => "claims: azp mismatch",
    JwtError.claims_azp_missing =>
      "claims: azp missing for a multi-valued audience",
    JwtError.claims_expired => "claims: token expired",
    JwtError.claims_not_yet_valid => "claims: token not yet valid",
    JwtError.claims_issued_in_future => "claims: issued in the future",
    JwtError.claims_nonce_mismatch => "claims: nonce mismatch",
    JwtError.claims_subject_empty => "claims: subject is empty",
    JwtError.claims_roles_invalid =>
      "claims: roles claim is not an array of strings",

    JwtError.verification_failed detail => detail,
    JwtError.signature_invalid => "jwt: signature is invalid"
  }
