/// Pure jsonwebtoken tests: compact-JWS parsing, JWKS selection, claim
/// validation, and the fake-verifier composition order. Both hosts run
/// these; the real verifier's vectors live in `ffi_tests.mo`.

use std::list {List.intercalate}
use std::base64 {B64Url.encode}
use json::json {Json, Json.make_null, Json.parse}
use crypto::types {CryptoSigAlg, CryptoPublicKey}
use jsonwebtoken::alg {Alg.name}
use jsonwebtoken::claims {
  Claims.check_id_token,
  Claims.validate_access_token,
  Claims.validate_id_token,
  ClaimsConfig,
}
use jsonwebtoken::errors {JwtError, JwtError.to_string}
use jsonwebtoken::jwt {Jwt, Jwt.parse}
use jsonwebtoken::jwks {Jwks.key_for}
use jsonwebtoken::principal {Principal}
use jsonwebtoken::verifier {JwtVerifier}

// ── fixtures ──────────────────────────────────────────────────────────────

/// RFC 7515 §A.2 modulus; only its shape matters to the selection tests.
def rsa_n : String := "ofgWCuLjybRlzo0tZWJjNiuSfb4p4fAkd_wWJcyQoTbji9k0l8W26mPddxHmfHQp-Vaw-4qPCJrcS2mJPMEzP1Pt0Bm4d4QlL-yRT-SFd2lZS-pCgNMsD1W_YpRPEwOWvG6b32690r2jZ47soMZo9wGzjb_7OMg0LOL-bSf63kpaSHSXndS5z5rexMdbBYUsLA9e-KXBdQOS-UTo7WTBEMa2R2CapHg665xsmtdVMTBQY4uDZlxvb3qCo5ZwKh9kG4LT6_I5IhlJH7aGhyxXFvUK-DWNmoudF8NAco9_h9iaGNj8q2ethFkMLs91kzk2PAcDTW9gb54h4FRWyuXpoQ"
def rsa_e : String := "AQAB"

/// RFC 7515 §A.3 P-256 coordinates.
def ec_x : String := "f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU"
def ec_y : String := "x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0"
def ec_jwk : String :=
  "{\"kty\":\"EC\",\"crv\":\"P-256\",\"x\":\"" ++ ec_x ++ "\",\"y\":\"" ++ ec_y ++ "\"}"

def config_of
  (issuer : String) (client_id : String) (audience : Option String)
  : ClaimsConfig :=
  let c : ClaimsConfig := {
    issuer := issuer,
    client_id := client_id,
    audience := audience,
    roles_claim := "roles",
    clock_skew_seconds := 60i64
  } in
  c

def good_config : ClaimsConfig :=
  config_of "https://idp.example" "abc" Option.none

def audience_config : ClaimsConfig :=
  config_of "https://idp.example" "abc" (Option.some "api://x")

def header_of (alg : String) : String :=
  "{\"alg\":\"" ++ alg ++ "\"}"

def header_kid (alg : String) (kid : String) : String :=
  "{\"alg\":\"" ++ alg ++ "\",\"kid\":\"" ++ kid ++ "\"}"

def b64 (s : String) : String :=
  B64Url.encode (String.to_list s)

def token_of (header : String) (claims : String) (sig : String) : String :=
  b64 header ++ "." ++ b64 claims ++ "." ++ sig

/// `.AQ` decodes to one 0x01 byte, enough for every fake-verifier case.
def token_json (header : String) (claims : String) : String :=
  token_of header claims "AQ"

def id_claims : String :=
  "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"abc\",\"exp\":1000,\"iat\":900,\"nonce\":\"n1\",\"scope\":\"openid profile\",\"roles\":[\"admin\"]}"

def id_token : String := token_json (header_of "RS256") id_claims

def rs_jwk : String :=
  "{\"kty\":\"RSA\",\"n\":\"" ++ rsa_n ++ "\",\"e\":\"" ++ rsa_e ++ "\"}"

def jwks_text (entries : List String) : String :=
  "{\"keys\":[" ++ List.intercalate "," entries ++ "]}"

def jwks_rsa_text : String := jwks_text [rs_jwk]

def jwks_rsa : Json :=
  match Json.parse jwks_rsa_text {
    Result.ok j => j,
    Result.err _ => Json.make_null
  }

def key_for_text
  (text : String) (kid : String) (alg : CryptoSigAlg)
  : Result JwtError CryptoPublicKey :=
  match Json.parse text {
    Result.err _ => Result.err JwtError.jwks_invalid_document,
    Result.ok doc => Jwks.key_for doc kid alg
  }

// ── result helpers ────────────────────────────────────────────────────────

def parse_err (token : String) (msg : String) : Bool :=
  match Jwt.parse token {
    Result.ok _ => false,
    Result.err e => JwtError.to_string e == msg
  }

def validate_id
  (cfg : ClaimsConfig) (now : I64) (nonce : String) (token : String)
  : Result JwtError Principal :=
  match Jwt.parse token {
    Result.err e => Result.err e,
    Result.ok j => Claims.validate_id_token cfg now nonce j
  }

def validate_access
  (cfg : ClaimsConfig) (now : I64) (token : String)
  : Result JwtError Principal :=
  match Jwt.parse token {
    Result.err e => Result.err e,
    Result.ok j => Claims.validate_access_token cfg now j
  }

def claims_err
  (r : Result JwtError Principal) (msg : String)
  : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => JwtError.to_string e == msg
  }

def claims_ok (r : Result JwtError Principal) : Bool :=
  match r {
    Result.ok _ => true,
    Result.err _ => false
  }

def key_ok (r : Result JwtError CryptoPublicKey) : Bool :=
  match r {
    Result.ok _ => true,
    Result.err _ => false
  }

def key_err (r : Result JwtError CryptoPublicKey) (msg : String) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => JwtError.to_string e == msg
  }

// ── parsing ───────────────────────────────────────────────────────────────

#[test]
def test_parse_accepts_rfc_shaped_token : Bool :=
  match Jwt.parse id_token {
    Result.err _ => false,
    Result.ok j =>
      j.signing_input == b64 (header_of "RS256") ++ "." ++ b64 id_claims
        && Alg.name j.alg == "RS256"
        && (match j.kid { Option.none => true, Option.some _ => false })
  }

#[test]
def test_parse_requires_three_segments : Bool :=
  parse_err "abc.def" "jwt: expected three dot-separated segments"
    && parse_err "a.b.c.d" "jwt: expected three dot-separated segments"
    && parse_err "a..b" "jwt: expected three dot-separated segments"

#[test]
def test_parse_rejects_bad_base64 : Bool :=
  parse_err "!!.e30.AQ" "jwt: invalid base64url in header"

#[test]
def test_parse_requires_json_objects : Bool :=
  parse_err (token_json "not json" "{}")
    "jwt: invalid JSON in header"
    && parse_err (token_json "[1]" "{}") "jwt: header is not a JSON object"
    && parse_err (token_json "{\"alg\":\"RS256\"}" "[1]")
         "jwt: claims is not a JSON object"

#[test]
def test_parse_rejects_alg_none_and_hmac : Bool :=
  parse_err (token_json (header_of "none") "{}")
    "jwt: unsupported alg none"
    && parse_err (token_json (header_of "HS256") "{}")
         "jwt: unsupported alg HS256"

#[test]
def test_parse_rejects_missing_alg : Bool :=
  parse_err (token_json "{}" "{}") "jwt: header has no alg"

#[test]
def test_parse_rejects_crit : Bool :=
  parse_err (token_json "{\"alg\":\"RS256\",\"crit\":[\"exp\"]}" "{}")
    "jwt: unsupported critical header"

#[test]
def test_parse_rejects_bad_kid : Bool :=
  parse_err (token_json "{\"alg\":\"RS256\",\"kid\":5}" "{}")
    "jwt: header kid is not a non-empty string"
    && parse_err (token_json (header_kid "RS256" "") "{}")
         "jwt: header kid is not a non-empty string"

#[test]
def test_parse_rejects_empty_signature : Bool :=
  parse_err (b64 (header_of "RS256") ++ "." ++ b64 "{}" ++ ".")
    "jwt: expected three dot-separated segments"

#[test]
def test_parse_rejects_oversize_token : Bool :=
  parse_err (String.repeat "a" 65537i64)
    "jwt: expected three dot-separated segments"

// ── JWKS ──────────────────────────────────────────────────────────────────

#[test]
def test_jwks_single_rsa_without_kid : Bool :=
  key_ok (key_for_text jwks_rsa_text "" CryptoSigAlg.rs256)

#[test]
def test_jwks_kid_selects_exactly : Bool :=
  let text := jwks_text [
    "{\"kty\":\"RSA\",\"kid\":\"a\",\"n\":\"" ++ rsa_n ++ "\",\"e\":\"" ++ rsa_e ++ "\"}",
    "{\"kty\":\"RSA\",\"kid\":\"b\",\"n\":\"" ++ rsa_n ++ "\",\"e\":\"" ++ rsa_e ++ "\"}"
  ] in
  key_ok (key_for_text text "b" CryptoSigAlg.rs256)
    && key_err (key_for_text text "c" CryptoSigAlg.rs256)
         "jwks: no key for the token's kid"

#[test]
def test_jwks_without_kid_must_be_unambiguous : Bool :=
  let text := jwks_text [rs_jwk, rs_jwk] in
  key_err (key_for_text text "" CryptoSigAlg.rs256)
    "jwks: token has no kid and the JWKS is not unambiguous"

#[test]
def test_jwks_rejects_private_key : Bool :=
  let jwk := "{\"kty\":\"RSA\",\"d\":\"AQAB\",\"n\":\"" ++ rsa_n ++ "\",\"e\":\"" ++ rsa_e ++ "\"}" in
  key_err (key_for_text (jwks_text [jwk]) "" CryptoSigAlg.rs256)
    "jwks: key contains private material"

#[test]
def test_jwks_rejects_weak_rsa : Bool :=
  let small := B64Url.encode (String.to_list (String.repeat "n" 128i64)) in
  let jwk := "{\"kty\":\"RSA\",\"n\":\"" ++ small ++ "\",\"e\":\"" ++ rsa_e ++ "\"}" in
  key_err (key_for_text (jwks_text [jwk]) "" CryptoSigAlg.rs256)
    "jwks: weak RSA key"

#[test]
def test_jwks_skips_encryption_keys : Bool :=
  let jwk := "{\"kty\":\"RSA\",\"use\":\"enc\",\"n\":\"" ++ rsa_n ++ "\",\"e\":\"" ++ rsa_e ++ "\"}" in
  key_err (key_for_text (jwks_text [jwk]) "" CryptoSigAlg.rs256)
    "jwks: no key for the token's algorithm"

#[test]
def test_jwks_skips_other_alg_names : Bool :=
  let jwk := "{\"kty\":\"RSA\",\"alg\":\"RS512\",\"n\":\"" ++ rsa_n ++ "\",\"e\":\"" ++ rsa_e ++ "\"}" in
  key_err (key_for_text (jwks_text [jwk]) "" CryptoSigAlg.rs256)
    "jwks: no key for the token's algorithm"

#[test]
def test_jwks_requires_verify_in_key_ops : Bool :=
  let good := "{\"kty\":\"RSA\",\"key_ops\":[\"verify\"],\"n\":\"" ++ rsa_n ++ "\",\"e\":\"" ++ rsa_e ++ "\"}" in
  let bad := "{\"kty\":\"RSA\",\"key_ops\":[\"encrypt\"],\"n\":\"" ++ rsa_n ++ "\",\"e\":\"" ++ rsa_e ++ "\"}" in
  key_ok (key_for_text (jwks_text [good]) "" CryptoSigAlg.rs256)
    && key_err (key_for_text (jwks_text [bad]) "" CryptoSigAlg.rs256)
         "jwks: no key for the token's algorithm"

#[test]
def test_jwks_private_member_anywhere_is_fatal : Bool :=
  // The public key would verify, but a JWKS carrying private material is a
  // misconfiguration and must be reported regardless of selection.
  let private_jwk := "{\"kty\":\"RSA\",\"d\":\"AQAB\",\"n\":\"" ++ rsa_n ++ "\",\"e\":\"" ++ rsa_e ++ "\"}" in
  key_err (key_for_text (jwks_text [rs_jwk, private_jwk]) "" CryptoSigAlg.rs256)
    "jwks: key contains private material"

#[test]
def test_jwks_mixed_curve_selects_p256 : Bool :=
  // A P-384 key must not count as a second compatible key for ES256.
  let p384 := "{\"kty\":\"EC\",\"crv\":\"P-384\"}" in
  key_ok (key_for_text (jwks_text [p384, ec_jwk]) "" CryptoSigAlg.es256)

#[test]
def test_jwks_non_string_alg_is_not_a_candidate : Bool :=
  let jwk := "{\"kty\":\"RSA\",\"alg\":5,\"n\":\"" ++ rsa_n ++ "\",\"e\":\"" ++ rsa_e ++ "\"}" in
  key_err (key_for_text (jwks_text [jwk]) "" CryptoSigAlg.rs256)
    "jwks: no key for the token's algorithm"

// ── claims ────────────────────────────────────────────────────────────────

#[test]
def test_id_token_happy_path : Bool :=
  match validate_id good_config 1000i64 "n1" id_token {
    Result.err _ => false,
    Result.ok p =>
      p.subject == "u1"
        && p.issuer == "https://idp.example"
        && p.audiences == ["abc"]
        && p.scopes == ["openid", "profile"]
        && p.roles == ["admin"]
        && p.expires_at == 1000i64
  }

#[test]
def test_id_token_wrong_issuer : Bool :=
  claims_err
    (validate_id (config_of "https://other.example" "abc" Option.none) 1000i64 "n1" id_token)
    "claims: issuer mismatch"

#[test]
def test_id_token_expired : Bool :=
  claims_err (validate_id good_config 2000i64 "n1" id_token)
    "claims: token expired"

#[test]
def test_id_token_nonce_mismatch : Bool :=
  claims_err (validate_id good_config 1000i64 "other" id_token)
    "claims: nonce mismatch"

#[test]
def test_id_token_wrong_audience : Bool :=
  let claims := "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"other\",\"exp\":1000,\"nonce\":\"n1\"}" in
  claims_err (validate_id good_config 1000i64 "n1" (token_json (header_of "RS256") claims))
    "claims: audience mismatch"

#[test]
def test_id_token_multi_audience_requires_azp : Bool :=
  let claims := "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":[\"abc\",\"other\"],\"exp\":1000,\"nonce\":\"n1\"}" in
  claims_err (validate_id good_config 1000i64 "n1" (token_json (header_of "RS256") claims))
    "claims: azp missing for a multi-valued audience"

#[test]
def test_id_token_multi_audience_with_azp : Bool :=
  let claims := "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":[\"abc\",\"other\"],\"azp\":\"abc\",\"exp\":1000,\"nonce\":\"n1\"}" in
  claims_ok (validate_id good_config 1000i64 "n1" (token_json (header_of "RS256") claims))

#[test]
def test_id_token_nbf : Bool :=
  let claims := "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"abc\",\"exp\":2000,\"nbf\":1100,\"nonce\":\"n1\"}" in
  let tok := token_json (header_of "RS256") claims in
  claims_err (validate_id good_config 1000i64 "n1" tok) "claims: token not yet valid"
    && claims_ok (validate_id good_config 1100i64 "n1" tok)

#[test]
def test_id_token_iat_in_future : Bool :=
  let claims := "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"abc\",\"exp\":2000,\"iat\":1200,\"nonce\":\"n1\"}" in
  claims_err (validate_id good_config 1000i64 "n1" (token_json (header_of "RS256") claims))
    "claims: issued in the future"

#[test]
def test_id_token_requires_sub : Bool :=
  let claims := "{\"iss\":\"https://idp.example\",\"aud\":\"abc\",\"exp\":1000,\"nonce\":\"n1\"}" in
  claims_err (validate_id good_config 1000i64 "n1" (token_json (header_of "RS256") claims))
    "claims: missing sub"

#[test]
def test_access_token_audience : Bool :=
  let good := "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"api://x\",\"exp\":1000,\"scp\":[\"read\"]}" in
  let bad := "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"abc\",\"exp\":1000}" in
  match validate_access audience_config 1000i64 (token_json (header_of "RS256") good) {
    Result.err _ => false,
    Result.ok p =>
      p.scopes == ["read"]
        && claims_err (validate_access audience_config 1000i64 (token_json (header_of "RS256") bad))
             "claims: audience mismatch"
  }

#[test]
def test_access_token_multi_audience_needs_no_azp : Bool :=
  // OIDC's multi-audience azp rule is an ID-token rule; RFC 9068 access
  // tokens do not carry one.
  let claims := "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":[\"api://x\",\"api://y\"],\"exp\":1000}" in
  claims_ok (validate_access audience_config 1000i64 (token_json (header_of "RS256") claims))

#[test]
def test_access_token_scp_string : Bool :=
  // Azure AD v1 spells `scp` as a space-separated string.
  let claims := "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"api://x\",\"exp\":1000,\"scp\":\"read write\"}" in
  match validate_access audience_config 1000i64 (token_json (header_of "RS256") claims) {
    Result.err _ => false,
    Result.ok p => p.scopes == ["read", "write"]
  }

// ── composition order ─────────────────────────────────────────────────────

#[test]
def test_check_rejects_signature_before_claims : IO Bool := do {
  // `now` makes the claims expired; a rejection must still be the
  // signature, which proves no claim was inspected first.
  let r <- Claims.check_id_token (JwtVerifier.fake false) jwks_rsa good_config
    2000i64 "n1" id_token;
  return (claims_err r "jwt: signature is invalid")
}

#[test]
def test_check_accepts_with_fake_verifier : IO Bool := do {
  let r <- Claims.check_id_token (JwtVerifier.fake true) jwks_rsa good_config
    1000i64 "n1" id_token;
  return (claims_ok r)
}

#[test]
def test_check_unknown_kid_stops_before_verifier : IO Bool := do {
  let token := token_json (header_kid "RS256" "missing") id_claims;
  let r <- Claims.check_id_token (JwtVerifier.fake true) jwks_rsa good_config
    1000i64 "n1" token;
  return (claims_err r "jwks: no key for the token's kid")
}
