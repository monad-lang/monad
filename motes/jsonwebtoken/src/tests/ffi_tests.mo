/// Real-signature tests for jsonwebtoken.
///
/// These go through `Jwt.parse` -> `Jwks.key_for` -> `JwtVerifier.real`, so
/// they force OpenSSL and `ByteBuf.ptr`; gated by `MONAD_JWT_FFI_TESTS=1`
/// and returns `true` when the variable is unset.
///
/// Vectors: RFC 7515 §A.2 (RS256), §A.3 (ES256), RFC 8037 §A.4 (EdDSA).
/// The RFC payloads are not OIDC claims (no `aud`/`sub`), so only signature
/// verification is exercised here; the claim matrix is pure and lives in
/// `unit_tests.mo`. RFC 8037's payload is plain text, not JSON, so that
/// vector goes through `Jwks.key_for` + `JwtVerifier.real` directly rather
/// than `Jwt.parse`.

use std::io {IO.get_env}
use std::base64 {B64Url.decode, B64Url.encode}
use json::json {Json, Json.make_null, Json.parse}
use crypto::types {CryptoSigAlg}
use jsonwebtoken::errors {JwtError, JwtError.to_string}
use jsonwebtoken::jwt {Jwt.parse, Jwt.verify}
use jsonwebtoken::jwks {Jwks.key_for}
use jsonwebtoken::verifier {JwtVerifier, JwtVerifier.run}

def ffi_enabled : IO Bool := do {
  let v <- IO.get_env "MONAD_JWT_FFI_TESTS";
  return (match v {
    Option.some s => s == "1",
    Option.none => false,
  })
}

def b64 (s : String) : String :=
  B64Url.encode (String.to_list s)

def jwks_of (text : String) : Json :=
  match Json.parse text {
    Result.ok j => j,
    Result.err _ => Json.make_null
  }

def verify_ok (r : Result JwtError Unit) : Bool :=
  match r {
    Result.ok _ => true,
    Result.err _ => false
  }

def verify_err (r : Result JwtError Unit) (msg : String) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => JwtError.to_string e == msg
  }

// ── RFC 7515 A.2 (RS256) ──────────────────────────────────────────────────

def rsa_n : String := "ofgWCuLjybRlzo0tZWJjNiuSfb4p4fAkd_wWJcyQoTbji9k0l8W26mPddxHmfHQp-Vaw-4qPCJrcS2mJPMEzP1Pt0Bm4d4QlL-yRT-SFd2lZS-pCgNMsD1W_YpRPEwOWvG6b32690r2jZ47soMZo9wGzjb_7OMg0LOL-bSf63kpaSHSXndS5z5rexMdbBYUsLA9e-KXBdQOS-UTo7WTBEMa2R2CapHg665xsmtdVMTBQY4uDZlxvb3qCo5ZwKh9kG4LT6_I5IhlJH7aGhyxXFvUK-DWNmoudF8NAco9_h9iaGNj8q2ethFkMLs91kzk2PAcDTW9gb54h4FRWyuXpoQ"
def rs_sig : String := "cC4hiUPoj9Eetdgtv3hF80EGrhuB__dzERat0XF9g2VtQgr9PJbu3XOiZj5RZmh7AAuHIm4Bh-0Qc_lF5YKt_O8W2Fp5jujGbds9uJdbF9CUAr7t1dnZcAcQjbKBYNX4BAynRFdiuB--f_nZLgrnbyTyWzO75vRK5h6xBArLIARNPvkSjtQBMHlb1L07Qe7K0GarZRmB_eSN9383LcOLn6_dO--xi12jzDwusC-eOkHWEsqtFZESc6BfI7noOPqvhJ1phCnvWh6IeYI2w9QOYEUipUTI8np6LbgGY9Fs98rqVt5AXLIhWkWywlVmtVrBp0igcN_IoypGlUPQGe77Rw"
def rs_header : String := "eyJhbGciOiJSUzI1NiJ9"
def shared_payload : String := "eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ"

def rs_token : String := rs_header ++ "." ++ shared_payload ++ "." ++ rs_sig

def rs_jwks : Json :=
  jwks_of ("{\"keys\":[{\"kty\":\"RSA\",\"n\":\"" ++ rsa_n ++ "\",\"e\":\"AQAB\"}]}")

// ── RFC 7515 A.3 (ES256) ──────────────────────────────────────────────────

def ec_x : String := "f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU"
def ec_y : String := "x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0"
def es_sig : String := "DtEhU3ljbEg8L38VWAfUAqOyKAM6-Xx-F4GawxaepmXFCgfTjDxw5djxLa8ISlSApmWQxfKTUJqPP3-Kg6NU1Q"
def es_header : String := "eyJhbGciOiJFUzI1NiJ9"
def es_token : String := es_header ++ "." ++ shared_payload ++ "." ++ es_sig

def es_jwks : Json :=
  jwks_of ("{\"keys\":[{\"kty\":\"EC\",\"crv\":\"P-256\",\"x\":\""
    ++ ec_x ++ "\",\"y\":\"" ++ ec_y ++ "\"}]}")

// ── RFC 8037 A.4 (EdDSA) ──────────────────────────────────────────────────

def ed_x : String := "11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo"
def ed_sig : String := "hgyY0il_MGCjP0JzlnLWG1PPOt7-09PGcvMg3AIbQR6dWbhijcNR4ki4iylGjg5BhVsPt9g7sVvpAr_MuM0KAg"
def ed_header : String := "eyJhbGciOiJFZERTQSJ9"
def ed_payload : String := "RXhhbXBsZSBvZiBFZDI1NTE5IHNpZ25pbmc"

def ed_jwks : Json :=
  jwks_of ("{\"keys\":[{\"kty\":\"OKP\",\"crv\":\"Ed25519\",\"x\":\""
    ++ ed_x ++ "\"}]}")

// ── helpers ───────────────────────────────────────────────────────────────

def verify_token (jwks : Json) (token : String) : IO (Result JwtError Unit) := do {
  match Jwt.parse token {
    Result.err e => return (Result.err e),
    Result.ok jwt => Jwt.verify JwtVerifier.real jwks jwt
  }
}

// ── positive vectors ──────────────────────────────────────────────────────

#[test]
def test_real_rs256_rfc7515 : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- verify_token rs_jwks rs_token;
    return (verify_ok r)
  }
  else return true
}

#[test]
def test_real_es256_rfc7515 : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- verify_token es_jwks es_token;
    return (verify_ok r)
  }
  else return true
}

#[test]
def test_real_eddsa_rfc8037 : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    // RFC 8037's payload is text, so `Jwt.parse` (JSON object required)
    // would reject it; exercise the key selection and real verifier.
    match Jwks.key_for ed_jwks "" CryptoSigAlg.eddsa {
      Result.err _ => return false,
      Result.ok key => do {
        let sig := match B64Url.decode ed_sig {
          Result.ok bs => bs,
          Result.err _ => List.empty
        };
        let r <- JwtVerifier.run JwtVerifier.real CryptoSigAlg.eddsa key
          (String.to_list (ed_header ++ "." ++ ed_payload)) sig;
        return (match r {
          Result.ok b => b,
          Result.err _ => false
        })
      }
    }
  }
  else return true
}

// ── negative matrix ───────────────────────────────────────────────────────

#[test]
def test_real_tampered_payload_is_rejected : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let tampered := rs_header ++ "." ++ b64 "{\"iss\":\"joe\"}" ++ "." ++ rs_sig;
    let r <- verify_token rs_jwks tampered;
    return (verify_err r "jwt: signature is invalid")
  }
  else return true
}

#[test]
def test_real_alg_key_mismatch_is_an_error : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    // The RS256 token against the EC-only JWKS: no compatible key.
    let r <- verify_token es_jwks rs_token;
    return (verify_err r "jwks: no key for the token's algorithm")
  }
  else return true
}

#[test]
def test_real_short_signature_is_an_error : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    // A 64-byte ES256 signature against the RSA key: the length gate must
    // reject it (the RSA modulus is 256 bytes), not the verifier.
    let token := rs_header ++ "." ++ shared_payload ++ "." ++ es_sig;
    let r <- verify_token rs_jwks token;
    return (verify_err r "pubkey: wrong signature length")
  }
  else return true
}

#[test]
def test_real_unknown_kid_is_an_error : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let header := "{\"alg\":\"RS256\",\"kid\":\"missing\"}";
    let token := b64 header ++ "." ++ shared_payload ++ "." ++ rs_sig;
    let r <- verify_token rs_jwks token;
    return (verify_err r "jwks: no key for the token's kid")
  }
  else return true
}
