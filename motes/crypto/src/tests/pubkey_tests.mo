/// OpenSSL verification tests for `motes/crypto`.
///
/// Forcing `Pubkey.verify` reaches C symbols and `ByteBuf.ptr`, neither of
/// which exists on the Rust host, so the suite is gated by
/// `MONAD_CRYPTO_FFI_TESTS=1` and returns `true` when the variable is
/// unset.
///
/// The positive vectors are RFC 7515 §A.2 (RS256), §A.3 (ES256, whose JWS
/// signature is raw `R || S`), and RFC 8037 §A.4 (EdDSA).

use std::io {IO.get_env}
use std::base64 {B64Url.decode}
use crypto::types {CryptoSigAlg, CryptoPublicKey}
use crypto::der {Der.ecdsa_raw_to_der}
use crypto::pubkey {Pubkey.verify}

def ffi_enabled : IO Bool := do {
  let v <- IO.get_env "MONAD_CRYPTO_FFI_TESTS";
  return (match v {
    Option.some s => s == "1",
    Option.none => false,
  })
}

def b64 (s : String) : List U8 :=
  match B64Url.decode s {
    Result.ok bs => bs,
    Result.err _ => List.empty
  }

def accepted (r : Result String Bool) : Bool :=
  match r {
    Result.ok b => b,
    Result.err _ => false
  }

/// A well-formed key and a wrong signature is `Ok false`, not `Err`.
def rejected (r : Result String Bool) : Bool :=
  match r {
    Result.ok b => Bool.not b,
    Result.err _ => false
  }

def failed (r : Result String Bool) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err _ => true
  }

#[terminating]
def first_n (n : I64) (xs : List U8) : List U8 :=
  if I64.beq n 0i64 then List.empty
  else match xs {
    List.empty => List.empty,
    List.cons x rest => List.cons x (first_n (I64.sub n 1i64) rest)
  }

// ── RFC 7515 A.2 (RS256) ──────────────────────────────────────────────────

def rsa_n : String := "ofgWCuLjybRlzo0tZWJjNiuSfb4p4fAkd_wWJcyQoTbji9k0l8W26mPddxHmfHQp-Vaw-4qPCJrcS2mJPMEzP1Pt0Bm4d4QlL-yRT-SFd2lZS-pCgNMsD1W_YpRPEwOWvG6b32690r2jZ47soMZo9wGzjb_7OMg0LOL-bSf63kpaSHSXndS5z5rexMdbBYUsLA9e-KXBdQOS-UTo7WTBEMa2R2CapHg665xsmtdVMTBQY4uDZlxvb3qCo5ZwKh9kG4LT6_I5IhlJH7aGhyxXFvUK-DWNmoudF8NAco9_h9iaGNj8q2ethFkMLs91kzk2PAcDTW9gb54h4FRWyuXpoQ"

def rsa_sig : String := "cC4hiUPoj9Eetdgtv3hF80EGrhuB__dzERat0XF9g2VtQgr9PJbu3XOiZj5RZmh7AAuHIm4Bh-0Qc_lF5YKt_O8W2Fp5jujGbds9uJdbF9CUAr7t1dnZcAcQjbKBYNX4BAynRFdiuB--f_nZLgrnbyTyWzO75vRK5h6xBArLIARNPvkSjtQBMHlb1L07Qe7K0GarZRmB_eSN9383LcOLn6_dO--xi12jzDwusC-eOkHWEsqtFZESc6BfI7noOPqvhJ1phCnvWh6IeYI2w9QOYEUipUTI8np6LbgGY9Fs98rqVt5AXLIhWkWywlVmtVrBp0igcN_IoypGlUPQGe77Rw"

/// Header `{"alg":"RS256"}` and the shared example payload.
def rsa_input : String := "eyJhbGciOiJSUzI1NiJ9.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ"

// ── RFC 7515 A.3 (ES256) ──────────────────────────────────────────────────

def ec_x : String := "f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU"
def ec_y : String := "x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0"
def ec_sig : String := "DtEhU3ljbEg8L38VWAfUAqOyKAM6-Xx-F4GawxaepmXFCgfTjDxw5djxLa8ISlSApmWQxfKTUJqPP3-Kg6NU1Q"
def ec_input : String := "eyJhbGciOiJFUzI1NiJ9.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ"

// ── RFC 8037 A.4 (EdDSA) ──────────────────────────────────────────────────

def ed_x : String := "11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo"
def ed_sig : String := "hgyY0il_MGCjP0JzlnLWG1PPOt7-09PGcvMg3AIbQR6dWbhijcNR4ki4iylGjg5BhVsPt9g7sVvpAr_MuM0KAg"
def ed_input : String := "eyJhbGciOiJFZERTQSJ9.RXhhbXBsZSBvZiBFZDI1NTE5IHNpZ25pbmc"

// ── fixtures ──────────────────────────────────────────────────────────────

def rsa_key : CryptoPublicKey := CryptoPublicKey.rsa (b64 rsa_n) (b64 "AQAB")
def ec_key : CryptoPublicKey := CryptoPublicKey.ec_p256 (b64 ec_x) (b64 ec_y)
def ed_key : CryptoPublicKey := CryptoPublicKey.ed25519 (b64 ed_x)

// ── positive vectors ──────────────────────────────────────────────────────

#[test]
def test_pubkey_rs256_rfc7515 : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- Pubkey.verify CryptoSigAlg.rs256 rsa_key
      (String.to_list rsa_input) (b64 rsa_sig);
    return (accepted r)
  }
  else return true
}

#[test]
def test_pubkey_es256_rfc7515 : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- Pubkey.verify CryptoSigAlg.es256 ec_key
      (String.to_list ec_input) (b64 ec_sig);
    return (accepted r)
  }
  else return true
}

#[test]
def test_pubkey_eddsa_rfc8037 : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- Pubkey.verify CryptoSigAlg.eddsa ed_key
      (String.to_list ed_input) (b64 ed_sig);
    return (accepted r)
  }
  else return true
}

// ── negative matrix ───────────────────────────────────────────────────────

#[test]
def test_pubkey_tampered_message_is_rejected : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- Pubkey.verify CryptoSigAlg.rs256 rsa_key
      (String.to_list (String.concat rsa_input "x")) (b64 rsa_sig);
    return (rejected r)
  }
  else return true
}

#[test]
def test_pubkey_eddsa_tampered_signature_is_rejected : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    // Length is preserved, so this reaches verification; only the
    // signature bytes are wrong.
    let sig := List.cons 0u8 (List.tail (b64 ed_sig));
    let r <- Pubkey.verify CryptoSigAlg.eddsa ed_key (String.to_list ed_input) sig;
    return (rejected r)
  }
  else return true
}

#[test]
def test_pubkey_algorithm_key_mismatch_fails : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- Pubkey.verify CryptoSigAlg.rs256 ec_key
      (String.to_list ec_input) (b64 rsa_sig);
    return (failed r)
  }
  else return true
}

#[test]
def test_pubkey_wrong_signature_length_fails : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    let r <- Pubkey.verify CryptoSigAlg.rs256 rsa_key
      (String.to_list rsa_input) List.empty;
    return (failed r)
  }
  else return true
}

#[test]
def test_pubkey_es256_treats_der_prefix_as_raw : IO Bool := do {
  let on <- ffi_enabled;
  if on
  then do {
    // A DER signature is 71 bytes, which the length gate would reject
    // before the conversion runs. Truncate to 64 so it reaches the raw
    // path: the bytes are re-encoded as if they were R || S and the
    // signature must fail, not accidentally verify.
    match Der.ecdsa_raw_to_der (b64 ec_sig) {
      Result.err _ => return false,
      Result.ok der => do {
        let r <- Pubkey.verify CryptoSigAlg.es256 ec_key
          (String.to_list ec_input) (first_n 64i64 der);
        return (rejected r)
      }
    }
  }
  else return true
}
