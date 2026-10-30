/// Public-key signature verification over OpenSSL's EVP interface.
///
/// One entry point: `Pubkey.verify` takes the JWS algorithm, a
/// `CryptoPublicKey` (the shape a JWK parses into), the signing input and
/// the JWS signature, and returns whether the signature is valid. A
/// malformed key or an OpenSSL failure is `Err`; a well-formed key with a
/// wrong signature is `Ok false`, so a caller can tell "unavailable" from
/// "rejected".
///
/// Algorithm/key-type mismatches, weak RSA keys, and wrong signature
/// lengths are rejected before any handle is allocated.
///
/// Compiled-backend only: every call below reaches a C symbol, and
/// `ByteBuf.ptr` has no Rust-host implementation. Tests that force it are
/// gated by `MONAD_CRYPTO_FFI_TESTS=1`.

use std::list {List.length}
use std::bytebuf {ByteBuf, ByteBuf.of_list, ByteBuf.ptr, ByteBuf.length, ByteBuf.free}
use lib::types {CryptoSigAlg, CryptoPublicKey}
use lib::der {Der.ecdsa_raw_to_der, Der.strip_leading_zeros}
use lib::ffi {
  BN_bin2bn, BN_free,
  EC_KEY_free, EC_KEY_get0_group, EC_KEY_new_by_curve_name,
  EC_KEY_set_public_key, EC_POINT_free, EC_POINT_new, EC_POINT_oct2point,
  EVP_DigestVerify, EVP_DigestVerifyInit, EVP_MD_CTX_free, EVP_MD_CTX_new,
  EVP_PKEY_free, EVP_PKEY_new, EVP_PKEY_new_raw_public_key,
  EVP_PKEY_set1_EC_KEY, EVP_PKEY_set1_RSA, EVP_sha256,
  RSA_free, RSA_new, RSA_set0_key,
}

/// OpenSSL's success value for the int-returning calls below.
def Pubkey.one : I32 := I64.to_i32 1i64

/// `EVP_DigestVerify`'s "signature is invalid" value.
def Pubkey.zero : I32 := I64.to_i32 0i64

/// `NID_X9_62_prime256v1`, the P-256 curve.
def Pubkey.nid_p256 : I32 := I64.to_i32 415i64

/// `EVP_PKEY_ED25519` (`NID_ED25519`).
def Pubkey.evp_ed25519 : I32 := I64.to_i32 1087i64

def Pubkey.min_rsa_bytes : I64 := 256i64
def Pubkey.max_rsa_bytes : I64 := 512i64
def Pubkey.p256_bytes : I64 := 32i64
def Pubkey.ed25519_sig_bytes : I64 := 64i64
def Pubkey.ecdsa_sig_bytes : I64 := 64i64

// ── pre-flight checks ────────────────────────────────────────────────────

def Pubkey.alg_is (alg : CryptoSigAlg) (which : I64) : Bool :=
  match alg {
    CryptoSigAlg.rs256 => I64.beq which 0i64,
    CryptoSigAlg.es256 => I64.beq which 1i64,
    CryptoSigAlg.eddsa => I64.beq which 2i64
  }

def Pubkey.key_matches (alg : CryptoSigAlg) (key : CryptoPublicKey) : Bool :=
  match key {
    CryptoPublicKey.rsa _ _ => Pubkey.alg_is alg 0i64,
    CryptoPublicKey.ec_p256 _ _ => Pubkey.alg_is alg 1i64,
    CryptoPublicKey.ed25519 _ => Pubkey.alg_is alg 2i64
  }

def Pubkey.shape_error (alg : CryptoSigAlg) : String :=
  match alg {
    CryptoSigAlg.rs256 => "pubkey: invalid RSA key",
    CryptoSigAlg.es256 => "pubkey: invalid P-256 key",
    CryptoSigAlg.eddsa => "pubkey: invalid Ed25519 key"
  }

def Pubkey.first_byte (xs : List U8) : U8 :=
  match xs {
    List.empty => 0u8,
    List.cons x _ => x
  }

def Pubkey.last_byte (xs : List U8) : U8 :=
  match xs {
    List.empty => 0u8,
    List.cons x rest =>
      match rest {
        List.empty => x,
        List.cons _ _ => Pubkey.last_byte rest
      }
  }

def Pubkey.odd (b : U8) : Bool :=
  let v : I64 := U8.to_i64 b in
  Bool.not (I64.beq (I64.mul (I64.div v 2i64) 2i64) v)

/// Non-empty, and numerically at least 3.
def Pubkey.exponent_ok (exponent : List U8) : Bool :=
  let e := Der.strip_leading_zeros exponent in
  let n := List.length e in
  if I64.lt n 1i64 then false
  else if I64.gt n 8i64 then false
  else if Bool.not (Pubkey.odd (Pubkey.last_byte e)) then false
  else if I64.gt n 1i64 then true
  else U8.gt (Pubkey.first_byte e) 2u8

/// RSA modulus is 2048-4096 bits (top bit set) and the exponent is sane.
def Pubkey.rsa_shape_ok (modulus : List U8) (exponent : List U8) : Bool :=
  let n := List.length modulus in
  I64.gt n (I64.sub Pubkey.min_rsa_bytes 1i64)
    && I64.lt n (I64.add Pubkey.max_rsa_bytes 1i64)
    && Bool.not (U8.lt (Pubkey.first_byte modulus) 128u8)
    && Pubkey.exponent_ok exponent

pub def Pubkey.key_shape_ok (key : CryptoPublicKey) : Bool :=
  match key {
    CryptoPublicKey.rsa modulus exponent => Pubkey.rsa_shape_ok modulus exponent,
    CryptoPublicKey.ec_p256 x y =>
      I64.beq (List.length x) Pubkey.p256_bytes
        && I64.beq (List.length y) Pubkey.p256_bytes,
    CryptoPublicKey.ed25519 raw => I64.beq (List.length raw) Pubkey.p256_bytes
  }

/// The signature size is fixed by the key: modulus-width for RSA, 64 raw
/// bytes for ES256, 64 for Ed25519.
def Pubkey.sig_len_ok (key : CryptoPublicKey) (sig : List U8) : Bool :=
  match key {
    CryptoPublicKey.rsa modulus _ => I64.beq (List.length sig) (List.length modulus),
    CryptoPublicKey.ec_p256 _ _ => I64.beq (List.length sig) Pubkey.ecdsa_sig_bytes,
    CryptoPublicKey.ed25519 _ => I64.beq (List.length sig) Pubkey.ed25519_sig_bytes
  }

/// ES256 signatures arrive as `R || S`; OpenSSL wants DER. The other two
/// algorithms use the JWS bytes unchanged.
def Pubkey.signature_bytes (alg : CryptoSigAlg) (sig : List U8) : Result String (List U8) :=
  match alg {
    CryptoSigAlg.rs256 => Result.ok sig,
    CryptoSigAlg.es256 => Der.ecdsa_raw_to_der sig,
    CryptoSigAlg.eddsa => Result.ok sig
  }

// ── the entry point ───────────────────────────────────────────────────────

pub def Pubkey.verify
  (alg : CryptoSigAlg) (key : CryptoPublicKey) (msg : List U8) (sig : List U8)
  : IO (Result String Bool) := do {
  if Bool.not (Pubkey.key_matches alg key)
  then return (Result.err "pubkey: algorithm and key type do not match")
  else if Bool.not (Pubkey.key_shape_ok key)
  then return (Result.err (Pubkey.shape_error alg))
  else if Bool.not (Pubkey.sig_len_ok key sig)
  then return (Result.err "pubkey: wrong signature length")
  else match Pubkey.signature_bytes alg sig {
    Result.err e => return (Result.err e),
    Result.ok sig_bytes => do {
      let msg_buf <- ByteBuf.of_list msg;
      let sig_buf <- ByteBuf.of_list sig_bytes;
      let msg_ptr := ByteBuf.ptr msg_buf;
      let msg_len := ByteBuf.length msg_buf;
      let sig_ptr := ByteBuf.ptr sig_buf;
      let sig_len := ByteBuf.length sig_buf;
      let out <- Pubkey.verify_key key msg_ptr msg_len sig_ptr sig_len;
      let _ <- ByteBuf.free msg_buf;
      let _ <- ByteBuf.free sig_buf;
      return out
    }
  }
}

def Pubkey.verify_key
  (key : CryptoPublicKey)
  (msg_ptr : Ptr) (msg_len : I64) (sig_ptr : Ptr) (sig_len : I64)
  : IO (Result String Bool) :=
  match key {
    CryptoPublicKey.rsa modulus exponent =>
      Pubkey.verify_rsa modulus exponent msg_ptr msg_len sig_ptr sig_len,
    CryptoPublicKey.ec_p256 x y =>
      Pubkey.verify_ec x y msg_ptr msg_len sig_ptr sig_len,
    CryptoPublicKey.ed25519 raw =>
      Pubkey.verify_ed raw msg_ptr msg_len sig_ptr sig_len
  }

// ── key construction ──────────────────────────────────────────────────────

def Pubkey.verify_rsa
  (modulus : List U8) (exponent : List U8)
  (msg_ptr : Ptr) (msg_len : I64) (sig_ptr : Ptr) (sig_len : I64)
  : IO (Result String Bool) := do {
  let n_buf <- ByteBuf.of_list modulus;
  let e_buf <- ByteBuf.of_list exponent;
  let n_bn <- IO.mk (BN_bin2bn (ByteBuf.ptr n_buf) (I64.to_i32 (ByteBuf.length n_buf)) Ptr.null);
  let e_bn <- IO.mk (BN_bin2bn (ByteBuf.ptr e_buf) (I64.to_i32 (ByteBuf.length e_buf)) Ptr.null);
  let _ <- ByteBuf.free n_buf;
  let _ <- ByteBuf.free e_buf;
  let rsa <- IO.mk RSA_new;
  let attached <- IO.mk (RSA_set0_key rsa n_bn e_bn Ptr.null);
  if Bool.not (I32.beq attached Pubkey.one)
  then do {
    let _ <- IO.mk (BN_free n_bn);
    let _ <- IO.mk (BN_free e_bn);
    let _ <- IO.mk (RSA_free rsa);
    return (Result.err "pubkey: could not build the RSA key")
  }
  else do {
    let pkey <- IO.mk EVP_PKEY_new;
    let assigned <- IO.mk (EVP_PKEY_set1_RSA pkey rsa);
    let _ <- IO.mk (RSA_free rsa);
    Pubkey.finish_key assigned pkey EVP_sha256 msg_ptr msg_len sig_ptr sig_len
  }
}

def Pubkey.verify_ec
  (x : List U8) (y : List U8)
  (msg_ptr : Ptr) (msg_len : I64) (sig_ptr : Ptr) (sig_len : I64)
  : IO (Result String Bool) := do {
  let point_bytes := List.cons 4u8 (List.append x y);
  let buf <- ByteBuf.of_list point_bytes;
  let ec <- IO.mk (EC_KEY_new_by_curve_name Pubkey.nid_p256);
  let group := EC_KEY_get0_group ec;
  let point <- IO.mk (EC_POINT_new group);
  let decoded <- IO.mk
    (EC_POINT_oct2point group point (ByteBuf.ptr buf) (ByteBuf.length buf) Ptr.null);
  let _ <- ByteBuf.free buf;
  if Bool.not (I32.beq decoded Pubkey.one)
  then do {
    let _ <- IO.mk (EC_POINT_free point);
    let _ <- IO.mk (EC_KEY_free ec);
    return (Result.err "pubkey: invalid P-256 point")
  }
  else do {
    let installed <- IO.mk (EC_KEY_set_public_key ec point);
    let _ <- IO.mk (EC_POINT_free point);
    if Bool.not (I32.beq installed Pubkey.one)
    then do {
      let _ <- IO.mk (EC_KEY_free ec);
      return (Result.err "pubkey: could not set the P-256 key")
    }
    else do {
      let pkey <- IO.mk EVP_PKEY_new;
      let assigned <- IO.mk (EVP_PKEY_set1_EC_KEY pkey ec);
      let _ <- IO.mk (EC_KEY_free ec);
      Pubkey.finish_key assigned pkey EVP_sha256 msg_ptr msg_len sig_ptr sig_len
    }
  }
}

def Pubkey.verify_ed
  (raw : List U8)
  (msg_ptr : Ptr) (msg_len : I64) (sig_ptr : Ptr) (sig_len : I64)
  : IO (Result String Bool) := do {
  let buf <- ByteBuf.of_list raw;
  let pkey <- IO.mk
    (EVP_PKEY_new_raw_public_key Pubkey.evp_ed25519 Ptr.null
      (ByteBuf.ptr buf) (ByteBuf.length buf));
  let _ <- ByteBuf.free buf;
  // Ed25519 signs the message directly: a NULL digest is not an error.
  Pubkey.verify_with_pkey pkey Ptr.null msg_ptr msg_len sig_ptr sig_len
}

// ── verification ──────────────────────────────────────────────────────────

def Pubkey.finish_key
  (assigned : I32) (pkey : Ptr) (md : Ptr)
  (msg_ptr : Ptr) (msg_len : I64) (sig_ptr : Ptr) (sig_len : I64)
  : IO (Result String Bool) :=
  if Bool.not (I32.beq assigned Pubkey.one)
  then do {
    let _ <- IO.mk (EVP_PKEY_free pkey);
    return (Result.err "pubkey: could not attach the public key")
  }
  else Pubkey.verify_with_pkey pkey md msg_ptr msg_len sig_ptr sig_len

/// Takes ownership of `pkey` on every path.
def Pubkey.verify_with_pkey
  (pkey : Ptr) (md : Ptr)
  (msg_ptr : Ptr) (msg_len : I64) (sig_ptr : Ptr) (sig_len : I64)
  : IO (Result String Bool) := do {
  let ctx <- IO.mk EVP_MD_CTX_new;
  let ready <- IO.mk (EVP_DigestVerifyInit ctx Ptr.null md Ptr.null pkey);
  if Bool.not (I32.beq ready Pubkey.one)
  then do {
    let _ <- IO.mk (EVP_MD_CTX_free ctx);
    let _ <- IO.mk (EVP_PKEY_free pkey);
    return (Result.err "pubkey: could not start verification")
  }
  else do {
    let rc <- IO.mk (EVP_DigestVerify ctx sig_ptr sig_len msg_ptr msg_len);
    let _ <- IO.mk (EVP_MD_CTX_free ctx);
    let _ <- IO.mk (EVP_PKEY_free pkey);
    if I32.beq rc Pubkey.one then return (Result.ok true)
    else if I32.beq rc Pubkey.zero then return (Result.ok false)
    else return (Result.err "pubkey: verification failed")
  }
}
