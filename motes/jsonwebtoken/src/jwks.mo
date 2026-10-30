/// JWK Set parsing and key selection.
///
/// `Jwks.key_for` takes the JWKS document as parsed JSON (fetching it is
/// the caller's job), a `kid` (empty means "the token carried none"), and
/// the token's algorithm. It returns at most one key:
///
///   * a supplied `kid` must match exactly one usable key -- no fallback;
///   * without a `kid`, exactly one compatible key must exist.
///
/// A key is usable when its `kty` matches the algorithm, its `use` (if
/// present) is `sig`, its `key_ops` (if present) contains `verify`, and its
/// `alg` (if present) names the same algorithm. Private material (`d`, the
/// CRT fields, or a symmetric `k`) is a hard error, not a skipped key.
///
/// RSA moduli outside 2048-4096 bits, even/absurd exponents, and EC/OKP
/// coordinates of the wrong length are rejected here and again by
/// `Pubkey.verify` before any OpenSSL handle is allocated.

use std::list {List.any, List.length}
use std::map {BTreeMap}
use std::base64 {B64Url.decode}
use json::json {Json, Json.get_array, Json.get_object, Json.get_str, Json.object_get}
use crypto::types {CryptoSigAlg, CryptoPublicKey}
use crypto::pubkey {Pubkey.key_shape_ok}
use crypto::der {Der.strip_leading_zeros}
use lib::alg {Alg.name}
use lib::errors {JwtError}

// ── field access ──────────────────────────────────────────────────────────

def Jwks.str_field_value (v : Json) : Option String :=
  match Json.get_str v {
    Result.err _ => Option.none,
    Result.ok s => Option.some s
  }

def Jwks.str_field (obj : BTreeMap String Json) (name : String) : Option String :=
  match Json.object_get name obj {
    Option.none => Option.none,
    Option.some v => Jwks.str_field_value v
  }

def Jwks.require_str
  (obj : BTreeMap String Json) (name : String)
  : Result JwtError String :=
  match Jwks.str_field obj name {
    Option.none => Result.err (JwtError.jwks_key_invalid name),
    Option.some s => Result.ok s
  }

def Jwks.bytes_value (name : String) (v : Json) : Result JwtError (List U8) :=
  match Json.get_str v {
    Result.err _ => Result.err (JwtError.jwks_key_invalid name),
    Result.ok s => Jwks.decode_bytes name s
  }

def Jwks.decode_bytes (name : String) (s : String) : Result JwtError (List U8) :=
  match B64Url.decode s {
    Result.err _ => Result.err (JwtError.jwks_key_invalid name),
    Result.ok bs => Result.ok bs
  }

def Jwks.bytes_field
  (obj : BTreeMap String Json) (name : String)
  : Result JwtError (List U8) :=
  match Json.object_get name obj {
    Option.none => Result.err (JwtError.jwks_key_invalid name),
    Option.some v => Jwks.bytes_value name v
  }

def Jwks.has_field (obj : BTreeMap String Json) (name : String) : Bool :=
  match Json.object_get name obj {
    Option.none => false,
    Option.some _ => true
  }

/// Any private member makes the whole key unusable. `k` is listed because
/// an HMAC JWK is symmetric even though this mote never verifies HS*.
def Jwks.private_field (obj : BTreeMap String Json) : Bool :=
  Jwks.has_field obj "d"
    || Jwks.has_field obj "p"
    || Jwks.has_field obj "q"
    || Jwks.has_field obj "dp"
    || Jwks.has_field obj "dq"
    || Jwks.has_field obj "qi"
    || Jwks.has_field obj "k"

// ── candidacy ─────────────────────────────────────────────────────────────

def Jwks.kty_ok (alg : CryptoSigAlg) (kty : String) : Bool :=
  match alg {
    CryptoSigAlg.rs256 => kty == "RSA",
    CryptoSigAlg.es256 => kty == "EC",
    CryptoSigAlg.eddsa => kty == "OKP"
  }

def Jwks.kty_matches (obj : BTreeMap String Json) (alg : CryptoSigAlg) : Bool :=
  match Jwks.str_field obj "kty" {
    Option.none => false,
    Option.some kty => Jwks.kty_ok alg kty
  }

def Jwks.alg_field_ok (obj : BTreeMap String Json) (alg : CryptoSigAlg) : Bool :=
  if Jwks.has_field obj "alg"
  then match Jwks.str_field obj "alg" {
    Option.none => false,
    Option.some s => s == Alg.name alg
  }
  else true

def Jwks.use_ok (obj : BTreeMap String Json) : Bool :=
  if Jwks.has_field obj "use"
  then match Jwks.str_field obj "use" {
    Option.none => false,
    Option.some s => s == "sig"
  }
  else true

/// Required for EC and OKP keys: a mixed-curve JWKS must not make the
/// compatible key look ambiguous.
def Jwks.crv_is (obj : BTreeMap String Json) (want : String) : Bool :=
  if Jwks.has_field obj "crv"
  then match Jwks.str_field obj "crv" {
    Option.none => false,
    Option.some s => s == want
  }
  else false

def Jwks.crv_ok (obj : BTreeMap String Json) (alg : CryptoSigAlg) : Bool :=
  match alg {
    CryptoSigAlg.rs256 => true,
    CryptoSigAlg.es256 => Jwks.crv_is obj "P-256",
    CryptoSigAlg.eddsa => Jwks.crv_is obj "Ed25519"
  }

def Jwks.json_string_is (x : Json) (want : String) : Bool :=
  match Json.get_str x {
    Result.err _ => false,
    Result.ok s => s == want
  }

def Jwks.key_ops_value (v : Json) : Bool :=
  match Json.get_array v {
    Result.err _ => false,
    Result.ok xs => List.any (fn (x : Json) => Jwks.json_string_is x "verify") xs
  }

def Jwks.key_ops_ok (obj : BTreeMap String Json) : Bool :=
  match Json.object_get "key_ops" obj {
    Option.none => true,
    Option.some v => Jwks.key_ops_value v
  }

def Jwks.kid_ok (obj : BTreeMap String Json) (kid : String) : Bool :=
  if String.is_empty kid
  then true
  else match Jwks.str_field obj "kid" {
    Option.none => false,
    Option.some k => k == kid
  }

def Jwks.candidate (alg : CryptoSigAlg) (kid : String) (jwk : Json) : Bool :=
  match Json.get_object jwk {
    Result.err _ => false,
    Result.ok obj =>
      Jwks.kty_matches obj alg
        && Jwks.alg_field_ok obj alg
        && Jwks.use_ok obj
        && Jwks.key_ops_ok obj
        && Jwks.crv_ok obj alg
        && Jwks.kid_ok obj kid
  }

// ── the scan ──────────────────────────────────────────────────────────────

struct JwksCandidates {
  found : Option Json,
  count : I64
}

def Jwks.candidates (found : Option Json) (count : I64) : JwksCandidates :=
  let c : JwksCandidates := { found := found, count := count } in
  c

/// Stop counting past two: only 0, 1 and "more than one" matter.
#[terminating]
def Jwks.scan
  (alg : CryptoSigAlg) (kid : String) (xs : List Json)
  (found : Option Json) (count : I64)
  : JwksCandidates :=
  match xs {
    List.empty => Jwks.candidates found count,
    List.cons k rest =>
      if Jwks.candidate alg kid k
      then if I64.gt count 0i64
           then Jwks.candidates found 2i64
           else Jwks.scan alg kid rest (Option.some k) 1i64
      else Jwks.scan alg kid rest found count
  }

// ── the document ──────────────────────────────────────────────────────────

def Jwks.keys_value (v : Json) : Result JwtError (List Json) :=
  match Json.get_array v {
    Result.err _ => Result.err JwtError.jwks_missing_keys,
    Result.ok xs =>
      if I64.lt (List.length xs) 1i64
      then Result.err JwtError.jwks_missing_keys
      else Result.ok xs
  }

def Jwks.keys_field
  (obj : BTreeMap String Json)
  : Result JwtError (List Json) :=
  match Json.object_get "keys" obj {
    Option.none => Result.err JwtError.jwks_missing_keys,
    Option.some v => Jwks.keys_value v
  }

def Jwks.keys_of (doc : Json) : Result JwtError (List Json) :=
  match Json.get_object doc {
    Result.err _ => Result.err JwtError.jwks_invalid_document,
    Result.ok obj => Jwks.keys_field obj
  }

pub def Jwks.key_for
  (doc : Json) (kid : String) (alg : CryptoSigAlg)
  : Result JwtError CryptoPublicKey :=
  match Jwks.keys_of doc {
    Result.err e => Result.err e,
    Result.ok keys => Jwks.select keys kid alg
  }

def Jwks.too_many (kid : String) : JwtError :=
  if String.is_empty kid
  then JwtError.jwks_missing_kid
  else JwtError.jwks_ambiguous_kid

def Jwks.none_for (kid : String) : JwtError :=
  if String.is_empty kid
  then JwtError.jwks_no_compatible_key
  else JwtError.jwks_unknown_kid

def Jwks.from_found
  (found : Option Json) (alg : CryptoSigAlg)
  : Result JwtError CryptoPublicKey :=
  match found {
    Option.none => Result.err JwtError.jwks_no_compatible_key,
    Option.some jwk => Jwks.parse_key jwk alg
  }

/// Private material is fatal for the whole document, not just the key that
/// selection happens to pick: a JWKS carrying a private key is a
/// misconfiguration worth reporting regardless of which key verifies.
#[terminating]
def Jwks.scan_private (keys : List Json) : Result JwtError Unit :=
  match keys {
    List.empty => Result.ok unit,
    List.cons k rest =>
      match Json.get_object k {
        Result.err _ => Jwks.scan_private rest,
        Result.ok obj =>
          if Jwks.private_field obj
          then Result.err JwtError.jwks_private_key
          else Jwks.scan_private rest
      }
  }

def Jwks.select
  (keys : List Json) (kid : String) (alg : CryptoSigAlg)
  : Result JwtError CryptoPublicKey :=
  match Jwks.scan_private keys {
    Result.err e => Result.err e,
    Result.ok _ => Jwks.select_public keys kid alg
  }

def Jwks.select_public
  (keys : List Json) (kid : String) (alg : CryptoSigAlg)
  : Result JwtError CryptoPublicKey :=
  match Jwks.scan alg kid keys Option.none 0i64 {
    { found, count } =>
      if I64.gt count 1i64 then Result.err (Jwks.too_many kid)
      else if I64.lt count 1i64 then Result.err (Jwks.none_for kid)
      else Jwks.from_found found alg
  }

// ── the chosen key ─────────────────────────────────────────────────────────

def Jwks.parse_key
  (jwk : Json) (alg : CryptoSigAlg)
  : Result JwtError CryptoPublicKey :=
  match Json.get_object jwk {
    Result.err _ => Result.err (JwtError.jwks_key_invalid "key"),
    Result.ok obj => Jwks.parse_obj obj alg
  }

def Jwks.parse_obj
  (obj : BTreeMap String Json) (alg : CryptoSigAlg)
  : Result JwtError CryptoPublicKey :=
  if Jwks.private_field obj
  then Result.err JwtError.jwks_private_key
  else Jwks.parse_for alg obj

def Jwks.parse_for
  (alg : CryptoSigAlg) (obj : BTreeMap String Json)
  : Result JwtError CryptoPublicKey :=
  match alg {
    CryptoSigAlg.rs256 => Jwks.parse_rsa obj,
    CryptoSigAlg.es256 => Jwks.parse_ec obj,
    CryptoSigAlg.eddsa => Jwks.parse_okp obj
  }

def Jwks.parse_rsa
  (obj : BTreeMap String Json)
  : Result JwtError CryptoPublicKey :=
  match Jwks.require_str obj "kty" {
    Result.err e => Result.err e,
    Result.ok kty =>
      if Bool.not (kty == "RSA")
      then Result.err (JwtError.jwks_unsupported_kty kty)
      else Jwks.rsa_from obj
  }

def Jwks.rsa_from
  (obj : BTreeMap String Json)
  : Result JwtError CryptoPublicKey :=
  match Jwks.bytes_field obj "n" {
    Result.err e => Result.err e,
    Result.ok n_raw =>
      match Jwks.bytes_field obj "e" {
        Result.err e => Result.err e,
        Result.ok e_bytes =>
          let n := Der.strip_leading_zeros n_raw in
          let key : CryptoPublicKey := CryptoPublicKey.rsa n e_bytes in
          if Pubkey.key_shape_ok key
          then Result.ok key
          else Result.err JwtError.jwks_weak_rsa
      }
  }

def Jwks.parse_ec
  (obj : BTreeMap String Json)
  : Result JwtError CryptoPublicKey :=
  match Jwks.require_str obj "crv" {
    Result.err e => Result.err e,
    Result.ok crv =>
      if Bool.not (crv == "P-256")
      then Result.err (JwtError.jwks_key_invalid "crv")
      else Jwks.ec_from obj
  }

def Jwks.ec_from
  (obj : BTreeMap String Json)
  : Result JwtError CryptoPublicKey :=
  match Jwks.bytes_field obj "x" {
    Result.err e => Result.err e,
    Result.ok x =>
      match Jwks.bytes_field obj "y" {
        Result.err e => Result.err e,
        Result.ok y =>
          let key : CryptoPublicKey := CryptoPublicKey.ec_p256 x y in
          if Pubkey.key_shape_ok key
          then Result.ok key
          else Result.err (JwtError.jwks_key_invalid "P-256 point")
      }
  }

def Jwks.parse_okp
  (obj : BTreeMap String Json)
  : Result JwtError CryptoPublicKey :=
  match Jwks.require_str obj "crv" {
    Result.err e => Result.err e,
    Result.ok crv =>
      if Bool.not (crv == "Ed25519")
      then Result.err (JwtError.jwks_key_invalid "crv")
      else Jwks.ed_from obj
  }

def Jwks.ed_from
  (obj : BTreeMap String Json)
  : Result JwtError CryptoPublicKey :=
  match Jwks.bytes_field obj "x" {
    Result.err e => Result.err e,
    Result.ok x =>
      let key : CryptoPublicKey := CryptoPublicKey.ed25519 x in
      if Pubkey.key_shape_ok key
      then Result.ok key
      else Result.err (JwtError.jwks_key_invalid "x")
  }
