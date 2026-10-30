/// Compact JWS parsing.
///
/// `Jwt.parse` is pure and does NOT establish trust: it only proves the
/// token is structurally a JWS with an allowlisted `alg`. The signature is
/// checked by `Jwt.verify` (or, preferably, by `Claims.check_*`, which
/// verifies before reading a single claim).
///
/// Rules: exactly three dot-separated, non-empty segments; base64url with
/// no non-canonical trailing bits (`std::base64` enforces that); header and
/// claims must be JSON objects; `alg` must be RS256, ES256 or EdDSA (so
/// `none` and every `HS*` are rejected here); a non-empty `crit` is
/// rejected; `kid`, when present, must be a non-empty string. `typ` is
/// ignored. The signing input is the first two segments verbatim, so it is
/// exactly what the issuer signed.

use std::list {List.length}
use std::map {BTreeMap}
use std::base64 {B64Url.decode}
use json::json {
  Json, Json.get_array, Json.get_object, Json.get_str, Json.object_get, Json.parse,
}
use crypto::types {CryptoSigAlg}
use lib::alg {Alg.parse}
use lib::split {Split.on_byte}
use lib::errors {JwtError}
use lib::jwks {Jwks.key_for}
use lib::verifier {JwtVerifier, JwtVerifier.run}

pub struct Jwt {
  header : BTreeMap String Json,
  claims : BTreeMap String Json,
  alg : CryptoSigAlg,
  kid : Option String,
  signing_input : String,
  signature : List U8
}

/// A JWT larger than this is not a credential any of our consumers issue;
/// the cap keeps parsing and the claims walk bounded.
def Jwt.max_token_bytes : I64 := 65536i64

def Jwt.dot : U8 := 46u8

// ── splitting ─────────────────────────────────────────────────────────────

/// Exactly three segments, or `Option.none`.
def Jwt.exactly_three (segs : List String) : Option (Pair String (Pair String String)) :=
  match segs {
    List.cons a rest =>
      match rest {
        List.cons b rest2 =>
          match rest2 {
            List.cons c rest3 =>
              match rest3 {
                List.empty => Option.some (Pair.pair a (Pair.pair b c)),
                List.cons _ _ => Option.none
              },
            _ => Option.none
          },
        _ => Option.none
      },
    _ => Option.none
  }

// ── segment decoding ──────────────────────────────────────────────────────

def Jwt.decode_part (part : String) (s : String) : Result JwtError (List U8) :=
  if String.is_empty s
  then Result.err (JwtError.jwt_invalid_base64 part)
  else match B64Url.decode s {
    Result.err _ => Result.err (JwtError.jwt_invalid_base64 part),
    Result.ok bs => Result.ok bs
  }

def Jwt.as_object
  (part : String) (j : Json)
  : Result JwtError (BTreeMap String Json) :=
  match Json.get_object j {
    Result.err _ => Result.err (JwtError.jwt_not_object part),
    Result.ok o => Result.ok o
  }

def Jwt.object_of
  (part : String) (bytes : List U8)
  : Result JwtError (BTreeMap String Json) :=
  match Json.parse (String.from_list bytes) {
    Result.err _ => Result.err (JwtError.jwt_invalid_json part),
    Result.ok j => Jwt.as_object part j
  }

def Jwt.parse_part
  (part : String) (s : String)
  : Result JwtError (BTreeMap String Json) :=
  match Jwt.decode_part part s {
    Result.err e => Result.err e,
    Result.ok bytes => Jwt.object_of part bytes
  }

// ── header fields ─────────────────────────────────────────────────────────

def Jwt.header_alg_value (v : Json) : Result JwtError CryptoSigAlg :=
  match Json.get_str v {
    Result.err _ => Result.err JwtError.jwt_missing_alg,
    Result.ok s => Jwt.alg_or_error s
  }

def Jwt.alg_or_error (s : String) : Result JwtError CryptoSigAlg :=
  match Alg.parse s {
    Option.none => Result.err (JwtError.jwt_alg_unsupported s),
    Option.some a => Result.ok a
  }

def Jwt.header_alg
  (header : BTreeMap String Json)
  : Result JwtError CryptoSigAlg :=
  match Json.object_get "alg" header {
    Option.none => Result.err JwtError.jwt_missing_alg,
    Option.some v => Jwt.header_alg_value v
  }

def Jwt.header_kid_value (v : Json) : Result JwtError (Option String) :=
  match Json.get_str v {
    Result.err _ => Result.err JwtError.jwt_bad_kid,
    Result.ok s =>
      if String.is_empty s
      then Result.err JwtError.jwt_bad_kid
      else Result.ok (Option.some s)
  }

def Jwt.header_kid
  (header : BTreeMap String Json)
  : Result JwtError (Option String) :=
  match Json.object_get "kid" header {
    Option.none => Result.ok Option.none,
    Option.some v => Jwt.header_kid_value v
  }

/// We understand no extensions, so any non-empty `crit` list is fatal.
/// A present-but-empty list promises nothing and is allowed.
def Jwt.crit_value (v : Json) : Bool :=
  match Json.get_array v {
    Result.err _ => false,
    Result.ok xs => I64.beq (List.length xs) 0i64
  }

def Jwt.crit_ok (header : BTreeMap String Json) : Bool :=
  match Json.object_get "crit" header {
    Option.none => true,
    Option.some v => Jwt.crit_value v
  }

// ── assembling ────────────────────────────────────────────────────────────

def Jwt.build
  (header : BTreeMap String Json) (claims : BTreeMap String Json)
  (signing_input : String) (signature : List U8)
  (alg : CryptoSigAlg) (kid : Option String)
  : Jwt :=
  let out : Jwt := {
    header := header,
    claims := claims,
    alg := alg,
    kid := kid,
    signing_input := signing_input,
    signature := signature
  } in
  out

pub def Jwt.parse (token : String) : Result JwtError Jwt :=
  if I64.gt (String.length token) Jwt.max_token_bytes
  then Result.err JwtError.jwt_malformed
  else Jwt.parse_segments (Split.on_byte Jwt.dot token)

def Jwt.parse_segments (segs : List String) : Result JwtError Jwt :=
  match Jwt.exactly_three segs {
    Option.none => Result.err JwtError.jwt_malformed,
    Option.some parts => Jwt.parse_parts_of parts
  }

def Jwt.parse_parts_of
  (parts : Pair String (Pair String String))
  : Result JwtError Jwt :=
  match parts {
    Pair.pair h rest =>
      match rest {
        Pair.pair c s => Jwt.parse_parts h c s
      }
  }

def Jwt.parse_parts (h : String) (c : String) (s : String) : Result JwtError Jwt :=
  if String.is_empty h || String.is_empty c || String.is_empty s
  then Result.err JwtError.jwt_malformed
  else match Jwt.parse_part "header" h {
    Result.err e => Result.err e,
    Result.ok header => Jwt.parse_claims header h c s
  }

def Jwt.parse_claims
  (header : BTreeMap String Json) (h : String) (c : String) (s : String)
  : Result JwtError Jwt :=
  match Jwt.parse_part "claims" c {
    Result.err e => Result.err e,
    Result.ok claims => Jwt.parse_signature header h claims c s
  }

def Jwt.parse_signature
  (header : BTreeMap String Json) (h : String)
  (claims : BTreeMap String Json) (c : String) (s : String)
  : Result JwtError Jwt :=
  match Jwt.decode_part "signature" s {
    Result.err e => Result.err e,
    Result.ok signature => Jwt.finish header h claims c signature
  }

def Jwt.finish
  (header : BTreeMap String Json) (h : String)
  (claims : BTreeMap String Json) (c : String) (signature : List U8)
  : Result JwtError Jwt :=
  if I64.lt (List.length signature) 1i64
  then Result.err JwtError.jwt_empty_signature
  else if Bool.not (Jwt.crit_ok header)
  then Result.err JwtError.jwt_crit_unsupported
  else match Jwt.header_alg header {
    Result.err e => Result.err e,
    Result.ok alg => Jwt.finish_kid header h claims c signature alg
  }

def Jwt.finish_kid
  (header : BTreeMap String Json) (h : String)
  (claims : BTreeMap String Json) (c : String) (signature : List U8)
  (alg : CryptoSigAlg)
  : Result JwtError Jwt :=
  match Jwt.header_kid header {
    Result.err e => Result.err e,
    Result.ok kid =>
      Result.ok
        (Jwt.build header claims
          (String.concat h (String.concat "." c)) signature alg kid)
  }

// ── verification ──────────────────────────────────────────────────────────

/// Select the key by the header's `kid` and `alg`, then verify the signature
/// over the verbatim signing input. On success the caller may trust the
/// claims; on `Ok false` the signature is simply wrong.
pub def Jwt.verify
  (v : JwtVerifier) (jwks : Json) (j : Jwt)
  : IO (Result JwtError Unit) := do {
  match j {
    { alg, kid, signing_input, signature, .. } =>
      let kid_text : String :=
        match kid {
          Option.none => "",
          Option.some k => k
        } in
      match Jwks.key_for jwks kid_text alg {
        Result.err e => return (Result.err e),
        Result.ok key => do {
          let checked <- JwtVerifier.run v alg key
            (String.to_list signing_input) signature;
          return (match checked {
            Result.err e => Result.err e,
            Result.ok verified =>
              if verified
              then Result.ok unit
              else Result.err JwtError.signature_invalid
          })
        }
      }
  }
}
