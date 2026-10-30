/// Claim validation, and the safe entry points that verify first.
///
/// `validate_id_token` / `validate_access_token` are pure and assume the
/// signature is already checked; they exist so tests and audits can inspect
/// claim rules directly. Applications should use `check_id_token` /
/// `check_access_token`, which parse, select the key, verify the signature,
/// and only then call the pure validator.
///
/// `now` is epoch SECONDS (JWT NumericDate), while `IO.current_time` is
/// milliseconds: the caller divides by 1000.

use std::list {List.any, List.filter, List.length}
use std::map {BTreeMap}
use json::json {
  Json, Json.get_array, Json.get_num, Json.get_num_i64, Json.get_str, Json.object_get,
}
use lib::errors {JwtError}
use lib::principal {Principal}
use lib::split {Split.on_byte}
use lib::jwt {Jwt, Jwt.parse, Jwt.verify}
use lib::verifier {JwtVerifier}

/// The configuration claim validation needs. `oauth` builds one from its
/// own `OauthConfig`; a standalone JWT consumer builds it directly.
pub struct ClaimsConfig {
  issuer : String,
  client_id : String,
  audience : Option String := Option.none,
  roles_claim : String := "roles",
  clock_skew_seconds : I64 := 60i64
}

def Claims.space : U8 := 32u8

// ── typed accessors ────────────────────────────────────────────────────────

def Claims.str_value (name : String) (v : Json) : Result JwtError String :=
  match Json.get_str v {
    Result.err _ => Result.err (JwtError.claims_invalid name),
    Result.ok s => Result.ok s
  }

def Claims.str_claim
  (name : String) (claims : BTreeMap String Json)
  : Result JwtError String :=
  match Json.object_get name claims {
    Option.none => Result.err (JwtError.claims_missing name),
    Option.some v => Claims.str_value name v
  }

def Claims.opt_str_value
  (name : String) (v : Json)
  : Result JwtError (Option String) :=
  match Json.get_str v {
    Result.err _ => Result.err (JwtError.claims_invalid name),
    Result.ok s => Result.ok (Option.some s)
  }

def Claims.opt_str_claim
  (name : String) (claims : BTreeMap String Json)
  : Result JwtError (Option String) :=
  match Json.object_get name claims {
    Option.none => Result.ok Option.none,
    Option.some v => Claims.opt_str_value name v
  }

def Claims.int_value (name : String) (v : Json) : Result JwtError I64 :=
  match Json.get_num_i64 (Json.get_num v) {
    Result.err _ => Result.err (JwtError.claims_invalid name),
    Result.ok n => Result.ok n
  }

def Claims.int_claim
  (name : String) (claims : BTreeMap String Json)
  : Result JwtError I64 :=
  match Json.object_get name claims {
    Option.none => Result.err (JwtError.claims_missing name),
    Option.some v => Claims.int_value name v
  }

def Claims.opt_int_value
  (name : String) (v : Json)
  : Result JwtError (Option I64) :=
  match Json.get_num_i64 (Json.get_num v) {
    Result.err _ => Result.err (JwtError.claims_invalid name),
    Result.ok n => Result.ok (Option.some n)
  }

def Claims.opt_int_claim
  (name : String) (claims : BTreeMap String Json)
  : Result JwtError (Option I64) :=
  match Json.object_get name claims {
    Option.none => Result.ok Option.none,
    Option.some v => Claims.opt_int_value name v
  }

// ── string arrays ──────────────────────────────────────────────────────────

#[terminating]
def Claims.strings_go
  (name : String) (xs : List Json) (acc : List String)
  : Result JwtError (List String) :=
  match xs {
    List.empty => Result.ok (List.reverse acc),
    List.cons x rest =>
      match Json.get_str x {
        Result.err _ => Result.err (JwtError.claims_invalid name),
        Result.ok s =>
          if String.is_empty s
          then Result.err (JwtError.claims_invalid name)
          else Claims.strings_go name rest (List.cons s acc)
      }
  }

def Claims.strings_of
  (name : String) (xs : List Json)
  : Result JwtError (List String) :=
  Claims.strings_go name xs List.empty

// ── audience, scopes, roles ────────────────────────────────────────────────

def Claims.aud_value (v : Json) : Result JwtError (List String) :=
  match Json.get_str v {
    Result.ok s =>
      if String.is_empty s
      then Result.err (JwtError.claims_invalid "aud")
      else Result.ok [s],
    Result.err _ => Claims.aud_array v
  }

def Claims.aud_array (v : Json) : Result JwtError (List String) :=
  match Json.get_array v {
    Result.err _ => Result.err (JwtError.claims_invalid "aud"),
    Result.ok xs => Claims.strings_of "aud" xs
  }

def Claims.audiences
  (claims : BTreeMap String Json)
  : Result JwtError (List String) :=
  match Json.object_get "aud" claims {
    Option.none => Result.err (JwtError.claims_missing "aud"),
    Option.some v => Claims.aud_value v
  }

def Claims.contains (want : String) (xs : List String) : Bool :=
  List.any (fn (x : String) => x == want) xs

def Claims.nonempty (xs : List String) : List String :=
  List.filter (fn (x : String) => Bool.not (String.is_empty x)) xs

/// `scp` is an array in Azure AD v2 and RFC 8693, but a space-separated
/// string in Azure AD v1; both forms name scopes, so accept both.
def Claims.scp_value (v : Json) : Result JwtError (List String) :=
  match Json.get_str v {
    Result.ok s => Result.ok (Claims.nonempty (Split.on_byte Claims.space s)),
    Result.err _ => Claims.scp_array v
  }

def Claims.scp_array (v : Json) : Result JwtError (List String) :=
  match Json.get_array v {
    Result.err _ => Result.err (JwtError.claims_invalid "scp"),
    Result.ok xs => Claims.strings_of "scp" xs
  }

def Claims.scp_claim
  (claims : BTreeMap String Json)
  : Result JwtError (List String) :=
  match Json.object_get "scp" claims {
    Option.none => Result.ok List.empty,
    Option.some v => Claims.scp_value v
  }

def Claims.scopes
  (claims : BTreeMap String Json)
  : Result JwtError (List String) :=
  match Claims.opt_str_claim "scope" claims {
    Result.err e => Result.err e,
    Result.ok o =>
      match o {
        Option.some s => Result.ok (Claims.nonempty (Split.on_byte Claims.space s)),
        Option.none => Claims.scp_claim claims
      }
  }

def Claims.roles_value (v : Json) : Result JwtError (List String) :=
  match Json.get_array v {
    Result.err _ => Result.err JwtError.claims_roles_invalid,
    Result.ok xs => Claims.roles_items xs
  }

def Claims.roles_items (xs : List Json) : Result JwtError (List String) :=
  match Claims.strings_of "roles" xs {
    Result.err _ => Result.err JwtError.claims_roles_invalid,
    Result.ok ss => Result.ok ss
  }

def Claims.roles
  (cfg : ClaimsConfig) (claims : BTreeMap String Json)
  : Result JwtError (List String) :=
  match Json.object_get cfg.roles_claim claims {
    Option.none => Result.ok List.empty,
    Option.some v => Claims.roles_value v
  }

// ── individual claim checks ────────────────────────────────────────────────

def Claims.check_issuer
  (cfg : ClaimsConfig) (claims : BTreeMap String Json)
  : Result JwtError Unit :=
  match Claims.str_claim "iss" claims {
    Result.err e => Result.err e,
    Result.ok iss =>
      if iss == cfg.issuer
      then Result.ok unit
      else Result.err JwtError.claims_issuer_mismatch
  }

def Claims.check_sub
  (claims : BTreeMap String Json)
  : Result JwtError String :=
  match Claims.str_claim "sub" claims {
    Result.err e => Result.err e,
    Result.ok sub =>
      if String.is_empty sub
      then Result.err JwtError.claims_subject_empty
      else Result.ok sub
  }

def Claims.check_exp
  (cfg : ClaimsConfig) (now : I64) (claims : BTreeMap String Json)
  : Result JwtError I64 :=
  match Claims.int_claim "exp" claims {
    Result.err e => Result.err e,
    Result.ok exp =>
      if I64.gt now (I64.add exp cfg.clock_skew_seconds)
      then Result.err JwtError.claims_expired
      else Result.ok exp
  }

def Claims.nbf_bound
  (cfg : ClaimsConfig) (now : I64) (o : Option I64)
  : Result JwtError Unit :=
  match o {
    Option.none => Result.ok unit,
    Option.some nbf =>
      if I64.lt (I64.add now cfg.clock_skew_seconds) nbf
      then Result.err JwtError.claims_not_yet_valid
      else Result.ok unit
  }

def Claims.check_nbf
  (cfg : ClaimsConfig) (now : I64) (claims : BTreeMap String Json)
  : Result JwtError Unit :=
  match Claims.opt_int_claim "nbf" claims {
    Result.err e => Result.err e,
    Result.ok o => Claims.nbf_bound cfg now o
  }

def Claims.iat_bound
  (cfg : ClaimsConfig) (now : I64) (o : Option I64)
  : Result JwtError Unit :=
  match o {
    Option.none => Result.ok unit,
    Option.some iat =>
      if I64.gt iat (I64.add now cfg.clock_skew_seconds)
      then Result.err JwtError.claims_issued_in_future
      else Result.ok unit
  }

def Claims.check_iat
  (cfg : ClaimsConfig) (now : I64) (claims : BTreeMap String Json)
  : Result JwtError Unit :=
  match Claims.opt_int_claim "iat" claims {
    Result.err e => Result.err e,
    Result.ok o => Claims.iat_bound cfg now o
  }

def Claims.check_azp
  (cfg : ClaimsConfig) (auds : List String) (claims : BTreeMap String Json)
  : Result JwtError Unit :=
  match Claims.opt_str_claim "azp" claims {
    Result.err e => Result.err e,
    Result.ok o =>
      match o {
        Option.none =>
          if I64.gt (List.length auds) 1i64
          then Result.err JwtError.claims_azp_missing
          else Result.ok unit,
        Option.some azp =>
          if azp == cfg.client_id
          then Result.ok unit
          else Result.err JwtError.claims_azp_mismatch
      }
  }

/// Access tokens have no OIDC `azp` requirement: if the claim is present
/// it must name this client, but a multi-valued `aud` does not demand it.
def Claims.check_azp_optional
  (cfg : ClaimsConfig) (claims : BTreeMap String Json)
  : Result JwtError Unit :=
  match Claims.opt_str_claim "azp" claims {
    Result.err e => Result.err e,
    Result.ok o =>
      match o {
        Option.none => Result.ok unit,
        Option.some azp =>
          if azp == cfg.client_id
          then Result.ok unit
          else Result.err JwtError.claims_azp_mismatch
      }
  }

def Claims.check_nonce
  (expected : String) (claims : BTreeMap String Json)
  : Result JwtError Unit :=
  match Claims.str_claim "nonce" claims {
    Result.err e => Result.err e,
    Result.ok nonce =>
      if nonce == expected
      then Result.ok unit
      else Result.err JwtError.claims_nonce_mismatch
  }

// ── Principal assembly ─────────────────────────────────────────────────────

def Claims.principal
  (sub : String) (iss : String) (auds : List String) (scopes : List String)
  (roles : List String) (claims : BTreeMap String Json) (exp : I64)
  : Principal :=
  let p : Principal := {
    subject := sub,
    issuer := iss,
    audiences := auds,
    scopes := scopes,
    roles := roles,
    claims := claims,
    expires_at := exp
  } in
  p

// ── ID-token validation ────────────────────────────────────────────────────

pub def Claims.validate_id_token
  (cfg : ClaimsConfig) (now : I64) (nonce : String) (j : Jwt)
  : Result JwtError Principal :=
  match j {
    { claims, .. } => Claims.id_issuer cfg now nonce claims
  }

def Claims.id_audiences
  (cfg : ClaimsConfig) (now : I64) (nonce : String) (sub : String) (exp : I64)
  (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.audiences claims {
    Result.err e => Result.err e,
    Result.ok auds =>
      if Claims.contains cfg.client_id auds
      then Claims.id_azp cfg now nonce sub exp auds claims
      else Result.err JwtError.claims_audience_mismatch
  }

def Claims.id_azp
  (cfg : ClaimsConfig) (now : I64) (nonce : String) (sub : String) (exp : I64)
  (auds : List String) (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_azp cfg auds claims {
    Result.err e => Result.err e,
    Result.ok _ => Claims.id_nonce cfg sub exp auds claims nonce
  }

def Claims.id_nonce
  (cfg : ClaimsConfig) (sub : String) (exp : I64) (auds : List String)
  (claims : BTreeMap String Json) (nonce : String)
  : Result JwtError Principal :=
  match Claims.check_nonce nonce claims {
    Result.err e => Result.err e,
    Result.ok _ => Claims.id_finish cfg sub exp auds claims
  }

def Claims.id_finish
  (cfg : ClaimsConfig) (sub : String) (exp : I64) (auds : List String)
  (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.scopes claims {
    Result.err e => Result.err e,
    Result.ok scopes => Claims.id_roles cfg sub exp auds scopes claims
  }

def Claims.id_roles
  (cfg : ClaimsConfig) (sub : String) (exp : I64) (auds : List String)
  (scopes : List String) (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.roles cfg claims {
    Result.err e => Result.err e,
    Result.ok rs => Result.ok (Claims.principal sub cfg.issuer auds scopes rs claims exp)
  }

// The shallow steps that carry a partially-validated token between checks.

def Claims.id_issuer
  (cfg : ClaimsConfig) (now : I64) (nonce : String) (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_issuer cfg claims {
    Result.err e => Result.err e,
    Result.ok _ => Claims.id_sub cfg now nonce claims
  }

def Claims.id_sub
  (cfg : ClaimsConfig) (now : I64) (nonce : String) (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_sub claims {
    Result.err e => Result.err e,
    Result.ok sub => Claims.id_exp cfg now nonce sub claims
  }

def Claims.id_exp
  (cfg : ClaimsConfig) (now : I64) (nonce : String) (sub : String)
  (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_exp cfg now claims {
    Result.err e => Result.err e,
    Result.ok exp => Claims.id_nbf cfg now nonce sub exp claims
  }

def Claims.id_nbf
  (cfg : ClaimsConfig) (now : I64) (nonce : String) (sub : String) (exp : I64)
  (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_nbf cfg now claims {
    Result.err e => Result.err e,
    Result.ok _ => Claims.id_iat cfg now nonce sub exp claims
  }

def Claims.id_iat
  (cfg : ClaimsConfig) (now : I64) (nonce : String) (sub : String) (exp : I64)
  (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_iat cfg now claims {
    Result.err e => Result.err e,
    Result.ok _ => Claims.id_audiences cfg now nonce sub exp claims
  }

// ── access-token validation ────────────────────────────────────────────────

pub def Claims.validate_access_token
  (cfg : ClaimsConfig) (now : I64) (j : Jwt)
  : Result JwtError Principal :=
  match j {
    { claims, .. } => Claims.access_issuer cfg now claims
  }

def Claims.expected_audience (cfg : ClaimsConfig) : String :=
  match cfg.audience {
    Option.none => cfg.client_id,
    Option.some a => a
  }

def Claims.access_issuer
  (cfg : ClaimsConfig) (now : I64) (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_issuer cfg claims {
    Result.err e => Result.err e,
    Result.ok _ => Claims.access_sub cfg now claims
  }

def Claims.access_sub
  (cfg : ClaimsConfig) (now : I64) (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_sub claims {
    Result.err e => Result.err e,
    Result.ok sub => Claims.access_exp cfg now sub claims
  }

def Claims.access_exp
  (cfg : ClaimsConfig) (now : I64) (sub : String) (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_exp cfg now claims {
    Result.err e => Result.err e,
    Result.ok exp => Claims.access_nbf cfg now sub exp claims
  }

def Claims.access_nbf
  (cfg : ClaimsConfig) (now : I64) (sub : String) (exp : I64)
  (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_nbf cfg now claims {
    Result.err e => Result.err e,
    Result.ok _ => Claims.access_iat cfg now sub exp claims
  }

def Claims.access_iat
  (cfg : ClaimsConfig) (now : I64) (sub : String) (exp : I64)
  (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_iat cfg now claims {
    Result.err e => Result.err e,
    Result.ok _ => Claims.access_aud cfg now sub exp claims
  }

def Claims.access_aud
  (cfg : ClaimsConfig) (now : I64) (sub : String) (exp : I64)
  (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.audiences claims {
    Result.err e => Result.err e,
    Result.ok auds =>
      if Claims.contains (Claims.expected_audience cfg) auds
      then Claims.access_azp cfg sub exp auds claims
      else Result.err JwtError.claims_audience_mismatch
  }

def Claims.access_azp
  (cfg : ClaimsConfig) (sub : String) (exp : I64) (auds : List String)
  (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.check_azp_optional cfg claims {
    Result.err e => Result.err e,
    Result.ok _ => Claims.access_finish cfg sub exp auds claims
  }

def Claims.access_finish
  (cfg : ClaimsConfig) (sub : String) (exp : I64) (auds : List String)
  (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.scopes claims {
    Result.err e => Result.err e,
    Result.ok scopes => Claims.access_roles cfg sub exp auds scopes claims
  }

def Claims.access_roles
  (cfg : ClaimsConfig) (sub : String) (exp : I64) (auds : List String)
  (scopes : List String) (claims : BTreeMap String Json)
  : Result JwtError Principal :=
  match Claims.roles cfg claims {
    Result.err e => Result.err e,
    Result.ok rs => Result.ok (Claims.principal sub cfg.issuer auds scopes rs claims exp)
  }

// ── the safe entry points ──────────────────────────────────────────────────

pub def Claims.check_id_token
  (v : JwtVerifier) (jwks : Json) (cfg : ClaimsConfig)
  (now : I64) (nonce : String) (token : String)
  : IO (Result JwtError Principal) := do {
  match Jwt.parse token {
    Result.err e => return (Result.err e),
    Result.ok jwt => Claims.check_id_parsed v jwks cfg now nonce jwt
  }
}

def Claims.check_id_parsed
  (v : JwtVerifier) (jwks : Json) (cfg : ClaimsConfig)
  (now : I64) (nonce : String) (jwt : Jwt)
  : IO (Result JwtError Principal) := do {
  let verified <- Jwt.verify v jwks jwt;
  match verified {
    Result.err e => return (Result.err e),
    Result.ok _ => return (Claims.validate_id_token cfg now nonce jwt)
  }
}

pub def Claims.check_access_token
  (v : JwtVerifier) (jwks : Json) (cfg : ClaimsConfig)
  (now : I64) (token : String)
  : IO (Result JwtError Principal) := do {
  match Jwt.parse token {
    Result.err e => return (Result.err e),
    Result.ok jwt => Claims.check_access_parsed v jwks cfg now jwt
  }
}

def Claims.check_access_parsed
  (v : JwtVerifier) (jwks : Json) (cfg : ClaimsConfig) (now : I64) (jwt : Jwt)
  : IO (Result JwtError Principal) := do {
  let verified <- Jwt.verify v jwks jwt;
  match verified {
    Result.err e => return (Result.err e),
    Result.ok _ => return (Claims.validate_access_token cfg now jwt)
  }
}
