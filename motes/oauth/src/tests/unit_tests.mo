/// Pure Phase 0-1 tests: RFC 7636 vectors, the exact
/// authorization URL, token parsing rules, configuration validation, and
/// redaction. Runs on the Rust host and the compiled backend alike.

use std::list {}
use std::base64 {B64Url.encode}
use http::types {Uri}
use http::body {Body.from_text}
use json::json {Json.make_array, Json.parse}
use jsonwebtoken::claims {Claims.validate_id_token}
use jsonwebtoken::errors {JwtError}
use jsonwebtoken::jwt {Jwt.parse}
use oauth::client {Client.authorize_url}
use oauth::errors {OauthError, OauthError.of_jwt, OauthError.to_string}
use oauth::config {
  ClientAuth, OauthConfig, OauthConfig.claims_config,
  OauthConfig.scope_string, OauthConfig.validate,
}
use oauth::discovery {Discovery.discovery_url, OauthEndpoints}
use oauth::pkce {Pkce.challenge, Pkce.valid_verifier}
use oauth::state {PendingAuth}
use oauth::token {OauthTokenSet, OauthTokenSet.summary, Token.parse, Token.parse_json, Token.parse_text}

// ── fixtures ─────────────────────────────────────────────────────────────

/// RFC 7636 Appendix B.
def rfc_verifier : String := "dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk"
def rfc_challenge : String := "E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM"

/// Both hosts must see every field spelled out: the Rust host cannot
/// lower a cross-mote struct literal that relies on a field default, so
/// this builder is the one place the full `OauthConfig` shape lives.
def config_of
  (issuer : String) (client_id : String) (redirect_uri : String)
  (scopes : List String) (audience : Option String)
  (client_auth : ClientAuth) (client_secret : Option String)
  (allow_insecure : Bool)
  : OauthConfig :=
  let cfg : OauthConfig := {
    issuer := issuer,
    client_id := client_id,
    redirect_uri := redirect_uri,
    client_secret := client_secret,
    client_auth := client_auth,
    scopes := scopes,
    audience := audience,
    roles_claim := "roles",
    clock_skew_seconds := 60i64,
    secure_cookies := true,
    allow_insecure_localhost := allow_insecure
  } in
  cfg

def good_config : OauthConfig :=
  config_of "https://idp.example" "abc" "https://app.example/callback"
    ["openid", "profile"] Option.none ClientAuth.client_public Option.none false

def no_scope_config : OauthConfig :=
  config_of "https://idp.example" "abc" "https://app.example/callback"
    List.empty (Option.some "api://x") ClientAuth.client_public Option.none false

def idp_authorize : Uri :=
  Uri.uri "https" Option.none "idp.example" Option.none "/authorize" Option.none Option.none

def idp_token : Uri :=
  Uri.uri "https" Option.none "idp.example" Option.none "/token" Option.none Option.none

def test_endpoints : OauthEndpoints := {
  authorization := idp_authorize,
  token := idp_token,
  userinfo := Option.none,
  jwks := Option.none,
  introspection := Option.none,
  end_session := Option.none
}

def test_pending : PendingAuth := {
  state := "st",
  nonce := "n",
  verifier := rfc_verifier,
  redirect_uri := "https://app.example/callback",
  created_at := 0i64,
  return_to := Option.none
}

// ── helpers ──────────────────────────────────────────────────────────────

def token_of (s : String) : Result OauthError OauthTokenSet :=
  match Json.parse s {
    Result.err _ => Result.err OauthError.token_invalid_json,
    Result.ok j => Token.parse_json j
  }

/// The message is what a caller sees: assert on the rendered text.
def err_is (r : Result OauthError OauthTokenSet) (msg : String) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => OauthError.to_string e == msg
  }

def config_ok (r : Result OauthError Unit) : Bool :=
  match r {
    Result.ok _ => true,
    Result.err _ => false
  }

def config_err (r : Result OauthError Unit) : String :=
  match r {
    Result.ok _ => "",
    Result.err e => OauthError.to_string e
  }

// ── PKCE ─────────────────────────────────────────────────────────────────

#[test]
def test_pkce_rfc7636_vector : Bool :=
  Pkce.challenge rfc_verifier == rfc_challenge

#[test]
def test_pkce_verifier_bounds : Bool :=
  Pkce.valid_verifier rfc_verifier
  && Bool.not (Pkce.valid_verifier (String.slice rfc_verifier 0 42i64))
  && Pkce.valid_verifier (String.slice rfc_verifier 0 43i64)
  && Bool.not (Pkce.valid_verifier "abc!")
  && Bool.not (Pkce.valid_verifier "")

// ── the authorization URL ───────────────────────────────────────────────

#[test]
def test_authorize_url_exact : Bool :=
  Client.authorize_url good_config test_endpoints test_pending
    == "https://idp.example/authorize?response_type=code&client_id=abc&redirect_uri=https%3A%2F%2Fapp.example%2Fcallback&scope=openid+profile&state=st&nonce=n&code_challenge=E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM&code_challenge_method=S256"

#[test]
def test_authorize_url_omits_empty_scope_and_adds_audience : Bool :=
  Client.authorize_url no_scope_config test_endpoints test_pending
    == "https://idp.example/authorize?response_type=code&client_id=abc&redirect_uri=https%3A%2F%2Fapp.example%2Fcallback&state=st&nonce=n&code_challenge=E9Melhoa2OwvFrEMTJguCHaoeK1t8URWbuGJSstw-cM&code_challenge_method=S256&audience=api%3A%2F%2Fx"

// ── token parsing ───────────────────────────────────────────────────────

#[test]
def test_token_minimal : Bool :=
  match token_of "{\"access_token\":\"AT\",\"token_type\":\"Bearer\"}" {
    Result.err _ => false,
    Result.ok t =>
      match t {
        { access_token, token_type, refresh_token, scope, .. } =>
          access_token == "AT"
            && token_type == "Bearer"
            && refresh_token == Option.none
            && scope == List.empty
      }
  }

#[test]
def test_token_expires_and_scope : Bool :=
  match token_of "{\"access_token\":\"AT\",\"token_type\":\"bearer\",\"expires_in\":3600,\"scope\":\"openid  profile \"}" {
    Result.err _ => false,
    Result.ok t =>
      match t {
        { expires_in, scope, .. } =>
          expires_in == Option.some 3600i64 && scope == ["openid", "profile"]
      }
  }

#[test]
def test_token_rejects_missing_access_token : Bool :=
  err_is (token_of "{\"token_type\":\"Bearer\"}") "token: missing access_token"

#[test]
def test_token_rejects_missing_token_type : Bool :=
  err_is (token_of "{\"access_token\":\"AT\"}") "token: missing token_type"

#[test]
def test_token_rejects_non_bearer : Bool :=
  err_is (token_of "{\"access_token\":\"AT\",\"token_type\":\"MAC\"}")
    "token: unsupported token_type MAC"

#[test]
def test_token_rejects_bad_expires : Bool :=
  err_is (token_of "{\"access_token\":\"AT\",\"token_type\":\"Bearer\",\"expires_in\":\"3600\"}")
    "token: invalid expires_in"
  && err_is (token_of "{\"access_token\":\"AT\",\"token_type\":\"Bearer\",\"expires_in\":-1}")
    "token: invalid expires_in"

#[test]
def test_token_rejects_empty_refresh : Bool :=
  err_is (token_of "{\"access_token\":\"AT\",\"token_type\":\"Bearer\",\"refresh_token\":\"\"}")
    "token: invalid refresh_token"

#[test]
def test_token_rejects_non_object_and_bad_json : Bool :=
  err_is (Token.parse_json (Json.make_array List.empty)) "token: invalid JSON"
  && err_is (Token.parse_text "not json") "token: invalid JSON"

#[test]
def test_token_parse_checks_status : Bool :=
  err_is (Token.parse 400u16 (Body.from_text "{\"access_token\":\"AT\"}"))
    "token: status 400"

#[test]
def test_summary_redacts_tokens : Bool :=
  match token_of "{\"access_token\":\"SECRET_AT\",\"token_type\":\"Bearer\",\"refresh_token\":\"SECRET_RT\",\"expires_in\":60}" {
    Result.err _ => false,
    Result.ok t =>
      let s := OauthTokenSet.summary t in
      Bool.not (String.contains s "SECRET")
        && String.contains s "expires_in=60"
        && String.contains s "refresh=yes"
  }

// ── configuration ────────────────────────────────────────────────────────

#[test]
def test_config_accepts_https : Bool :=
  config_ok (OauthConfig.validate good_config)

#[test]
def test_scope_string : Bool :=
  OauthConfig.scope_string good_config == "openid profile"

#[test]
def test_config_rejects_http_issuer : Bool :=
  let cfg : OauthConfig :=
    config_of "http://idp.example" "abc" "https://app.example/callback"
      ["openid", "profile"] Option.none ClientAuth.client_public Option.none false
  in
  config_err (OauthConfig.validate cfg) == "config: issuer must use https"

#[test]
def test_config_rejects_issuer_query : Bool :=
  let cfg : OauthConfig :=
    config_of "https://idp.example?x=1" "abc" "https://app.example/callback"
      ["openid", "profile"] Option.none ClientAuth.client_public Option.none false
  in
  config_err (OauthConfig.validate cfg) == "config: invalid issuer"

#[test]
def test_config_allows_loopback : Bool :=
  let cfg : OauthConfig :=
    config_of "http://localhost:8080" "abc" "http://localhost:8080/callback"
      List.empty Option.none ClientAuth.client_public Option.none true
  in
  config_ok (OauthConfig.validate cfg)

#[test]
def test_config_requires_client_id : Bool :=
  let cfg : OauthConfig :=
    config_of "https://idp.example" "" "https://app.example/callback"
      ["openid", "profile"] Option.none ClientAuth.client_public Option.none false
  in
  config_err (OauthConfig.validate cfg) == "config: client_id is empty"

#[test]
def test_config_requires_secret_for_confidential : Bool :=
  let cfg : OauthConfig :=
    config_of "https://idp.example" "abc" "https://app.example/callback"
      ["openid", "profile"] Option.none ClientAuth.client_secret_basic Option.none false
  in
  config_err (OauthConfig.validate cfg)
    == "config: client_secret is required for confidential clients"

#[test]
def test_config_accepts_confidential_with_secret : Bool :=
  let cfg : OauthConfig :=
    config_of "https://idp.example" "abc" "https://app.example/callback"
      ["openid", "profile"] Option.none ClientAuth.client_secret_basic
      (Option.some "s3cret") false
  in
  config_ok (OauthConfig.validate cfg)

// ── discovery URL ────────────────────────────────────────────────────────

#[test]
def test_discovery_url : Bool :=
  Discovery.discovery_url "https://idp.example"
    == "https://idp.example/.well-known/openid-configuration"
  && Discovery.discovery_url "https://idp.example/"
    == "https://idp.example/.well-known/openid-configuration"

// ── jsonwebtoken adapter ─────────────────────────────────────────────────

def jwt_token (header : String) (claims : String) : String :=
  B64Url.encode (String.to_list header)
    ++ "." ++ B64Url.encode (String.to_list claims) ++ ".AQ"

#[test]
def test_claims_config_maps_every_field : Bool :=
  let c := OauthConfig.claims_config no_scope_config in
  c.issuer == "https://idp.example"
    && c.client_id == "abc"
    && c.roles_claim == "roles"
    && c.clock_skew_seconds == 60i64
    && (match c.audience {
      Option.none => false,
      Option.some a => a == "api://x"
    })

#[test]
def test_of_jwt_renders_the_jwt_error : Bool :=
  match OauthError.of_jwt JwtError.claims_expired {
    OauthError.jwt detail => detail == "claims: token expired",
    _ => false
  }

#[test]
def test_oauth_config_validates_an_id_token : Bool :=
  let claims := "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"abc\",\"exp\":1000,\"nonce\":\"n1\"}" in
  match Jwt.parse (jwt_token "{\"alg\":\"RS256\"}" claims) {
    Result.err _ => false,
    Result.ok j =>
      match Claims.validate_id_token (OauthConfig.claims_config good_config) 1000i64 "n1" j {
        Result.ok p => p.subject == "u1",
        Result.err _ => false
      }
  }
