/// Fake-IdP tests: no socket, no network. Discovery, token exchange,
/// refresh, userinfo, and the state store's one-time / TTL / cap rules.
///
/// The state-store rows call the package-private `begin_at`/`take_at`
/// seams so `now` is fixed and no RNG is involved; they run on both hosts.
/// Everything that would force `Random` is in `ffi_tests.mo` instead.

use std::list {}
use http::types {Headers, Headers.empty, Uri}
use http::uri {Uri.format}
use json::json {Json.to_string}
use oauth::client {Client.exchange_code, Client.refresh, Client.userinfo}
use oauth::config {ClientAuth, OauthConfig}
use oauth::discovery {Discovery.load, OauthEndpoints}
use oauth::errors {OauthError, OauthError.to_string}
use oauth::http_client {OauthHttp.fake, ScriptedExchange}
use oauth::state {
  OauthStateStore.begin_at, OauthStateStore.new, OauthStateStore.take_at, PendingAuth,
}

// ── fixtures ─────────────────────────────────────────────────────────────

/// Every field is spelled: the Rust host cannot lower a cross-mote
/// struct literal that relies on a field default.
def config_of
  (issuer : String) (client_id : String) (redirect_uri : String)
  (allow_insecure : Bool)
  : OauthConfig :=
  let cfg : OauthConfig := {
    issuer := issuer,
    client_id := client_id,
    redirect_uri := redirect_uri,
    client_secret := Option.none,
    client_auth := ClientAuth.client_public,
    scopes := List.empty,
    audience := Option.none,
    roles_claim := "roles",
    clock_skew_seconds := 60i64,
    secure_cookies := true,
    allow_insecure_localhost := allow_insecure
  } in
  cfg

def idp_config : OauthConfig :=
  config_of "https://idp.example" "abc" "https://app.example/callback" false

def loopback_config : OauthConfig :=
  config_of "http://localhost:8080" "abc" "http://localhost:8080/callback" true

def well_known_path : String := "/.well-known/openid-configuration"

/// Struct literals in argument/list position are not inferred by both
/// hosts; these annotated constructors keep every fixture a plain call.
def exchange_of (path : String) (status : U16) (body : String) : ScriptedExchange :=
  let ex : ScriptedExchange := {
    path := path,
    status := status,
    body := body,
    headers := Headers.empty,
    body_contains := ""
  } in
  ex

def exchange_with
  (path : String) (status : U16) (body : String) (needle : String)
  : ScriptedExchange :=
  let ex : ScriptedExchange := {
    path := path,
    status := status,
    body := body,
    headers := Headers.empty,
    body_contains := needle
  } in
  ex

def good_doc : String :=
  "{\"issuer\":\"https://idp.example\",\"authorization_endpoint\":\"https://idp.example/authorize\",\"token_endpoint\":\"https://idp.example/token\",\"userinfo_endpoint\":\"https://idp.example/userinfo\",\"jwks_uri\":\"https://idp.example/jwks\"}"

def bad_issuer_doc : String :=
  "{\"issuer\":\"https://other.example\",\"authorization_endpoint\":\"https://idp.example/authorize\",\"token_endpoint\":\"https://idp.example/token\"}"

def no_token_doc : String :=
  "{\"issuer\":\"https://idp.example\",\"authorization_endpoint\":\"https://idp.example/authorize\"}"

def cross_origin_doc : String :=
  "{\"issuer\":\"https://idp.example\",\"authorization_endpoint\":\"https://idp.example/authorize\",\"token_endpoint\":\"https://evil.example/token\"}"

def insecure_doc : String :=
  "{\"issuer\":\"https://idp.example\",\"authorization_endpoint\":\"https://idp.example/authorize\",\"token_endpoint\":\"http://idp.example/token\"}"

def loopback_doc : String :=
  "{\"issuer\":\"http://localhost:8080\",\"authorization_endpoint\":\"http://localhost:8080/authorize\",\"token_endpoint\":\"http://localhost:8080/token\"}"

def token_json_code : String :=
  "{\"access_token\":\"AT_CODE\",\"token_type\":\"Bearer\",\"expires_in\":3600,\"refresh_token\":\"RT1\"}"

def token_json_refresh : String :=
  "{\"access_token\":\"AT_REFRESH\",\"token_type\":\"Bearer\",\"expires_in\":3600,\"refresh_token\":\"RT2\"}"

def userinfo_json : String := "{\"sub\":\"u1\",\"email\":\"u1@example.test\"}"

def token_endpoints : OauthEndpoints := {
  authorization := Uri.uri "https" Option.none "idp.example" Option.none "/authorize" Option.none Option.none,
  token := Uri.uri "https" Option.none "idp.example" Option.none "/token" Option.none Option.none,
  userinfo := Option.none,
  jwks := Option.none,
  introspection := Option.none,
  end_session := Option.none
}

def userinfo_endpoints : OauthEndpoints := {
  authorization := Uri.uri "https" Option.none "idp.example" Option.none "/authorize" Option.none Option.none,
  token := Uri.uri "https" Option.none "idp.example" Option.none "/token" Option.none Option.none,
  userinfo := Option.some (Uri.uri "https" Option.none "idp.example" Option.none "/userinfo" Option.none Option.none),
  jwks := Option.none,
  introspection := Option.none,
  end_session := Option.none
}

def token_posts : List ScriptedExchange := [
  exchange_with "/token" 200u16 token_json_code "grant_type=authorization_code",
  exchange_with "/token" 200u16 token_json_refresh "grant_type=refresh_token"
]

// ── helpers ──────────────────────────────────────────────────────────────

def uri_is (o : Option Uri) (s : String) : Bool :=
  match o {
    Option.none => false,
    Option.some u => Uri.format u == s
  }

def ep_authorization (r : Result OauthError OauthEndpoints) : String :=
  match r {
    Result.err _ => "",
    Result.ok ep => match ep {
      { authorization, .. } => Uri.format authorization
    }
  }

def ep_token (r : Result OauthError OauthEndpoints) : String :=
  match r {
    Result.err _ => "",
    Result.ok ep => match ep {
      { token, .. } => Uri.format token
    }
  }

def ep_userinfo (r : Result OauthError OauthEndpoints) : Option Uri :=
  match r {
    Result.err _ => Option.none,
    Result.ok ep => match ep {
      { userinfo, .. } => userinfo
    }
  }

def ep_jwks (r : Result OauthError OauthEndpoints) : Option Uri :=
  match r {
    Result.err _ => Option.none,
    Result.ok ep => match ep {
      { jwks, .. } => jwks
    }
  }

def discovery_err (r : Result OauthError OauthEndpoints) : String :=
  match r {
    Result.err e => OauthError.to_string e,
    Result.ok _ => ""
  }

def is_some (o : Option PendingAuth) : Bool :=
  match o {
    Option.none => false,
    Option.some _ => true
  }

def begun_ok (r : Result OauthError PendingAuth) : Bool :=
  match r {
    Result.ok _ => true,
    Result.err _ => false
  }

def one_get (body : String) : List ScriptedExchange := [
  exchange_of well_known_path 200u16 body
]

// ── discovery ────────────────────────────────────────────────────────────

#[test]
def test_discovery_ok : IO Bool := do {
  let h <- OauthHttp.fake (one_get good_doc) List.empty;
  let r <- Discovery.load h idp_config;
  return (ep_authorization r == "https://idp.example/authorize"
    && ep_token r == "https://idp.example/token"
    && uri_is (ep_userinfo r) "https://idp.example/userinfo"
    && uri_is (ep_jwks r) "https://idp.example/jwks")
}

#[test]
def test_discovery_issuer_mismatch : IO Bool := do {
  let h <- OauthHttp.fake (one_get bad_issuer_doc) List.empty;
  let r <- Discovery.load h idp_config;
  return (discovery_err r == "discovery: issuer mismatch")
}

#[test]
def test_discovery_missing_token_endpoint : IO Bool := do {
  let h <- OauthHttp.fake (one_get no_token_doc) List.empty;
  let r <- Discovery.load h idp_config;
  return (discovery_err r == "discovery: missing token_endpoint")
}

#[test]
def test_discovery_rejects_cross_origin : IO Bool := do {
  let h <- OauthHttp.fake (one_get cross_origin_doc) List.empty;
  let r <- Discovery.load h idp_config;
  return (discovery_err r == "discovery: cross-origin token_endpoint")
}

#[test]
def test_discovery_rejects_insecure_endpoint : IO Bool := do {
  let h <- OauthHttp.fake (one_get insecure_doc) List.empty;
  let r <- Discovery.load h idp_config;
  return (discovery_err r == "discovery: insecure token_endpoint")
}

#[test]
def test_discovery_rejects_redirect : IO Bool := do {
  let gets : List ScriptedExchange := [
    exchange_of well_known_path 302u16 ""
  ];
  let h <- OauthHttp.fake gets List.empty;
  let r <- Discovery.load h idp_config;
  return (discovery_err r == "discovery: redirect not followed")
}

#[test]
def test_discovery_rejects_invalid_json : IO Bool := do {
  let h <- OauthHttp.fake (one_get "not json") List.empty;
  let r <- Discovery.load h idp_config;
  return (discovery_err r == "discovery: invalid JSON")
}

#[test]
def test_discovery_allows_loopback : IO Bool := do {
  let h <- OauthHttp.fake (one_get loopback_doc) List.empty;
  let r <- Discovery.load h loopback_config;
  return (ep_token r == "http://localhost:8080/token")
}

// ── token exchange, refresh, userinfo ─────────────────────────────────────

#[test]
def test_exchange_code : IO Bool := do {
  let h <- OauthHttp.fake List.empty token_posts;
  let r <- Client.exchange_code h idp_config token_endpoints "CODE" "VERIFIER";
  return (match r {
    Result.ok t => t.access_token == "AT_CODE",
    Result.err _ => false,
  })
}

#[test]
def test_refresh : IO Bool := do {
  let h <- OauthHttp.fake List.empty token_posts;
  let r <- Client.refresh h idp_config token_endpoints "RT1";
  return (match r {
    Result.ok t => t.access_token == "AT_REFRESH",
    Result.err _ => false,
  })
}

#[test]
def test_exchange_rejects_bad_token_body : IO Bool := do {
  let posts : List ScriptedExchange := [
    exchange_of "/token" 400u16 "{\"error\":\"invalid_grant\"}"
  ];
  let h <- OauthHttp.fake List.empty posts;
  let r <- Client.exchange_code h idp_config token_endpoints "CODE" "VERIFIER";
  return (match r {
    Result.ok _ => false,
    Result.err e => OauthError.to_string e == "token: status 400",
  })
}

#[test]
def test_userinfo_ok : IO Bool := do {
  let gets : List ScriptedExchange := [
    exchange_of "/userinfo" 200u16 userinfo_json
  ];
  let h <- OauthHttp.fake gets List.empty;
  let r <- Client.userinfo h userinfo_endpoints "AT";
  return (match r {
    Result.ok j => String.contains (Json.to_string j) "\"sub\":\"u1\"",
    Result.err _ => false,
  })
}

#[test]
def test_userinfo_not_configured : IO Bool := do {
  let h <- OauthHttp.fake List.empty List.empty;
  let r <- Client.userinfo h token_endpoints "AT";
  return (match r {
    Result.ok _ => false,
    Result.err e => OauthError.to_string e == "userinfo: not configured",
  })
}

// ── state store ───────────────────────────────────────────────────────────

def redirect_uri : String := "https://app.example/callback"

#[test]
def test_state_take_is_one_time : IO Bool := do {
  let st <- OauthStateStore.new 600i64 4i64;
  let begun <- OauthStateStore.begin_at st 1000i64 "state1" "nonce1" "verifier1" redirect_uri Option.none;
  if begun_ok begun
  then do {
    let first <- OauthStateStore.take_at st 1000i64 "state1" redirect_uri;
    let second <- OauthStateStore.take_at st 1000i64 "state1" redirect_uri;
    return (is_some first && Bool.not (is_some second))
  }
  else return false
}

#[test]
def test_state_wrong_redirect_burns_the_state : IO Bool := do {
  let st <- OauthStateStore.new 600i64 4i64;
  let begun <- OauthStateStore.begin_at st 1000i64 "state2" "nonce2" "verifier2" redirect_uri Option.none;
  if begun_ok begun
  then do {
    let wrong <- OauthStateStore.take_at st 1000i64 "state2" "https://app.example/other";
    let right <- OauthStateStore.take_at st 1000i64 "state2" redirect_uri;
    return (Bool.not (is_some wrong) && Bool.not (is_some right))
  }
  else return false
}

#[test]
def test_state_ttl_expiry : IO Bool := do {
  let st <- OauthStateStore.new 600i64 4i64;
  let begun <- OauthStateStore.begin_at st 1000i64 "state3" "nonce3" "verifier3" redirect_uri Option.none;
  if begun_ok begun
  then do {
    let late <- OauthStateStore.take_at st 601001i64 "state3" redirect_uri;
    return (Bool.not (is_some late))
  }
  else return false
}

#[test]
def test_state_cap_rejects : IO Bool := do {
  let st <- OauthStateStore.new 600i64 2i64;
  let b1 <- OauthStateStore.begin_at st 1000i64 "s1" "n1" "v1" redirect_uri Option.none;
  let b2 <- OauthStateStore.begin_at st 1000i64 "s2" "n2" "v2" redirect_uri Option.none;
  let b3 <- OauthStateStore.begin_at st 1000i64 "s3" "n3" "v3" redirect_uri Option.none;
  return (begun_ok b1 && begun_ok b2 && Bool.not (begun_ok b3))
}

#[test]
def test_state_prunes_expired_at_the_cap : IO Bool := do {
  let st <- OauthStateStore.new 600i64 2i64;
  let b1 <- OauthStateStore.begin_at st 1000i64 "s1" "n1" "v1" redirect_uri Option.none;
  let b2 <- OauthStateStore.begin_at st 1000i64 "s2" "n2" "v2" redirect_uri Option.none;
  let b3 <- OauthStateStore.begin_at st 700000i64 "s3" "n3" "v3" redirect_uri Option.none;
  return (begun_ok b1 && begun_ok b2 && begun_ok b3)
}
