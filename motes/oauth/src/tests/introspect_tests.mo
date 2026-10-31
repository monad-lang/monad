/// RFC 7662 introspection tests: a scripted transport, no socket.
///
/// Covers the active mapping, the username fallback, inactive/expired tokens,
/// malformed and unavailable responses, the SHA-256-keyed cache (including
/// the `exp` bound and the absence of a negative cache), both client-auth
/// body forms, and the bearer guard in introspection mode.

use http::types {
  Headers.empty, Headers.get, Headers.set, Request, Request.get, Response,
  Response.text, Status.forbidden, Status.internal_server_error, Status.ok, Uri,
}
use http::body {Body.to_bytes_pure}
use jsonwebtoken::principal {Principal}
use oauth::bearer {
  Bearer.require_at, BearerValidator, BearerValidator.introspect,
}
use oauth::config {ClientAuth, OauthConfig}
use oauth::discovery {OauthEndpoints}
use oauth::errors {AuthError, AuthError.to_string}
use oauth::http_client {OauthHttp.fake, ScriptedExchange}
use oauth::introspect {
  Introspect.form, Introspect.headers, Introspector, Introspector.new,
  Introspector.principal,
}

// ── fixtures ──────────────────────────────────────────────────────────────

def config_of (auth : ClientAuth) (secret : Option String) : OauthConfig :=
  let c : OauthConfig := {
    issuer := "https://idp.example",
    client_id := "abc",
    redirect_uri := "https://app.example/callback",
    client_secret := secret,
    client_auth := auth,
    scopes := List.empty,
    audience := Option.some "api://x",
    roles_claim := "roles",
    clock_skew_seconds := 60i64,
    secure_cookies := true,
    allow_insecure_localhost := false
  } in
  c

def basic_config : OauthConfig :=
  config_of ClientAuth.client_secret_basic (Option.some "s3cret")

def post_config : OauthConfig :=
  config_of ClientAuth.client_secret_post (Option.some "s3cret")

def idp_authorize : Uri :=
  Uri.uri "https" Option.none "idp.example" Option.none "/authorize" Option.none Option.none
def idp_token : Uri :=
  Uri.uri "https" Option.none "idp.example" Option.none "/token" Option.none Option.none
def introspect_uri : Uri :=
  Uri.uri "https" Option.none "idp.example" Option.none "/introspect" Option.none Option.none

def endpoints_with (intro : Option Uri) : OauthEndpoints := {
  authorization := idp_authorize,
  token := idp_token,
  userinfo := Option.none,
  jwks := Option.none,
  introspection := intro,
  end_session := Option.none
}

def exchange_of
  (status : U16) (body : String) (needle : String)
  : ScriptedExchange :=
  let ex : ScriptedExchange := {
    path := "/introspect",
    status := status,
    body := body,
    headers := Headers.empty,
    body_contains := needle
  } in
  ex

def active_post (body : String) : ScriptedExchange :=
  exchange_of 200u16 body "token_type_hint=access_token"

def introspector_with
  (cfg : OauthConfig) (posts : List ScriptedExchange)
  : IO Introspector := do {
  let no_gets : List ScriptedExchange := List.empty;
  let http <- OauthHttp.fake no_gets posts;
  Introspector.new cfg (endpoints_with (Option.some introspect_uri)) http
}

def active_body : String :=
  "{\"active\":true,\"sub\":\"u1\",\"iss\":\"https://idp.example\",\"aud\":\"api://x\",\"scope\":\"read write\",\"exp\":3000,\"roles\":[\"admin\"]}"

def principal_of
  (r : Result AuthError Principal)
  : Option Principal :=
  match r {
    Result.ok p => Option.some p,
    Result.err _ => Option.none
  }

def auth_err_is (r : Result AuthError Principal) (msg : String) : Bool :=
  match r {
    Result.ok _ => false,
    Result.err e => AuthError.to_string e == msg
  }

// ── mapping ───────────────────────────────────────────────────────────────

#[test]
def test_introspect_active_maps_principal : IO Bool := do {
  let i <- introspector_with basic_config [active_post active_body];
  let r <- Introspector.principal i 2000i64 "tok";
  return (match principal_of r {
    Option.none => false,
    Option.some p =>
      p.subject == "u1"
        && p.issuer == "https://idp.example"
        && p.audiences == ["api://x"]
        && p.scopes == ["read", "write"]
        && p.roles == ["admin"]
        && p.expires_at == 3000i64
  })
}

#[test]
def test_introspect_requires_sub : IO Bool := do {
  // `username` is not a stable subject and must not silently become one.
  let body := "{\"active\":true,\"username\":\"alice\",\"iss\":\"https://idp.example\",\"exp\":3000}";
  let i <- introspector_with basic_config [active_post body];
  let r <- Introspector.principal i 2000i64 "tok";
  return (auth_err_is r "auth: invalid token: missing sub")
}

#[test]
def test_introspect_audience_mismatch : IO Bool := do {
  let body := "{\"active\":true,\"sub\":\"u1\",\"aud\":\"api://other\",\"exp\":3000}";
  let i <- introspector_with basic_config [active_post body];
  let r <- Introspector.principal i 2000i64 "tok";
  return (auth_err_is r "auth: invalid token: audience mismatch")
}

#[test]
def test_introspect_refresh_token_rejected : IO Bool := do {
  let body := "{\"active\":true,\"sub\":\"u1\",\"aud\":\"api://x\",\"token_type\":\"refresh_token\",\"exp\":3000}";
  let i <- introspector_with basic_config [active_post body];
  let r <- Introspector.principal i 2000i64 "tok";
  return (auth_err_is r "auth: invalid token: unsupported token_type refresh_token")
}

#[test]
def test_introspect_no_exp_uses_the_cache_horizon : IO Bool := do {
  let body := "{\"active\":true,\"sub\":\"u1\",\"aud\":\"api://x\"}";
  let i <- introspector_with basic_config [active_post body];
  let r <- Introspector.principal i 2000i64 "tok";
  return (match principal_of r {
    Option.none => false,
    Option.some p => p.expires_at == 2060i64
  })
}

#[test]
def test_introspect_bad_client_credentials_is_server_error : IO Bool := do {
  // A 401 from the introspection endpoint is this server's misconfiguration,
  // not the caller's token and not a retryable outage.
  let i <- introspector_with basic_config [exchange_of 401u16 "bad client" "token="];
  let r <- Introspector.principal i 2000i64 "tok";
  return (auth_err_is r "auth: introspection client credentials or endpoint are misconfigured")
}

#[test]
def test_introspect_issuer_mismatch : IO Bool := do {
  let body := "{\"active\":true,\"sub\":\"u1\",\"iss\":\"https://other.example\",\"exp\":3000}";
  let i <- introspector_with basic_config [active_post body];
  let r <- Introspector.principal i 2000i64 "tok";
  return (auth_err_is r "auth: invalid token: issuer mismatch")
}

// ── inactive, expired, malformed, unavailable ──────────────────────────────

#[test]
def test_introspect_inactive_rejected : IO Bool := do {
  let i <- introspector_with basic_config [active_post "{\"active\":false}"];
  let r <- Introspector.principal i 2000i64 "secret-token";
  return (auth_err_is r "auth: invalid token: token is not active")
}

#[test]
def test_introspect_error_does_not_leak_the_token : IO Bool := do {
  let i <- introspector_with basic_config [active_post "{\"active\":false}"];
  let r <- Introspector.principal i 2000i64 "secret-token";
  return (match r {
    Result.ok _ => false,
    Result.err e => Bool.not (String.contains (AuthError.to_string e) "secret-token")
  })
}

#[test]
def test_introspect_expired_rejected : IO Bool := do {
  let body := "{\"active\":true,\"sub\":\"u1\",\"exp\":1000}";
  let i <- introspector_with basic_config [active_post body];
  let r <- Introspector.principal i 2000i64 "tok";
  return (auth_err_is r "auth: token expired")
}

#[test]
def test_introspect_malformed_is_unavailable : IO Bool := do {
  let i <- introspector_with basic_config [active_post "not json"];
  let r <- Introspector.principal i 2000i64 "tok";
  return (auth_err_is r "auth: identity provider temporarily unavailable")
}

#[test]
def test_introspect_active_not_bool_is_unavailable : IO Bool := do {
  let i <- introspector_with basic_config [active_post "{\"active\":\"yes\"}"];
  let r <- Introspector.principal i 2000i64 "tok";
  return (auth_err_is r "auth: identity provider temporarily unavailable")
}

#[test]
def test_introspect_http_error_is_unavailable : IO Bool := do {
  let i <- introspector_with basic_config [exchange_of 500u16 "down" "token="];
  let r <- Introspector.principal i 2000i64 "tok";
  return (auth_err_is r "auth: identity provider temporarily unavailable")
}

#[test]
def test_introspect_missing_endpoint_is_unavailable : IO Bool := do {
  let no_gets : List ScriptedExchange := List.empty;
  let no_posts : List ScriptedExchange := List.empty;
  let http <- OauthHttp.fake no_gets no_posts;
  let i <- Introspector.new basic_config (endpoints_with Option.none) http;
  let r <- Introspector.principal i 2000i64 "tok";
  return (auth_err_is r "auth: identity provider temporarily unavailable")
}

// ── cache ──────────────────────────────────────────────────────────────────

#[test]
def test_introspect_cache_reused : IO Bool := do {
  let i <- introspector_with basic_config [active_post active_body];
  let r1 <- Introspector.principal i 2000i64 "tok";
  let r2 <- Introspector.principal i 2001i64 "tok";
  // Only one POST is scripted; a second fetch would fail as unavailable.
  return (match r1 {
    Result.ok _ => match r2 {
      Result.ok _ => true,
      Result.err _ => false
    },
    Result.err _ => false
  })
}

#[test]
def test_introspect_cache_ttl_bounded_by_exp : IO Bool := do {
  let first := "{\"active\":true,\"sub\":\"u1\",\"exp\":2030}";
  let second := "{\"active\":true,\"sub\":\"u2\",\"exp\":3000}";
  let i <- introspector_with basic_config [active_post first, active_post second];
  let r1 <- Introspector.principal i 2000i64 "tok";
  let r2 <- Introspector.principal i 2031i64 "tok";
  return (match principal_of r1 {
    Option.none => false,
    Option.some p1 => match principal_of r2 {
      Option.none => false,
      Option.some p2 => p1.subject == "u1" && p2.subject == "u2"
    }
  })
}

#[test]
def test_introspect_no_negative_cache : IO Bool := do {
  let active := "{\"active\":true,\"sub\":\"u1\",\"exp\":3000}";
  let i <- introspector_with basic_config
    [active_post "{\"active\":false}", active_post active];
  let r1 <- Introspector.principal i 2000i64 "tok";
  let r2 <- Introspector.principal i 2000i64 "tok";
  // If the inactive response were cached, the second call would not fetch
  // the active document and would still fail.
  return (auth_err_is r1 "auth: invalid token: token is not active"
    && (match principal_of r2 {
      Option.some p => p.subject == "u1",
      Option.none => false
    }))
}

// ── client authentication ─────────────────────────────────────────────────

#[test]
def test_introspect_client_secret_post_form : IO Bool := do {
  let post := exchange_of 200u16 active_body "client_secret=s3cret";
  let i <- introspector_with post_config [post];
  let r <- Introspector.principal i 2000i64 "tok";
  return (match principal_of r {
    Option.some p => p.subject == "u1",
    Option.none => false
  })
}

// ── the bearer guard in introspection mode ─────────────────────────────────

def request_auth (value : String) : Request :=
  let base := Request.get
    (Uri.uri "https" Option.none "api.example" Option.none "/me" Option.none Option.none) in
  let out : Request := {
    base with headers := Headers.set "Authorization" value Headers.empty
  } in
  out

def ok_handler : Principal -> Request -> IO (Result String Response) :=
  fn (p : Principal) (_req : Request) =>
    IO.pure (Result.ok (Response.text Status.ok p.subject))

def status_of (r : Result String Response) : U16 :=
  match r {
    Result.ok res => res.status,
    Result.err _ => 0u16
  }

def body_of (r : Result String Response) : String :=
  match r {
    Result.ok res => String.from_list (Body.to_bytes_pure res.body),
    Result.err e => e
  }

#[test]
def test_bearer_introspect_mode : IO Bool := do {
  let no_posts : List ScriptedExchange := List.empty;
  let no_gets : List ScriptedExchange := List.empty;
  let http <- OauthHttp.fake no_gets [active_post active_body];
  let v <- BearerValidator.introspect basic_config
    (endpoints_with (Option.some introspect_uri)) http;
  let req := request_auth "Bearer opaque-token";
  let r1 <- Bearer.require_at v List.empty ok_handler req 2000i64;
  let r2 <- Bearer.require_at v ["admin"] ok_handler req 2000i64;
  return (U16.beq (status_of r1) Status.ok
    && body_of r1 == "u1"
    && U16.beq (status_of r2) Status.forbidden)
}

#[test]
def test_introspect_basic_auth_uses_the_header : Bool :=
  let h := Introspect.headers basic_config in
  let basic_ok : Bool :=
    match Headers.get "Authorization" h {
      Option.some v => String.starts_with "Basic " v,
      Option.none => false
    } in
  let form := Introspect.form basic_config "tok" in
  basic_ok
    && String.contains form "token=tok"
    && Bool.not (String.contains form "client_secret")

#[test]
def test_introspect_post_auth_uses_the_form : Bool :=
  let form := Introspect.form post_config "tok" in
  String.contains form "client_secret=s3cret"
    && (match Headers.get "Authorization" (Introspect.headers post_config) {
      Option.none => true,
      Option.some _ => false
    })

#[test]
def test_introspect_rejects_oversize_token : IO Bool := do {
  let no_posts : List ScriptedExchange := List.empty;
  let i <- introspector_with basic_config no_posts;
  let r <- Introspector.principal i 2000i64 (String.repeat "a" 16385i64);
  return (auth_err_is r "auth: invalid token: token exceeds 16 KiB")
}
