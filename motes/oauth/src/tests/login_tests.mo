/// Login/callback/refresh/logout tests against a scripted IdP.
///
/// No socket and no RNG: the state store's `begin_at`, the session-id
/// generator, the clock seams, and `JwtVerifier.fake` make the whole flow
/// deterministic on both hosts. The JWKS document carries the RFC 7515 A.2
/// RSA key so key selection succeeds; the fake verifier decides the
/// signature.

use std::list {List.any}
use std::map {BTreeMap}
use std::ref {Ref, Ref.new, Ref.update}
use std::base64 {B64Url.encode}
use http::types {
  Headers, Headers.empty, Headers.get, Headers.get_all, Headers.set, Request,
  Request.get, Response, Status.bad_gateway, Status.bad_request, Status.forbidden,
  Status.see_other,
  Status.unauthorized, Uri,
}
use http::body {Body.to_bytes_pure}
use http::uri {Uri.percent_encode}
use http::strings {Strings.split_at_byte, Strings.split_on}
use json::json {Json}
use jsonwebtoken::principal {Principal}
use jsonwebtoken::verifier {JwtVerifier}
use oauth::bearer {BearerValidator, BearerValidator.jwt}
use oauth::config {ClientAuth, OauthConfig}
use oauth::discovery {OauthEndpoints}
use oauth::errors {AuthError}
use oauth::http_client {OauthHttp.fake, ScriptedExchange}
use oauth::login {
  Login.deps, Login.handle_callback_at, Login.handle_login_with,
  Login.handle_logout_at, Login.handle_refresh_at, Login.with_session_id,
  Login.with_userinfo, LoginDeps,
}
use oauth::session {
  AuthSession, OauthSessionStore, OauthSessionStore.create_with_id,
  OauthSessionStore.csrf_token, OauthSessionStore.lookup,
  OauthSessionStore.login_state_name, OauthSessionStore.new_with_secret,
  OauthSessionStore.session_name,
}
use oauth::state {OauthStateStore}
use oauth::token {OauthTokenSet}

// ── fixtures ──────────────────────────────────────────────────────────────

def secret : String := "0123456789abcdef0123456789abcdef"

def rfc_verifier : String := "dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk"

def rsa_n : String := "ofgWCuLjybRlzo0tZWJjNiuSfb4p4fAkd_wWJcyQoTbji9k0l8W26mPddxHmfHQp-Vaw-4qPCJrcS2mJPMEzP1Pt0Bm4d4QlL-yRT-SFd2lZS-pCgNMsD1W_YpRPEwOWvG6b32690r2jZ47soMZo9wGzjb_7OMg0LOL-bSf63kpaSHSXndS5z5rexMdbBYUsLA9e-KXBdQOS-UTo7WTBEMa2R2CapHg665xsmtdVMTBQY4uDZlxvb3qCo5ZwKh9kG4LT6_I5IhlJH7aGhyxXFvUK-DWNmoudF8NAco9_h9iaGNj8q2ethFkMLs91kzk2PAcDTW9gb54h4FRWyuXpoQ"

def config : OauthConfig := {
  issuer := "https://idp.example",
  client_id := "abc",
  redirect_uri := "https://app.example/callback",
  client_secret := Option.none,
  client_auth := ClientAuth.client_public,
  scopes := List.empty,
  audience := Option.some "api://x",
  roles_claim := "roles",
  clock_skew_seconds := 60i64,
  secure_cookies := true,
  allow_insecure_localhost := false
}

def idp_authorize : Uri :=
  Uri.uri "https" Option.none "idp.example" Option.none "/authorize" Option.none Option.none
def idp_token : Uri :=
  Uri.uri "https" Option.none "idp.example" Option.none "/token" Option.none Option.none
def idp_jwks : Uri :=
  Uri.uri "https" Option.none "idp.example" Option.none "/jwks" Option.none Option.none
def idp_userinfo : Uri :=
  Uri.uri "https" Option.none "idp.example" Option.none "/userinfo" Option.none Option.none
def idp_logout : Uri :=
  Uri.uri "https" Option.none "idp.example" Option.none "/logout" Option.none Option.none

def endpoints : OauthEndpoints := {
  authorization := idp_authorize,
  token := idp_token,
  userinfo := Option.some idp_userinfo,
  jwks := Option.some idp_jwks,
  introspection := Option.none,
  end_session := Option.some idp_logout
}

def jwks_body : String :=
  "{\"keys\":[{\"kty\":\"RSA\",\"n\":\"" ++ rsa_n ++ "\",\"e\":\"AQAB\"}]}"

def b64 (s : String) : String :=
  B64Url.encode (String.to_list s)

def id_token_with (nonce : String) : String :=
  let claims :=
    "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"abc\",\"exp\":3000,\"nonce\":\""
      ++ nonce ++ "\"}" in
  b64 "{\"alg\":\"RS256\"}" ++ "." ++ b64 claims ++ ".AQ"

def token_body (id_token : String) (refresh : String) : String :=
  "{\"access_token\":\"at\",\"token_type\":\"Bearer\",\"expires_in\":300,\"refresh_token\":\""
    ++ refresh ++ "\",\"id_token\":\"" ++ id_token ++ "\",\"scope\":\"read\"}"

def exchange_of
  (method_path : String) (status : U16) (body : String) (needle : String)
  : ScriptedExchange :=
  let ex : ScriptedExchange := {
    path := method_path,
    status := status,
    body := body,
    headers := Headers.empty,
    body_contains := needle
  } in
  ex

def jwks_exchange : ScriptedExchange :=
  exchange_of "/jwks" 200u16 jwks_body ""

def userinfo_exchange (body : String) : ScriptedExchange :=
  exchange_of "/userinfo" 200u16 body ""

def exchange_post (id_token : String) : ScriptedExchange :=
  exchange_of "/token" 200u16 (token_body id_token "rt") "grant_type=authorization_code"

def refresh_post (id_token : String) : ScriptedExchange :=
  exchange_of "/token" 200u16 (token_body id_token "rt2") "grant_type=refresh_token"

def principal_of (subject : String) : Principal :=
  let claims : BTreeMap String Json := BTreeMap.empty in
  let p : Principal := {
    subject := subject,
    issuer := "https://idp.example",
    audiences := ["api://x"],
    scopes := ["read"],
    roles := List.empty,
    claims := claims,
    expires_at := 3000i64
  } in
  p

def tokens_of (refresh : Option String) : OauthTokenSet :=
  let t : OauthTokenSet := {
    access_token := "at",
    token_type := "Bearer",
    expires_in := Option.some 300i64,
    refresh_token := refresh,
    id_token := Option.none,
    scope := ["read"]
  } in
  t

// Deterministic session ids: sid-1, sid-2, ...
def ids_from (start : I64) : IO (IO (Result AuthError String)) := do {
  let cell <- Ref.new start;
  let gen : IO (Result AuthError String) := do {
    let n <- Ref.update cell (fn (x : I64) => I64.add x 1i64);
    return (Result.ok ("sid-" ++ I64.to_string n))
  };
  return gen
}

def deps_with_endpoints
  (ep : OauthEndpoints) (gets : List ScriptedExchange) (posts : List ScriptedExchange)
  : IO LoginDeps := do {
  let http <- OauthHttp.fake gets posts;
  let states <- OauthStateStore.new 600i64 10i64;
  let sessions <- OauthSessionStore.new_with_secret secret 3600i64 600i64 true;
  let bearer <- BearerValidator.jwt config ep http (JwtVerifier.fake true);
  let gen <- ids_from 0i64;
  let base := Login.deps config ep states sessions http bearer;
  return (Login.with_session_id base gen)
}

def deps_with
  (gets : List ScriptedExchange) (posts : List ScriptedExchange)
  : IO LoginDeps :=
  deps_with_endpoints endpoints gets posts

def no_userinfo_endpoints : OauthEndpoints := {
  authorization := idp_authorize,
  token := idp_token,
  userinfo := Option.none,
  jwks := Option.some idp_jwks,
  introspection := Option.none,
  end_session := Option.some idp_logout
}

// ── requests and responses ─────────────────────────────────────────────────

def api_uri : Uri :=
  Uri.uri "https" Option.none "api.example" Option.none "/me" Option.none Option.none

def login_request (return_to : Option String) : Request :=
  let query : Option String :=
    match return_to {
      Option.none => Option.none,
      Option.some t => Option.some ("return_to=" ++ Uri.percent_encode t)
    } in
  Request.get (Uri.uri "https" Option.none "app.example" Option.none "/login" query Option.none)

def callback_request (state : String) (code : String) : Request :=
  let q := "state=" ++ Uri.percent_encode state ++ "&code=" ++ Uri.percent_encode code in
  Request.get (Uri.uri "https" Option.none "app.example" Option.none "/callback" (Option.some q) Option.none)

def callback_request_for (d : LoginDeps) (state : String) (code : String) : Request :=
  let base := callback_request state code in
  let out : Request := {
    base with headers := Headers.set "Cookie"
      (OauthSessionStore.login_state_name d.sessions ++ "=" ++ state) base.headers
  } in
  out

def callback_request_with_cookie
  (d : LoginDeps) (state : String) (code : String) (cookie_state : String)
  : Request :=
  let base := callback_request state code in
  let out : Request := {
    base with headers := Headers.set "Cookie"
      (OauthSessionStore.login_state_name d.sessions ++ "=" ++ cookie_state) base.headers
  } in
  out

def origin_form_callback_request (d : LoginDeps) (state : String) (code : String) : Request :=
  let q := "state=" ++ Uri.percent_encode state ++ "&code=" ++ Uri.percent_encode code in
  let base := Request.get
    (Uri.uri "" Option.none "" Option.none "/callback" (Option.some q) Option.none) in
  let out : Request := {
    base with headers := Headers.set "Cookie"
      (OauthSessionStore.login_state_name d.sessions ++ "=" ++ state) base.headers
  } in
  out

def error_request (err : String) : Request :=
  let q := "error=" ++ Uri.percent_encode err in
  Request.get (Uri.uri "https" Option.none "app.example" Option.none "/callback" (Option.some q) Option.none)

def state_only_request (state : String) : Request :=
  let q := "state=" ++ Uri.percent_encode state in
  Request.get (Uri.uri "https" Option.none "app.example" Option.none "/callback" (Option.some q) Option.none)

def request_session_cookie
  (d : LoginDeps) (id : String) (csrf : Option String)
  : Request :=
  let cookie := OauthSessionStore.session_name d.sessions ++ "=" ++ id in
  let base := Request.get api_uri in
  let with_cookie : Request := {
    base with headers := Headers.set "Cookie" cookie Headers.empty
  } in
  match csrf {
    Option.none => with_cookie,
    Option.some t =>
      let out : Request := {
        with_cookie with headers := Headers.set "X-CSRF-Token" t with_cookie.headers
      } in
      out
  }

def status_of (r : Result String Response) : U16 :=
  match r {
    Result.ok res => res.status,
    Result.err _ => 0u16
  }

def header_of (r : Result String Response) (name : String) : String :=
  match r {
    Result.ok res =>
      match Headers.get name res.headers {
        Option.some v => v,
        Option.none => ""
      },
    Result.err _ => ""
  }

def cookies_of (r : Result String Response) : List String :=
  match r {
    Result.ok res => Headers.get_all "Set-Cookie" res.headers,
    Result.err _ => List.empty
  }

def body_of (r : Result String Response) : String :=
  match r {
    Result.ok res => String.from_list (Body.to_bytes_pure res.body),
    Result.err e => e
  }

def cookie_value_of (c : String) (name : String) : Option String :=
  match Strings.split_on ";" c {
    List.cons first _ =>
      match Strings.split_at_byte 61u8 (String.to_list first) {
        Pair.pair name_b value_b =>
          if String.from_list name_b == name
          then Option.some (String.from_list value_b)
          else Option.none
      },
    List.empty => Option.none
  }

#[terminating]
def cookie_named (cookies : List String) (name : String) : Option String :=
  match cookies {
    List.empty => Option.none,
    List.cons c rest =>
      match cookie_value_of c name {
        Option.some v => Option.some v,
        Option.none => cookie_named rest name
      }
  }

def begin_with
  (d : LoginDeps) (return_to : Option String) (nonce : String)
  : IO (Result String Response) :=
  Login.handle_login_with d (login_request return_to) "state1" nonce rfc_verifier 2000000i64

def raw_login_request (query : String) : Request :=
  Request.get (Uri.uri "https" Option.none "app.example" Option.none "/login"
    (Option.some query) Option.none)

def begin_with_query
  (d : LoginDeps) (query : String) (nonce : String)
  : IO (Result String Response) :=
  Login.handle_login_with d (raw_login_request query) "state1" nonce rfc_verifier 2000000i64

// ── login ──────────────────────────────────────────────────────────────────

#[test]
def test_login_redirect : IO Bool := do {
  let d <- deps_with List.empty List.empty;
  let r <- begin_with d Option.none "nonce1";
  let loc := header_of r "Location";
  return (U16.beq (status_of r) Status.see_other
    && String.contains loc "state=state1"
    && String.contains loc "nonce=nonce1"
    && String.contains loc "code_challenge_method=S256"
    && String.contains loc "redirect_uri=https%3A%2F%2Fapp.example%2Fcallback")
}

// ── callback ───────────────────────────────────────────────────────────────

#[test]
def test_callback_creates_session : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with [jwks_exchange] [exchange_post idt];
  let _ <- begin_with d Option.none "nonce1";
  let r <- Login.handle_callback_at d (callback_request_for d "state1" "abc") 2000i64;
  let cookies := cookies_of r;
  return (U16.beq (status_of r) Status.see_other
    && header_of r "Location" == "/"
    && (match cookie_named cookies "__Host-oauth_session" {
      Option.some v => v == "sid-1",
      Option.none => false
    })
    && (match cookie_named cookies "__Host-oauth_csrf" {
      Option.some _ => true,
      Option.none => false
    })
    && header_of r "Cache-Control" == "no-store"
    && header_of r "Referrer-Policy" == "no-referrer")
}

#[test]
def test_callback_return_to : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with [jwks_exchange] [exchange_post idt];
  let _ <- begin_with d (Option.some "/dashboard") "nonce1";
  let r <- Login.handle_callback_at d (callback_request_for d "state1" "abc") 2000i64;
  return (header_of r "Location" == "/dashboard")
}

#[test]
def test_callback_open_redirect_rejected : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with [jwks_exchange] [exchange_post idt];
  let _ <- begin_with d (Option.some "https://evil.example/") "nonce1";
  let r <- Login.handle_callback_at d (callback_request_for d "state1" "abc") 2000i64;
  return (header_of r "Location" == "/")
}

#[test]
def test_callback_state_replay_rejected : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with [jwks_exchange] [exchange_post idt];
  let _ <- begin_with d Option.none "nonce1";
  let first <- Login.handle_callback_at d (callback_request_for d "state1" "abc") 2000i64;
  let second <- Login.handle_callback_at d (callback_request_for d "state1" "abc") 2000i64;
  return (U16.beq (status_of first) Status.see_other
    && U16.beq (status_of second) Status.bad_request)
}

#[test]
def test_callback_nonce_mismatch_rejected : IO Bool := do {
  let idt := id_token_with "wrong";
  let d <- deps_with [jwks_exchange] [exchange_post idt];
  let _ <- begin_with d Option.none "nonce1";
  let r <- Login.handle_callback_at d (callback_request_for d "state1" "abc") 2000i64;
  return (U16.beq (status_of r) Status.bad_request)
}

#[test]
def test_callback_error_param_rejected : IO Bool := do {
  let d <- deps_with List.empty List.empty;
  let r <- Login.handle_callback_at d (error_request "access_denied") 2000i64;
  return (U16.beq (status_of r) Status.bad_request)
}

#[test]
def test_callback_missing_code_rejected : IO Bool := do {
  let d <- deps_with List.empty List.empty;
  let r <- Login.handle_callback_at d (state_only_request "state1") 2000i64;
  return (U16.beq (status_of r) Status.bad_request)
}

// ── refresh ────────────────────────────────────────────────────────────────

def create_session
  (d : LoginDeps) (id : String) (refresh : Option String) (now : I64)
  : IO AuthSession :=
  OauthSessionStore.create_with_id d.sessions id (principal_of "u1")
    (tokens_of refresh) now

#[test]
def test_refresh_requires_csrf : IO Bool := do {
  let d <- deps_with List.empty List.empty;
  let _ <- create_session d "old-id" (Option.some "rt") 2000i64;
  let r <- Login.handle_refresh_at d (request_session_cookie d "old-id" Option.none) 2001i64;
  return (U16.beq (status_of r) Status.forbidden)
}

#[test]
def test_refresh_rotates_and_updates_tokens : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with List.empty [refresh_post idt];
  let s <- create_session d "old-id" (Option.some "rt") 2000i64;
  let token := OauthSessionStore.csrf_token d.sessions s;
  let r <- Login.handle_refresh_at d
    (request_session_cookie d "old-id" (Option.some token)) 2001i64;
  let new_cookie := cookie_named (cookies_of r) "__Host-oauth_session";
  let old <- OauthSessionStore.lookup d.sessions
    (request_session_cookie d "old-id" Option.none) 2002i64;
  return (U16.beq (status_of r) Status.see_other
    && (match new_cookie { Option.some v => v == "sid-1", Option.none => false })
    && (match old { Option.none => true, Option.some _ => false }))
}

#[test]
def test_refresh_without_refresh_token_is_unauthorized : IO Bool := do {
  let d <- deps_with List.empty List.empty;
  let s <- create_session d "old-id" Option.none 2000i64;
  let token := OauthSessionStore.csrf_token d.sessions s;
  let r <- Login.handle_refresh_at d
    (request_session_cookie d "old-id" (Option.some token)) 2001i64;
  return (U16.beq (status_of r) Status.unauthorized)
}

// ── logout ─────────────────────────────────────────────────────────────────

#[test]
def test_logout_destroys_and_redirects : IO Bool := do {
  let d <- deps_with List.empty List.empty;
  let s <- create_session d "old-id" (Option.some "rt") 2000i64;
  let token := OauthSessionStore.csrf_token d.sessions s;
  let r <- Login.handle_logout_at d
    (request_session_cookie d "old-id" (Option.some token)) 2001i64;
  let cleared := List.any
    (fn (c : String) =>
      String.contains c "__Host-oauth_session=" && String.contains c "Max-Age=0")
    (cookies_of r);
  let gone <- OauthSessionStore.lookup d.sessions
    (request_session_cookie d "old-id" Option.none) 2002i64;
  return (U16.beq (status_of r) Status.see_other
    && header_of r "Location" == "https://idp.example/logout?client_id=abc"
    && cleared
    && (match gone { Option.none => true, Option.some _ => false }))
}

#[test]
def test_logout_requires_csrf : IO Bool := do {
  let d <- deps_with List.empty List.empty;
  let _ <- create_session d "old-id" (Option.some "rt") 2000i64;
  let r <- Login.handle_logout_at d (request_session_cookie d "old-id" Option.none) 2001i64;
  let live <- OauthSessionStore.lookup d.sessions
    (request_session_cookie d "old-id" Option.none) 2002i64;
  return (U16.beq (status_of r) Status.forbidden
    && (match live { Option.some _ => true, Option.none => false }))
}

// ── userinfo cross-check ───────────────────────────────────────────────────

#[test]
def test_userinfo_sub_match : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with [jwks_exchange, userinfo_exchange "{\"sub\":\"u1\"}"]
    [exchange_post idt];
  let d2 := Login.with_userinfo d;
  let _ <- begin_with d2 Option.none "nonce1";
  let r <- Login.handle_callback_at d2 (callback_request_for d2 "state1" "abc") 2000i64;
  return (U16.beq (status_of r) Status.see_other)
}

#[test]
def test_userinfo_sub_mismatch : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with [jwks_exchange, userinfo_exchange "{\"sub\":\"other\"}"]
    [exchange_post idt];
  let d2 := Login.with_userinfo d;
  let _ <- begin_with d2 Option.none "nonce1";
  let r <- Login.handle_callback_at d2 (callback_request_for d2 "state1" "abc") 2000i64;
  return (U16.beq (status_of r) Status.bad_request)
}

#[test]
def test_callback_control_char_return_to_rejected : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with [jwks_exchange] [exchange_post idt];
  let _ <- begin_with_query d "return_to=%2F%0D%0AX-Injected%3A1" "nonce1";
  let r <- Login.handle_callback_at d (callback_request_for d "state1" "abc") 2000i64;
  return (header_of r "Location" == "/")
}

#[test]
def test_callback_oversize_state_rejected : IO Bool := do {
  let d <- deps_with List.empty List.empty;
  let big := String.repeat "a" 5000i64;
  let r <- Login.handle_callback_at d (callback_request_for d big "abc") 2000i64;
  return (U16.beq (status_of r) Status.bad_request)
}

#[test]
def test_callback_same_origin_absolute_return_to : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with [jwks_exchange] [exchange_post idt];
  let _ <- begin_with d (Option.some "https://app.example/dashboard") "nonce1";
  // Origin-form, as a real server builds it: the check compares the
  // CONFIGURED redirect_uri, not the request URI.
  let r <- Login.handle_callback_at d
    (origin_form_callback_request d "state1" "abc") 2000i64;
  return (header_of r "Location" == "https://app.example/dashboard")
}

def token_body_access_only : String :=
  "{\"access_token\":\"at2\",\"token_type\":\"Bearer\",\"expires_in\":300}"

def refresh_post_no_refresh : ScriptedExchange :=
  exchange_of "/token" 200u16 token_body_access_only "grant_type=refresh_token"

def invalid_grant_post : ScriptedExchange :=
  exchange_of "/token" 400u16 "{\"error\":\"invalid_grant\"}" "grant_type=refresh_token"

def jwks_down_exchange : ScriptedExchange :=
  exchange_of "/jwks" 500u16 "down" ""

#[test]
def test_callback_without_login_cookie_rejected : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with [jwks_exchange] [exchange_post idt];
  let _ <- begin_with d Option.none "nonce1";
  let r <- Login.handle_callback_at d (callback_request "state1" "abc") 2000i64;
  return (U16.beq (status_of r) Status.bad_request)
}

#[test]
def test_callback_wrong_login_cookie_rejected : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with [jwks_exchange] [exchange_post idt];
  let _ <- begin_with d Option.none "nonce1";
  let r <- Login.handle_callback_at d
    (callback_request_with_cookie d "state1" "abc" "other") 2000i64;
  return (U16.beq (status_of r) Status.bad_request)
}

#[test]
def test_refresh_preserves_omitted_refresh_token : IO Bool := do {
  let d <- deps_with List.empty [refresh_post_no_refresh];
  let s <- create_session d "old-id" (Option.some "rt") 2000i64;
  let token := OauthSessionStore.csrf_token d.sessions s;
  let r <- Login.handle_refresh_at d
    (request_session_cookie d "old-id" (Option.some token)) 2001i64;
  let rotated <- OauthSessionStore.lookup d.sessions
    (request_session_cookie d "sid-1" Option.none) 2002i64;
  return (U16.beq (status_of r) Status.see_other
    && (match rotated {
      Option.some live => match live.refresh_token {
        Option.some rt => rt == "rt",
        Option.none => false
      },
      Option.none => false
    }))
}

#[test]
def test_refresh_invalid_grant_destroys_session : IO Bool := do {
  let d <- deps_with List.empty [invalid_grant_post];
  let s <- create_session d "old-id" (Option.some "rt") 2000i64;
  let token := OauthSessionStore.csrf_token d.sessions s;
  let r <- Login.handle_refresh_at d
    (request_session_cookie d "old-id" (Option.some token)) 2001i64;
  let gone <- OauthSessionStore.lookup d.sessions
    (request_session_cookie d "old-id" Option.none) 2002i64;
  return (U16.beq (status_of r) Status.unauthorized
    && (match gone { Option.none => true, Option.some _ => false }))
}

#[test]
def test_callback_jwks_outage_is_502 : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with [jwks_down_exchange] [exchange_post idt];
  let _ <- begin_with d Option.none "nonce1";
  let r <- Login.handle_callback_at d (callback_request_for d "state1" "abc") 2000i64;
  return (U16.beq (status_of r) Status.bad_gateway)
}

#[test]
def test_userinfo_without_endpoint_is_502 : IO Bool := do {
  let idt := id_token_with "nonce1";
  let d <- deps_with_endpoints no_userinfo_endpoints
    [jwks_exchange] [exchange_post idt];
  let d2 := Login.with_userinfo d;
  let _ <- begin_with d2 Option.none "nonce1";
  let r <- Login.handle_callback_at d2 (callback_request_for d2 "state1" "abc") 2000i64;
  return (U16.beq (status_of r) Status.bad_gateway)
}
