/// Bearer-middleware tests: no socket and no server. `OauthHttp.fake`
/// serves the JWKS, `JwtVerifier.fake` decides the signature outcome, and
/// `Bearer.require_at` fixes the clock so expiry and the cache TTL are
/// deterministic. Both hosts run these.

use std::list {List.any, List.length}
use std::ref {Ref, Ref.new, Ref.update}
use std::base64 {B64Url.encode}
use std::io {IO.current_time}
use http::types {
  Headers, Headers.add, Headers.empty, Headers.get, Headers.set,
  Request, Request.get, Response, Response.text, Status.forbidden, Status.ok,
  Status.service_unavailable, Status.unauthorized, Uri,
}
use http::body {Body.to_bytes_pure}
use jsonwebtoken::principal {Principal}
use oauth::audit {AuditEvent, AuditEvent.render}
use jsonwebtoken::verifier {JwtVerifier}
use oauth::bearer {
  Bearer.require, Bearer.require_at, BearerValidator, BearerValidator.jwt,
  BearerValidator.with_audit,
}
use oauth::config {ClientAuth, OauthConfig}
use oauth::discovery {OauthEndpoints}
use oauth::http_client {OauthHttp.fake, ScriptedExchange}

// ── fixtures ──────────────────────────────────────────────────────────────

/// RFC 7515 §A.2 modulus; the fake verifier never uses its contents.
def rsa_n : String := "ofgWCuLjybRlzo0tZWJjNiuSfb4p4fAkd_wWJcyQoTbji9k0l8W26mPddxHmfHQp-Vaw-4qPCJrcS2mJPMEzP1Pt0Bm4d4QlL-yRT-SFd2lZS-pCgNMsD1W_YpRPEwOWvG6b32690r2jZ47soMZo9wGzjb_7OMg0LOL-bSf63kpaSHSXndS5z5rexMdbBYUsLA9e-KXBdQOS-UTo7WTBEMa2R2CapHg665xsmtdVMTBQY4uDZlxvb3qCo5ZwKh9kG4LT6_I5IhlJH7aGhyxXFvUK-DWNmoudF8NAco9_h9iaGNj8q2ethFkMLs91kzk2PAcDTW9gb54h4FRWyuXpoQ"

def idp_config : OauthConfig := {
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
def jwks_uri : Uri :=
  Uri.uri "https" Option.none "idp.example" Option.none "/jwks" Option.none Option.none

def endpoints : OauthEndpoints := {
  authorization := idp_authorize,
  token := idp_token,
  userinfo := Option.none,
  jwks := Option.some jwks_uri,
  introspection := Option.none,
  end_session := Option.none
}

def no_jwks_endpoints : OauthEndpoints := {
  authorization := idp_authorize,
  token := idp_token,
  userinfo := Option.none,
  jwks := Option.none,
  introspection := Option.none,
  end_session := Option.none
}

def api_uri : Uri :=
  Uri.uri "https" Option.none "api.example" Option.none "/me" Option.none Option.none

def plain_request : Request := Request.get api_uri

def request_auth (value : String) : Request :=
  let base := Request.get api_uri in
  let out : Request := {
    base with headers := Headers.set "Authorization" value Headers.empty
  } in
  out

def request_two_auth (first : String) (second : String) : Request :=
  let base := Request.get api_uri in
  let out : Request := {
    base with headers :=
      Headers.add "Authorization" second
        (Headers.set "Authorization" first Headers.empty)
  } in
  out

def b64 (s : String) : String :=
  B64Url.encode (String.to_list s)

def token_of (header : String) (claims : String) : String :=
  b64 header ++ "." ++ b64 claims ++ ".AQ"

def valid_claims : String :=
  "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"api://x\",\"exp\":3000,\"scope\":\"read\"}"

def valid_token : String := token_of "{\"alg\":\"RS256\"}" valid_claims

def expired_token : String :=
  token_of "{\"alg\":\"RS256\"}"
    "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"api://x\",\"exp\":1000,\"scope\":\"read\"}"

def kid2_token : String :=
  token_of "{\"alg\":\"RS256\",\"kid\":\"k2\"}" valid_claims

def kid3_token : String :=
  token_of "{\"alg\":\"RS256\",\"kid\":\"k3\"}" valid_claims

def jwks_json (kid : Option String) : String :=
  match kid {
    Option.none =>
      "{\"keys\":[{\"kty\":\"RSA\",\"n\":\"" ++ rsa_n ++ "\",\"e\":\"AQAB\"}]}",
    Option.some k =>
      "{\"keys\":[{\"kty\":\"RSA\",\"kid\":\"" ++ k ++ "\",\"n\":\""
        ++ rsa_n ++ "\",\"e\":\"AQAB\"}]}"
  }

def exchange_of (path : String) (status : U16) (body : String) : ScriptedExchange :=
  let ex : ScriptedExchange := {
    path := path,
    status := status,
    body := body,
    headers := Headers.empty,
    body_contains := ""
  } in
  ex

def jwks_exchange : ScriptedExchange := exchange_of "/jwks" 200u16 (jwks_json Option.none)

def validator_with (gets : List ScriptedExchange) (accept : Bool) : IO BearerValidator := do {
  let no_posts : List ScriptedExchange := List.empty;
  let http <- OauthHttp.fake gets no_posts;
  BearerValidator.jwt idp_config endpoints http (JwtVerifier.fake accept)
}

def ok_handler : Principal -> Request -> IO (Result String Response) :=
  fn (p : Principal) (_req : Request) =>
    IO.pure (Result.ok (Response.text Status.ok p.subject))

def fail_handler : Principal -> Request -> IO (Result String Response) :=
  fn (_p : Principal) (_req : Request) =>
    IO.pure (Result.err "handler called")

// ── response inspection ───────────────────────────────────────────────────

def header_of (res : Response) (name : String) : String :=
  match Headers.get name res.headers {
    Option.some v => v,
    Option.none => ""
  }

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

def auth_fail
  (r : Result String Response) (status : U16) (www : String) (body : String)
  : Bool :=
  match r {
    Result.err _ => false,
    Result.ok res =>
      U16.beq res.status status
        && header_of res "WWW-Authenticate" == www
        && header_of res "Cache-Control" == "no-store"
        && header_of res "Referrer-Policy" == "no-referrer"
        && body_of (Result.ok res) == body
  }

// ── extraction failures ───────────────────────────────────────────────────

#[test]
def test_bearer_missing_token : IO Bool := do {
  let v <- validator_with [jwks_exchange] true;
  let r <- Bearer.require_at v List.empty ok_handler plain_request 2000i64;
  return (auth_fail r Status.unauthorized "Bearer realm=\"api\""
    "{\"error\":\"unauthorized\"}")
}

#[test]
def test_bearer_non_bearer_scheme_is_missing : IO Bool := do {
  let v <- validator_with [jwks_exchange] true;
  let r <- Bearer.require_at v List.empty ok_handler
    (request_auth "Basic dXNlcjpwYXNz") 2000i64;
  return (auth_fail r Status.unauthorized "Bearer realm=\"api\""
    "{\"error\":\"unauthorized\"}")
}

#[test]
def test_bearer_duplicate_headers_rejected : IO Bool := do {
  let v <- validator_with [jwks_exchange] true;
  let r <- Bearer.require_at v List.empty ok_handler
    (request_two_auth ("Bearer " ++ valid_token) ("Bearer " ++ valid_token)) 2000i64;
  return (auth_fail r Status.unauthorized
    "Bearer realm=\"api\", error=\"invalid_token\""
    "{\"error\":\"invalid_token\"}")
}

#[test]
def test_bearer_oversize_token_rejected : IO Bool := do {
  let v <- validator_with [jwks_exchange] true;
  let huge := "Bearer " ++ String.repeat "a" 16385i64;
  let r <- Bearer.require_at v List.empty ok_handler (request_auth huge) 2000i64;
  return (auth_fail r Status.unauthorized
    "Bearer realm=\"api\", error=\"invalid_token\""
    "{\"error\":\"invalid_token\"}")
}

// ── verification and claims ───────────────────────────────────────────────

#[test]
def test_bearer_valid_token_reaches_handler : IO Bool := do {
  let v <- validator_with [jwks_exchange] true;
  let r <- Bearer.require_at v List.empty ok_handler
    (request_auth ("Bearer " ++ valid_token)) 2000i64;
  return (U16.beq (status_of r) Status.ok && body_of r == "u1")
}

#[test]
def test_bearer_scheme_is_case_insensitive : IO Bool := do {
  let v <- validator_with [jwks_exchange] true;
  let r <- Bearer.require_at v List.empty ok_handler
    (request_auth ("bearer " ++ valid_token)) 2000i64;
  return (U16.beq (status_of r) Status.ok)
}

#[test]
def test_bearer_invalid_signature_rejected : IO Bool := do {
  let v <- validator_with [jwks_exchange] false;
  let r <- Bearer.require_at v List.empty ok_handler
    (request_auth ("Bearer " ++ valid_token)) 2000i64;
  return (auth_fail r Status.unauthorized
    "Bearer realm=\"api\", error=\"invalid_token\""
    "{\"error\":\"invalid_token\"}")
}

#[test]
def test_bearer_expired_rejected : IO Bool := do {
  let v <- validator_with [jwks_exchange] true;
  let r <- Bearer.require_at v List.empty ok_handler
    (request_auth ("Bearer " ++ expired_token)) 2000i64;
  return (auth_fail r Status.unauthorized
    "Bearer realm=\"api\", error=\"invalid_token\""
    "{\"error\":\"invalid_token\"}")
}

#[test]
def test_bearer_insufficient_scope : IO Bool := do {
  let v <- validator_with [jwks_exchange] true;
  let r <- Bearer.require_at v ["write"] ok_handler
    (request_auth ("Bearer " ++ valid_token)) 2000i64;
  return (auth_fail r Status.forbidden
    "Bearer realm=\"api\", error=\"insufficient_scope\", scope=\"write\""
    "{\"error\":\"insufficient_scope\"}")
}

#[test]
def test_bearer_handler_error_passes_through : IO Bool := do {
  let v <- validator_with [jwks_exchange] true;
  let r <- Bearer.require_at v List.empty fail_handler
    (request_auth ("Bearer " ++ valid_token)) 2000i64;
  return (match r {
    Result.err msg => msg == "handler called",
    Result.ok _ => false
  })
}

// ── JWKS availability and cache ────────────────────────────────────────────

#[test]
def test_bearer_jwks_unavailable_is_503 : IO Bool := do {
  let v <- validator_with [exchange_of "/jwks" 500u16 "down"] true;
  let r <- Bearer.require_at v List.empty ok_handler
    (request_auth ("Bearer " ++ valid_token)) 2000i64;
  return (auth_fail r Status.service_unavailable
    "Bearer realm=\"api\", error=\"temporarily_unavailable\""
    "{\"error\":\"temporarily_unavailable\"}")
}

#[test]
def test_bearer_no_jwks_endpoint_is_503 : IO Bool := do {
  let no_posts : List ScriptedExchange := List.empty;
  let http <- OauthHttp.fake List.empty no_posts;
  let v <- BearerValidator.jwt idp_config no_jwks_endpoints http (JwtVerifier.fake true);
  let r <- Bearer.require_at v List.empty ok_handler
    (request_auth ("Bearer " ++ valid_token)) 2000i64;
  return (auth_fail r Status.service_unavailable
    "Bearer realm=\"api\", error=\"temporarily_unavailable\""
    "{\"error\":\"temporarily_unavailable\"}")
}

#[test]
def test_bearer_jwks_cache_reused : IO Bool := do {
  let v <- validator_with [jwks_exchange] true;
  let req := request_auth ("Bearer " ++ valid_token);
  let r1 <- Bearer.require_at v List.empty ok_handler req 2000i64;
  let r2 <- Bearer.require_at v List.empty ok_handler req 2001i64;
  // Only one GET is scripted: a second fetch would fail as 503.
  return (U16.beq (status_of r1) Status.ok && U16.beq (status_of r2) Status.ok)
}

#[test]
def test_bearer_unknown_kid_refetches_once : IO Bool := do {
  let v <- validator_with
    [exchange_of "/jwks" 200u16 (jwks_json (Option.some "k1")),
     exchange_of "/jwks" 200u16 (jwks_json (Option.some "k2"))]
    true;
  let r <- Bearer.require_at v List.empty ok_handler
    (request_auth ("Bearer " ++ kid2_token)) 2000i64;
  return (U16.beq (status_of r) Status.ok)
}

#[test]
def test_bearer_malformed_jwks_is_503 : IO Bool := do {
  // Valid JSON, but not a JWKS: the issuer is misconfigured, so the client
  // is told to retry rather than that its token is invalid.
  let v <- validator_with [exchange_of "/jwks" 200u16 "{}"] true;
  let r <- Bearer.require_at v List.empty ok_handler
    (request_auth ("Bearer " ++ valid_token)) 2000i64;
  return (auth_fail r Status.service_unavailable
    "Bearer realm=\"api\", error=\"temporarily_unavailable\""
    "{\"error\":\"temporarily_unavailable\"}")
}

#[test]
def test_bearer_failed_refetch_is_rate_limited : IO Bool := do {
  // Only the first JWKS GET is scripted; the forced refetch after the
  // unknown kid fails (503) but must count against the rate limit, so a
  // second request in the same second answers 503 without fetching again.
  let v <- validator_with [exchange_of "/jwks" 200u16 (jwks_json (Option.some "k1"))] true;
  let req := request_auth ("Bearer " ++ kid2_token);
  let r1 <- Bearer.require_at v List.empty ok_handler req 2000i64;
  let r2 <- Bearer.require_at v List.empty ok_handler req 2000i64;
  return (U16.beq (status_of r1) Status.service_unavailable
    && U16.beq (status_of r2) Status.service_unavailable)
}

#[test]
def test_bearer_unknown_kid_refetch_is_rate_limited : IO Bool := do {
  // Three documents are scripted. The first request consumes k1 (TTL) and
  // k2 (forced refetch). A second, different kid in the same second must
  // NOT consume k3: if the forced-refetch clock failed, it would fetch k3
  // and succeed.
  let v <- validator_with
    [exchange_of "/jwks" 200u16 (jwks_json (Option.some "k1")),
     exchange_of "/jwks" 200u16 (jwks_json (Option.some "k2")),
     exchange_of "/jwks" 200u16 (jwks_json (Option.some "k3"))]
    true;
  let r1 <- Bearer.require_at v List.empty ok_handler
    (request_auth ("Bearer " ++ kid2_token)) 2000i64;
  let r2 <- Bearer.require_at v List.empty ok_handler
    (request_auth ("Bearer " ++ kid3_token)) 2000i64;
  return (U16.beq (status_of r1) Status.ok
    && U16.beq (status_of r2) Status.service_unavailable)
}

#[test]
def test_bearer_jwks_outage_is_rate_limited : IO Bool := do {
  // A failed cold fetch counts against the clock: the second request in the
  // same second must not consume the healthy second document; one second
  // later it may, and succeeds.
  let v <- validator_with
    [exchange_of "/jwks" 500u16 "down",
     exchange_of "/jwks" 200u16 (jwks_json Option.none)]
    true;
  let req := request_auth ("Bearer " ++ valid_token);
  let r1 <- Bearer.require_at v List.empty ok_handler req 2000i64;
  let r2 <- Bearer.require_at v List.empty ok_handler req 2000i64;
  let r3 <- Bearer.require_at v List.empty ok_handler req 2001i64;
  return (U16.beq (status_of r1) Status.service_unavailable
    && U16.beq (status_of r2) Status.service_unavailable
    && U16.beq (status_of r3) Status.ok)
}

#[test]
def test_bearer_require_uses_the_wall_clock : IO Bool := do {
  // `Bearer.require` divides IO.current_time's milliseconds by 1000. A token
  // that expires an hour from now must pass; without the division it would
  // look long expired.
  let v <- validator_with [jwks_exchange] true;
  let ms <- IO.current_time;
  let now := I64.div ms 1000i64;
  let claims := "{\"iss\":\"https://idp.example\",\"sub\":\"u1\",\"aud\":\"api://x\",\"exp\":"
    ++ I64.to_string (I64.add now 3600i64) ++ ",\"scope\":\"read\"}";
  let token := token_of "{\"alg\":\"RS256\"}" claims;
  let r <- Bearer.require v List.empty ok_handler (request_auth ("Bearer " ++ token));
  return (U16.beq (status_of r) Status.ok)
}

def audit_log : IO (Pair (Ref (List String)) (AuditEvent -> IO Unit)) := do {
  let cell <- Ref.new (List.empty : List String);
  let hook : AuditEvent -> IO Unit := fn (e : AuditEvent) => do {
    let _ <- Ref.update cell
      (fn (xs : List String) => List.append xs [AuditEvent.render e]);
    return unit
  };
  return (Pair.pair cell hook)
}

#[test]
def test_bearer_audits_allowed_and_denied : IO Bool := do {
  let pair <- audit_log;
  match pair {
    Pair.pair cell hook => do {
      let v <- validator_with [jwks_exchange] true;
      let v2 := BearerValidator.with_audit v hook;
      let req := request_auth ("Bearer " ++ valid_token);
      let _ <- Bearer.require_at v2 List.empty ok_handler req 2000i64;
      let vd <- validator_with [jwks_exchange] false;
      let vd2 := BearerValidator.with_audit vd hook;
      let _ <- Bearer.require_at vd2 List.empty ok_handler req 2000i64;
      let entries <- Ref.get cell;
      let allowed := List.any
        (fn (s : String) =>
          String.contains s "oauth allowed"
            && String.contains s "sub=\"u1\""
            && String.contains s "status=200")
        entries;
      let denied := List.any
        (fn (s : String) =>
          String.contains s "oauth denied"
            && String.contains s "reason=\"invalid_token\"")
        entries;
      let leaked := List.any (fn (s : String) => String.contains s valid_token) entries;
      return (I64.beq (List.length entries) 2i64 && allowed && denied
        && Bool.not leaked)
    }
  }
}
