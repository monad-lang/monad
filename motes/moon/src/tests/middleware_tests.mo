/// Phase 8 tests — HTTP middleware composition over the Result handler type.
///
/// Tests verify that middleware wraps handlers correctly: CORS headers are
/// added, Content-Type is inferred, auth checks reject unauthorized requests,
/// and `recover` maps a handler `Err` to an error response.

use http::body {Body.to_bytes_pure}
use http::types {
  GET, Headers.empty, Headers.get, Headers.set, Request, Response,
  Status.forbidden, Status.internal_server_error, Status.ok, Status.unauthorized,
  empty, http1_1, text, uri,
}
use moon::middleware {
  Middleware.auth_basic, Middleware.auth_bearer, Middleware.content_type,
  Middleware.cors, Middleware.recover,
}
use http::strings {}

// ── test infrastructure ─────────────────────────────────────────────────

/// Build a GET request with optional Authorization header.
def mk_req (path : String) (auth : Option String) : Request :=
  let hs := match auth {
    Option.none => Headers.empty,
    Option.some cred => Headers.set "Authorization" cred Headers.empty
  } in
  { method := Method.GET, uri := Uri.uri "" Option.none "" Option.none path Option.none Option.none, headers := hs, version := HttpVersion.http1_1, body := Body.empty }

/// Handler that returns 200 "ok".
def ok_handler (_ : Request) : IO (Result String Response) :=
  return (Result.ok (Response.ok_text "ok"))

/// Handler that fails.
def fail_handler (_ : Request) : IO (Result String Response) :=
  return (Result.err "boom")

/// A 500-shaped error page.
def error_response (msg : String) : Response :=
  { status := Status.internal_server_error, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text msg }

/// Run a Result middleware; an `Err` becomes an error response so the
/// assertions can inspect it.
def run_mw (mw : Request -> IO (Result String Response)) (req : Request) : IO Response := do {
  let r <- mw req;
  match r {
    Result.ok res => return res,
    Result.err msg => return (error_response msg)
  }
}

/// Check status + body.
def resp_ok (res : Response) (want_status : U16) (want_body : String) : Bool :=
  Bool.and (U16.beq res.status want_status) (String.beq (String.from_list (Body.to_bytes_pure res.body)) want_body)

/// Check that a header exists with the expected value.
def has_header (res : Response) (key : String) (want : String) : Bool :=
  match Headers.get key res.headers {
    Option.some v => String.beq v want,
    Option.none => false
  }

// ── tests ──────────────────────────────────────────────────────────────

/// CORS middleware adds Access-Control-Allow-Origin: *.
#[test]
def test_middleware_cors : IO Bool := do {
  let res <- run_mw (Middleware.cors ok_handler) (mk_req "/test" Option.none);
  return (Bool.and (resp_ok res Status.ok "ok") (has_header res "Access-Control-Allow-Origin" "*"))
}

/// Content-Type middleware infers text/plain for text body.
#[test]
def test_middleware_content_type : IO Bool := do {
  let res <- run_mw (Middleware.content_type ok_handler) (mk_req "/test" Option.none);
  return (Bool.and (resp_ok res Status.ok "ok") (has_header res "Content-Type" "text/plain; charset=utf-8"))
}

/// Recover passes a successful response through unchanged.
#[test]
def test_middleware_recover_passes_ok : IO Bool := do {
  let res <- run_mw (Middleware.recover error_response ok_handler) (mk_req "/test" Option.none);
  return (resp_ok res Status.ok "ok")
}

/// Recover maps a handler Err to the configured error page.
#[test]
def test_middleware_recover_maps_err : IO Bool := do {
  let res <- run_mw (Middleware.recover error_response fail_handler) (mk_req "/test" Option.none);
  return (resp_ok res Status.internal_server_error "boom")
}

/// Auth basic: missing Authorization header → 401.
#[test]
def test_middleware_auth_basic_missing : IO Bool := do {
  let res <- run_mw (Middleware.auth_basic (fn _ => true) ok_handler) (mk_req "/test" Option.none);
  return (resp_ok res Status.unauthorized "Unauthorized")
}

/// Auth basic: valid credential → 200. The header is base64 (RFC 7617);
/// `YWRtaW46c2VjcmV0` is "admin:secret", so this also pins that the
/// predicate sees the DECODED text and not the encoded form.
#[test]
def test_middleware_auth_basic_valid : IO Bool := do {
  let res <- run_mw (Middleware.auth_basic (fn cred => String.beq cred "admin:secret") ok_handler) (mk_req "/test" (Option.some "Basic YWRtaW46c2VjcmV0"));
  return (resp_ok res Status.ok "ok")
}

/// Auth basic: a credential that decodes, but not to the expected one → 403.
/// `d3Jvbmc6d3Jvbmc=` is "wrong:wrong" (the `=` also exercises padding).
#[test]
def test_middleware_auth_basic_invalid : IO Bool := do {
  let res <- run_mw (Middleware.auth_basic (fn cred => String.beq cred "admin:secret") ok_handler) (mk_req "/test" (Option.some "Basic d3Jvbmc6d3Jvbmc="));
  return (resp_ok res Status.forbidden "Forbidden")
}

/// Auth basic: a credential that is not valid base64 at all → 401, never
/// the predicate (which must not be shown text no encoder could produce).
#[test]
def test_middleware_auth_basic_malformed : IO Bool := do {
  let res <- run_mw (Middleware.auth_basic (fn _ => true) ok_handler) (mk_req "/test" (Option.some "Basic admin:secret"));
  return (resp_ok res Status.unauthorized "Unauthorized")
}

/// Auth bearer: missing Authorization header → 401.
#[test]
def test_middleware_auth_bearer_missing : IO Bool := do {
  let res <- run_mw (Middleware.auth_bearer (fn _ => true) ok_handler) (mk_req "/test" Option.none);
  return (resp_ok res Status.unauthorized "Unauthorized")
}

/// Auth bearer: valid token → 200.
#[test]
def test_middleware_auth_bearer_valid : IO Bool := do {
  let res <- run_mw (Middleware.auth_bearer (fn tok => String.beq tok "abc123") ok_handler) (mk_req "/test" (Option.some "Bearer abc123"));
  return (resp_ok res Status.ok "ok")
}

/// Auth bearer: invalid token → 401.
#[test]
def test_middleware_auth_bearer_invalid : IO Bool := do {
  let res <- run_mw (Middleware.auth_bearer (fn tok => String.beq tok "abc123") ok_handler) (mk_req "/test" (Option.some "Bearer wrong"));
  return (resp_ok res Status.unauthorized "Unauthorized")
}

/// Composition: CORS wrapping content_type wrapping handler.
#[test]
def test_middleware_compose_cors_content_type : IO Bool := do {
  let wrapped := Middleware.cors (Middleware.content_type ok_handler);
  let res <- run_mw wrapped (mk_req "/test" Option.none);
  return (Bool.and
    (resp_ok res Status.ok "ok")
    (Bool.and (has_header res "Access-Control-Allow-Origin" "*") (has_header res "Content-Type" "text/plain; charset=utf-8")))
}
