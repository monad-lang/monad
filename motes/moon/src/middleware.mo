/// HTTP middleware — `moon` mote, Layer 0 (pure composition).
///
/// Middleware wraps a handler, transforming either the request before it
/// reaches the handler or the response after. The pattern is simply
/// function composition: each middleware takes a handler and returns a new
/// handler. Compose by nesting: `Middleware.cors (Middleware.content_type handler)`.
///
/// Built-in middleware:
///   - `Middleware.logging`      — prints method + path to stdout
///   - `Middleware.cors`         — adds Access-Control-Allow-* headers
///   - `Middleware.content_type` — sets Content-Type if not present
///   - `Middleware.recover`     — placeholder for error recovery (no-op in v1)
///   - `Middleware.auth_basic`   — checks Basic Authorization header
///   - `Middleware.auth_bearer`  — checks Bearer token in Authorization header

use http::types {
  Headers.empty, Headers.get, Headers.set, Request, Response, Status.forbidden,
  Status.unauthorized, http1_1, text,
}
use http::body {Body.content_type}
use http::strings {
  Strings.base64_decode, Strings.list_drop_prefix, Strings.list_starts_with,
}

/// Log the request method and path to stdout before calling the handler.
pub def Middleware.logging (handler : Request -> IO Response) (req : Request) : IO Response := do {
  IO.println req.uri.path;
  handler req
}

// ── CORS ────────────────────────────────────────────────────────────────

/// Add permissive CORS headers to the response. Allows all origins, common
/// methods, and common headers.
pub def Middleware.cors (handler : Request -> IO Response) (req : Request) : IO Response :=
  Monad.bind (handler req) (fn res =>
    return (Middleware.cors_response res))

/// Add CORS headers to a response.
def Middleware.cors_response (res : Response) : Response :=
  let h1 := Headers.set "Access-Control-Allow-Origin" "*" res.headers in
  let h2 := Headers.set "Access-Control-Allow-Methods" "GET, POST, PUT, DELETE, PATCH, OPTIONS" h1 in
  let h3 := Headers.set "Access-Control-Allow-Headers" "Content-Type, Authorization" h2 in
  { res with headers := h3 }

// ── content_type ────────────────────────────────────────────────────────

/// If the response has a body but no Content-Type header, infer one from
/// the body variant (text → text/plain, bytes → application/octet-stream, etc.).
pub def Middleware.content_type (handler : Request -> IO Response) (req : Request) : IO Response :=
  Monad.bind (handler req) (fn res =>
    return (Middleware.ensure_content_type res))

/// Add Content-Type if missing, inferred from the body.
def Middleware.ensure_content_type (res : Response) : Response :=
  match Headers.get "Content-Type" res.headers {
    Option.some _ => res,
    Option.none =>
      let ct := Body.content_type res.body in
      if String.is_empty ct
      then res
      else { res with headers := Headers.set "Content-Type" ct res.headers }
  }

// ── recover ─────────────────────────────────────────────────────────────

/// Catch handler errors and return a 500 response. Since Monad IO has no
/// built-in exception catching (no try/catch), this is a no-op wrapper in v1.
/// It exists as a placeholder for when error handling lands; the handler
/// runs directly.
pub def Middleware.recover (handler : Request -> IO Response) (req : Request) : IO Response :=
  handler req

// ── auth_basic ──────────────────────────────────────────────────────────

/// Check for a Basic Authorization header. If missing or invalid, return 401.
/// The predicate validates the decoded "user:pass" credential string: the
/// header carries it base64-encoded (RFC 7617), so `check` sees plain
/// `user:pass` and a credential that is not valid base64 is rejected as
/// unauthorized rather than handed to `check` as encoded text.
pub def Middleware.auth_basic (check : String -> Bool) (handler : Request -> IO Response) (req : Request) : IO Response :=
  match Headers.get "Authorization" req.headers {
    Option.none => Middleware.unauthorized,
    Option.some cred =>
      if Strings.list_starts_with (String.to_list "Basic ") (String.to_list cred)
      then
        let encoded := String.from_list (Strings.list_drop_prefix (String.to_list "Basic ") (String.to_list cred)) in
        match Strings.base64_decode encoded {
          Result.err _ => Middleware.unauthorized,
          Result.ok bytes =>
            if check (String.from_list bytes)
            then handler req
            else Middleware.forbidden
        }
      else Middleware.unauthorized
  }

/// 401 Unauthorized response with WWW-Authenticate header.
def Middleware.unauthorized : IO Response :=
  return ({ status := Status.unauthorized, headers := Headers.set "WWW-Authenticate" "Basic realm=\"Restricted\"" Headers.empty, version := HttpVersion.http1_1, body := Body.text "Unauthorized" } : Response)

/// 403 Forbidden response.
def Middleware.forbidden : IO Response :=
  return ({ status := Status.forbidden, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text "Forbidden" } : Response)

// ── auth_bearer ────────────────────────────────────────────────────────

/// Check for a Bearer token in the Authorization header. If missing or the
/// token doesn't pass the predicate, return 401.
pub def Middleware.auth_bearer (check : String -> Bool) (handler : Request -> IO Response) (req : Request) : IO Response :=
  match Headers.get "Authorization" req.headers {
    Option.none => Middleware.unauthorized,
    Option.some cred =>
      if Strings.list_starts_with (String.to_list "Bearer ") (String.to_list cred)
      then
        let token := String.from_list (Strings.list_drop_prefix (String.to_list "Bearer ") (String.to_list cred)) in
        if check token
        then handler req
        else Middleware.unauthorized
      else Middleware.unauthorized
  }
