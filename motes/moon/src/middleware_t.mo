/// Middleware over `HandlerT IO Response`.
///
/// The shape is `HandlerT IO Response -> HandlerT IO Response`; compose by
/// nesting, the same way the original `Middleware` functions do. The
/// response-transforming cores (`cors_response`, `ensure_content_type`) are
/// shared with `middleware.mo`, so the two APIs cannot drift.
///
/// The auth helpers here compare with `Strings.ct_eq`; the old predicate
/// variants remain for callers that need a custom check.

use init::borrow {Borrow, Borrow.get}
use std::list {List.any}
use http::types {
  Body, Headers, Headers.add, Headers.empty, Headers.get, Headers.set, HttpVersion,
  Method, Request, Response, Status.forbidden, Status.no_content,
  Status.unauthorized,
}
use http::strings {
  Strings.base64_decode, Strings.ct_eq, Strings.list_drop_prefix,
  Strings.list_starts_with,
}
use lib::context {Ctx, Ctx.request}
use lib::handler_t {
  HandlerT, HandlerT.catch_io, HandlerT.io_bind, HandlerT.pure_io, HandlerT.run,
  HttpError,
}
use lib::middleware {Middleware.cors_response, Middleware.ensure_content_type}

/// Log the request path, then run the handler.
pub def MiddlewareT.logging (next : HandlerT IO Response) : HandlerT IO Response :=
  HandlerT.mk (fn (ctx : Borrow Ctx) =>
    let rb : Borrow Request := Ctx.request (Borrow.get ctx) in
    let req : Request := Borrow.get rb in
    HandlerT.io_bind (IO.println req.uri.path) (fn (_ : Unit) =>
      HandlerT.run next ctx))

/// Apply a pure transformation to every successful response.
pub def MiddlewareT.map_response (f : Response -> Response)
    (next : HandlerT IO Response) : HandlerT IO Response :=
  HandlerT.mk (fn (ctx : Borrow Ctx) =>
    HandlerT.io_bind (HandlerT.run next ctx) (fn (r : Result HttpError Response) =>
      match r {
        Result.ok res => IO.pure (Result.ok (f res)),
        Result.err e => IO.pure (Result.err e)
      }))

pub def MiddlewareT.cors (next : HandlerT IO Response) : HandlerT IO Response :=
  MiddlewareT.map_response Middleware.cors_response next

// ── configurable CORS ───────────────────────────────────────────────────
//
// The wildcard `cors` above is the historical behaviour. The configurable
// form never sends `*`: it echoes the request's Origin, adds `Vary:
// Origin` (so caches do not serve one origin's response to another), and
// answers preflight with 204. The default is same-origin (no headers).

pub struct CorsConfig {
  origins : List String,
  any_origin : Bool,
  methods : String,
  headers : String,
  max_age_seconds : I64,
  allow_credentials : Bool
}

pub def CorsConfig.default : CorsConfig :=
  let c : CorsConfig :=
    { origins := List.empty, any_origin := false,
      methods := "GET, POST, PUT, DELETE, PATCH, OPTIONS",
      headers := "Content-Type, Authorization", max_age_seconds := 600i64,
      allow_credentials := false } in
  c

pub def CorsConfig.allow_origin (origin : String) (cfg : CorsConfig) : CorsConfig :=
  let c : CorsConfig := { cfg with origins := List.cons origin cfg.origins } in c

def MiddlewareT.origin_allowed (cfg : CorsConfig) (origin : String) : Bool :=
  if cfg.any_origin
  then true
  else List.any (fn (o : String) => String.beq o origin) cfg.origins

def MiddlewareT.has_header (name : String) (headers : Headers) : Bool :=
  match Headers.get name headers {
    Option.some _ => true,
    Option.none => false
  }

def MiddlewareT.is_preflight (req : Request) : Bool :=
  match req {
    { method, headers, .. } =>
      Bool.and (BEq.beq method Method.OPTIONS)
        (MiddlewareT.has_header "Access-Control-Request-Method" headers)
  }

def MiddlewareT.preflight_response (cfg : CorsConfig) (origin : String) : Response :=
  let h1 := Headers.set "Access-Control-Allow-Origin" origin Headers.empty in
  let h2 := Headers.add "Vary" "Origin" h1 in
  let h3 := Headers.set "Access-Control-Allow-Methods" cfg.methods h2 in
  let h4 := Headers.set "Access-Control-Allow-Headers" cfg.headers h3 in
  let h5 := Headers.set "Access-Control-Max-Age" (I64.to_string cfg.max_age_seconds) h4 in
  let h6 :=
    if cfg.allow_credentials
    then Headers.set "Access-Control-Allow-Credentials" "true" h5
    else h5 in
  { status := Status.no_content, headers := h6, version := HttpVersion.http1_1,
    body := Body.empty }

def MiddlewareT.add_cors_headers (cfg : CorsConfig) (origin : String)
    (res : Response) : Response :=
  match res {
    { status, headers, version, body } =>
      let h1 := Headers.set "Access-Control-Allow-Origin" origin headers in
      let h2 := Headers.add "Vary" "Origin" h1 in
      let h3 :=
        if cfg.allow_credentials
        then Headers.set "Access-Control-Allow-Credentials" "true" h2
        else h2 in
      { status := status, headers := h3, version := version, body := body }
  }

def MiddlewareT.cors_origin_at (cfg : CorsConfig) (origin : String)
    (next : HandlerT IO Response) (req : Request) (ctx : Borrow Ctx) :
    IO (Result HttpError Response) := do {
  if Bool.not (MiddlewareT.origin_allowed cfg origin)
  then HandlerT.run next ctx
  else if MiddlewareT.is_preflight req
  then IO.pure (Result.ok (MiddlewareT.preflight_response cfg origin))
  else do {
    let r <- HandlerT.run next ctx;
    match r {
      Result.ok res => IO.pure (Result.ok (MiddlewareT.add_cors_headers cfg origin res)),
      Result.err e => IO.pure (Result.err e)
    }
  }
}

def MiddlewareT.cors_at (cfg : CorsConfig) (next : HandlerT IO Response)
    (ctx : Borrow Ctx) : IO (Result HttpError Response) := do {
  let req : Request := Borrow.get (Ctx.request (Borrow.get ctx));
  match Headers.get "Origin" req.headers {
    Option.none => HandlerT.run next ctx,
    Option.some origin => MiddlewareT.cors_origin_at cfg origin next req ctx
  }
}

/// CORS with an explicit policy. Compose like any other middleware.
pub def MiddlewareT.cors_with (cfg : CorsConfig)
    (next : HandlerT IO Response) : HandlerT IO Response :=
  HandlerT.mk (MiddlewareT.cors_at cfg next)

pub def MiddlewareT.content_type (next : HandlerT IO Response) : HandlerT IO Response :=
  MiddlewareT.map_response Middleware.ensure_content_type next

/// Map a handler failure to a response. The result is `Ok`: an error page
/// is a successful generation of a response.
pub def MiddlewareT.recover (on_error : HttpError -> Response)
    (next : HandlerT IO Response) : HandlerT IO Response :=
  HandlerT.catch_io next (fn (e : HttpError) => HandlerT.pure_io (on_error e))

// ── auth ────────────────────────────────────────────────────────────────

def MiddlewareT.unauthorized_response : Response :=
  { status := Status.unauthorized,
    headers := Headers.set "WWW-Authenticate" "Basic realm=\"Restricted\"" Headers.empty,
    version := HttpVersion.http1_1, body := Body.text "Unauthorized" }

def MiddlewareT.forbidden_response : Response :=
  { status := Status.forbidden, headers := Headers.empty,
    version := HttpVersion.http1_1, body := Body.text "Forbidden" }

def MiddlewareT.auth_basic_at (expected : String) (next : HandlerT IO Response)
    (ctx : Borrow Ctx) : IO (Result HttpError Response) :=
  let req : Request := Borrow.get (Ctx.request (Borrow.get ctx)) in
  match Headers.get "Authorization" req.headers {
    Option.none => IO.pure (Result.ok MiddlewareT.unauthorized_response),
    Option.some cred =>
      let cred_s : String := cred in
      if Strings.list_starts_with (String.to_list "Basic ") (String.to_list cred_s)
      then
        let encoded := String.from_list
          (Strings.list_drop_prefix (String.to_list "Basic ") (String.to_list cred_s)) in
        match Strings.base64_decode encoded {
          Result.err _ => IO.pure (Result.ok MiddlewareT.unauthorized_response),
          Result.ok bytes =>
            let decoded := String.from_list bytes in
            if Strings.ct_eq decoded expected
            then HandlerT.run next ctx
            else IO.pure (Result.ok MiddlewareT.forbidden_response)
        }
      else IO.pure (Result.ok MiddlewareT.unauthorized_response)
  }

/// Basic auth against a `user:password` credential, compared in constant
/// time.
pub def MiddlewareT.auth_basic_ct (expected : String)
    (next : HandlerT IO Response) : HandlerT IO Response :=
  HandlerT.mk (MiddlewareT.auth_basic_at expected next)

def MiddlewareT.auth_bearer_at (expected : String) (next : HandlerT IO Response)
    (ctx : Borrow Ctx) : IO (Result HttpError Response) :=
  let req : Request := Borrow.get (Ctx.request (Borrow.get ctx)) in
  match Headers.get "Authorization" req.headers {
    Option.none => IO.pure (Result.ok MiddlewareT.unauthorized_response),
    Option.some cred =>
      let cred_s : String := cred in
      if Strings.list_starts_with (String.to_list "Bearer ") (String.to_list cred_s)
      then
        let token := String.from_list
          (Strings.list_drop_prefix (String.to_list "Bearer ") (String.to_list cred_s)) in
        if Strings.ct_eq token expected
        then HandlerT.run next ctx
        else IO.pure (Result.ok MiddlewareT.unauthorized_response)
      else IO.pure (Result.ok MiddlewareT.unauthorized_response)
  }

/// Bearer auth against an expected token, compared in constant time.
pub def MiddlewareT.auth_bearer_ct (expected : String)
    (next : HandlerT IO Response) : HandlerT IO Response :=
  HandlerT.mk (MiddlewareT.auth_bearer_at expected next)
