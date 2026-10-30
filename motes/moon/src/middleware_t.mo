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
use http::types {
  Body, Headers, Headers.empty, Headers.get, Headers.set, HttpVersion, Request,
  Response, Status.forbidden, Status.unauthorized,
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
