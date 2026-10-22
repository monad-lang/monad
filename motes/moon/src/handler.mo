/// The server's error channel.
///
/// Monad's `IO` has no exception channel, so a handler that can fail says so
/// in its type: `Request -> IO (Result String Response)`. `Err` is an error
/// message, not a response; the server (or `Handler.try`) decides how to map
/// it. This is what makes `Middleware.recover` real rather than a no-op.
///
/// `of_response` bridges the old `Request -> IO Response` shape, so existing
/// route handlers and tests keep working.

use http::types {Request, Response}

/// Lift a total handler into the error-aware form.
pub def Handler.of_response (h : Request -> IO Response) : Request -> IO (Result String Response) :=
  fn (req : Request) => do {
    let res <- h req;
    return (Result.ok res)
  }

/// Map a handler failure to a response. The result stays `Ok`: an error page
/// is a successful generation of a response.
pub def Handler.recover (on_error : String -> Response) (h : Request -> IO (Result String Response)) (req : Request) : IO (Result String Response) := do {
  let r <- h req;
  match r {
    Result.ok res => return (Result.ok res),
    Result.err msg => return (Result.ok (on_error msg))
  }
}

/// Transform the error message, leaving a successful response alone.
pub def Handler.map_error (f : String -> String) (h : Request -> IO (Result String Response)) (req : Request) : IO (Result String Response) := do {
  let r <- h req;
  match r {
    Result.ok res => return (Result.ok res),
    Result.err msg => return (Result.err (f msg))
  }
}

/// Run a handler and answer `fallback` on failure. This is the server's
/// edge adapter: the wire writer still takes a `Response`.
pub def Handler.try (fallback : Response) (h : Request -> IO (Result String Response)) (req : Request) : IO Response := do {
  let r <- h req;
  match r {
    Result.ok res => return res,
    Result.err _ => return fallback
  }
}
