/// Session middleware for `HandlerT`.
///
/// Kept out of `session.mo` to avoid a `context -> session -> handler`
/// import cycle: this module is the only one that needs both the context
/// slot and the session store. The original `SessionStore.with_session`
/// (over `Request -> IO (Result String Response)`) stays in `session.mo`.

use std::ref {Ref, Ref.get, Ref.new}
use http::types {Response}
use lib::context {Ctx, Ctx.header, Ctx.with_session, SessionSlot}
use lib::handler_t {HandlerT, HandlerT.run, HttpError, HttpError.make}
use lib::session {
  Session, SessionHandle, SessionHandle.make, SessionStore, SessionStore.add_cookies,
  SessionStore.begin, SessionStore.commit, SessionStore.load_header,
}

/// Load or create the request's session, install it into the context,
/// run `next`, then commit it and attach the `Set-Cookie` pairs to a
/// successful response. An `Err` passes through untouched.
pub def SessionStore.with_session_t (st : SessionStore)
    (next : HandlerT IO Response) : HandlerT IO Response :=
  HandlerT.mk (SessionStore.with_session_t_at st next)

def SessionStore.initial_t (st : SessionStore) (loaded : Option Session) :
    IO (Result String Session) :=
  match loaded {
    Option.none => SessionStore.begin_checked st,
    Option.some s => IO.pure (Result.ok s)
  }

def SessionStore.commit_session (st : SessionStore) (cell : Ref Session)
    (res : Response) : IO (Result HttpError Response) := do {
  let final <- Ref.get cell;
  let pairs <- SessionStore.commit st final;
  IO.pure (Result.ok (SessionStore.add_cookies res pairs))
}

def SessionStore.with_session_start (st : SessionStore)
    (next : HandlerT IO Response) (ctx : Ctx) (session : Session) :
    IO (Result HttpError Response) := do {
  let cell : Ref Session <- Ref.new session;
  let handle : SessionHandle := SessionHandle.make cell;
  let slot : SessionSlot := SessionSlot.present handle;
  let c2 : Ctx := Ctx.with_session ctx (Shared.of slot);
  let r <- HandlerT.run next c2;
  match r {
    Result.err e => IO.pure (Result.err e),
    Result.ok res => SessionStore.commit_session st cell res
  }
}

def SessionStore.with_session_t_at (st : SessionStore)
    (next : HandlerT IO Response) (ctx : Ctx) :
    IO (Result HttpError Response) := do {
  let cookie : Option String := Ctx.header "cookie" ctx;
  let loaded <- SessionStore.load_header st cookie;
  let initial <- SessionStore.initial_t st loaded;
  match initial {
    Result.err e => IO.pure (Result.err (HttpError.make 500u16 e)),
    Result.ok session => SessionStore.with_session_start st next ctx session
  }
}
