/// Session middleware for `HandlerT`.
///
/// Kept out of `session.mo` to avoid a `context -> session -> handler`
/// import cycle: this module is the only one that needs both the context
/// slot and the session store. The original `SessionStore.with_session`
/// (over `Request -> IO (Result String Response)`) stays in `session.mo`.

use init::borrow {Borrow, Borrow.get}
use std::ref {Ref, Ref.get, Ref.new}
use http::types {Request, Response}
use lib::context {Ctx, Ctx.request, Ctx.with_session, SessionSlot}
use lib::handler_t {HandlerT, HandlerT.run, HttpError}
use lib::session {
  Session, SessionHandle, SessionHandle.make, SessionStore, SessionStore.add_cookies,
  SessionStore.begin, SessionStore.commit, SessionStore.load,
}

/// Load or create the request's session, install it into the context,
/// run `next`, then commit it and attach the `Set-Cookie` pairs to a
/// successful response. An `Err` passes through untouched.
pub def SessionStore.with_session_t (st : SessionStore)
    (next : HandlerT IO Response) : HandlerT IO Response :=
  HandlerT.mk (SessionStore.with_session_t_at st next)

def SessionStore.initial_t (st : SessionStore) (loaded : Option Session) : IO Session :=
  match loaded {
    Option.none => SessionStore.begin st,
    Option.some s => IO.pure s
  }

def SessionStore.with_session_t_at (st : SessionStore)
    (next : HandlerT IO Response) (ctx : Borrow Ctx) :
    IO (Result HttpError Response) := do {
  let req : Request := Borrow.get (Ctx.request (Borrow.get ctx));
  let loaded <- SessionStore.load st req;
  let initial <- SessionStore.initial_t st loaded;
  let cell : Ref Session <- Ref.new initial;
  let handle : SessionHandle := SessionHandle.make cell;
  let slot : SessionSlot := SessionSlot.present (Borrow.of handle);
  let c2 : Ctx := Ctx.with_session (Borrow.get ctx) (Borrow.of slot);
  let r <- HandlerT.run next (Borrow.of c2);
  match r {
    Result.err e => IO.pure (Result.err e),
    Result.ok res => do {
      let final <- Ref.get cell;
      let pairs <- SessionStore.commit st final;
      IO.pure (Result.ok (SessionStore.add_cookies res pairs))
    }
  }
}
