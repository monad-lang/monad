/// The read-only context a `HandlerT` computation runs in.
///
/// `Ctx` is passed as `Borrow Ctx` and its fields are themselves `Borrow`s:
/// `Borrow A` is `Copy` (`init/src/borrow.mo`), so `bind`, middleware and
/// routing can read the same context repeatedly without spending an affine
/// budget and without copying the request. That is what makes `HandlerT`
/// affine-clean at a non-Copy environment (the reason `ReaderT`'s own
/// `bind` needed the Borrow fix).
///
/// CONTRACT: a handler must not store the values behind these borrows. The
/// affine rule does not yet enforce `Borrow` escape (`Borrow.get` is
/// unrestricted); treat `Ctx` as read-only for the duration of one request.

use init::borrow {Borrow}
use http::types {Request}
use lib::session {SessionHandle}

/// The session middleware's presence in the context.
pub type SessionSlot {
  absent,
  present (handle : Borrow SessionHandle)
}

pub struct Ctx {
  request : Borrow Request,
  session : Borrow SessionSlot
}

/// The installed session handle, if session middleware ran. Matching the
/// constructor stays in this module; handlers match an `Option` instead.
pub def SessionSlot.handle (s : SessionSlot) : Option (Borrow SessionHandle) :=
  match s {
    SessionSlot.absent => Option.none,
    SessionSlot.present h => Option.some h
  }

pub def Ctx.request (c : Ctx) : Borrow Request := c.request

pub def Ctx.session (c : Ctx) : Borrow SessionSlot := c.session

/// Build a context. A `let`-bound helper rather than a bare struct literal
/// at the call site: the annotated-literal rule the codebase follows.
pub def Ctx.make (request : Borrow Request) (session : Borrow SessionSlot) : Ctx :=
  let c : Ctx := { request := request, session := session } in c

/// Rebuild only the request half (the router attaches path params this way).
pub def Ctx.with_request (c : Ctx) (request : Borrow Request) : Ctx :=
  let c2 : Ctx := { request := request, session := c.session } in c2

/// Rebuild only the session half (session middleware installs its handle).
pub def Ctx.with_session (c : Ctx) (session : Borrow SessionSlot) : Ctx :=
  let c2 : Ctx := { request := c.request, session := session } in c2
