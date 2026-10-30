/// `HandlerT` — the transformer-shaped handler API, alongside the original
/// `Request -> IO Response` surface (both stay supported; nothing here
/// deprecates the old one).
///
/// Shape: `HandlerT M A = Borrow Ctx -> M (Result HttpError A)`. That is a
/// `ReaderT Ctx (ResultT HttpError M)` with the environment borrowed once
/// and the error channel typed. The concrete newtype plus a hand-written
/// `Monad` instance is deliberate: resolving the generic
/// `Monad (ReaderT Ctx (ResultT E M))` miscompiles self-hosted (the same
/// reason `motes/sql/src/db.mo` hand-writes `DbM.bind`).
///
/// IO-specialised `_io` operations exist because a `[Monad M]`-constrained
/// helper called from inside a lambda crashes the compiled backend
/// (measured). `HandlerT.catch_io (fn e => HandlerT.throw_io e)` is safe;
/// the generic `HandlerT.catch (fn e => HandlerT.throw e)` is not. Inside
/// lambdas use the `_io` forms, `Monad.pure`/`Monad.bind` at IO, and
/// unconstrained helpers (`run`, `local`, `ask_io`, `request_io`).

use init::borrow {Borrow, Borrow.get}
use http::types {
  Body, Headers, Headers.set, HttpVersion, Request, Response,
  Status.bad_request, Status.forbidden, Status.internal_server_error,
  Status.not_found, Status.payload_too_large, Status.request_header_fields_too_large,
  Status.unauthorized,
}
use lib::context {
  Ctx, Ctx.make, Ctx.request, Ctx.session, Ctx.with_request, Ctx.with_session,
  SessionSlot,
}

// ── the error channel ───────────────────────────────────────────────────

pub struct HttpError {
  status : U16,
  headers : Headers,
  body : Body,
  detail : String
}

pub def HttpError.make (status : U16) (detail : String) : HttpError :=
  let e : HttpError :=
    { status := status, headers := Headers.empty, body := Body.text detail, detail := detail } in
  e

/// A response carrying this error's status/headers/body.
pub def HttpError.to_response (e : HttpError) : Response :=
  match e {
    { status, headers, body, .. } =>
      let r : Response :=
        { status := status, headers := headers, version := HttpVersion.http1_1, body := body } in
      r
  }

pub def HttpError.with_header (key : String) (value : String) (e : HttpError) : HttpError :=
  match e {
    { status, headers, body, detail } =>
      let hs : Headers := Headers.set key value headers in
      let e2 : HttpError := { status := status, headers := hs, body := body, detail := detail } in
      e2
  }

pub def HttpError.not_found : HttpError :=
  HttpError.make Status.not_found "Not Found"

pub def HttpError.bad_request : HttpError :=
  HttpError.make Status.bad_request "Bad Request"

pub def HttpError.forbidden : HttpError :=
  HttpError.make Status.forbidden "Forbidden"

pub def HttpError.unauthorized : HttpError :=
  HttpError.make Status.unauthorized "Unauthorized"

pub def HttpError.internal : HttpError :=
  HttpError.make Status.internal_server_error "Internal Server Error"

pub def HttpError.payload_too_large : HttpError :=
  HttpError.make Status.payload_too_large "Payload Too Large"

pub def HttpError.headers_too_large : HttpError :=
  HttpError.make Status.request_header_fields_too_large "Request Header Fields Too Large"

// ── the transformer ─────────────────────────────────────────────────────

pub type HandlerT (M : Type -> Type) (A : Type) {
  mk (run : Borrow Ctx -> M (Result HttpError A))
}

pub def HandlerT.run {M : Type -> Type} {A : Type}
    (h : HandlerT M A) (ctx : Borrow Ctx) : M (Result HttpError A) :=
  match h {
    HandlerT.mk r => r ctx
  }

// ── Monad (hand-written, concrete head) ─────────────────────────────────

def HandlerT.bind_step [Monad M] {A : Type} {B : Type}
    (f : A -> HandlerT M B) (ctx : Borrow Ctx) (r : Result HttpError A) :
    M (Result HttpError B) :=
  match r {
    Result.ok a => HandlerT.run (f a) ctx,
    Result.err e => Monad.pure (Result.err e)
  }

def HandlerT.bind_at [Monad M] {A : Type} {B : Type}
    (ma : HandlerT M A) (f : A -> HandlerT M B) (ctx : Borrow Ctx) :
    M (Result HttpError B) :=
  Monad.bind (HandlerT.run ma ctx) (HandlerT.bind_step f ctx)

pub instance [Monad M] Monad (HandlerT M) {
  def pure (a : A) : HandlerT M A :=
    HandlerT.mk (fn (_ : Borrow Ctx) => Monad.pure (Result.ok a))
  def bind (ma : HandlerT M A) (f : A -> HandlerT M B) : HandlerT M B :=
    HandlerT.mk (HandlerT.bind_at ma f)
}

// ── generic operations ─────────────────────────────────────────────────

pub def HandlerT.pure [Monad M] {A : Type} (a : A) : HandlerT M A :=
  HandlerT.mk (fn (_ : Borrow Ctx) => Monad.pure (Result.ok a))

pub def HandlerT.lift [Monad M] {A : Type} (m : M A) : HandlerT M A :=
  HandlerT.mk (fn (_ : Borrow Ctx) =>
    Monad.bind m (fn a => Monad.pure (Result.ok a)))

pub def HandlerT.ask [Monad M] : HandlerT M (Borrow Ctx) :=
  HandlerT.mk (fn (ctx : Borrow Ctx) => Monad.pure (Result.ok ctx))

pub def HandlerT.request [Monad M] : HandlerT M (Borrow Request) :=
  HandlerT.mk (fn (ctx : Borrow Ctx) =>
    Monad.pure (Result.ok (Ctx.request (Borrow.get ctx))))

pub def HandlerT.session [Monad M] : HandlerT M (Borrow SessionSlot) :=
  HandlerT.mk (fn (ctx : Borrow Ctx) =>
    Monad.pure (Result.ok (Ctx.session (Borrow.get ctx))))

pub def HandlerT.throw [Monad M] {A : Type} (e : HttpError) : HandlerT M A :=
  HandlerT.mk (fn (_ : Borrow Ctx) => Monad.pure (Result.err e))

def HandlerT.catch_step [Monad M] {A : Type}
    (on_error : HttpError -> HandlerT M A) (ctx : Borrow Ctx)
    (r : Result HttpError A) : M (Result HttpError A) :=
  match r {
    Result.ok a => Monad.pure (Result.ok a),
    Result.err e => HandlerT.run (on_error e) ctx
  }

def HandlerT.catch_at [Monad M] {A : Type}
    (h : HandlerT M A) (on_error : HttpError -> HandlerT M A) (ctx : Borrow Ctx) :
    M (Result HttpError A) :=
  Monad.bind (HandlerT.run h ctx) (HandlerT.catch_step on_error ctx)

pub def HandlerT.catch [Monad M] {A : Type}
    (h : HandlerT M A) (on_error : HttpError -> HandlerT M A) : HandlerT M A :=
  HandlerT.mk (HandlerT.catch_at h on_error)

pub def HandlerT.map_error [Monad M] {A : Type}
    (f : HttpError -> HttpError) (h : HandlerT M A) : HandlerT M A :=
  HandlerT.mk (fn (ctx : Borrow Ctx) =>
    Monad.bind (HandlerT.run h ctx) (fn (r : Result HttpError A) =>
      match r {
        Result.ok a => Monad.pure (Result.ok a),
        Result.err e => Monad.pure (Result.err (f e))
      }))

/// Run `h` in a locally modified context. Unconstrained, so it is safe in
/// lambdas.
pub def HandlerT.local {M : Type -> Type} {A : Type}
    (f : Ctx -> Ctx) (h : HandlerT M A) : HandlerT M A :=
  HandlerT.mk (HandlerT.local_at f h)

def HandlerT.local_at {M : Type -> Type} {A : Type}
    (f : Ctx -> Ctx) (h : HandlerT M A) (ctx : Borrow Ctx) :
    M (Result HttpError A) :=
  let inner : Borrow Ctx := Borrow.of (f (Borrow.get ctx)) in
  HandlerT.run h inner

/// Replace the request half of the context (the router attaches params).
pub def HandlerT.with_request {M : Type -> Type} {A : Type}
    (req : Borrow Request) (h : HandlerT M A) : HandlerT M A :=
  HandlerT.local (fn (c : Ctx) => Ctx.with_request c req) h

/// Replace the session half of the context.
pub def HandlerT.with_session {M : Type -> Type} {A : Type}
    (slot : Borrow SessionSlot) (h : HandlerT M A) : HandlerT M A :=
  HandlerT.local (fn (c : Ctx) => Ctx.with_session c slot) h

// ── IO-specialised operations (safe inside lambdas) ────────────────────
//
// `io_bind` is an unconstrained wrapper over the concrete `Monad IO`
// instance, so these bodies never mention a class-constrained def and can
// be used inside a `catch`/`map_error` lambda.

pub def HandlerT.io_bind {A : Type} {B : Type} (m : IO A) (f : A -> IO B) : IO B :=
  Monad.bind m f

pub def HandlerT.pure_io {A : Type} (a : A) : HandlerT IO A :=
  HandlerT.mk (fn (_ : Borrow Ctx) => IO.pure (Result.ok a))

pub def HandlerT.throw_io {A : Type} (e : HttpError) : HandlerT IO A :=
  HandlerT.mk (fn (_ : Borrow Ctx) => IO.pure (Result.err e))

pub def HandlerT.lift_io {A : Type} (m : IO A) : HandlerT IO A :=
  HandlerT.mk (fn (_ : Borrow Ctx) =>
    HandlerT.io_bind m (fn a => IO.pure (Result.ok a)))

pub def HandlerT.ask_io : HandlerT IO (Borrow Ctx) :=
  HandlerT.mk (fn (ctx : Borrow Ctx) => IO.pure (Result.ok ctx))

pub def HandlerT.request_io : HandlerT IO (Borrow Request) :=
  HandlerT.mk (fn (ctx : Borrow Ctx) =>
    IO.pure (Result.ok (Ctx.request (Borrow.get ctx))))

pub def HandlerT.session_io : HandlerT IO (Borrow SessionSlot) :=
  HandlerT.mk (fn (ctx : Borrow Ctx) =>
    IO.pure (Result.ok (Ctx.session (Borrow.get ctx))))

def HandlerT.catch_step_io {A : Type}
    (on_error : HttpError -> HandlerT IO A) (ctx : Borrow Ctx)
    (r : Result HttpError A) : IO (Result HttpError A) :=
  match r {
    Result.ok a => IO.pure (Result.ok a),
    Result.err e => HandlerT.run (on_error e) ctx
  }

def HandlerT.catch_at_io {A : Type}
    (h : HandlerT IO A) (on_error : HttpError -> HandlerT IO A) (ctx : Borrow Ctx) :
    IO (Result HttpError A) :=
  HandlerT.io_bind (HandlerT.run h ctx) (HandlerT.catch_step_io on_error ctx)

pub def HandlerT.catch_io {A : Type}
    (h : HandlerT IO A) (on_error : HttpError -> HandlerT IO A) : HandlerT IO A :=
  HandlerT.mk (HandlerT.catch_at_io h on_error)

pub def HandlerT.map_error_io {A : Type}
    (f : HttpError -> HttpError) (h : HandlerT IO A) : HandlerT IO A :=
  HandlerT.mk (fn (ctx : Borrow Ctx) =>
    HandlerT.io_bind (HandlerT.run h ctx) (fn (r : Result HttpError A) =>
      match r {
        Result.ok a => IO.pure (Result.ok a),
        Result.err e => IO.pure (Result.err (f e))
      }))

// ── running at the edges ────────────────────────────────────────────────

/// Run a handler against a bare request, with no session middleware.
pub def HandlerT.run_io {A : Type} (h : HandlerT IO A) (req : Request) :
    IO (Result HttpError A) :=
  let slot : SessionSlot := SessionSlot.absent in
  let c : Ctx := Ctx.make (Borrow.of req) (Borrow.of slot) in
  HandlerT.run h (Borrow.of c)

/// Adapt a transformer handler to the old total handler shape.
pub def HandlerT.to_old (h : HandlerT IO Response) (req : Request) : IO Response := do {
  let r <- HandlerT.run_io h req;
  match r {
    Result.ok res => IO.pure res,
    Result.err e => IO.pure (HttpError.to_response e)
  }
}

/// Adapt an old total handler into the transformer shape.
pub def HandlerT.of_old (h : Request -> IO Response) : HandlerT IO Response :=
  HandlerT.mk (fn (ctx : Borrow Ctx) =>
    HandlerT.io_bind (h (Borrow.get (Ctx.request (Borrow.get ctx))))
      (fn res => IO.pure (Result.ok res)))
