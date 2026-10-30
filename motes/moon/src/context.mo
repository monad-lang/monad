/// The read-only context a `HandlerT` computation runs in.
///
/// `Ctx` is a **Copy struct of Copy handles**: the method is a nullary enum
/// (`Copy Method`), the path is a `String`, and the headers, body, params
/// and session slot are `Shared` handles. A manual `Copy Ctx` instance is
/// sound for exactly that reason, and it is what lets `HandlerT.bind`,
/// middleware and routing read the same context repeatedly without views,
/// copies of the request, or an affine budget.
///
/// `Shared.get` is only used *inside* an accessor to read a field; the
/// result is either a Copy value (`Method`, `String`, `Option String`) or a
/// fresh `Shared` handle. `Ctx` never hands out a borrowed view.

use init::copy {Copy}
use init::shared {Shared, Shared.get}
use http::types {Body, Headers, Method, Request, Uri}
use lib::session {SessionHandle}

/// The session middleware's presence in the context.
pub type SessionSlot {
  absent,
  present (handle : SessionHandle)
}

pub struct Ctx {
  method : Method,
  path : String,
  headers : Shared Headers,
  body : Shared Body,
  params : Shared (List (Pair String String)),
  session : Shared SessionSlot
}

/// Every field is Copy, so duplicating the record duplicates only handles.
pub instance Copy Ctx {
  def copy (c : Ctx) : Pair Ctx Ctx := Pair.pair c c
}

// ── construction ────────────────────────────────────────────────────────

def Ctx.uri_path (u : Uri) : String :=
  match u {
    Uri.uri _ _ _ _ p _ _ => p
  }

/// Build a context from an owned request. The path is the request's own
/// path; `Ctx.with_route` overrides it for a mounted sub-router.
pub def Ctx.make (req : Request) (session : Shared SessionSlot) : Ctx :=
  match req {
    { method, uri, headers, body, .. } =>
      let path := Ctx.uri_path uri in
      let c : Ctx :=
        { method := method, path := path, headers := Shared.of headers,
          body := Shared.of body, params := Shared.of List.empty,
          session := session } in
      c
  }

pub def Ctx.with_route (c : Ctx) (path : String)
    (params : List (Pair String String)) : Ctx :=
  let c2 : Ctx :=
    { method := c.method, path := path, headers := c.headers, body := c.body,
      params := Shared.of params, session := c.session } in
  c2

pub def Ctx.with_session (c : Ctx) (session : Shared SessionSlot) : Ctx :=
  let c2 : Ctx :=
    { method := c.method, path := c.path, headers := c.headers, body := c.body,
      params := c.params, session := session } in
  c2

// ── accessors ────────────────────────────────────────────────────────────

pub def Ctx.method (c : Ctx) : Method := c.method

pub def Ctx.path (c : Ctx) : String := c.path

pub def Ctx.headers (c : Ctx) : Shared Headers := c.headers

pub def Ctx.body (c : Ctx) : Shared Body := c.body

pub def Ctx.params (c : Ctx) : Shared (List (Pair String String)) := c.params

pub def Ctx.session (c : Ctx) : Shared SessionSlot := c.session

/// The installed session handle, if session middleware ran. A fresh
/// `Shared` handle is made from the matched view (re-wrapping a view is
/// explicitly allowed; returning the raw view is not).
pub def Ctx.session_handle (c : Ctx) : Option (Shared SessionHandle) :=
  match Shared.get c.session {
    SessionSlot.absent => Option.none,
    SessionSlot.present h => Option.some (Shared.of h)
  }

/// `SessionSlot.handle` for a slot handle.
pub def SessionSlot.handle (s : Shared SessionSlot) : Option (Shared SessionHandle) :=
  match Shared.get s {
    SessionSlot.absent => Option.none,
    SessionSlot.present h => Option.some (Shared.of h)
  }

// ── header / param lookup over shared lists ─────────────────────────────

#[terminating]
def Ctx.header_pairs (name : String)
    (pairs : Shared (List (Pair String String))) : Option String :=
  match Shared.get pairs {
    List.empty => Option.none,
    List.cons p rest =>
      match p {
        Pair.pair k v =>
          if String.beq (String.to_lowercase k) (String.to_lowercase name)
          then Option.some v
          else Ctx.header_pairs name (Shared.of rest)
      }
  }

/// Case-insensitive header lookup from the context.
pub def Ctx.header (name : String) (c : Ctx) : Option String :=
  match Shared.get c.headers {
    Headers.headers pairs => Ctx.header_pairs name (Shared.of pairs)
  }

#[terminating]
def Ctx.param_pairs (name : String)
    (pairs : Shared (List (Pair String String))) : Option String :=
  match Shared.get pairs {
    List.empty => Option.none,
    List.cons p rest =>
      match p {
        Pair.pair k v =>
          if String.beq k name
          then Option.some v
          else Ctx.param_pairs name (Shared.of rest)
      }
  }

/// Path parameter lookup (the transformer router stores them here).
pub def Ctx.param (name : String) (c : Ctx) : Option String :=
  Ctx.param_pairs name c.params

// ── body projection ─────────────────────────────────────────────────────

#[terminating]
def Ctx.copy_bytes (xs : Shared (List U8)) : List U8 :=
  match Shared.get xs {
    List.empty => List.empty,
    List.cons b rest => List.cons b (Ctx.copy_bytes (Shared.of rest))
  }

/// The request body as bytes. `bytes`/`text` are copied once; `form` and
/// `stream` are not projected here (a stream view cannot be moved out).
pub def Ctx.body_bytes (c : Ctx) : List U8 :=
  match Shared.get c.body {
    Body.empty => List.empty,
    Body.text s => String.to_list s,
    Body.bytes data => Ctx.copy_bytes (Shared.of data),
    Body.form _ => List.empty,
    Body.stream _ => List.empty
  }

pub def Ctx.body_text (c : Ctx) : Option String :=
  match Shared.get c.body {
    Body.text s => Option.some s,
    Body.empty => Option.none,
    Body.bytes _ => Option.none,
    Body.form _ => Option.none,
    Body.stream _ => Option.none
  }
