/// The injectable HTTP transport.
///
/// Every identity-provider call goes through an `OauthHttp`: `real` uses
/// `motes/moose` and never follows a redirect, `fake` answers from a
/// scripted list so the whole client flow is testable with no socket.
///
/// The fake keeps its two scripts in two separate `Ref`s — one captured by
/// each closure. A single `Ref` shared by both would be a use-after-move
/// in an affine language, and a `Ref` is not `Copy`.
///
/// A scripted entry matches on the request path, and optionally on text
/// the request body must contain (`body_contains`, `""` meaning "no
/// constraint") — that is how two exchanges to `/token`
/// (`grant_type=authorization_code` and `grant_type=refresh_token`) are
/// told apart. A matched entry is consumed.

use http::types {
  Body, Headers, Headers.empty, HttpVersion, Request, Request.get, Response, Uri,
}
use http::body {Body.from_text, Body.to_bytes_pure}
use moose::client {Client.post, Client.request}
use std::ref {Ref, Ref.new, Ref.update}
use lib::errors {OauthError}

pub struct OauthHttp {
  get : Uri -> Headers -> IO (Result OauthError Response),
  post : Uri -> Headers -> Body -> IO (Result OauthError Response)
}

/// One canned response. `GET` and `POST` scripts are separate lists, so
/// there is no method field to get wrong.
pub struct ScriptedExchange {
  path : String,
  status : U16,
  body : String,
  headers : Headers := Headers.empty,
  body_contains : String := ""
}

// ── the real transport ───────────────────────────────────────────────────

/// The ONE transport wrap: moose reports text, and this is the only place
/// that text becomes an `OauthError`.
def OauthHttp.of_transport (r : Result String Response) : Result OauthError Response :=
  match r {
    Result.ok resp => Result.ok resp,
    Result.err msg => Result.err (OauthError.transport msg)
  }

/// A GET with ZERO redirects (`Client.request`, not `Client.get`, whose
/// ten-redirect policy would let a 3xx carry credentials or a body to a
/// different origin).
def OauthHttp.real_get (u : Uri) (hdrs : Headers) : IO (Result OauthError Response) := do {
  let base : Request := Request.get u;
  let req : Request := { base with headers := hdrs };
  let r <- Client.request req;
  return (OauthHttp.of_transport r)
}

/// `Client.post` also follows zero redirects.
def OauthHttp.real_post
  (u : Uri) (hdrs : Headers) (body : Body) : IO (Result OauthError Response) := do {
  let r <- Client.post u hdrs body;
  return (OauthHttp.of_transport r)
}

pub def OauthHttp.real : OauthHttp :=
  let h : OauthHttp := {
    get := OauthHttp.real_get,
    post := OauthHttp.real_post
  } in
  h

/// Call the record's own fields. Kept here so callers never depend on
/// field-call syntax for a function-typed field.
pub def OauthHttp.send_get
  (h : OauthHttp) (u : Uri) (hdrs : Headers) : IO (Result OauthError Response) :=
  match h {
    { get, .. } => get u hdrs
  }

pub def OauthHttp.send_post
  (h : OauthHttp) (u : Uri) (hdrs : Headers) (body : Body)
  : IO (Result OauthError Response) :=
  match h {
    { post, .. } => post u hdrs body
  }

// ── the scripted transport ───────────────────────────────────────────────

struct FakeCell {
  remaining : List ScriptedExchange,
  matched : Option Response
}

def OauthHttp.response_of (status : U16) (headers : Headers) (body : String) : Response :=
  let r : Response := {
    status := status,
    headers := headers,
    version := HttpVersion.http1_1,
    body := Body.from_text body
  } in
  r

def OauthHttp.exchange_of
  (path : String) (status : U16) (body : String) (headers : Headers) (body_contains : String)
  : ScriptedExchange :=
  let ex : ScriptedExchange := {
    path := path,
    status := status,
    body := body,
    headers := headers,
    body_contains := body_contains
  } in
  ex

def OauthHttp.cell_of (remaining : List ScriptedExchange) : FakeCell :=
  let c : FakeCell := { remaining := remaining, matched := Option.none } in
  c

def OauthHttp.exchange_matches
  (ex_path : String) (ex_needle : String) (want_path : String) (want_body : String)
  : Bool :=
  ex_path == want_path
    && (String.is_empty ex_needle || String.contains want_body ex_needle)

/// The first matching entry is REMOVED from the script and its response
/// returned; everything before it is kept in order.
#[terminating]
def OauthHttp.claim_scan
  (want_path : String) (want_body : String)
  (xs : List ScriptedExchange) (seen : List ScriptedExchange)
  : Pair (List ScriptedExchange) (Option Response) :=
  match xs {
    List.empty => Pair.pair (List.reverse seen) Option.none,
    List.cons ex rest =>
      match ex {
        { path, status, body, headers, body_contains, .. } =>
          if OauthHttp.exchange_matches path body_contains want_path want_body
          then Pair.pair
                 (List.append (List.reverse seen) rest)
                 (Option.some (OauthHttp.response_of status headers body))
          else OauthHttp.claim_scan want_path want_body rest
                 (List.cons (OauthHttp.exchange_of path status body headers body_contains) seen)
      }
  }

def OauthHttp.claim_pure (path : String) (body_text : String) (cell : FakeCell) : FakeCell :=
  match cell {
    { remaining, .. } =>
      match OauthHttp.claim_scan path body_text remaining List.empty {
        Pair.pair left found =>
          let out : FakeCell := { remaining := left, matched := found } in
          out
      }
  }

def OauthHttp.claim
  (cell : Ref FakeCell) (path : String) (body_text : String)
  : IO (Result OauthError Response) := do {
  let next <- Ref.update cell (OauthHttp.claim_pure path body_text);
  return (match next.matched {
    Option.some r => Result.ok r,
    Option.none => Result.err (OauthError.fake_no_response path),
  })
}

pub def OauthHttp.fake_get
  (cell : Ref FakeCell) (u : Uri) (hdrs : Headers)
  : IO (Result OauthError Response) :=
  OauthHttp.claim cell u.path ""

pub def OauthHttp.fake_post
  (cell : Ref FakeCell) (u : Uri) (hdrs : Headers) (body : Body)
  : IO (Result OauthError Response) :=
  OauthHttp.claim cell u.path (String.from_list (Body.to_bytes_pure body))

/// A transport answering from `gets`/`posts` in order. Each list is used
/// once and owned by one `Ref`.
pub def OauthHttp.fake
  (gets : List ScriptedExchange) (posts : List ScriptedExchange)
  : IO OauthHttp := do {
  let get_cell <- Ref.new (OauthHttp.cell_of gets);
  let post_cell <- Ref.new (OauthHttp.cell_of posts);
  let h : OauthHttp := {
    get := OauthHttp.fake_get get_cell,
    post := OauthHttp.fake_post post_cell
  };
  return h
}
