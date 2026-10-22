/// HTTP router — `moon` mote, Layer 0 (pure).
///
/// Path-pattern matching with `:param` capture, method dispatch, and
/// prefix-mounted sub-routers. No framework state — the router is a pure
/// function from `List Route` + `Request` to `IO Response`.
///
/// Pattern syntax:
///   `/users/:id`     — captures the segment as `params` ("id", value)
///   `/users/:id/*`   — wildcard matches any remaining path (no capture)
///   `/health`        — exact match, no params
///
/// Unmatched routes fall through to a 404 response.

use http::types {
  Headers.empty, Method, Request, Response, Status.not_found, Uri, http1_1, text,
}
use http::strings {
  Strings.list_drop_prefix, Strings.list_starts_with, Strings.split_on,
}

// ── Route type ──────────────────────────────────────────────────────────

/// A route matches a method + path pattern with `:param` captures.
pub struct Route {
  method : Method,
  pattern : String,
  handler : Request -> IO Response
}

// ── path splitting ──────────────────────────────────────────────────────

/// Split a path on `/`, dropping a leading slash. E.g. `/users/:id` →
/// `["users", ":id"]`.
def Router.split_path (path : String) : List String :=
  Router.split_path_go (Strings.split_on "/" path)

/// Filter the split result: drop empty leading segments (from leading `/`
/// or `//`), keep the rest.
#[terminating]
def Router.split_path_go (parts : List String) : List String :=
  match parts {
    List.empty => List.empty,
    List.cons head rest =>
      if String.is_empty head
      then Router.split_path_go rest
      else List.cons head (Router.split_path_go rest)
  }

// ── path matching ───────────────────────────────────────────────────────

/// Match a pattern against a request path. Returns `Option.none` on
/// mismatch, `Option.some params` on match (list of captured `:param`
/// name-value pairs).
def Router.match_path (pattern : String) (path : String) : Option (List (Pair String String)) :=
  Router.match_segments (Router.split_path pattern) (Router.split_path path)

/// Match pattern segments against path segments.
#[terminating]
def Router.match_segments (pat : List String) (path : List String) : Option (List (Pair String String)) :=
  match pat {
    List.empty =>
      match path {
        List.empty => Option.some List.empty,
        List.cons _ _ => Option.none
      },
    List.cons ph pt =>
      if String.beq ph "*"
      then
        match pt {
          List.empty => Option.some List.empty,
          List.cons _ _ => Option.none
        }
      else Router.match_param_or_literal ph pt path
  }

/// Check if the pattern segment is a `:param` capture or a literal.
#[terminating]
def Router.match_param_or_literal (ph : String) (pt : List String) (path : List String) : Option (List (Pair String String)) :=
  match Router.is_param ph {
    Option.none => Router.match_literal ph pt path,
    Option.some pname => Router.match_param pname pt path
  }

/// Match a literal segment: must equal the path segment exactly.
#[terminating]
def Router.match_literal (ph : String) (pt : List String) (path : List String) : Option (List (Pair String String)) :=
  match path {
    List.empty => Option.none,
    List.cons seg rest =>
      if String.beq ph seg
      then Router.match_segments pt rest
      else Option.none
  }

/// Match a `:param` segment: captures the value and continues.
#[terminating]
def Router.match_param (pname : String) (pt : List String) (path : List String) : Option (List (Pair String String)) :=
  match path {
    List.empty => Option.none,
    List.cons seg rest =>
      match Router.match_segments pt rest {
        Option.none => Option.none,
        Option.some sub_params => Option.some (List.cons (Pair.pair pname seg) sub_params)
      }
  }

/// If a segment starts with `:`, return the param name (without `:`).
/// Otherwise return none.
def Router.is_param (seg : String) : Option String :=
  match String.to_list seg {
    List.empty => Option.none,
    List.cons colon rest =>
      if U8.beq colon 58u8
      then Option.some (String.from_list rest)
      else Option.none
  }

// ── method dispatch ─────────────────────────────────────────────────────

/// The main entry point: try each route in order. The first route whose
/// method matches and whose pattern matches the request path wins.
/// On match, the captured params are attached to the request before
/// calling the handler. On no match, return 404.
pub def Router.route (routes : List Route) (req : Request) : IO Response :=
  Router.try_routes routes req

/// Try routes one by one. First match wins.
#[terminating]
def Router.try_routes (routes : List Route) (req : Request) : IO Response :=
  match routes {
    List.empty => Router.not_found,
    List.cons r rest =>
      if Router.route_matches r req
      then Router.dispatch_route r req
      else Router.try_routes rest req
  }

/// A route matches if the method matches and the pattern matches the path.
def Router.route_matches (r : Route) (req : Request) : Bool :=
  Bool.and (BEq.beq r.method req.method) (Router.match_path_ok r.pattern req.uri.path)

/// Did `match_path` return `some`?
def Router.match_path_ok (pattern : String) (path : String) : Bool :=
  match Router.match_path pattern path {
    Option.none => false,
    Option.some _ => true
  }

/// Dispatch to the route's handler with params attached to the request.
def Router.dispatch_route (r : Route) (req : Request) : IO Response :=
  match Router.match_path r.pattern req.uri.path {
    Option.none => Router.not_found,
    Option.some params => r.handler { req with params := params }
  }

/// Default 404 response when no route matches.
def Router.not_found : IO Response :=
  return ({ status := Status.not_found, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text "Not Found" } : Response)

// ── sub-router / prefix mounting ───────────────────────────────────────

/// Mount a sub-router at a prefix. Strips the prefix from the request path
/// before dispatching to the sub-routes. If the request path doesn't start
/// with the prefix, returns 404.
pub def Router.mount (prefix : String) (sub_routes : List Route) (req : Request) : IO Response :=
  match Router.strip_prefix prefix req.uri.path {
    Option.none => Router.not_found,
    Option.some sub_path => Router.mount_dispatch sub_routes req sub_path
  }

/// Dispatch to sub-routes with the prefix stripped from the request path.
def Router.mount_dispatch (sub_routes : List Route) (req : Request) (sub_path : String) : IO Response :=
  let sub_req : Request := Router.req_with_path req sub_path in
  Router.route sub_routes sub_req

/// Build a copy of `req` with the path replaced (Uri is a type, not struct,
/// so we reconstruct it field by field).
def Router.req_with_path (req : Request) (path : String) : Request :=
  match req.uri {
    Uri.uri scheme userinfo host port _ query fragment =>
      { req with uri := Uri.uri scheme userinfo host port path query fragment }
  }

/// Strip a prefix from a path. Returns `none` if the path doesn't start
/// with the prefix. Ensures prefix ends with `/` for clean stripping.
def Router.strip_prefix (prefix : String) (path : String) : Option String :=
  let pfx := Router.ensure_trailing_slash prefix in
  if Strings.list_starts_with (String.to_list pfx) (String.to_list path)
  then Option.some (String.from_list (Strings.list_drop_prefix (String.to_list pfx) (String.to_list path)))
  else Option.none

/// Ensure a prefix ends with `/`.
def Router.ensure_trailing_slash (s : String) : String :=
  match String.to_list s {
    List.empty => "/",
    List.cons _ rest =>
      match List.reverse (String.to_list s) {
        List.empty => s,
        List.cons last _ =>
          if U8.beq last 47u8
          then s
          else String.concat s "/"
      }
  }

// ── convenience route constructors ─────────────────────────────────────

pub def Router.get (pattern : String) (handler : Request -> IO Response) : Route :=
  { method := Method.GET, pattern := pattern, handler := handler }

pub def Router.post (pattern : String) (handler : Request -> IO Response) : Route :=
  { method := Method.POST, pattern := pattern, handler := handler }

pub def Router.put (pattern : String) (handler : Request -> IO Response) : Route :=
  { method := Method.PUT, pattern := pattern, handler := handler }

pub def Router.delete (pattern : String) (handler : Request -> IO Response) : Route :=
  { method := Method.DELETE, pattern := pattern, handler := handler }

pub def Router.patch (pattern : String) (handler : Request -> IO Response) : Route :=
  { method := Method.PATCH, pattern := pattern, handler := handler }

// ── param lookup ───────────────────────────────────────────────────────

/// Look up a path parameter by name from a request's `params` list.
pub def Router.param (name : String) (req : Request) : Option String :=
  Router.param_lookup name req.params

#[terminating]
def Router.param_lookup (name : String) (params : List (Pair String String)) : Option String :=
  match params {
    List.empty => Option.none,
    List.cons head rest =>
      match head {
        Pair.pair k v =>
          if String.beq k name
          then Option.some v
          else Router.param_lookup name rest
      }
  }
