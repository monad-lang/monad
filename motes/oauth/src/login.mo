/// Login, callback, refresh, and logout handlers.
///
/// The handlers have Moon's canonical type `Request -> IO (Result String
/// Response)` without importing Moon, so an application registers them with
/// its router. Client errors (bad/expired state, provider error, a rejected
/// ID token, a bad CSRF token) are `Ok` 400/401/403 pages; an unexpected
/// failure is `Err`, which the application's recover middleware turns into a
/// 500.
///
/// The application supplies a JWT-mode `BearerValidator` for ID-token
/// validation (it carries the JWKS cache), the one-time `OauthStateStore`,
/// and the `OauthSessionStore`. `Login.with_userinfo` additionally requires
/// the userinfo `sub` to match the ID token's subject.

use http::types {
  Headers, Headers.add, Headers.empty, Headers.set, Request, Response,
  Response.json, Response.redirect, Response.with_header, Status.bad_gateway,
  Status.bad_request, Status.forbidden, Status.see_other, Uri,
}
use http::request {Request.param}
use http::uri {Uri.parse, Uri.parse_query, Uri.format, Uri.format_query, Uri.same_origin}
use json::json {Json, Json.get_object, Json.get_str, Json.object_get}
use jsonwebtoken::principal {Principal}
use lib::bearer {BearerValidator, BearerValidator.validate_id_token}
use lib::client {
  Client.append_query, Client.authorize_url, Client.exchange_code, Client.refresh,
  Client.userinfo,
}
use lib::config {OauthConfig}
use lib::discovery {OauthEndpoints}
use lib::errors {AuthError, AuthError.to_string, OauthError, OauthError.to_string}
use lib::http_client {OauthHttp}
use lib::session {
  AuthSession, OauthSessionStore, OauthSessionStore.add_cookie,
  OauthSessionStore.add_cookies, OauthSessionStore.clear_login_cookie,
  OauthSessionStore.check_csrf, OauthSessionStore.clear_cookies,
  OauthSessionStore.create_with_id, OauthSessionStore.csrf_cookie,
  OauthSessionStore.destroy, OauthSessionStore.login_cookie, OauthSessionStore.login_state,
  OauthSessionStore.lookup, OauthSessionStore.new_id,
  OauthSessionStore.rotate_with_id_tokens, OauthSessionStore.session_cookie,
  OauthSessionStore.unauthorized,
}
use lib::state {OauthStateStore, PendingAuth}
use lib::token {OauthTokenSet}

pub struct LoginDeps {
  config : OauthConfig,
  endpoints : OauthEndpoints,
  http : OauthHttp,
  states : OauthStateStore,
  sessions : OauthSessionStore,
  bearer : BearerValidator,
  /// Also require the userinfo endpoint's `sub` to equal the ID token's.
  check_userinfo : Bool,
  /// Session-id source; the CSPRNG in production, deterministic in tests.
  /// A thunk so constructing the deps never runs it.
  session_id : Unit -> IO (Result AuthError String)
}

pub def Login.deps
  (cfg : OauthConfig) (ep : OauthEndpoints) (states : OauthStateStore)
  (sessions : OauthSessionStore) (h : OauthHttp) (bearer : BearerValidator)
  : LoginDeps :=
  let d : LoginDeps := {
    config := cfg,
    endpoints := ep,
    http := h,
    states := states,
    sessions := sessions,
    bearer := bearer,
    check_userinfo := false,
    session_id := fn (_ : Unit) => OauthSessionStore.new_id
  } in
  d

pub def Login.with_userinfo (d : LoginDeps) : LoginDeps :=
  let out : LoginDeps := { d with check_userinfo := true } in
  out

def Login.with_session_id
  (d : LoginDeps) (gen : IO (Result AuthError String))
  : LoginDeps :=
  let out : LoginDeps := { d with session_id := fn (_ : Unit) => gen } in
  out

// ── query helpers ──────────────────────────────────────────────────────────

def Login.query (req : Request) : List (Pair String String) :=
  match req.uri {
    Uri.uri scheme userinfo host port path query fragment =>
      match query {
        Option.none => List.empty,
        Option.some q => Uri.parse_query q
      }
  }

// ── small responses ────────────────────────────────────────────────────────

def Login.redirect (target : String) : Response :=
  Response.with_header "Cache-Control" "no-store"
    (Response.redirect Status.see_other target)

def Login.bad_request : Response :=
  Response.with_header "Cache-Control" "no-store"
    (Response.json Status.bad_request "{\"error\":\"callback_failed\"}")

def Login.upstream_error : Response :=
  Response.with_header "Cache-Control" "no-store"
    (Response.json Status.bad_gateway "{\"error\":\"callback_failed\"}")

def Login.forbidden : Response :=
  Response.with_header "Cache-Control" "no-store"
    (Response.json Status.forbidden "{\"error\":\"invalid_request\"}")

/// Only a relative path (`/...`, not `//...`) or a same-origin absolute URL
/// is a safe `return_to`; anything else falls back to `/`.
pub def Login.safe_return_to
  (cfg : OauthConfig) (return_to : Option String)
  : String :=
  match return_to {
    Option.none => "/",
    Option.some target => Login.checked_target cfg target
  }

#[terminating]
def Login.has_control_bytes (bs : List U8) : Bool :=
  match bs {
    List.empty => false,
    List.cons b rest =>
      if U8.lt b 32u8 || U8.beq b 127u8
      then true
      else Login.has_control_bytes rest
  }

def Login.has_control (s : String) : Bool :=
  Login.has_control_bytes (String.to_list s)

def Login.checked_target (cfg : OauthConfig) (target : String) : String :=
  if String.is_empty target
  then "/"
  else if String.starts_with "//" target
  then "/"
  else if String.contains target "\\"
  then "/"
  else if Login.has_control target
  then "/"
  else if String.starts_with "/" target
  then target
  else match Uri.parse target {
    Result.err _ => "/",
    Result.ok u =>
      match Uri.parse cfg.redirect_uri {
        Result.err _ => "/",
        Result.ok app => if Uri.same_origin app u then target else "/"
      }
  }

// ── login ──────────────────────────────────────────────────────────────────

pub def Login.handle_login
  (d : LoginDeps) (req : Request)
  : IO (Result String Response) := do {
  let return_to := Request.param "return_to" (Login.query req);
  let started <- OauthStateStore.begin d.states d.config.redirect_uri return_to;
  match started {
    Result.err e => return (Result.err ("login: " ++ OauthError.to_string e)),
    Result.ok pending => do {
      let url := Client.authorize_url d.config d.endpoints pending;
      let res := OauthSessionStore.add_cookie
        (OauthSessionStore.login_cookie d.sessions pending.state)
        (Login.redirect url);
      return (Result.ok res)
    }
  }
}

/// The deterministic login seam: the caller supplies the three one-time
/// values and the state store's clock (milliseconds).
def Login.handle_login_with
  (d : LoginDeps) (req : Request)
  (state : String) (nonce : String) (verifier : String) (now_ms : I64)
  : IO (Result String Response) := do {
  let return_to := Request.param "return_to" (Login.query req);
  let started <- OauthStateStore.begin_at d.states now_ms state nonce verifier
    d.config.redirect_uri return_to;
  match started {
    Result.err e => return (Result.err ("login: " ++ OauthError.to_string e)),
    Result.ok pending => do {
      let url := Client.authorize_url d.config d.endpoints pending;
      let res := OauthSessionStore.add_cookie
        (OauthSessionStore.login_cookie d.sessions pending.state)
        (Login.redirect url);
      return (Result.ok res)
    }
  }
}

// ── callback ───────────────────────────────────────────────────────────────

pub def Login.handle_callback
  (d : LoginDeps) (req : Request)
  : IO (Result String Response) := do {
  let ms <- IO.current_time;
  Login.handle_callback_at d req (I64.div ms 1000i64)
}

/// The deterministic callback seam: `now` is epoch seconds.
def Login.handle_callback_at
  (d : LoginDeps) (req : Request) (now : I64)
  : IO (Result String Response) := do {
  let r <- Login.callback_flow d req now;
  return (Login.with_cleared_login_cookie d r)
}

def Login.with_cleared_login_cookie
  (d : LoginDeps) (r : Result String Response)
  : Result String Response :=
  match r {
    Result.ok res =>
      Result.ok
        (OauthSessionStore.add_cookie
          (OauthSessionStore.clear_login_cookie d.sessions) res),
    Result.err e => Result.err e
  }

def Login.callback_flow
  (d : LoginDeps) (req : Request) (now : I64)
  : IO (Result String Response) := do {
  let params := Login.query req;
  match Request.param "error" params {
    Option.some _ => return (Result.ok Login.bad_request),
    Option.none => Login.callback_state d req now params
  }
}

def Login.callback_state
  (d : LoginDeps) (req : Request) (now : I64)
  (params : List (Pair String String))
  : IO (Result String Response) := do {
  match Request.param "state" params {
    Option.none => return (Result.ok Login.bad_request),
    Option.some state =>
      match OauthSessionStore.login_state d.sessions req {
        Option.none => return (Result.ok Login.bad_request),
        Option.some cookie_state =>
          if Bool.not (cookie_state == state)
          then return (Result.ok Login.bad_request)
          else Login.callback_code d req now params state
      }
  }
}

def Login.callback_code
  (d : LoginDeps) (req : Request) (now : I64)
  (params : List (Pair String String)) (state : String)
  : IO (Result String Response) := do {
  match Request.param "code" params {
    Option.none => return (Result.ok Login.bad_request),
    Option.some code => Login.consume_state d req now state code
  }
}

def Login.consume_state
  (d : LoginDeps) (req : Request) (now : I64) (state : String) (code : String)
  : IO (Result String Response) := do {
  if I64.gt (String.length state) 4096i64 || I64.gt (String.length code) 4096i64
  then return (Result.ok Login.bad_request)
  else do {
    let pending <- OauthStateStore.take_at d.states
      (I64.mul now 1000i64) state d.config.redirect_uri;
    match pending {
      Option.none => return (Result.ok Login.bad_request),
      Option.some p => Login.exchange d req now p code
    }
  }
}

def Login.exchange
  (d : LoginDeps) (req : Request) (now : I64) (pending : PendingAuth) (code : String)
  : IO (Result String Response) := do {
  let tr <- Client.exchange_code d.http d.config d.endpoints code pending.verifier;
  match tr {
    Result.err _ => return (Result.ok Login.upstream_error),
    Result.ok tokens => Login.validate_tokens d req now pending tokens
  }
}

def Login.validate_tokens
  (d : LoginDeps) (req : Request) (now : I64) (pending : PendingAuth)
  (tokens : OauthTokenSet)
  : IO (Result String Response) := do {
  match tokens.id_token {
    Option.none => return (Result.ok Login.bad_request),
    Option.some id_token =>
      Login.check_id_token d req now pending tokens id_token
  }
}

def Login.check_id_token
  (d : LoginDeps) (req : Request) (now : I64) (pending : PendingAuth)
  (tokens : OauthTokenSet) (id_token : String)
  : IO (Result String Response) := do {
  let vr <- BearerValidator.validate_id_token d.bearer now pending.nonce id_token;
  match vr {
    Result.err e => Login.id_token_error d e,
    Result.ok principal => Login.after_identity d req now pending tokens principal
  }
}

/// An IdP/JWKS outage or a mode misconfiguration is 502; a rejected token is
/// 400.
def Login.id_token_error
  (d : LoginDeps) (e : AuthError)
  : IO (Result String Response) :=
  match e {
    AuthError.auth_temporarily_unavailable => return (Result.ok Login.upstream_error),
    AuthError.auth_server_misconfigured => return (Result.ok Login.upstream_error),
    _ => return (Result.ok Login.bad_request)
  }

def Login.after_identity
  (d : LoginDeps) (req : Request) (now : I64) (pending : PendingAuth)
  (tokens : OauthTokenSet) (principal : Principal)
  : IO (Result String Response) := do {
  if Bool.not d.check_userinfo
  then Login.start_session d req now pending tokens principal
  else match d.endpoints.userinfo {
    Option.none => return (Result.ok Login.upstream_error),
    Option.some _ => Login.fetch_userinfo d req now pending tokens principal
  }
}

def Login.userinfo_sub (j : Json) : Option String :=
  match Json.get_object j {
    Result.err _ => Option.none,
    Result.ok obj =>
      match Json.object_get "sub" obj {
        Option.none => Option.none,
        Option.some v =>
          match Json.get_str v {
            Result.err _ => Option.none,
            Result.ok s => if String.is_empty s then Option.none else Option.some s
          }
      }
  }

def Login.fetch_userinfo
  (d : LoginDeps) (req : Request) (now : I64) (pending : PendingAuth)
  (tokens : OauthTokenSet) (principal : Principal)
  : IO (Result String Response) := do {
  let ur <- Client.userinfo d.http d.endpoints tokens.access_token;
  match ur {
    Result.err _ => return (Result.ok Login.upstream_error),
    Result.ok j =>
      match Login.userinfo_sub j {
        Option.none => return (Result.ok Login.bad_request),
        Option.some sub =>
          if sub == principal.subject
          then Login.start_session d req now pending tokens principal
          else return (Result.ok Login.bad_request)
      }
  }
}

def Login.start_session
  (d : LoginDeps) (req : Request) (now : I64) (pending : PendingAuth)
  (tokens : OauthTokenSet) (principal : Principal)
  : IO (Result String Response) := do {
  let idr <- d.session_id unit;
  match idr {
    Result.err e => return (Result.err ("login: " ++ AuthError.to_string e)),
    Result.ok id => do {
      let s <- OauthSessionStore.create_with_id d.sessions id principal tokens now;
      let target := Login.safe_return_to d.config pending.return_to;
      let res := OauthSessionStore.add_cookies
        [OauthSessionStore.session_cookie d.sessions s,
         OauthSessionStore.csrf_cookie d.sessions s]
        (Response.with_header "Referrer-Policy" "no-referrer"
          (Login.redirect target));
      return (Result.ok res)
    }
  }
}

// ── refresh ────────────────────────────────────────────────────────────────

pub def Login.handle_refresh
  (d : LoginDeps) (req : Request)
  : IO (Result String Response) := do {
  let ms <- IO.current_time;
  Login.handle_refresh_at d req (I64.div ms 1000i64)
}

def Login.handle_refresh_at
  (d : LoginDeps) (req : Request) (now : I64)
  : IO (Result String Response) := do {
  let found <- OauthSessionStore.lookup d.sessions req now;
  match found {
    Option.none => return (Result.ok (OauthSessionStore.unauthorized d.sessions)),
    Option.some session =>
      if Bool.not (OauthSessionStore.check_csrf d.sessions session req)
      then return (Result.ok Login.forbidden)
      else match session.refresh_token {
        Option.none => return (Result.ok (OauthSessionStore.unauthorized d.sessions)),
        Option.some refresh => Login.do_refresh d req now session refresh
      }
  }
}

def Login.do_refresh
  (d : LoginDeps) (req : Request) (now : I64) (session : AuthSession)
  (refresh : String)
  : IO (Result String Response) := do {
  let tr <- Client.refresh d.http d.config d.endpoints refresh;
  match tr {
    Result.err e => Login.refresh_error d req e,
    Result.ok tokens => Login.rotate_session d req now session tokens
  }
}

/// A 400/401 from the token endpoint rejects the refresh token itself
/// (revoked/expired): destroy the session and answer 401. Only an outage or
/// a 5xx is 502.
def Login.refresh_error
  (d : LoginDeps) (req : Request) (e : OauthError)
  : IO (Result String Response) := do {
  match e {
    OauthError.token_status status =>
      if U16.beq status 400u16 || U16.beq status 401u16
      then do {
        let _ <- OauthSessionStore.destroy d.sessions req;
        return (Result.ok (OauthSessionStore.unauthorized d.sessions))
      }
      else return (Result.ok Login.upstream_error),
    _ => return (Result.ok Login.upstream_error)
  }
}

def Login.rotate_session
  (d : LoginDeps) (req : Request) (now : I64)
  (session : AuthSession) (tokens : OauthTokenSet)
  : IO (Result String Response) := do {
  let idr <- d.session_id unit;
  match idr {
    Result.err e => return (Result.err ("refresh: " ++ AuthError.to_string e)),
    Result.ok id => do {
      let rotated <- OauthSessionStore.rotate_with_id_tokens d.sessions session id tokens now;
      let target := Login.safe_return_to d.config Option.none;
      let res := OauthSessionStore.add_cookies
        [OauthSessionStore.session_cookie d.sessions rotated,
         OauthSessionStore.csrf_cookie d.sessions rotated]
        (Login.redirect target);
      return (Result.ok res)
    }
  }
}

// ── logout ─────────────────────────────────────────────────────────────────

pub def Login.handle_logout
  (d : LoginDeps) (req : Request)
  : IO (Result String Response) := do {
  let ms <- IO.current_time;
  Login.handle_logout_at d req (I64.div ms 1000i64)
}

def Login.handle_logout_at
  (d : LoginDeps) (req : Request) (now : I64)
  : IO (Result String Response) := do {
  let found <- OauthSessionStore.lookup d.sessions req now;
  match found {
    Option.none => return (Result.ok (Login.logged_out d)),
    Option.some session =>
      if Bool.not (OauthSessionStore.check_csrf d.sessions session req)
      then return (Result.ok Login.forbidden)
      else do {
        let _ <- OauthSessionStore.destroy d.sessions req;
        return (Result.ok (Login.logged_out d))
      }
  }
}

def Login.end_session_url (d : LoginDeps) (u : Uri) : String :=
  Client.append_query (Uri.format u)
    (Uri.format_query [Pair.pair "client_id" d.config.client_id])

def Login.logged_out (d : LoginDeps) : Response :=
  let target : String :=
    match d.endpoints.end_session {
      Option.none => "/",
      Option.some u => Login.end_session_url d u
    } in
  OauthSessionStore.add_cookies (OauthSessionStore.clear_cookies d.sessions)
    (Login.redirect target)
