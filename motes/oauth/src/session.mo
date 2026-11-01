/// OAuth's own authentication session store.
///
/// Server-side sessions keyed by a CSPRNG id (`Random.token CryptoRandom.new
/// 32`), carried in an `HttpOnly` cookie; when `secure` is set the name is
/// `__Host-oauth_session` (no Domain, Path=/, Secure) and a matching
/// `__Host-oauth_csrf` cookie carries a CSRF token derived as
/// `base64url(HMAC-SHA256(secret, session.id))`. The CSRF cookie is readable
/// by the page (not HttpOnly); handlers require the value again in the
/// `X-CSRF-Token` header and compare with `Ct.eq`.
///
/// Sessions carry an idle and an absolute TTL, are swept on every create and
/// on an expired lookup, and are capped at `max_sessions`. Session ids rotate
/// on login and refresh (the old id is removed), and `destroy` removes the
/// entry; the cookie is only a pointer, so there are no tokens in cookies.

use std::list {List.filter}
use std::map {BTreeMap}
use std::base64 {B64Url.encode}
use std::ref {Ref, Ref.get, Ref.new, Ref.update}
use std::random {Random.token}
use crypto::ct {Ct.eq}
use crypto::hmac {Hmac.sha256}
use crypto::random {CryptoRandom.new}
use http::types {
  Headers.add, Headers.get, Request, Response, Response.json,
  Response.with_header, Status.unauthorized,
}
use http::cookie {Cookie.parse_headers, Cookie.set_cookie, Cookie.clear, CookieAttrs, SameSite}
use json::json {Json}
use jsonwebtoken::principal {Principal}
use lib::errors {AuthError, OauthError}
use lib::token {OauthTokenSet}

pub struct AuthSession {
  id : String,
  subject : String,
  issuer : String,
  access_expires_at : I64,
  refresh_token : Option String,
  created_at : I64,
  last_seen_at : I64,
  data : BTreeMap String Json
}

pub struct OauthSessionStore {
  sessions : Ref (List AuthSession),
  /// Base names; `secure` prepends `__Host-` at use time.
  cookie_name : String,
  csrf_cookie_name : String,
  absolute_ttl : I64,
  idle_ttl : I64,
  secure : Bool,
  max_sessions : I64,
  csrf_secret : String
}

// ── construction ───────────────────────────────────────────────────────────

/// The production constructor: a process-local CSPRNG secret for the CSRF
/// MAC. Sessions do not survive a restart, so the secret need not.
pub def OauthSessionStore.new
  (absolute_ttl : I64) (idle_ttl : I64) (secure : Bool)
  : IO (Result OauthError OauthSessionStore) := do {
  let r <- Random.token CryptoRandom.new 32;
  match r {
    Result.err _ => return (Result.err OauthError.rng_failed),
    Result.ok secret => do {
      let st <- OauthSessionStore.new_with_secret secret absolute_ttl idle_ttl secure;
      return (Result.ok st)
    }
  }
}

/// The deterministic seam used by tests (and by an application that manages
/// the CSRF secret itself). The secret must be at least 32 bytes; `new`
/// generates a CSPRNG one.
pub def OauthSessionStore.new_with_secret
  (secret : String) (absolute_ttl : I64) (idle_ttl : I64) (secure : Bool)
  : IO OauthSessionStore := do {
  let empty : List AuthSession := List.empty;
  let cell <- Ref.new empty;
  let out : OauthSessionStore := {
    sessions := cell,
    cookie_name := "oauth_session",
    csrf_cookie_name := "oauth_csrf",
    absolute_ttl := absolute_ttl,
    idle_ttl := idle_ttl,
    secure := secure,
    max_sessions := 1024i64,
    csrf_secret := secret
  };
  return out
}

// ── cookies and CSRF ───────────────────────────────────────────────────────

pub def OauthSessionStore.session_name (st : OauthSessionStore) : String :=
  if st.secure then "__Host-oauth_session" else st.cookie_name

pub def OauthSessionStore.csrf_name (st : OauthSessionStore) : String :=
  if st.secure then "__Host-oauth_csrf" else st.csrf_cookie_name

def OauthSessionStore.session_attrs (st : OauthSessionStore) : CookieAttrs := {
  path := "/",
  max_age := Option.none,
  http_only := true,
  secure := st.secure,
  same_site := SameSite.lax
}

def OauthSessionStore.csrf_attrs (st : OauthSessionStore) : CookieAttrs := {
  path := "/",
  max_age := Option.none,
  http_only := false,
  secure := st.secure,
  same_site := SameSite.lax
}

/// `base64url(HMAC-SHA256(secret, session.id))`.
pub def OauthSessionStore.csrf_token
  (st : OauthSessionStore) (s : AuthSession)
  : String :=
  B64Url.encode
    (Hmac.sha256 (String.to_list st.csrf_secret) (String.to_list s.id))

/// Constant-time comparison of the `X-CSRF-Token` header with the derived
/// token.
pub def OauthSessionStore.check_csrf
  (st : OauthSessionStore) (s : AuthSession) (req : Request)
  : Bool :=
  match Headers.get "X-CSRF-Token" req.headers {
    Option.none => false,
    Option.some got =>
      Ct.eq (String.to_list got) (String.to_list (OauthSessionStore.csrf_token st s))
  }

pub def OauthSessionStore.session_cookie
  (st : OauthSessionStore) (s : AuthSession)
  : Pair String String :=
  Cookie.set_cookie (OauthSessionStore.session_name st) s.id
    (OauthSessionStore.session_attrs st)

pub def OauthSessionStore.csrf_cookie
  (st : OauthSessionStore) (s : AuthSession)
  : Pair String String :=
  Cookie.set_cookie (OauthSessionStore.csrf_name st)
    (OauthSessionStore.csrf_token st s) (OauthSessionStore.csrf_attrs st)

/// The browser-binding cookie for a pending authorization: the callback must
/// present the same value as its `state` parameter, so an attacker-initiated
/// callback URL cannot be replayed into another browser (login CSRF).
pub def OauthSessionStore.login_state_name (st : OauthSessionStore) : String :=
  if st.secure then "__Host-oauth_state" else "oauth_state"

def OauthSessionStore.login_state_attrs (st : OauthSessionStore) : CookieAttrs := {
  path := "/",
  max_age := Option.some 600i64,
  http_only := true,
  secure := st.secure,
  same_site := SameSite.lax
}

pub def OauthSessionStore.login_cookie
  (st : OauthSessionStore) (state : String)
  : Pair String String :=
  Cookie.set_cookie (OauthSessionStore.login_state_name st) state
    (OauthSessionStore.login_state_attrs st)

pub def OauthSessionStore.clear_login_cookie
  (st : OauthSessionStore)
  : Pair String String :=
  Cookie.clear (OauthSessionStore.login_state_name st)
    (OauthSessionStore.login_state_attrs st)

pub def OauthSessionStore.login_state
  (st : OauthSessionStore) (req : Request)
  : Option String :=
  OauthSessionStore.single_cookie (OauthSessionStore.login_state_name st) req

pub def OauthSessionStore.clear_cookies
  (st : OauthSessionStore)
  : List (Pair String String) := [
  Cookie.clear (OauthSessionStore.session_name st) (OauthSessionStore.session_attrs st),
  Cookie.clear (OauthSessionStore.csrf_name st) (OauthSessionStore.csrf_attrs st)
]

def OauthSessionStore.add_cookie
  (pair : Pair String String) (res : Response)
  : Response :=
  match pair {
    Pair.pair k v => { res with headers := Headers.add k v res.headers }
  }

def OauthSessionStore.add_cookies
  (pairs : List (Pair String String)) (res : Response)
  : Response :=
  match pairs {
    List.empty => res,
    List.cons p rest => OauthSessionStore.add_cookies rest (OauthSessionStore.add_cookie p res)
  }

/// The 401 for a missing/duplicate/expired session, clearing both cookies.
pub def OauthSessionStore.unauthorized (st : OauthSessionStore) : Response :=
  let res := Response.with_header "Referrer-Policy" "no-referrer"
    (Response.with_header "Cache-Control" "no-store"
      (Response.json Status.unauthorized "{\"error\":\"unauthorized\"}")) in
  OauthSessionStore.add_cookies (OauthSessionStore.clear_cookies st) res

// ── lookup ─────────────────────────────────────────────────────────────────

#[terminating]
def OauthSessionStore.cookie_matches
  (name : String) (cookies : List (Pair String String))
  : List String :=
  match cookies {
    List.empty => List.empty,
    List.cons c rest =>
      match c {
        Pair.pair k v =>
          if k == name
          then List.cons v (OauthSessionStore.cookie_matches name rest)
          else OauthSessionStore.cookie_matches name rest
      }
  }

/// Exactly one non-empty value for `name`, or `Option.none`: duplicates are
/// rejected rather than guessed at.
def OauthSessionStore.single_cookie
  (name : String) (req : Request)
  : Option String :=
  let values := OauthSessionStore.cookie_matches name
    (Cookie.parse_headers req.headers) in
  match values {
    List.cons one rest =>
      match rest {
        List.empty =>
          if String.is_empty one then Option.none else Option.some one,
        List.cons _ _ => Option.none
      },
    List.empty => Option.none
  }

def OauthSessionStore.session_id
  (st : OauthSessionStore) (req : Request)
  : Option String :=
  OauthSessionStore.single_cookie (OauthSessionStore.session_name st) req

#[terminating]
def OauthSessionStore.find
  (sessions : List AuthSession) (id : String)
  : Option AuthSession :=
  match sessions {
    List.empty => Option.none,
    List.cons s rest =>
      if s.id == id then Option.some s else OauthSessionStore.find rest id
  }

def OauthSessionStore.expired
  (st : OauthSessionStore) (s : AuthSession) (now : I64)
  : Bool :=
  I64.gt (I64.sub now s.created_at) st.absolute_ttl
    || I64.gt (I64.sub now s.last_seen_at) st.idle_ttl

def OauthSessionStore.prune
  (st : OauthSessionStore) (sessions : List AuthSession) (now : I64)
  : List AuthSession :=
  List.filter (fn (s : AuthSession) => Bool.not (OauthSessionStore.expired st s now))
    sessions

/// Look up the request's session. An expired entry is dropped; a live one is
/// touched. A duplicate session cookie is treated as no session. `now` is
/// epoch seconds. The table is a list: lookup and touch are O(sessions).
pub def OauthSessionStore.lookup
  (st : OauthSessionStore) (req : Request) (now : I64)
  : IO (Option AuthSession) := do {
  let sessions <- Ref.get st.sessions;
  match OauthSessionStore.session_id st req {
    Option.none => return Option.none,
    Option.some id =>
      match OauthSessionStore.find sessions id {
        Option.none => return Option.none,
        Option.some s =>
          if OauthSessionStore.expired st s now
          then do {
            let _ <- Ref.update st.sessions
              (fn (xs : List AuthSession) => OauthSessionStore.prune st xs now);
            return Option.none
          }
          else do {
            let _ <- Ref.update st.sessions
              (fn (xs : List AuthSession) => OauthSessionStore.touch xs id now);
            return (Option.some s)
          }
      }
  }
}

#[terminating]
def OauthSessionStore.touch
  (sessions : List AuthSession) (id : String) (now : I64)
  : List AuthSession :=
  match sessions {
    List.empty => List.empty,
    List.cons s rest =>
      if s.id == id
      then
        let updated : AuthSession := { s with last_seen_at := now } in
        List.cons updated rest
      else List.cons s (OauthSessionStore.touch rest id now)
  }

pub def OauthSessionStore.with_session
  (st : OauthSessionStore)
  (handler : AuthSession -> Request -> IO (Result String Response))
  (req : Request)
  : IO (Result String Response) := do {
  let ms <- IO.current_time;
  let now := I64.div ms 1000i64;
  let found <- OauthSessionStore.lookup st req now;
  match found {
    Option.none => return (Result.ok (OauthSessionStore.unauthorized st)),
    Option.some s => handler s req
  }
}

// ── mutation ───────────────────────────────────────────────────────────────

def OauthSessionStore.without_id
  (sessions : List AuthSession) (id : String)
  : List AuthSession :=
  List.filter (fn (s : AuthSession) => Bool.not (s.id == id)) sessions

#[terminating]
def OauthSessionStore.take
  (n : I64) (sessions : List AuthSession)
  : List AuthSession :=
  if I64.lt n 1i64
  then List.empty
  else match sessions {
    List.empty => List.empty,
    List.cons s rest => List.cons s (OauthSessionStore.take (I64.sub n 1i64) rest)
  }

def OauthSessionStore.cap
  (st : OauthSessionStore) (sessions : List AuthSession)
  : List AuthSession :=
  OauthSessionStore.take st.max_sessions sessions

def OauthSessionStore.expiry_of (now : I64) (tokens : OauthTokenSet) : I64 :=
  match tokens.expires_in {
    Option.none => I64.add now 300i64,
    Option.some n => I64.add now n
  }

/// `now` is epoch seconds (the same unit as `AuthSession`'s timestamps).
def OauthSessionStore.create_with_id
  (st : OauthSessionStore) (id : String) (principal : Principal)
  (tokens : OauthTokenSet) (now : I64)
  : IO AuthSession := do {
  let expires_at : I64 := OauthSessionStore.expiry_of now tokens;
  let data : BTreeMap String Json := BTreeMap.empty;
  let s : AuthSession := {
    id := id,
    subject := principal.subject,
    issuer := principal.issuer,
    access_expires_at := expires_at,
    refresh_token := tokens.refresh_token,
    created_at := now,
    last_seen_at := now,
    data := data
  };
  let _ <- Ref.update st.sessions (fn (xs : List AuthSession) =>
    let live := OauthSessionStore.prune st xs now in
    OauthSessionStore.cap st
      (List.cons s (OauthSessionStore.without_id live id)));
  return s
}

/// A fresh CSPRNG session id.
pub def OauthSessionStore.new_id : IO (Result AuthError String) := do {
  let r <- Random.token CryptoRandom.new 32;
  match r {
    Result.err _ => return (Result.err AuthError.auth_server_misconfigured),
    Result.ok id => return (Result.ok id)
  }
}

/// Create a session with a fresh CSPRNG id. `now` is epoch seconds.
pub def OauthSessionStore.create
  (st : OauthSessionStore) (principal : Principal)
  (tokens : OauthTokenSet) (now : I64)
  : IO (Result AuthError AuthSession) := do {
  let r <- OauthSessionStore.new_id;
  match r {
    Result.err e => return (Result.err e),
    Result.ok id => do {
      let s <- OauthSessionStore.create_with_id st id principal tokens now;
      return (Result.ok s)
    }
  }
}

/// Rotate the session id (login, refresh, privilege change) and return the
/// renewed session. The old id is removed, so a captured cookie is dead.
pub def OauthSessionStore.rotate
  (st : OauthSessionStore) (s : AuthSession)
  : IO (Result AuthError AuthSession) := do {
  let ms <- IO.current_time;
  OauthSessionStore.rotate_at st s (I64.div ms 1000i64)
}

/// Rotate the id AND replace the token set (refresh/logout flows).
def OauthSessionStore.rotate_with_id_tokens
  (st : OauthSessionStore) (s : AuthSession) (id : String)
  (tokens : OauthTokenSet) (now : I64)
  : IO AuthSession := do {
  // RFC 6749 §6 lets a refresh response omit `refresh_token`, meaning the old
  // one stays valid; never replace it with nothing.
  let next_refresh : Option String :=
    match tokens.refresh_token {
      Option.none => s.refresh_token,
      Option.some t => Option.some t
    };
  let rotated : AuthSession := {
    s with
    id := id,
    last_seen_at := now,
    refresh_token := next_refresh,
    access_expires_at := OauthSessionStore.expiry_of now tokens
  };
  let _ <- Ref.update st.sessions (fn (xs : List AuthSession) =>
    OauthSessionStore.cap st
      (List.cons rotated (OauthSessionStore.without_id xs s.id)));
  return rotated
}

pub def OauthSessionStore.rotate_with_tokens
  (st : OauthSessionStore) (s : AuthSession)
  (tokens : OauthTokenSet) (now : I64)
  : IO (Result AuthError AuthSession) := do {
  let r <- OauthSessionStore.new_id;
  match r {
    Result.err e => return (Result.err e),
    Result.ok id => do {
      let rotated <- OauthSessionStore.rotate_with_id_tokens st s id tokens now;
      return (Result.ok rotated)
    }
  }
}

/// The deterministic rotation seam: replace `s`'s id with `id`.
def OauthSessionStore.rotate_with_id
  (st : OauthSessionStore) (s : AuthSession) (id : String) (now : I64)
  : IO AuthSession := do {
  let rotated : AuthSession := { s with id := id, last_seen_at := now };
  let _ <- Ref.update st.sessions (fn (xs : List AuthSession) =>
    OauthSessionStore.cap st
      (List.cons rotated (OauthSessionStore.without_id xs s.id)));
  return rotated
}

/// `now` is epoch seconds.
def OauthSessionStore.rotate_at
  (st : OauthSessionStore) (s : AuthSession) (now : I64)
  : IO (Result AuthError AuthSession) := do {
  let r <- Random.token CryptoRandom.new 32;
  match r {
    Result.err _ => return (Result.err AuthError.auth_server_misconfigured),
    Result.ok id => do {
      let rotated <- OauthSessionStore.rotate_with_id st s id now;
      return (Result.ok rotated)
    }
  }
}

pub def OauthSessionStore.destroy
  (st : OauthSessionStore) (req : Request)
  : IO Unit := do {
  match OauthSessionStore.session_id st req {
    Option.none => return unit,
    Option.some id => do {
      let _ <- Ref.update st.sessions
        (fn (xs : List AuthSession) => OauthSessionStore.without_id xs id);
      return unit
    }
  }
}
