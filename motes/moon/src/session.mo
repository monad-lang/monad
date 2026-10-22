/// Server-side sessions on top of `Ref`.
///
/// A `SessionStore` is a `Ref (List Session)` — a bounded in-memory table.
/// IDs come from a SHA-256 of (nanoseconds, process id, counter); this is
/// NOT a cryptographic RNG, and the module says so. Use `rotate` after login
/// to avoid fixation. The store sweeps expired sessions on every commit.
///
/// `with_session` loads or creates the session, hands it to the handler, and
/// attaches the `Set-Cookie` on an `Ok` response. `middleware` is the
/// no-session-data variant: it ensures a cookie exists.

use std::io {IO.current_time_nano}
use std::process {process_id}
use std::ref {Ref, Ref.add_i64, Ref.get, Ref.new, Ref.set, Ref.update}
use std::sha256 {Sha256.hash}
use http::cookie {
  CookieAttrs, CookieAttrs.default, Cookie.clear, Cookie.lookup,
  Cookie.parse_headers, Cookie.set_cookie,
}
use http::types {Headers, Headers.add, Request, Response}

pub struct Session {
  id : String,
  data : List (Pair String String),
  expires_at : I64
}

pub struct SessionStore {
  sessions : Ref (List Session),
  counter : Ref I64,
  cookie_name : String,
  ttl_seconds : I64,
  secure : Bool,
  max_sessions : I64
}

pub def SessionStore.new (cookie_name : String) (ttl_seconds : I64) : IO SessionStore := do {
  let sessions : Ref (List Session) <- Ref.new List.empty;
  let counter : Ref I64 <- Ref.new 0i64;
  let st : SessionStore :=
    { sessions := sessions, counter := counter, cookie_name := cookie_name,
      ttl_seconds := ttl_seconds, secure := false, max_sessions := 1000 };
  return st
}

/// A fresh id. Documented as not a CSPRNG: it is unpredictable enough for a
/// local session table, not for a security-critical token.
pub def SessionStore.new_id (st : SessionStore) : IO String := do {
  let n <- Ref.add_i64 st.counter 1;
  let t <- IO.current_time_nano;
  return (Sha256.hash
    (String.concat (I64.to_string t)
      (String.concat ":"
        (String.concat (I64.to_string process_id)
          (String.concat ":" (I64.to_string n))))))
}

pub def SessionStore.begin (st : SessionStore) : IO Session := do {
  let id <- SessionStore.new_id st;
  let now <- IO.current_time_nano;
  let s : Session :=
    { id := id, data := List.empty,
      expires_at := I64.add now (I64.mul st.ttl_seconds 1000000000i64) };
  return s
}

// ── session data ────────────────────────────────────────────────────────

pub def Session.get (s : Session) (key : String) : Option String :=
  Session.lookup key s.data

#[terminating]
def Session.lookup (key : String) (data : List (Pair String String)) : Option String :=
  match data {
    List.empty => Option.none,
    List.cons head rest =>
      match head {
        Pair.pair k v => if String.beq k key then Option.some v else Session.lookup key rest
      }
  }

/// Replace `key`, preserving the other fields.
pub def Session.put (s : Session) (key : String) (value : String) : Session :=
  let data := List.cons (Pair.pair key value) (Session.remove_key key s.data) in
  { s with data := data }

#[terminating]
def Session.remove_key (key : String) (data : List (Pair String String)) : List (Pair String String) :=
  match data {
    List.empty => List.empty,
    List.cons head rest =>
      match head {
        Pair.pair k _ =>
          if String.beq k key then Session.remove_key key rest
          else List.cons head (Session.remove_key key rest)
      }
  }

// ── store ───────────────────────────────────────────────────────────────

pub def SessionStore.load (st : SessionStore) (req : Request) : IO (Option Session) := do {
  let cookies := Cookie.parse_headers req.headers;
  match Cookie.lookup st.cookie_name cookies {
    Option.none => return Option.none,
    Option.some id => do {
      let now <- IO.current_time_nano;
      let sessions <- Ref.get st.sessions;
      return (Session.find_live id now sessions)
    }
  }
}

#[terminating]
def Session.find_live (id : String) (now : I64) (sessions : List Session) : Option Session :=
  match sessions {
    List.empty => Option.none,
    List.cons s rest =>
      if String.beq s.id id
      then (if I64.lt now s.expires_at then Option.some s else Option.none)
      else Session.find_live id now rest
  }

/// Store the session (upsert), sweep expired entries, and return the
/// `Set-Cookie` pairs. Duplicate ids cannot exist: `upsert` removes the old
/// entry first.
pub def SessionStore.commit (st : SessionStore) (s : Session) : IO (List (Pair String String)) := do {
  let now <- IO.current_time_nano;
  let _ <- Ref.update st.sessions
    (fn (sessions : List Session) => Session.upsert s now st.max_sessions sessions);
  return (List.cons (Cookie.set_cookie st.cookie_name s.id (SessionStore.attrs st)) List.empty)
}

def SessionStore.attrs (st : SessionStore) : CookieAttrs :=
  let base := CookieAttrs.default in
  let attrs : CookieAttrs :=
    { base with secure := st.secure, max_age := Option.some st.ttl_seconds } in
  attrs

#[terminating]
def Session.upsert (s : Session) (now : I64) (max : I64) (sessions : List Session) : List Session :=
  let live := Session.sweep now sessions in
  let others := Session.remove_id s.id live in
  Session.take max (List.cons s others)

#[terminating]
def Session.sweep (now : I64) (sessions : List Session) : List Session :=
  match sessions {
    List.empty => List.empty,
    List.cons s rest =>
      if I64.lt now s.expires_at
      then List.cons s (Session.sweep now rest)
      else Session.sweep now rest
  }

#[terminating]
def Session.remove_id (id : String) (sessions : List Session) : List Session :=
  match sessions {
    List.empty => List.empty,
    List.cons s rest =>
      if String.beq s.id id
      then Session.remove_id id rest
      else List.cons s (Session.remove_id id rest)
  }

#[terminating]
def Session.take (n : I64) (sessions : List Session) : List Session :=
  if I64.lt n 1
  then List.empty
  else
    match sessions {
      List.empty => List.empty,
      List.cons s rest => List.cons s (Session.take (I64.sub n 1) rest)
    }

/// New id and a fresh expiry. Call after a successful login.
pub def SessionStore.rotate (st : SessionStore) (s : Session) : IO Session := do {
  let id <- SessionStore.new_id st;
  let now <- IO.current_time_nano;
  let rotated : Session :=
    { s with id := id, expires_at := I64.add now (I64.mul st.ttl_seconds 1000000000i64) };
  return rotated
}

/// Remove the request's session and return the clearing cookie.
pub def SessionStore.destroy (st : SessionStore) (req : Request) : IO (List (Pair String String)) := do {
  let cookies := Cookie.parse_headers req.headers;
  let found := Cookie.lookup st.cookie_name cookies;
  match found {
    Option.none => return (List.cons (Cookie.clear st.cookie_name (SessionStore.attrs st)) List.empty),
    Option.some id => do {
      let _ <- Ref.update st.sessions (fn (sessions : List Session) => Session.remove_id id sessions);
      return (List.cons (Cookie.clear st.cookie_name (SessionStore.attrs st)) List.empty)
    }
  }
}

// ── middleware ─────────────────────────────────────────────────────────

/// The handler's view of the session: a mutable slot. `put` edits it; the
/// middleware commits the final value on an `Ok` response.
pub struct SessionHandle {
  session : Ref Session
}

pub def SessionHandle.get (h : SessionHandle) : IO Session := Ref.get h.session

pub def SessionHandle.put (h : SessionHandle) (key : String) (value : String) : IO Unit := do {
  let s <- Ref.get h.session;
  Ref.set h.session (Session.put s key value)
}

/// Load or begin the session, hand the handler a mutable handle, then commit
/// the final value and attach `Set-Cookie` to a successful response. An
/// `Err` passes through without touching the store.
pub def SessionStore.with_session
    (st : SessionStore)
    (handler : SessionHandle -> Request -> IO (Result String Response))
    (req : Request)
    : IO (Result String Response) := do {
  let loaded <- SessionStore.load st req;
  let initial <- SessionStore.initial st loaded;
  let session_ref : Ref Session <- Ref.new initial;
  let handle : SessionHandle := { session := session_ref };
  let r <- handler handle req;
  match r {
    Result.err e => return (Result.err e),
    Result.ok res => do {
      let final <- Ref.get session_ref;
      let pairs <- SessionStore.commit st final;
      return (Result.ok (SessionStore.add_cookies res pairs))
    }
  }
}

def SessionStore.initial (st : SessionStore) (loaded : Option Session) : IO Session :=
  match loaded {
    Option.none => SessionStore.begin st,
    Option.some s => IO.pure s
  }

/// Ensure a session cookie exists without exposing the session to the
/// handler. Handlers that mutate session data use `with_session` instead.
pub def SessionStore.middleware
    (st : SessionStore)
    (handler : Request -> IO (Result String Response))
    (req : Request)
    : IO (Result String Response) :=
  SessionStore.with_session st (fn (_ : SessionHandle) (r : Request) => handler r) req

def SessionStore.add_cookies (res : Response) (pairs : List (Pair String String)) : Response :=
  let hs := SessionStore.add_cookie_pairs res.headers pairs in
  { res with headers := hs }

#[terminating]
def SessionStore.add_cookie_pairs (headers : Headers) (pairs : List (Pair String String)) : Headers :=
  match pairs {
    List.empty => headers,
    List.cons head rest =>
      match head {
        Pair.pair k v => SessionStore.add_cookie_pairs (Headers.add k v headers) rest
      }
  }
