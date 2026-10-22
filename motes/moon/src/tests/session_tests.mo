/// Session store tests: round-trip, expiry, rotation, destroy, and the
/// handle-based middleware commit.

use http::cookie {Cookie.lookup, Cookie.parse}
use http::types {
  Body, Headers, Headers.empty, Headers.get, Headers.set, Method, Request,
  Response.ok_text, Uri, http1_1,
}
use moon::session {
  Session.get, Session.put, SessionHandle, SessionHandle.put,
  SessionStore.begin, SessionStore.commit, SessionStore.destroy, SessionStore.load,
  SessionStore.middleware, SessionStore.new, SessionStore.rotate,
  SessionStore.with_session,
}

def get_req : Request :=
  let req : Request :=
    { method := Method.GET, uri := Uri.uri "" Option.none "" Option.none "/" Option.none Option.none,
      headers := Headers.empty, version := HttpVersion.http1_1, body := Body.empty } in
  req

def req_with_session (name : String) (id : String) : Request :=
  let hs := Headers.set "Cookie" (String.concat name (String.concat "=" id)) Headers.empty in
  let req : Request :=
    { method := Method.GET, uri := Uri.uri "" Option.none "" Option.none "/" Option.none Option.none,
      headers := hs, version := HttpVersion.http1_1, body := Body.empty } in
  req

def cookie_id (name : String) (set_cookie : String) : Option String :=
  Cookie.lookup name (Cookie.parse (Option.some set_cookie))

#[test]
def test_roundtrip : IO Bool := do {
  let st <- SessionStore.new "sid" 3600i64;
  let s <- SessionStore.begin st;
  let s2 := Session.put s "user" "alice";
  let _ <- SessionStore.commit st s2;
  let loaded <- SessionStore.load st (req_with_session "sid" s2.id);
  match loaded {
    Option.none => return false,
    Option.some got =>
      match Session.get got "user" {
        Option.some v => return (String.beq v "alice"),
        Option.none => return false
      }
  }
}

#[test]
def test_expired_session_is_not_loaded : IO Bool := do {
  let st <- SessionStore.new "sid" (-1i64);
  let s <- SessionStore.begin st;
  let _ <- SessionStore.commit st s;
  let loaded <- SessionStore.load st (req_with_session "sid" s.id);
  match loaded {
    Option.none => return true,
    Option.some _ => return false
  }
}

#[test]
def test_rotate_changes_id : IO Bool := do {
  let st <- SessionStore.new "sid" 3600i64;
  let s <- SessionStore.begin st;
  let rotated <- SessionStore.rotate st s;
  return (Bool.not (String.beq rotated.id s.id))
}

#[test]
def test_destroy_clears_session : IO Bool := do {
  let st <- SessionStore.new "sid" 3600i64;
  let s <- SessionStore.begin st;
  let _ <- SessionStore.commit st s;
  let _ <- SessionStore.destroy st (req_with_session "sid" s.id);
  let loaded <- SessionStore.load st (req_with_session "sid" s.id);
  match loaded {
    Option.none => return true,
    Option.some _ => return false
  }
}

#[test]
def test_with_session_commits_handle : IO Bool := do {
  let st <- SessionStore.new "sid" 3600i64;
  let handler := fn (h : SessionHandle) (_ : Request) => do {
    SessionHandle.put h "user" "alice";
    return (Result.ok (Response.ok_text "ok"))
  };
  let r <- SessionStore.with_session st handler get_req;
  match r {
    Result.err _ => return false,
    Result.ok res =>
      match Headers.get "Set-Cookie" res.headers {
        Option.none => return false,
        Option.some sc =>
          match cookie_id "sid" sc {
            Option.none => return false,
            Option.some id => do {
              let loaded <- SessionStore.load st (req_with_session "sid" id);
              match loaded {
                Option.none => return false,
                Option.some got =>
                  match Session.get got "user" {
                    Option.some v => return (String.beq v "alice"),
                    Option.none => return false
                  }
              }
            }
          }
      }
  }
}

#[test]
def test_middleware_sets_cookie : IO Bool := do {
  let st <- SessionStore.new "sid" 3600i64;
  let handler := fn (_ : Request) => IO.pure (Result.ok (Response.ok_text "ok"));
  let r <- SessionStore.middleware st handler get_req;
  match r {
    Result.err _ => return false,
    Result.ok res =>
      match Headers.get "Set-Cookie" res.headers {
        Option.some _ => return true,
        Option.none => return false
      }
  }
}
