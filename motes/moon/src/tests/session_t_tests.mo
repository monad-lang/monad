/// Session middleware over `HandlerT`: the handle is installed into the
/// context, committed after the handler, and loadable on the next request.

use init::borrow {Borrow, Borrow.get}
use std::test {}
use http::cookie {SameSite}
use http::strings {Strings.split_on}
use http::body {Body.to_bytes_pure}
use http::types {
  Headers, Headers.add, Headers.get, Request, Request.get, Response,
  Response.ok_text, Uri,
}
use moon::context {SessionSlot, SessionSlot.handle}
use moon::handler_t {
  HandlerT, HandlerT.lift_io, HandlerT.pure_io, HandlerT.run_io,
  HandlerT.session_io, HandlerT.throw_io, HttpError, HttpError.make,
}
use moon::session {
  Session, Session.get, SessionConfig, SessionConfig.default, SessionHandle,
  SessionHandle.get, SessionHandle.put, SessionStore, SessionStore.new,
  SessionStore.new_with,
}
use moon::session_mw {SessionStore.with_session_t}

def get_req (path : String) : Request :=
  Request.get (Uri.uri "" Option.none "" Option.none path Option.none Option.none)

def with_header (name : String) (value : String) (req : Request) : Request :=
  match req {
    { method, uri, headers, version, body, params } =>
      let req2 : Request :=
        { method := method, uri := uri,
          headers := Headers.add name value headers,
          version := version, body := body, params := params } in
      req2
  }

def set_session_value (handle : Borrow SessionHandle) : HandlerT IO Response := do {
  let h : SessionHandle := Borrow.get handle;
  let _u : Unit <- HandlerT.lift_io (SessionHandle.put h "k" "v");
  HandlerT.pure_io (Response.ok_text "ok")
}

def set_value : HandlerT IO Response := do {
  let slot : Borrow SessionSlot <- HandlerT.session_io;
  let slot_value : SessionSlot := Borrow.get slot;
  match SessionSlot.handle slot_value {
    Option.some handle => set_session_value handle,
    Option.none => HandlerT.throw_io (HttpError.make 500u16 "no session")
  }
}

def read_session_value (handle : Borrow SessionHandle) : HandlerT IO Response := do {
  let h : SessionHandle := Borrow.get handle;
  let s : Session <- HandlerT.lift_io (SessionHandle.get h);
  match Session.get s "k" {
    Option.some v => HandlerT.pure_io (Response.ok_text v),
    Option.none => HandlerT.throw_io (HttpError.make 500u16 "missing key")
  }
}

def read_value : HandlerT IO Response := do {
  let slot : Borrow SessionSlot <- HandlerT.session_io;
  let slot_value : SessionSlot := Borrow.get slot;
  match SessionSlot.handle slot_value {
    Option.some handle => read_session_value handle,
    Option.none => HandlerT.throw_io (HttpError.make 500u16 "no session")
  }
}

def first_cookie_part (set_cookie : String) : String :=
  match Strings.split_on ";" set_cookie {
    List.cons p _ => String.trim p,
    List.empty => ""
  }

#[test]
def test_with_session_t_sets_cookie : IO Bool := do {
  let st : SessionStore <- SessionStore.new "sid" 3600i64;
  let r <- HandlerT.run_io (SessionStore.with_session_t st set_value) (get_req "/");
  match r {
    Result.ok res =>
      IO.pure (match Headers.get "Set-Cookie" res.headers {
        Option.some v => String.starts_with "sid=" v,
        Option.none => false
      }),
    Result.err _ => IO.pure false
  }
}

def load_after_cookie (st : SessionStore) (cookie : String) : IO Bool := do {
  let req2 := with_header "Cookie" cookie (get_req "/");
  let second <- HandlerT.run_io (SessionStore.with_session_t st read_value) req2;
  match second {
    Result.ok res2 =>
      IO.pure (String.beq (String.from_list (Body.to_bytes_pure res2.body)) "v"),
    Result.err _ => IO.pure false
  }
}

#[test]
def test_session_roundtrip_through_context : IO Bool := do {
  let st : SessionStore <- SessionStore.new "sid" 3600i64;
  let first <- HandlerT.run_io (SessionStore.with_session_t st set_value) (get_req "/");
  match first {
    Result.err _ => IO.pure false,
    Result.ok res =>
      match Headers.get "Set-Cookie" res.headers {
        Option.none => IO.pure false,
        Option.some set_cookie => load_after_cookie st (first_cookie_part set_cookie)
      }
  }
}

// ── explicit session policy ─────────────────────────────────────────────

#[test]
def test_session_secure_cookie : IO Bool := do {
  let cfg := SessionConfig.default "sid" 3600i64;
  let cfg2 : SessionConfig := { cfg with secure := true };
  let st_res <- SessionStore.new_with cfg2;
  match st_res {
    Result.err _ => IO.pure false,
    Result.ok st => do {
      let r <- HandlerT.run_io (SessionStore.with_session_t st set_value) (get_req "/");
      match r {
        Result.ok res =>
          IO.pure (match Headers.get "Set-Cookie" res.headers {
            Option.some v =>
              Bool.and (String.contains v "Secure") (String.contains v "SameSite=Lax"),
            Option.none => false
          }),
        Result.err _ => IO.pure false
      }
    }
  }
}

#[test]
def test_same_site_none_requires_secure : IO Bool := do {
  let cfg := SessionConfig.default "sid" 3600i64;
  let cfg2 : SessionConfig := { cfg with same_site := SameSite.none };
  let r <- SessionStore.new_with cfg2;
  match r {
    Result.err _ => IO.pure true,
    Result.ok _ => IO.pure false
  }
}

#[test]
def test_same_site_none_with_secure_ok : IO Bool := do {
  let cfg := SessionConfig.default "sid" 3600i64;
  let cfg2 : SessionConfig := { cfg with same_site := SameSite.none, secure := true };
  let r <- SessionStore.new_with cfg2;
  match r {
    Result.ok _ => IO.pure true,
    Result.err _ => IO.pure false
  }
}
