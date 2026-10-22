/// Handler error-channel tests: the four adapters in `moon/handler.mo`.

use http::body {Body.to_bytes_pure}
use http::types {
  Headers.empty, Request, Request.get, Response, Status.internal_server_error,
  Uri, http1_1, text,
}
use moon::handler {
  Handler.map_error, Handler.of_response, Handler.recover, Handler.try,
}

/// A request the handlers ignore.
def dummy_req : Request :=
  Request.get (Uri.uri "" Option.none "" Option.none "/" Option.none Option.none)

def ok_handler (_ : Request) : IO Response :=
  return (Response.ok_text "ok")

def fail_handler (_ : Request) : IO (Result String Response) :=
  return (Result.err "boom")

def error_page (msg : String) : Response :=
  { status := Status.internal_server_error, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text msg }

def body_text (res : Response) : String :=
  String.from_list (Body.to_bytes_pure res.body)

#[test]
def test_of_response_lifts : IO Bool := do {
  let r <- Handler.of_response ok_handler dummy_req;
  match r {
    Result.ok res => return (String.beq (body_text res) "ok"),
    Result.err _ => return false
  }
}

#[test]
def test_recover_maps_err : IO Bool := do {
  let r <- Handler.recover error_page fail_handler dummy_req;
  match r {
    Result.ok res => return (Bool.and (U16.beq res.status Status.internal_server_error) (String.beq (body_text res) "boom")),
    Result.err _ => return false
  }
}

#[test]
def test_recover_passes_ok : IO Bool := do {
  let r <- Handler.recover error_page (Handler.of_response ok_handler) dummy_req;
  match r {
    Result.ok res => return (String.beq (body_text res) "ok"),
    Result.err _ => return false
  }
}

#[test]
def test_map_error_transforms_message : IO Bool := do {
  let r <- Handler.map_error (fn (m : String) => String.concat m "!") fail_handler dummy_req;
  match r {
    Result.ok _ => return false,
    Result.err msg => return (String.beq msg "boom!")
  }
}

#[test]
def test_try_returns_fallback_on_err : IO Bool := do {
  let res <- Handler.try (Response.ok_text "fallback") fail_handler dummy_req;
  return (String.beq (body_text res) "fallback")
}

#[test]
def test_try_returns_response_on_ok : IO Bool := do {
  let res <- Handler.try (Response.ok_text "fallback") (Handler.of_response ok_handler) dummy_req;
  return (String.beq (body_text res) "ok")
}
