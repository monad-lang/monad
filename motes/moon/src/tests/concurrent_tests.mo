/// Phase 7 tests — concurrent server fiber dispatch.
///
/// Tests verify that the fiber-per-request API works: fork a handler fiber,
/// await it, and the response is correct.
///
/// `forkIO` is eager, not lazy — it starts the handler immediately — but the
/// tests still use the sequential interleaved TCP pattern of the server tests,
/// one connection at a time, so every fork/await pair stays deterministic.

use std::concurrent::fiber {Fiber, await_fiber}
use moon::server {
  Server.drain_fibers, Server.handle_connection_fiber, Server.read_message,
}
use std::stream {Stream, FdStream}
use http::types {Transport, Transport.read_bytes, Transport.write_bytes, GET, Request, Response, Status.ok, Uri, uri}
use http::wire {Wire.format_request, Wire.frame_response, Wire.parse_response}
use http::body {Body.to_bytes_pure}
use http::uri {Uri.parse}

// ── socket bytes ────────────────────────────────────────────────────────

/// One read of at most `max` bytes, as a list (`Transport.read_bytes`
/// over a bare socket).
def tcp_read_bytes (sock : FdStream) (max : I64) : IO (Result String (List U8)) :=
  let t : Transport := Transport.plain sock in
  Transport.read_bytes t max

/// Write all of `bytes` (`Transport.write_bytes` over a bare socket).
def tcp_write_bytes (sock : FdStream) (bytes : List U8) : IO (Result String U64) :=
  let t : Transport := Transport.plain sock in
  Transport.write_bytes t bytes

// ── test infrastructure ─────────────────────────────────────────────────

/// Build a loopback URL for a given port.
def url_for (port : U16) : String :=
  String.concat (String.concat "http://127.0.0.1:" (U16.to_string port)) "/"

/// Parse a URL to `Uri`, returning a root-URI on parse error.
def uri_of (url : String) : Uri :=
  match Uri.parse url {
    Result.err _ => Uri.uri "" Option.none "" Option.none "/" Option.none Option.none,
    Result.ok u => u
  }

/// Make a GET request for a loopback URL.
def get_req (port : U16) : Request :=
  Request.get (uri_of (url_for port))

/// Check a response: status matches and body text matches.
def resp_ok (resp : Result String Response) (want_status : U16) (want_body : String) : Bool :=
  match resp {
    Result.ok r => Bool.and (U16.beq r.status want_status) (String.beq (String.from_list (Body.to_bytes_pure r.body)) want_body),
    Result.err _ => false
  }

/// Request bytes for a test. Serialising a test request cannot fail -- none of
/// them carries a `Body.stream` -- so an error here is a bug in the test, and
/// it goes out as a malformed request line, which shows up as a 400 rather
/// than as a test that hangs waiting for a response that cannot come.
def client_req_bytes (req : Request) : List U8 :=
  match Wire.format_request req {
    Result.ok bytes => bytes,
    Result.err _ => String.to_list "SERIALIZE-FAILED\r\n\r\n"
  }

/// Client writes a raw request to a socket.
def client_write (sock : FdStream) (req : Request) : IO Unit := do {
  tcp_write_bytes sock (client_req_bytes req);
  return unit
}

/// Read one response from a socket. Framed by `Content-Length` rather than
/// read-to-close, so the connection stays usable for a second request.
def client_read (sock : FdStream) : IO (Result String Response) :=
  Monad.bind (Server.read_message (fn bytes => Wire.frame_response bytes Method.GET) sock List.empty) (fn msg_res =>
    match msg_res {
      Result.err e => return (Result.err e),
      Result.ok msg =>
        match msg {
          Option.none => return (Result.err "connection closed before a response"),
          Option.some pr =>
            match pr {
              Pair.pair bytes _rest => return (Wire.parse_response bytes)
            }
        }
    })

/// Handler that returns 200 "hello".
def hello_handler (_ : Request) : IO Response :=
  return (Response.ok_text "hello")

/// Handler that returns 200 "fiber".
def fiber_handler (_ : Request) : IO Response :=
  return (Response.ok_text "fiber")

// ── tests ──────────────────────────────────────────────────────────────

/// Fork + await a single connection: equivalent to handle_connection
/// but exercises the fiber API.
#[test]
def test_fork_await_single : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res <- IO.tcp_connect "127.0.0.1" port;
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok client_sock => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Stream.close client_sock; return false },
            Result.ok server_sock => do {
              client_write client_sock (get_req port);
              // Fork the handler as a fiber (deferred).
              let fiber <- Server.handle_connection_fiber hello_handler server_sock;
              // Await the fiber (runs the handler synchronously).
              await_fiber fiber;
              let resp <- client_read client_sock;
              Stream.close client_sock;
              return (resp_ok resp Status.ok "hello")
            }
          }
        }
      }
    }
  }
}

/// Fork two connections, drain both: verify both responses are correct.
#[test]
def test_fork_drain_two : IO Bool := do {
  let l1_res <- IO.tcp_listen 0u16;
  match l1_res {
    Result.err _ => return false,
    Result.ok l1 => do {
      let p1 <- IO.tcp_local_port l1;
      let c1_res <- IO.tcp_connect "127.0.0.1" p1;
      match c1_res {
        Result.err _ => do { Stream.close l1; return false },
        Result.ok client1 => do {
          let a1_res <- IO.tcp_accept l1;
          Stream.close l1;
          match a1_res {
            Result.err _ => do { Stream.close client1; return false },
            Result.ok server1 => do {
              let l2_res <- IO.tcp_listen 0u16;
              match l2_res {
                Result.err _ => do { Stream.close client1; return false },
                Result.ok l2 => do {
                  let p2 <- IO.tcp_local_port l2;
                  let c2_res <- IO.tcp_connect "127.0.0.1" p2;
                  match c2_res {
                    Result.err _ => do { Stream.close l2; Stream.close client1; return false },
                    Result.ok client2 => do {
                      let a2_res <- IO.tcp_accept l2;
                      Stream.close l2;
                      match a2_res {
                        Result.err _ => do { Stream.close client1; Stream.close client2; return false },
                        Result.ok server2 => do {
                          // Client 1 writes, fork handler 1 (deferred).
                          client_write client1 (get_req p1);
                          let f1 <- Server.handle_connection_fiber hello_handler server1;
                          // Client 2 writes, fork handler 2 (deferred).
                          client_write client2 (get_req p2);
                          let f2 <- Server.handle_connection_fiber fiber_handler server2;
                          // Drain both fibers (runs handlers synchronously).
                          Server.drain_fibers (List.cons f1 (List.cons f2 List.empty));
                          // Read both responses.
                          let resp1 <- client_read client1;
                          let resp2 <- client_read client2;
                          Stream.close client1;
                          Stream.close client2;
                          return (Bool.and (resp_ok resp1 Status.ok "hello") (resp_ok resp2 Status.ok "fiber"))
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

/// drain_fibers on an empty list is a no-op.
#[test]
def test_drain_empty : IO Bool := do {
  Server.drain_fibers (List.empty : List (Fiber Unit));
  return true
}
