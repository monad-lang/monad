/// Phase 6 tests — HTTP/1.1 sequential server roundtrips.
///
/// Tests use a sequential interleaved TCP pattern (no concurrency needed):
///   listen → connect → accept →
///   client writes request → Server.handle_connection reads+dispatches+writes → client reads.
/// The OS TCP buffer holds data between writes and reads, so each step
/// completes before the next starts.

use std::process {process_id}
use moon::server {
  Server.handle_connection, Server.header_has_token, Server.keep_alive,
  Server.read_message, Server.read_request, Server.serve_connection,
  Server.static, Server.with_connection_header,
}
use std::stream {Stream, FdStream}
use http::types {
  Transport, Transport.read_bytes, Transport.write_bytes,
  GET, Headers, Headers.empty, Headers.get, Headers.set, POST, Request, Response,
  Status.bad_request, Status.not_found, Status.ok, Uri, empty, http1_0, http1_1,
  text,
}
use http::strings {Strings.drop_bytes}
use http::wire {
  Wire.format_request, Wire.frame_response, Wire.parse_response,
  Wire.take_bytes,
}
use http::body {Body.from_text, Body.to_bytes_pure}
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

/// Make a POST request with a text body for a loopback URL.
def post_req (port : U16) (body : String) : Request :=
  { method := Method.POST, uri := uri_of (url_for port), headers := Headers.empty, version := HttpVersion.http1_1, body := Body.from_text body }

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

/// Read one response from a socket.
///
/// Framed, not read-to-close: this server always declares a `Content-Length`,
/// so the message ends where that length says and a kept-alive connection can
/// be read once more afterwards. `Wire.frame_response` is the same framing
/// rule the server reads requests with, run in the other direction.
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

/// Build a request with a bare path (no scheme/host).
def static_req (path : String) : Request :=
  Request.get (Uri.uri "" Option.none "" Option.none path Option.none Option.none)

/// Handler that always returns 200 "hello".
def hello_handler (_ : Request) : IO Response :=
  return (Response.ok_text "hello")

/// Handler that echoes the request body as text.
def echo_handler (req : Request) : IO Response :=
  return (Response.ok_text (String.from_list (Body.to_bytes_pure req.body)))

/// Handler that returns 404.
def not_found_handler (_ : Request) : IO Response :=
  return ({ status := Status.not_found, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.text "Not Found" } : Response)

/// Handler that returns the Host header value as the body.
def host_handler (req : Request) : IO Response :=
  match Headers.get "Host" req.headers {
    Option.some h => return (Response.ok_text (String.concat "host:" h)),
    Option.none => return (Response.ok_text "no-host")
  }

// ── tests ──────────────────────────────────────────────────────────────

/// Simple GET: client writes request, server responds 200 "hello".
#[test]
def test_serve_simple : IO Bool := do {
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
              Server.handle_connection hello_handler server_sock;
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

/// POST echo: server echoes the request body back as text.
#[test]
def test_serve_post_echo : IO Bool := do {
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
              client_write client_sock (post_req port "echo-me");
              Server.handle_connection echo_handler server_sock;
              let resp <- client_read client_sock;
              Stream.close client_sock;
              return (resp_ok resp Status.ok "echo-me")
            }
          }
        }
      }
    }
  }
}

/// 404 response: handler returns 404, client reads it.
#[test]
def test_serve_404 : IO Bool := do {
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
              Server.handle_connection not_found_handler server_sock;
              let resp <- client_read client_sock;
              Stream.close client_sock;
              return (resp_ok resp Status.not_found "Not Found")
            }
          }
        }
      }
    }
  }
}

/// Bad request: client writes garbage, server responds 400.
#[test]
def test_serve_bad_request : IO Bool := do {
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
              // Write garbage with CRLFCRLF so server finds header boundary
              // but fails to parse the request line as a valid method.
              tcp_write_bytes client_sock (String.to_list "GARBAGE\r\n\r\n");
              Server.handle_connection hello_handler server_sock;
              let resp <- client_read client_sock;
              Stream.close client_sock;
              return (resp_ok resp Status.bad_request "Bad Request")
            }
          }
        }
      }
    }
  }
}

/// Host header: handler inspects Host, client verifies response body.
#[test]
def test_serve_with_headers : IO Bool := do {
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
              let req : Request := { method := Method.GET, uri := uri_of (url_for port), headers := Headers.set "Host" (String.concat "127.0.0.1:" (U16.to_string port)) Headers.empty, version := HttpVersion.http1_1, body := Body.empty };
              client_write client_sock req;
              Server.handle_connection host_handler server_sock;
              let resp <- client_read client_sock;
              Stream.close client_sock;
              let want := String.concat "host:127.0.0.1:" (U16.to_string port);
              return (resp_ok resp Status.ok want)
            }
          }
        }
      }
    }
  }
}

/// Static file serving: write a temp file, serve it, verify 200 + content.
/// Also test missing file returns 404.
#[test]
def test_static_file : IO Bool := do {
  // Process-scoped: `/tmp` is shared with every sibling worktree, so a fixed
  // name lets two concurrent runs write over each other's fixture.
  let path := String.concat "/tmp/moon_test_static_" (String.concat (I64.to_string process_id) ".txt");
  let wrote <- IO.write_file_native path "static content";
  let res_ok : Response <- Server.static "" (static_req path);
  let res_404 : Response <- Server.static "" (static_req (String.concat path "_missing"));
  return (Result.is_ok wrote && Bool.and
    (Bool.and (U16.beq res_ok.status Status.ok) (String.beq (String.from_list (Body.to_bytes_pure res_ok.body)) "static content"))
    (U16.beq res_404.status Status.not_found))
}

// ── keep-alive ─────────────────────────────────────────────────────────

/// A GET request that asks the server to close after this response.
def close_get_req (port : U16) : Request :=
  { method := Method.GET, uri := uri_of (url_for port), headers := Headers.set "Connection" "close" Headers.empty, version := HttpVersion.http1_1, body := Body.empty }

/// A GET request in HTTP/1.0, with `Connection` set to `token` if given.
def http10_req (token : Option String) : Request :=
  let hdrs : Headers :=
    match token {
      Option.some t => Headers.set "Connection" t Headers.empty,
      Option.none => Headers.empty
    } in
  { method := Method.GET, uri := uri_of (url_for 0u16), headers := hdrs, version := HttpVersion.http1_0, body := Body.empty }

/// HTTP/1.1 keeps the connection when the peer says nothing.
#[test]
def test_keep_alive_http11_default : Bool :=
  Server.keep_alive (get_req 0u16) 1

/// An explicit `Connection: close` wins over the version default.
#[test]
def test_keep_alive_connection_close : Bool :=
  Bool.not (Server.keep_alive (close_get_req 0u16) 1)

/// HTTP/1.0 closes unless the peer asks, and honours the ask.
#[test]
def test_keep_alive_http10 : Bool :=
  Bool.and
    (Bool.not (Server.keep_alive (http10_req Option.none) 1))
    (Server.keep_alive (http10_req (Option.some "keep-alive")) 1)

/// The request cap closes a connection even when the peer wants it open: a
/// client that never says `close` must not hold one forever.
#[test]
def test_keep_alive_request_cap : Bool :=
  Bool.and
    (Server.keep_alive (get_req 0u16) 99)
    (Bool.not (Server.keep_alive (get_req 0u16) 100))

/// Header values are matched case-insensitively, and a value's surrounding
/// whitespace does not hide the token.
#[test]
def test_header_has_token_case_insensitive : Bool :=
  Server.header_has_token "connection" "close" (Headers.set "Connection" " CLOSE " Headers.empty)

/// A response that ends the connection says so; one that does not stays
/// silent, since `Connection: close` is the only signal the peer gets -- a
/// body framed without a `Content-Length` ends where the connection ends.
#[test]
def test_connection_header_says_close : Bool :=
  let closing : Response := Server.with_connection_header true (Response.ok_text "x") in
  let open_res : Response := Server.with_connection_header false (Response.ok_text "x") in
  Bool.and
    (match Headers.get "connection" closing.headers {
      Option.some v => String.beq v "close",
      Option.none => false
    })
    (match Headers.get "connection" open_res.headers {
      Option.some _ => false,
      Option.none => true
    })

/// True when the response carries `Connection: close`.
def resp_says_close (resp : Response) : Bool :=
  match Headers.get "connection" resp.headers {
    Option.some v => String.beq v "close",
    Option.none => false
  }

/// True when the response is a 200 whose body is `hello`.
def resp_hello (resp : Response) : Bool :=
  Bool.and
    (U16.beq resp.status Status.ok)
    (String.beq (String.from_list (Body.to_bytes_pure resp.body)) "hello")

/// The first response in a list, if there is one. The list is matched inside a
/// def whose parameter type is declared, so `List.cons` cannot be confused
/// with `Vec.cons`.
def first_response (responses : List Response) : Option Response :=
  match responses {
    List.cons r _ => Option.some r,
    List.empty => Option.none
  }

/// The second response in a list, if there is one.
def second_response (responses : List Response) : Option Response :=
  match responses {
    List.cons _ rest =>
      match rest {
        List.cons r _ => Option.some r,
        List.empty => Option.none
      },
    List.empty => Option.none
  }

/// Read `want` responses that came back to back on one connection.
///
/// Buffered once and framed repeatedly rather than one read per response: two
/// responses written in a row routinely arrive in a single read, and the
/// framing -- not the read boundary -- is what separates them.
#[terminating]
def client_read_n (sock : FdStream) (want : I64) (got_n : I64) (acc : List U8) (got : List Response) : IO (Result String (List Response)) := do {
  if I64.beq want got_n
  then return (Result.ok got)
  else do {
    let frame : Result String (Option I64) := Wire.frame_response acc Method.GET;
    match frame {
      Result.err e => return (Result.err e),
      Result.ok opt =>
        match opt {
          Option.some n =>
            match Wire.parse_response (Wire.take_bytes n acc) {
              Result.err e => return (Result.err e),
              Result.ok res => client_read_n sock want (I64.add got_n 1) (Strings.drop_bytes n acc) (List.append got (List.cons res List.empty))
            },
          Option.none => do {
            let read_res <- tcp_read_bytes sock 4096;
            match read_res {
              Result.err e => return (Result.err e),
              Result.ok chunk =>
                if List.is_empty chunk
                then return (Result.err "connection closed before every response arrived")
                else client_read_n sock want got_n (List.append acc chunk) got
            }
          }
        }
    }
  }
}

/// Two requests in one write, served in order on one connection.
///
/// The second request is already in the socket buffer when the first is
/// served, so it can only come from the bytes the first read left over: a
/// server that re-read would block waiting for bytes already delivered, and
/// one that discarded the remainder would drop the request. The second request
/// asks for `Connection: close`, which is what ends the connection -- and the
/// response says so, which is the only way the client learns it.
#[test]
def test_serve_pipelined_requests : IO Bool := do {
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
              let both := String.concat
                (String.from_list (client_req_bytes (get_req port)))
                (String.from_list (client_req_bytes (close_get_req port)));
              tcp_write_bytes client_sock (String.to_list both);
              Server.serve_connection hello_handler server_sock List.empty 1;
              let resps <- client_read_n client_sock 2 0 List.empty List.empty;
              Stream.close client_sock;
              match resps {
                Result.err _ => return false,
                Result.ok l =>
                  match first_response l {
                    Option.some r1 =>
                      match second_response l {
                        Option.some r2 =>
                          return (Bool.and
                            (Bool.and (resp_hello r1) (Bool.not (resp_says_close r1)))
                            (Bool.and (resp_hello r2) (resp_says_close r2))),
                        Option.none => return false
                      },
                    Option.none => return false
                  }
              }
            }
          }
        }
      }
    }
  }
}

// ── truncation ─────────────────────────────────────────────────────────

/// True when a message read failed.
def read_failed (msg_res : Result String (Option (Pair (List U8) (List U8)))) : Bool :=
  match msg_res {
    Result.err _ => true,
    Result.ok _ => false
  }

/// True when a message read reported a clean end of the connection.
def read_clean_end (msg_res : Result String (Option (Pair (List U8) (List U8)))) : Bool :=
  match msg_res {
    Result.err _ => false,
    Result.ok msg =>
      match msg {
        Option.none => true,
        Option.some _ => false
      }
  }

/// A body cut off mid-message is an error, not a short body.
///
/// The read used to answer `ok` with however much had arrived when the peer
/// closed, so a request the client never finished sending was parsed as a
/// complete one. Nothing distinguishes the two at the parse step -- only the
/// reader knows the peer left -- so the reader is where it has to be caught.
#[test]
def test_read_truncated_body_fails : IO Bool := do {
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
              // `Content-Length: 5`, two bytes of body, then the peer is gone.
              tcp_write_bytes client_sock (String.to_list "POST / HTTP/1.1\r\nContent-Length: 5\r\n\r\nab");
              Stream.close client_sock;
              let msg_res <- Server.read_request server_sock List.empty;
              Stream.close server_sock;
              return (read_failed msg_res)
            }
          }
        }
      }
    }
  }
}

/// A peer that closes between messages ends the connection cleanly: nothing
/// was in flight, so there is nothing to be truncated. This is the case a
/// keep-alive server sees every time a client is done.
#[test]
def test_read_closed_connection_is_clean : IO Bool := do {
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
              Stream.close client_sock;
              let msg_res <- Server.read_request server_sock List.empty;
              Stream.close server_sock;
              return (read_clean_end msg_res)
            }
          }
        }
      }
    }
  }
}
