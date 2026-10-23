/// Phase 5 tests — HTTP/1.1 client roundtrips.
///
/// Tests use a sequential interleaved TCP pattern (no concurrency needed):
///   listen → connect → accept →
///   client writes request → server reads+writes → client reads response.
/// The OS TCP buffer holds data between writes and reads, so each step
/// completes before the next starts.

use moose::client {
  Client.close, Client.connect, Client.connect_with_timeout,
  Client.connect_with_timeout_io, Client.get,
  Client.get_timeout, Client.host_port, Client.read_response,
  Client.redirect_request, Client.stream_response, Client.stream_response_timeout,
  Client.write_request, Connection,
}
use std::stream {Stream, FdStream}
use http::types {
  Transport, Transport.read_bytes, Transport.write_bytes,
  Body.is_empty, GET, HEAD, Headers, Headers.empty, Headers.get, Headers.set,
  POST, Request, Response, Status.found, Status.moved_permanently, Status.ok,
  Status.permanent_redirect, Status.see_other, Status.temporary_redirect, Uri,
  empty, http1_1, text,
}
use http::wire {Wire.format_response, Wire.parse_request}
use http::body {Body.from_text, Body.to_bytes_pure}
use http::uri {Uri.parse, Uri.resolve}

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

/// Check a response: status matches and body text matches.
def resp_ok (resp : Result String Response) (want_status : U16) (want_body : String) : Bool :=
  match resp {
    Result.ok r => Bool.and (U16.beq r.status want_status) (String.beq (String.from_list (Body.to_bytes_pure r.body)) want_body),
    Result.err _ => false
  }

/// Make a GET request for a loopback URL.
def get_req (port : U16) : Request :=
  Request.get (uri_of (url_for port))

/// Make a POST request with a text body for a loopback URL.
def post_req (port : U16) (body : String) : Request :=
  { method := Method.POST, uri := uri_of (url_for port), headers := Headers.empty, version := HttpVersion.http1_1, body := Body.from_text body }

/// Serialise a test response. Serialising a `Body.text` cannot fail, so an
/// error here is a bug in the test, and the marker it goes out as fails the
/// response parse on the client side instead of hanging.
def server_res_bytes (res : Response) : List U8 :=
  match Wire.format_response res {
    Result.ok bytes => bytes,
    Result.err _ => String.to_list "SERIALIZE-FAILED\r\n\r\n"
  }

/// Server writes a response and closes (assumes request already read).
def server_write_close (sock : FdStream) (res : Response) : IO Unit := do {
  tcp_write_bytes sock (server_res_bytes res);
  Stream.close sock
}

/// Server reads and discards the request bytes, then writes a response.
def server_read_respond (sock : FdStream) (res : Response) : IO Unit := do {
  tcp_read_bytes sock 8192;
  server_write_close sock res
}

/// Server reads the request, echoes the body back as text response, closes.
def server_read_echo (sock : FdStream) : IO Unit := do {
  let read_res <- tcp_read_bytes sock 8192;
  server_echo_send sock read_res
}

/// After reading: parse the request and echo the body.
def server_echo_send (sock : FdStream) (read_res : Result String (List U8)) : IO Unit :=
  match read_res {
    Result.err _ => Stream.close sock,
    Result.ok req_bytes =>
      match Wire.parse_request req_bytes {
        Result.err _ => Stream.close sock,
        Result.ok req => do {
          let echo := String.from_list (Body.to_bytes_pure req.body);
          server_write_close sock (Response.ok_text echo)
        }
      }
  }

/// Server reads the request, checks Host header, responds, closes.
def server_read_check_host (sock : FdStream) : IO Unit := do {
  let read_res <- tcp_read_bytes sock 4096;
  server_check_host_send sock read_res
}

/// After reading: parse and check Host header.
def server_check_host_send (sock : FdStream) (read_res : Result String (List U8)) : IO Unit :=
  match read_res {
    Result.err _ => Stream.close sock,
    Result.ok req_bytes =>
      match Wire.parse_request req_bytes {
        Result.err _ => Stream.close sock,
        Result.ok req =>
          let body := match Headers.get "Host" req.headers {
            Option.some h => String.concat "host:" h,
            Option.none => "no-host"
          } in
          server_write_close sock (Response.ok_text body)
      }
  }

/// Build a 302 redirect response pointing to the given port.
def redirect_response (port : U16) : Response :=
  { status := Status.found, headers := Headers.set "Location" (url_for port) Headers.empty, version := HttpVersion.http1_1, body := Body.empty }

/// Make a HEAD request for a loopback URL.
def head_req (port : U16) : Request :=
  { method := Method.HEAD, uri := uri_of (url_for port), headers := Headers.empty, version := HttpVersion.http1_1, body := Body.empty }

/// A `HEAD` response as a server sends one: the `Content-Length` of the body
/// the equivalent GET would have returned, and no body, because a response to
/// a HEAD has none (RFC 9110 §9.3.2). Written as bytes because
/// `Wire.format_response` would compute a length from the body it has.
def head_response_bytes : List U8 :=
  String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n"

// ── tests ────────────────────────────────────────────────────────────────

/// Simple GET roundtrip: client writes request, server responds 200 "hello".
#[test]
def test_get_simple : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res : Result String Connection <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Client.close conn; return false },
            Result.ok sock => do {
              Client.write_request conn (get_req port);
              server_read_respond sock (Response.ok_text "hello");
              let resp : Result String Response <- Client.read_response conn.socket Method.GET;
              Client.close conn;
              return (resp_ok resp Status.ok "hello")
            }
          }
        }
      }
    }
  }
}

/// POST echo roundtrip: server echoes the POST body back as text.
#[test]
def test_post_echo : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res : Result String Connection <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Client.close conn; return false },
            Result.ok sock => do {
              Client.write_request conn (post_req port "echo-me");
              server_read_echo sock;
              let resp : Result String Response <- Client.read_response conn.socket Method.GET;
              Client.close conn;
              return (resp_ok resp Status.ok "echo-me")
            }
          }
        }
      }
    }
  }
}

/// 302 redirect: server1 returns 302 → server2, client follows manually.
#[test]
def test_redirect_302 : IO Bool := do {
  let l1_res <- IO.tcp_listen 0u16;
  match l1_res {
    Result.err _ => return false,
    Result.ok l1 => do {
      let p1 <- IO.tcp_local_port l1;
      let l2_res <- IO.tcp_listen 0u16;
      match l2_res {
        Result.err _ => do { Stream.close l1; return false },
        Result.ok l2 => do {
          let p2 <- IO.tcp_local_port l2;
          // Server1: connect, accept, write redirect.
          let conn1_res : Result String Connection <- Client.connect (url_for p1);
          match conn1_res {
            Result.err _ => do { Stream.close l1; Stream.close l2; return false },
            Result.ok conn1 => do {
              let acc1_res <- IO.tcp_accept l1;
              Stream.close l1;
              match acc1_res {
                Result.err _ => do { Client.close conn1; Stream.close l2; return false },
                Result.ok sock1 => do {
                  // Client writes request 1, server reads + writes redirect.
                  Client.write_request conn1 (get_req p1);
                  server_read_respond sock1 (redirect_response p2);
                  // Client reads redirect response.
                  let resp1 : Result String Response <- Client.read_response conn1.socket Method.GET;
                  Client.close conn1;
                  // Server2: connect, accept, write ok.
                  let conn2_res : Result String Connection <- Client.connect (url_for p2);
                  match conn2_res {
                    Result.err _ => do { Stream.close l2; return false },
                    Result.ok conn2 => do {
                      let acc2_res <- IO.tcp_accept l2;
                      Stream.close l2;
                      match acc2_res {
                        Result.err _ => do { Client.close conn2; return false },
                        Result.ok sock2 => do {
                          // Follow redirect: write request to server2.
                          // Follow through the real policy rather than
                          // hand-building a GET: the request that goes out on
                          // the second hop is the one `redirect_request`
                          // produces for this status.
                          let loc := match resp1 {
                            Result.ok r1 =>
                              match Headers.get "Location" r1.headers {
                                Option.some l => l,
                                Option.none => url_for p2
                              },
                            Result.err _ => url_for p2
                          };
                          let req1 : Request := get_req p1;
                          let resolved : Uri := Uri.resolve req1.uri (uri_of loc);
                          Client.write_request conn2 (Client.redirect_request req1 Status.found resolved);
                          server_read_respond sock2 (Response.ok_text "found");
                          let resp2 : Result String Response <- Client.read_response conn2.socket Method.GET;
                          Client.close conn2;
                          return (resp_ok resp2 Status.ok "found")
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

/// Connect to a definitely-closed port: expect `Result.err`.
#[test]
def test_connect_refused : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      Stream.close listener;
      let resp <- Client.get (uri_of (url_for port)) Headers.empty;
      return (match resp {
        Result.ok _ => false,
        Result.err _ => true
      })
    }
  }
}

/// URI with no port: `Client.host_port` defaults to 80.
#[test]
def test_host_port_default : Bool :=
  let u : Uri := Uri.uri "http" Option.none "example.com" Option.none "/path" Option.none Option.none in
  match Client.host_port u {
    Pair.pair host port => Bool.and (String.beq host "example.com") (U16.beq port 80u16)
  }

/// Client sets Host header: server checks it received one.
#[test]
def test_get_with_headers : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res : Result String Connection <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Client.close conn; return false },
            Result.ok sock => do {
              Client.write_request conn (get_req port);
              server_read_check_host sock;
              let resp : Result String Response <- Client.read_response conn.socket Method.GET;
              Client.close conn;
              let want := String.concat "host:127.0.0.1:" (U16.to_string port);
              return (resp_ok resp Status.ok want)
            }
          }
        }
      }
    }
  }
}

/// Keep-alive: two requests on one connection, both return 200.
#[test]
def test_keep_alive_reuse : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res : Result String Connection <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Client.close conn; return false },
            Result.ok sock => do {
              // Request 1: client writes, server reads+writes, client reads.
              Client.write_request conn (get_req port);
              tcp_read_bytes sock 8192;
              tcp_write_bytes sock (server_res_bytes (Response.ok_text "one"));
              let resp1 <- Client.read_response conn.socket Method.GET;
              // Request 2: same pattern on the same connection.
              Client.write_request conn (get_req port);
              tcp_read_bytes sock 8192;
              tcp_write_bytes sock (server_res_bytes (Response.ok_text "two"));
              let resp2 <- Client.read_response conn.socket Method.GET;
              Stream.close sock;
              Client.close conn;
              return (Bool.and (resp_ok resp1 Status.ok "one") (resp_ok resp2 Status.ok "two"))
            }
          }
        }
      }
    }
  }
}

/// A HEAD response declares the `Content-Length` of the body it is not
/// sending. A reader that honours that number waits for five bytes that never
/// come -- this test only terminates because the method reaches the frame.
/// Nothing but the head is ever written, so a regression here hangs rather
/// than failing, which is exactly what the review reported.
#[test]
def test_head_response_has_no_body : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res : Result String Connection <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Client.close conn; return false },
            Result.ok sock => do {
              Client.write_request conn (head_req port);
              tcp_read_bytes sock 8192;
              tcp_write_bytes sock head_response_bytes;
              let resp : Result String Response <- Client.read_response conn.socket Method.HEAD;
              Client.close conn;
              return (resp_ok resp Status.ok "")
            }
          }
        }
      }
    }
  }
}

/// The same bytes read as the answer to a GET *are* a body: five bytes that
/// have not arrived yet, so the read reports the truncation when the peer
/// closes instead of inventing an empty body.
#[test]
def test_truncated_response_fails : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res : Result String Connection <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Client.close conn; return false },
            Result.ok sock => do {
              Client.write_request conn (get_req port);
              tcp_read_bytes sock 8192;
              tcp_write_bytes sock head_response_bytes;
              Stream.close sock;
              let resp : Result String Response <- Client.read_response conn.socket Method.GET;
              Client.close conn;
              match resp {
                Result.err _ => return true,
                Result.ok _ => return false
              }
            }
          }
        }
      }
    }
  }
}

// ── chunked responses ─────────────────────────────────────────────────────
//
// Servers switch to `Transfer-Encoding: chunked` once an answer outgrows a
// buffer, so the buffered reader has to complete a chunked body the same way
// it completes a `Content-Length` one: keep reading until the terminal chunk
// frames the message.

/// A chunked 200 written in two pieces: the data chunk, then the terminal
/// chunk. The reader keeps reading until the second piece frames the message.
#[test]
def test_chunked_response_roundtrip : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res : Result String Connection <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Client.close conn; return false },
            Result.ok sock => do {
              Client.write_request conn (get_req port);
              tcp_read_bytes sock 8192;
              tcp_write_bytes sock (String.to_list "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n");
              tcp_write_bytes sock (String.to_list "0\r\n\r\n");
              Stream.close sock;
              let resp : Result String Response <- Client.read_response conn.socket Method.GET;
              Client.close conn;
              return (resp_ok resp Status.ok "hello")
            }
          }
        }
      }
    }
  }
}

/// EOF before the terminal chunk: the read reports a truncation rather than
/// handing back the bytes decoded so far as a complete body.
#[test]
def test_chunked_response_eof_mid_chunk_fails : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res : Result String Connection <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Client.close conn; return false },
            Result.ok sock => do {
              Client.write_request conn (get_req port);
              tcp_read_bytes sock 8192;
              tcp_write_bytes sock (String.to_list "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhel");
              Stream.close sock;
              let resp : Result String Response <- Client.read_response conn.socket Method.GET;
              Client.close conn;
              match resp {
                Result.err _ => return true,
                Result.ok _ => return false
              }
            }
          }
        }
      }
    }
  }
}

// ── redirect policy ─────────────────────────────────────────────────────
//
// Pure: `Client.redirect_request` is the whole decision, so every status can
// be pinned without a socket.

/// True when `h` carries no value under `name`.
def h_absent (name : String) (h : Headers) : Bool :=
  match Headers.get name h {
    Option.none => true,
    Option.some _ => false
  }

/// True when `h` carries exactly `want` under `name`.
def h_is (name : String) (want : String) (h : Headers) : Bool :=
  match Headers.get name h {
    Option.some v => String.beq v want,
    Option.none => false
  }

/// `http://example.com:port/start`.
def rp_origin (port : U16) : Uri :=
  // The port is bound rather than written inline: `Option.some port` in
  // argument position parses as a partial application of the constructor.
  let p : Option U16 := Option.some port in
  Uri.uri "http" Option.none "example.com" p "/start" Option.none Option.none

/// A POST carrying a body and the headers that describe it, plus a credential.
def rp_post (u : Uri) : Request :=
  { method := Method.POST,
    uri := u,
    headers := Headers.set "Authorization" "Bearer t" (Headers.set "Content-Length" "7" (Headers.set "Content-Type" "text/plain" Headers.empty)),
    version := HttpVersion.http1_1,
    body := Body.text "payload" }

def rp_get (u : Uri) : Request :=
  Request.get u

def rp_head (u : Uri) : Request :=
  { method := Method.HEAD, uri := u, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.empty }

/// A redirect followed with the same method and the same body.
def rp_keeps (req : Request) (status : U16) (to : Uri) : Bool :=
  let r := Client.redirect_request req status to in
  Bool.and (r.method == req.method) (String.beq (String.from_list (Body.to_bytes_pure r.body)) (String.from_list (Body.to_bytes_pure req.body)))

/// A redirect followed with a bodyless GET.
def rp_gets (req : Request) (status : U16) (to : Uri) : Bool :=
  let r := Client.redirect_request req status to in
  Bool.and (r.method == Method.GET) (Body.is_empty r.body)

#[test]
def test_redirect_307_preserves_post : Bool :=
  rp_keeps (rp_post (rp_origin 80u16)) Status.temporary_redirect (rp_origin 8080u16)

#[test]
def test_redirect_308_preserves_post : Bool :=
  rp_keeps (rp_post (rp_origin 80u16)) Status.permanent_redirect (rp_origin 8080u16)

/// 301 and 302 predate 307, so what they mean for a POST is the convention
/// every client follows: ask again with a bodyless GET.
#[test]
def test_redirect_301_post_becomes_get : Bool :=
  rp_gets (rp_post (rp_origin 80u16)) Status.moved_permanently (rp_origin 8080u16)

#[test]
def test_redirect_302_post_becomes_get : Bool :=
  rp_gets (rp_post (rp_origin 80u16)) Status.found (rp_origin 8080u16)

/// 303 asks for the resource, not for the request to be repeated.
#[test]
def test_redirect_303_post_becomes_get : Bool :=
  rp_gets (rp_post (rp_origin 80u16)) Status.see_other (rp_origin 80u16)

/// A GET carries nothing to preserve or drop, so a 301 leaves it alone.
#[test]
def test_redirect_301_keeps_get : Bool :=
  rp_keeps (rp_get (rp_origin 80u16)) Status.moved_permanently (rp_origin 8080u16)

/// A redirected HEAD stays a HEAD: answering it with a GET would deliver a
/// body that was never asked for.
#[test]
def test_redirect_303_keeps_head : Bool :=
  rp_keeps (rp_head (rp_origin 80u16)) Status.see_other (rp_origin 8080u16)

/// The headers that describe a body go when the body does -- a `Content-Type`
/// left on a GET describes something that is not being sent.
#[test]
def test_redirect_dropped_body_drops_body_headers : Bool :=
  let r := Client.redirect_request (rp_post (rp_origin 80u16)) Status.see_other (rp_origin 80u16) in
  Bool.and (h_absent "Content-Type" r.headers) (h_absent "Content-Length" r.headers)

/// A 307 keeps the body, so it keeps the headers that describe it.
#[test]
def test_redirect_preserved_body_keeps_body_headers : Bool :=
  let r := Client.redirect_request (rp_post (rp_origin 80u16)) Status.temporary_redirect (rp_origin 80u16) in
  h_is "Content-Type" "text/plain" r.headers

/// `http://example.com` and `http://example.com:80` are one origin, so moving
/// between them is no reason to drop anything.
#[test]
def test_redirect_same_origin_by_effective_port : Bool :=
  let to := Uri.uri "http" Option.none "example.com" Option.none "/elsewhere" Option.none Option.none in
  let r := Client.redirect_request (rp_post (rp_origin 80u16)) Status.temporary_redirect to in
  h_is "Authorization" "Bearer t" r.headers

/// Leaving the origin drops the credentials. A `Location` is chosen by the
/// server, so following one must not hand a host that server names the
/// client's `Authorization` -- or its `Cookie`, under the same rule.
#[test]
def test_redirect_cross_origin_drops_credentials : Bool :=
  let r := Client.redirect_request (rp_post (rp_origin 80u16)) Status.temporary_redirect (rp_origin 8080u16) in
  Bool.and (h_absent "Authorization" r.headers) (h_absent "Cookie" r.headers)

/// Only the credentials go: everything else about the request still travels.
#[test]
def test_redirect_cross_origin_keeps_other_headers : Bool :=
  let r := Client.redirect_request (rp_post (rp_origin 80u16)) Status.temporary_redirect (rp_origin 8080u16) in
  h_is "Content-Type" "text/plain" r.headers

// ── streaming responses ──────────────────────────────────────────────────
//
// `Client.stream_response` is the staged half of `Client.post_stream`,
// split out for the same reason `Client.read_response` is: the fake server
// is single-threaded, so the client's reads happen after the server's
// writes, never interleaved with them. The invariant the tests pin is that
// the bytes the callback saw and the body the client assembled are the same
// bytes -- whatever the read boundaries turn out to be.

/// An `on_bytes` that concatenates everything it saw, so a test can compare
/// the deltas against the assembled body. A top-level def, not a lambda: a
/// closure in argument position is a compiled-backend miscompile family.
def seen_concat (seen : String) (bytes : List U8) : IO (Result String (Pair String Unit)) :=
  return (Result.ok (Pair.pair (String.concat seen (String.from_list bytes)) unit))

/// An `on_bytes` that refuses: a callback's error must abort the stream with
/// that error rather than being swallowed into a "successful" short body.
def seen_fail (seen : String) (bytes : List U8) : IO (Result String (Pair String Unit)) :=
  return (Result.err "callback-failed")

/// A chunked SSE-ish body in two chunks, written in three pieces so the
/// walker's reads and the chunk boundaries do not align.
#[test]
def test_stream_response_chunked : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res : Result String Connection <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Client.close conn; return false },
            Result.ok sock => do {
              let init_seen : String := "";
              Client.write_request conn (get_req port);
              tcp_read_bytes sock 8192;
              tcp_write_bytes sock (String.to_list "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n8\r\ndata: a\n");
              tcp_write_bytes sock (String.to_list "\r\n9\r\ndata: b\n\n");
              tcp_write_bytes sock (String.to_list "\r\n0\r\n\r\n");
              Stream.close sock;
              let res <- Client.stream_response Method.GET conn.socket init_seen seen_concat;
              Client.close conn;
              match res {
                Result.err _ => return false,
                Result.ok pr =>
                  match pr {
                    Pair.pair seen resp =>
                      let body : String := String.from_list (Body.to_bytes_pure resp.body) in
                      return (Bool.and (body == "data: a\ndata: b\n\n") (seen == "data: a\ndata: b\n\n"))
                  }
              }
            }
          }
        }
      }
    }
  }
}

/// A `Content-Length` body split across writes: the length counts the read
/// down and the callback sees the same bytes the assembled body holds.
#[test]
def test_stream_response_content_length : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res : Result String Connection <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Client.close conn; return false },
            Result.ok sock => do {
              let init_seen : String := "";
              Client.write_request conn (get_req port);
              tcp_read_bytes sock 8192;
              tcp_write_bytes sock (String.to_list "HTTP/1.1 200 OK\r\nContent-Length: 17\r\n\r\ndata: a\n");
              tcp_write_bytes sock (String.to_list "data: b\n\n");
              Stream.close sock;
              let res <- Client.stream_response Method.GET conn.socket init_seen seen_concat;
              Client.close conn;
              match res {
                Result.err _ => return false,
                Result.ok pr =>
                  match pr {
                    Pair.pair seen resp =>
                      let body : String := String.from_list (Body.to_bytes_pure resp.body) in
                      return (Bool.and (body == "data: a\ndata: b\n\n") (seen == "data: a\ndata: b\n\n"))
                  }
              }
            }
          }
        }
      }
    }
  }
}

/// A callback error aborts the stream with that error, rather than the
/// stream reporting a successful (short) body the caller rejected.
#[test]
def test_stream_response_callback_error_aborts : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res : Result String Connection <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Client.close conn; return false },
            Result.ok sock => do {
              let init_seen : String := "";
              Client.write_request conn (get_req port);
              tcp_read_bytes sock 8192;
              tcp_write_bytes sock (String.to_list "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n8\r\ndata: a\n\r\n0\r\n\r\n");
              Stream.close sock;
              let res <- Client.stream_response Method.GET conn.socket init_seen seen_fail;
              Client.close conn;
              match res {
                Result.err e => return (e == "callback-failed"),
                Result.ok _ => return false
              }
            }
          }
        }
      }
    }
  }
}

// ── timeouts ────────────────────────────────────────────────────────────

/// A listener that never accepts or answers: the client's connect and
/// write complete (the kernel backlog holds them), then the read waits
/// under its deadline instead of hanging.
#[test]
def test_get_timeout_is_bounded : IO Bool := do {
  let lr <- IO.tcp_listen 0u16;
  match lr {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let u : Uri := uri_of (url_for port);
      let start <- IO.current_time;
      let res <- Client.get_timeout u Headers.empty 200i64;
      let now <- IO.current_time;
      let elapsed : I64 := now - start;
      Stream.close listener;
      match res {
        Result.err e => return (String.contains e "timed out" && elapsed < 3000i64),
        Result.ok _ => return false
      }
    }
  }
}

#[test]
def test_connect_with_timeout_completes_on_loopback : IO Bool := do {
  let lr <- IO.tcp_listen 0u16;
  match lr {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let res <- Client.connect_with_timeout (url_for port) 1000i64;
      Stream.close listener;
      match res {
        Result.err _ => return false,
        Result.ok conn => do { Client.close conn; return true }
      }
    }
  }
}

/// The two-bound connect path: the connection keeps the connect value as
/// its non-streaming deadline while the socket carries the I/O bound.
/// Loopback cannot observe SO_RCVTIMEO, so this pins the wiring and the
/// preserved `Connection.timeout_ms`.
#[test]
def test_connect_with_timeout_io_completes_on_loopback : IO Bool := do {
  let lr <- IO.tcp_listen 0u16;
  match lr {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let res <- Client.connect_with_timeout_io (url_for port) 1000i64 60000i64;
      Stream.close listener;
      match res {
        Result.err _ => return false,
        Result.ok conn => do {
          let deadline : I64 := conn.timeout_ms;
          let ok : Bool := I64.beq deadline 1000i64;
          Client.close conn;
          return ok
        }
      }
    }
  }
}

/// Headers plus one chunk, then silence: the body walker's per-read idle
/// bound fails the read rather than waiting for a terminal chunk forever.
#[test]
def test_stream_idle_timeout_is_bounded : IO Bool := do {
  let lr <- IO.tcp_listen 0u16;
  match lr {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res <- Client.connect (url_for port);
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok conn => do {
          let srv <- IO.tcp_accept listener;
          match srv {
            Result.err _ => do { Client.close conn; Stream.close listener; return false },
            Result.ok sock => do {
              Client.write_request conn (get_req port);
              tcp_read_bytes sock 8192;
              tcp_write_bytes sock (String.to_list "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n");
              let init : List U8 := List.empty;
              let collect : List U8 -> List U8 -> IO (Result String (Pair (List U8) Unit)) :=
                fn (acc : List U8) (bytes : List U8) => IO.pure (Result.ok (Pair.pair acc unit));
              let start <- IO.current_time;
              let res <- Client.stream_response_timeout Method.GET conn.socket 200i64 init collect;
              let now <- IO.current_time;
              let elapsed : I64 := now - start;
              Client.close conn;
              Stream.close sock;
              Stream.close listener;
              match res {
                Result.err e => return (String.contains e "timed out" && elapsed < 3000i64),
                Result.ok _ => return false
              }
            }
          }
        }
      }
    }
  }
}
