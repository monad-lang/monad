/// Streaming server tests: a chunked SSE response over a real socket.

use std::ref {Ref, Ref.get, Ref.new, Ref.set}
use std::stream {FdStream, Stream}
use http::sse {Sse.response, SseEvent}
use http::types {
  Request, Request.get, Response, Transport, Transport.read_bytes,
  Transport.write_bytes, Uri,
}
use http::wire {Wire.format_request}
use moon::server {Server.handle_connection}

/// A source that emits one event, then ends.
def one_event : IO (Unit -> IO (Option SseEvent)) := do {
  let sent : Ref Bool <- Ref.new false;
  return (fn (_ : Unit) => do {
    let done <- Ref.get sent;
    if done
    then IO.pure Option.none
    else do {
      Ref.set sent true;
      let ev : SseEvent := { event := "msg", data := "hi" };
      return (Option.some ev)
    }
  })
}

def stream_handler (_ : Request) : IO Response := do {
  let source <- one_event;
  return (Sse.response source)
}

def get_req_bytes : List U8 :=
  let req : Request :=
    Request.get (Uri.uri "" Option.none "" Option.none "/stream" Option.none Option.none) in
  match Wire.format_request req {
    Result.ok bytes => bytes,
    Result.err _ => String.to_list "GET /stream HTTP/1.1\r\n\r\n"
  }

def tcp_read (sock : FdStream) (max : I64) : IO (Result String (List U8)) :=
  let t : Transport := Transport.plain sock in
  Transport.read_bytes t max

/// Read until the chunked terminal chunk (or EOF).
#[terminating]
def read_until_done (sock : FdStream) (acc : List U8) (tries : I64) : IO (Result String (List U8)) := do {
  if I64.lt tries 1
  then IO.pure (Result.ok acc)
  else do {
    let r <- tcp_read sock 4096;
    match r {
      Result.err e => IO.pure (Result.err e),
      Result.ok chunk =>
        let next := List.append acc chunk in
        if List.is_empty chunk
        then IO.pure (Result.ok next)
        else if String.ends_with (String.from_list next) "0\r\n\r\n"
        then IO.pure (Result.ok next)
        else read_until_done sock next (I64.sub tries 1)
    }
  }
}

#[test]
def test_sse_chunked_response : IO Bool := do {
  let listen_res <- IO.tcp_listen 0u16;
  match listen_res {
    Result.err _ => return false,
    Result.ok listener => do {
      let port <- IO.tcp_local_port listener;
      let conn_res <- IO.tcp_connect "127.0.0.1" port;
      match conn_res {
        Result.err _ => do { Stream.close listener; return false },
        Result.ok client => do {
          let accept_res <- IO.tcp_accept listener;
          Stream.close listener;
          match accept_res {
            Result.err _ => do { Stream.close client; return false },
            Result.ok server_sock => do {
              let t : Transport := Transport.plain client;
              let _ <- Transport.write_bytes t get_req_bytes;
              Server.handle_connection stream_handler server_sock;
              let read <- read_until_done client List.empty 10i64;
              Stream.close client;
              match read {
                Result.err _ => return false,
                Result.ok bytes =>
                  let raw := String.from_list bytes in
                  let head := "HTTP/1.1 200 \r\ntransfer-encoding: chunked\r\nx-accel-buffering: no\r\ncache-control: no-cache\r\ncontent-type: text/event-stream\r\n\r\n" in
                  return (Bool.and (String.starts_with head raw)
                    (String.ends_with raw "event: msg\ndata: hi\n\n\r\n0\r\n\r\n"))
              }
            }
          }
        }
      }
    }
  }
}
