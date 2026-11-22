/// The WebSocket client against a small in-test server (moon cannot be a
/// dependency of moose: a client mote must not depend on the server mote).
/// The fake server does the handshake by hand and then uses the same
/// `http::websocket_io` session an app would, so the client is exercised
/// end to end over a real socket.

use std::concurrent::combine {sleepIO}
use std::concurrent::fiber {Fiber, FiberError, forkIO, await_fiber}
use std::list {}
use std::stream {Stream, FdStream}
use std::test {}
use std::io {IO.println}
use http::types {
    Body, Headers, Headers.empty, HttpVersion, Method, Request, Response, Status.switching_protocols,
    Transport, Transport.read_bytes, Transport.write_bytes,
}
use http::strings {Strings.drop_bytes}
use http::wire {Wire.find_body_start, Wire.parse_request, Wire.take_bytes}
use http::websocket {Ws.accept_key, WsMessage, WsMessage.text_of}
use http::websocket_io {WsConfig, WsConn, WsError, WsRole, Ws.start, Ws.recv, Ws.recv_timeout, Ws.send_text, Ws.close}
use moose::websocket {MooseWs.connect, MooseWs.key_from}

def cfg : WsConfig :=
    let c : WsConfig := { max_message := 65536i64, ping_interval_ms := 2000i64,
        idle_timeout_ms := 10000i64, poll_ms := 20i64 } in
    c

#[terminating]
def echo_loop (conn : WsConn) : IO Unit := do {
    let r <- Ws.recv conn;
    match r {
        Result.err _ => IO.pure unit,
        Result.ok m => do {
            let _ <- Ws.send_text conn (WsMessage.text_of m);
            echo_loop conn
        }
    }
}

/// Read until the request head (and any bytes already read) end.
#[terminating]
def read_head (t : Transport) (acc : List U8) : IO (Result String (Pair Request (List U8))) := do {
    let r <- Transport.read_bytes t 4096i64;
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok chunk => do {
            let all := List.append acc chunk;
            match Wire.find_body_start all {
                Option.none => read_head t all,
                Option.some end =>
                    match Wire.parse_request (Wire.take_bytes end all) {
                        Result.err e => IO.pure (Result.err e),
                        Result.ok req => IO.pure (Result.ok (Pair.pair req (Strings.drop_bytes end all)))
                    }
            }
        }
    }
}

def accept_key_of (req : Request) : Option String :=
    match req.headers {
        Headers.headers pairs => accept_key_scan pairs
    }

#[terminating]
def accept_key_scan (pairs : List (Pair String String)) : Option String :=
    match pairs {
        List.empty => Option.none,
        List.cons p rest => match p {
            Pair.pair k v =>
                if String.beq (String.to_lowercase k) "sec-websocket-key"
                then Option.some (String.trim v)
                else accept_key_scan rest
        }
    }

/// The handshake, then the echo session, for one accepted socket.
def serve_one (sock : FdStream) : IO Unit := do {
    let t : Transport := Transport.plain sock;
    let r <- read_head t List.empty;
    match r {
        Result.err _ => Stream.close sock,
        Result.ok pr => match pr {
            Pair.pair req rest =>
                match accept_key_of req {
                    Option.none => Stream.close sock,
                    Option.some key => do {
                        let accept := Ws.accept_key key;
                        let head :=
                            String.concat "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\n"
                                (String.concat "Connection: Upgrade\r\nSec-WebSocket-Accept: "
                                    (String.concat accept "\r\n\r\n"));
                        let _ <- Transport.write_bytes t (String.to_list head);
                        let started <- Ws.start cfg WsRole.server t rest;
                        match started {
                            Result.err _ => Stream.close sock,
                            Result.ok conn => echo_loop conn
                        }
                    }
                }
        }
    }
}

def listen_one : IO (Result String (Pair FdStream U16)) := do {
    let l <- IO.tcp_listen 0u16;
    match l {
        Result.err e => IO.pure (Result.err e.message),
        Result.ok listener => do {
            let port <- IO.tcp_local_port listener;
            IO.pure (Result.ok (Pair.pair listener port))
        }
    }
}

def spawn_server (listener : FdStream) : IO (Fiber Unit) := do {
    let f <- forkIO (fn (_ : Unit) => do {
        let s <- IO.tcp_accept listener;
        match s {
            Result.err _ => IO.pure unit,
            Result.ok sock => serve_one sock
        }
    });
    IO.pure f
}

def url_for (port : U16) : String :=
    String.concat "ws://127.0.0.1:" (String.concat (U16.to_string port) "/ws")

#[test]
def test_echo : IO Bool := do {
    let l <- listen_one;
    match l {
        Result.err _ => IO.pure false,
        Result.ok pr => match pr {
            Pair.pair listener port => do {
                let f <- spawn_server listener;
                let c <- MooseWs.connect (url_for port) [] Headers.empty cfg;
                match c {
                    Result.err e => do {
                        let _ <- IO.println (String.concat "connect: " e);
                        Stream.close listener;
                        IO.pure false
                    },
                    Result.ok conn => do {
                        let _ <- Ws.send_text conn "over the wire";
                        let got <- Ws.recv_timeout conn 2000i64;
                        let _ <- Ws.close conn 1000i64 "done";
                        Stream.close listener;
                        let _f : Result FiberError Unit <- await_fiber f;
                        match got {
                            Result.ok o => match o {
                                Option.some m => IO.pure (WsMessage.text_of m == "over the wire"),
                                Option.none => IO.pure false
                            },
                            Result.err e => do {
                                let _ <- IO.println (String.concat "recv err: " (WsError.message e));
                                IO.pure false
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
def test_key_source_is_deterministic : Bool :=
    MooseWs.key_from 42i64 == MooseWs.key_from 42i64
        && Bool.not (MooseWs.key_from 42i64 == MooseWs.key_from 43i64)
