/// WebSocket routes end to end: a real server on a localhost port, a raw
/// HTTP upgrade written by hand, then the `http` client session over the
/// upgraded socket.

use std::list {}
use std::stream {Stream, FdStream}
use std::test {}
use http::types {
    Headers, Headers.get, Method, Request, Response, Response.ok_text, Response.text,
    Status.ok, Status.switching_protocols, Transport,
}
use http::wire {Wire.find_body_start, Wire.parse_response, Wire.take_bytes}
use http::strings {Strings.drop_bytes}
use std::concurrent::combine {sleepIO}
use std::concurrent::fiber {FiberError}
use http::websocket {WsMessage, WsMessage.text_of}
use http::websocket_io {WsConfig, WsConn, WsError, WsRole, Ws.start, Ws.recv, Ws.send_text, Ws.close}
use moon::context {Ctx}
use moon::handler_t {HandlerT, HandlerT.pure_io}
use moon::router {RouterT.get, RouterT.route}
use moon::server {
    ServerConfig, ServerConfig.on, ServerConfig.with_timeouts, ServerHandleT,
    Server.start_t, Server.shutdown_t, Server.wait_t,
}
use moon::websocket {MoonWs.handler, WsHub, WsHubEvent, WsHub.broadcast, WsHub.drain, WsHub.new}

def cfg : WsConfig :=
    let c : WsConfig := { max_message := 65536i64, ping_interval_ms := 2000i64,
        idle_timeout_ms := 10000i64, poll_ms := 20i64 } in
    c

/// An echo session: every message the client sends comes back.
def echo_session (ctx : Ctx) (conn : WsConn) : IO Unit :=
    echo_loop conn

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

def start (router : HandlerT IO Response) : IO (Result String (Pair ServerHandleT U16)) := do {
    let cfg := ServerConfig.with_timeouts 5000i64 5000i64 15000i64 5000i64 (ServerConfig.on 0u16);
    let started <- Server.start_t cfg router;
    start_ok started
}

def start_ok (started : Result String ServerHandleT) : IO (Result String (Pair ServerHandleT U16)) :=
    match started {
        Result.err e => IO.pure (Result.err e),
        Result.ok h => do {
            let port <- IO.tcp_local_port h.listener;
            IO.pure (Result.ok (Pair.pair h port))
        }
    }

def stop (h : ServerHandleT) : IO Unit := do {
    Server.shutdown_t h;
    let _w : Result FiberError Unit <- Server.wait_t h;
    return unit
}

/// The HTTP upgrade handshake, written by hand; returns whatever the server
/// sent past the head.
def upgrade_request : String :=
    "GET /ws HTTP/1.1\r\nHost: localhost\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
        ++ "Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n\r\n"

def write_text (sock : FdStream) (s : String) : IO Bool := do {
    let t : Transport := Transport.plain sock;
    let r <- Transport.write_bytes t (String.to_list s);
    match r {
        Result.err _ => IO.pure false,
        Result.ok _ => IO.pure true
    }
}

/// Read a whole response (head + declared body). The leftover is what
/// followed the head, which for a 101 is the first frames.
#[terminating]
def read_head (sock : FdStream) (acc : List U8) : IO (Result String (Pair U16 (List U8))) := do {
    let t : Transport := Transport.plain sock;
    let r <- Transport.read_bytes t 4096i64;
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok chunk => do {
            let all := List.append acc chunk;
            match Wire.find_body_start all {
                Option.none => read_head sock all,
                Option.some end =>
                    match Wire.parse_response all {
                        Result.err _ => read_head sock all,
                        Result.ok res =>
                            match res {
                                { status, .. } => IO.pure (Result.ok (Pair.pair status (Strings.drop_bytes end all)))
                            }
                    }
            }
        }
    }
}

/// A client session on a raw socket, after its handshake.
def client_conn (sock : FdStream) (rest : List U8) : IO (Result WsError WsConn) :=
    Ws.start cfg WsRole.client (Transport.plain sock) rest

// ── tests ───────────────────────────────────────────────────────────────

#[test]
def test_plain_get_is_426 : IO Bool := do {
    let router := RouterT.route [RouterT.get "/ws" (MoonWs.handler cfg [] (fn (c : Ctx) (k : WsConn) => IO.pure unit))];
    let s <- start router;
    match s {
        Result.err _ => IO.pure false,
        Result.ok pr => match pr {
            Pair.pair h port => do {
                let c <- IO.tcp_connect "127.0.0.1" port;
                match c {
                    Result.err _ => IO.pure false,
                    Result.ok sock => do {
                        let _ <- write_text sock "GET /ws HTTP/1.1\r\nHost: localhost\r\n\r\n";
                        let got <- read_head sock List.empty;
                        Stream.close sock;
                        stop h;
                        match got {
                            Result.err _ => IO.pure false,
                            Result.ok p => match p {
                                Pair.pair status _ => IO.pure (U16.beq status 426u16)
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
def test_upgrade_and_echo : IO Bool := do {
    let router := RouterT.route [RouterT.get "/ws" (MoonWs.handler cfg [] echo_session)];
    let s <- start router;
    match s {
        Result.err _ => IO.pure false,
        Result.ok pr => match pr {
            Pair.pair h port => do {
                let c <- IO.tcp_connect "127.0.0.1" port;
                match c {
                    Result.err _ => IO.pure false,
                    Result.ok sock => do {
                        let _ <- write_text sock upgrade_request;
                        let got <- read_head sock List.empty;
                        match got {
                            Result.err _ => do { Stream.close sock; stop h; IO.pure false },
                            Result.ok p => match p {
                                Pair.pair status rest => do {
                                    let conn <- client_conn sock rest;
                                    let ok_header := U16.beq status Status.switching_protocols;
                                    match conn {
                                        Result.err _ => do { Stream.close sock; stop h; IO.pure ok_header },
                                        Result.ok k => do {
                                            let _ <- Ws.send_text k "echo me";
                                            let got2 <- Ws.recv k;
                                            let _ <- Ws.close k 1000i64 "done";
                                            Stream.close sock;
                                            stop h;
                                            let ok_echo := match got2 {
                                                Result.ok m => WsMessage.text_of m == "echo me",
                                                Result.err _ => false
                                            };
                                            IO.pure (ok_header && ok_echo)
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

#[test]
def test_hub_broadcast : IO Bool := do {
    let hub <- WsHub.new 8i64;
    let router := RouterT.route [RouterT.get "/ws" (WsHub.handler hub cfg [])];
    let s <- start router;
    match s {
        Result.err _ => IO.pure false,
        Result.ok pr => match pr {
            Pair.pair h port => do {
                let c <- IO.tcp_connect "127.0.0.1" port;
                match c {
                    Result.err _ => IO.pure false,
                    Result.ok sock => do {
                        let _ <- write_text sock upgrade_request;
                        let got <- read_head sock List.empty;
                        match got {
                            Result.err _ => do { Stream.close sock; stop h; IO.pure false },
                            Result.ok p => match p {
                                Pair.pair status rest => do {
                                    let conn <- client_conn sock rest;
                                    match conn {
                                        Result.err _ => do { Stream.close sock; stop h; IO.pure false },
                                        Result.ok k => do {
                                            // Let the server's reader loop start and
                                            // register the session.
                                            let _ <- sleepIO 50i64;
                                            let _ <- WsHub.broadcast hub (WsMessage.text "welcome");
                                            let got2 <- Ws.recv k;
                                            let events <- WsHub.drain hub;
                                            let _ <- Ws.close k 1000i64 "bye";
                                            Stream.close sock;
                                            stop h;
                                            let ok_msg := match got2 {
                                                Result.ok m => WsMessage.text_of m == "welcome",
                                                Result.err _ => false
                                            };
                                            IO.pure (ok_msg && has_joined events)
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

#[terminating]
def has_joined (events : List WsHubEvent) : Bool :=
    match events {
        List.empty => false,
        List.cons e rest => match e { WsHubEvent.joined _ => true, _ => has_joined rest }
    }
