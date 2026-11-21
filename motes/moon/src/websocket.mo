/// WebSocket routes for `moon`: a handler that performs the upgrade and a
/// broadcast hub for a game server.
///
/// The handler validates the upgrade request (`http::websocket`), schedules
/// the connection takeover on the request's `Ctx` and returns the 101. The
/// server writes that head without a `Connection: close` and hands the
/// transport plus the bytes it had already read to the session, which runs
/// in the connection's fiber until the peer closes.
///
/// `WsHub` is the game-server shape: every session reports into one inbox
/// (`joined`, `message`, `left`), which a fixed-step tick drains with
/// `WsHub.drain`; replies go out with `WsHub.send` or `WsHub.broadcast`.
/// A failed send drops that client (and reports `left`), so one dead peer
/// cannot stall the tick for longer than the server's write timeout.

use std::ref {Ref, Ref.get, Ref.set}
use http::types {
    Headers, Method, Response, Transport, Status.service_unavailable, Status.bad_request,
    Status.upgrade_required,
}
use http::websocket {
    WsClose, WsOffer, WsMessage, Ws.accept_response, Ws.check_upgrade, Ws.select_protocol,
    Ws.upgrade_required, WsClose.of,
}
use http::websocket_io {
    WsConfig, WsConn, WsError, WsRole, Ws.start, Ws.recv, Ws.send, Ws.close,
    Ws.drain as ws_drain,
}
use lib::context {Ctx, Ctx.takeover, Ctx.upgrade_slot, Ctx.method, Ctx.headers, UpgradeSlot}
use lib::handler_t {HandlerT, HttpError}

// ── one route ───────────────────────────────────────────────────────────

/// A `HandlerT` route that accepts a WebSocket upgrade and runs `session`
/// with the live connection. `protocols` is the server's subprotocol
/// preference order; the first one the client offered is selected.
///
/// A request that is not an upgrade (or offers none of `protocols` and is
/// therefore refused by its caller) is answered here: 426 with
/// `Sec-WebSocket-Version: 13`, 400 for a malformed key, 405 for a
/// non-GET.
pub def MoonWs.handler (cfg : WsConfig) (protocols : List String)
    (session : Ctx -> WsConn -> IO Unit) : HandlerT IO Response :=
    HandlerT.mk (fn (ctx : Ctx) => do {
        let hs := Ctx.headers ctx;
        match Ws.check_upgrade (Ctx.method ctx) hs {
            Result.err refusal => IO.pure (Result.ok refusal),
            Result.ok offer =>
                MoonWs.accept ctx offer cfg protocols session
        }
    })

def MoonWs.accept (ctx : Ctx) (offer : WsOffer) (cfg : WsConfig) (protocols : List String)
    (session : Ctx -> WsConn -> IO Unit) : IO (Result HttpError Response) := do {
    let protocol := Ws.select_protocol (Shared.of offer.protocols) protocols;
    let res := Ws.accept_response offer.key protocol;
    let run := fn (t : Transport) (rest : List U8) => do {
        let started <- Ws.start cfg WsRole.server t rest;
        match started {
            Result.err _ => IO.pure unit,
            Result.ok conn => session ctx conn
        }
    };
    let _ <- Ctx.takeover ctx run;
    IO.pure (Result.ok res)
}

// ── the hub ─────────────────────────────────────────────────────────────

/// What happened on the hub since the last drain.
pub type WsHubEvent {
    joined (id : I64),
    message (id : I64) (m : WsMessage),
    left (id : I64) (c : WsClose)
}

/// Every live session, one inbox for the tick.
///
/// `clients` is the live set; the reader loop of each session appends to
/// `inbox` and removes itself on exit. Sends run in the caller's fiber (a
/// tick), each taking the connection's own write lock, so two ticks never
/// interleave a frame.
pub struct WsHub {
    inbox : Ref (List WsHubEvent),
    clients : Ref (List (Pair I64 WsConn)),
    next_id : Ref I64,
    max_clients : I64
}

pub def WsHub.new (max_clients : I64) : IO WsHub := do {
    let inbox <- Ref.new ([] : List WsHubEvent);
    let clients <- Ref.new ([] : List (Pair I64 WsConn));
    let next_id <- Ref.new 1i64;
    let hub : WsHub := { inbox := inbox, clients := clients, next_id := next_id, max_clients := max_clients };
    IO.pure hub
}

def WsHub.emit (hub : WsHub) (e : WsHubEvent) : IO Unit := do {
    let cur <- Ref.get hub.inbox;
    Ref.set hub.inbox (List.cons e cur)
}

/// Everything since the last call, oldest first.
pub def WsHub.drain (hub : WsHub) : IO (List WsHubEvent) := do {
    let cur <- Ref.get hub.inbox;
    let _ <- Ref.set hub.inbox List.empty;
    IO.pure (List.reverse cur)
}

/// The live client ids.
pub def WsHub.clients (hub : WsHub) : IO (List I64) := do {
    let live <- Ref.get hub.clients;
    IO.pure (WsHub.ids live)
}

#[terminating]
def WsHub.ids (live : List (Pair I64 WsConn)) : List I64 :=
    match live {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Pair.pair id _ => List.cons id (WsHub.ids rest)
            }
    }

/// A route like `MoonWs.handler` that registers the session on the hub.
/// Over `max_clients` the upgrade is refused with 503 before the 101.
pub def WsHub.handler (hub : WsHub) (cfg : WsConfig) (protocols : List String)
    : HandlerT IO Response :=
    MoonWs.handler cfg protocols (fn (ctx : Ctx) (conn : WsConn) => WsHub.session hub ctx conn)

def WsHub.session (hub : WsHub) (ctx : Ctx) (conn : WsConn) : IO Unit := do {
    let live <- Ref.get hub.clients;
    if Bool.not (I64.lt (List.length live) hub.max_clients) then do {
        let _ <- Ws.close conn 1013i64 "server busy";
        IO.pure unit
    }
    else do {
        let id <- Ref.get hub.next_id;
        let _ <- Ref.set hub.next_id (I64.add id 1i64);
        let _ <- Ref.set hub.clients (List.cons (Pair.pair id conn) live);
        let _ <- WsHub.emit hub (WsHubEvent.joined id);
        WsHub.read_loop hub id conn
    }
}

/// The reader loop: every message goes to the inbox; the loop ends when
/// the peer closes, the transport dies or the protocol breaks, and reports
/// `left`.
#[terminating] // each turn either yields a message or ends the loop
def WsHub.read_loop (hub : WsHub) (id : I64) (conn : WsConn) : IO Unit := do {
    let r <- Ws.recv conn;
    match r {
        Result.err e => do {
            let _ <- WsHub.drop_client hub id;
            WsHub.emit hub (WsHubEvent.left id (WsHub.code_of e))
        },
        Result.ok m => do {
            let _ <- WsHub.emit hub (WsHubEvent.message id m);
            WsHub.read_loop hub id conn
        }
    }
}

def WsHub.code_of (e : WsError) : WsClose :=
    match e {
        WsError.closed c => c,
        WsError.protocol c => c,
        WsError.transport _ => WsClose.of 1006i64 "",
        WsError.already_closed => WsClose.of 1005i64 ""
    }

def WsHub.drop_client (hub : WsHub) (id : I64) : IO Unit := do {
    let live <- Ref.get hub.clients;
    Ref.set hub.clients (WsHub.without live id)
}

#[terminating]
def WsHub.without (live : List (Pair I64 WsConn)) (id : I64) : List (Pair I64 WsConn) :=
    match live {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Pair.pair cid conn =>
                    if I64.beq cid id
                    then WsHub.without rest id
                    else List.cons (Pair.pair cid conn) (WsHub.without rest id)
            }
    }

def WsHub.find (live : List (Pair I64 WsConn)) (id : I64) : Option WsConn :=
    match live {
        List.empty => Option.none,
        List.cons p rest =>
            match p {
                Pair.pair cid conn =>
                    if I64.beq cid id then Option.some conn else WsHub.find rest id
            }
    }

/// Send to one client; a failed send drops it (and reports `left`).
pub def WsHub.send (hub : WsHub) (id : I64) (m : WsMessage) : IO Bool := do {
    let live <- Ref.get hub.clients;
    match WsHub.find live id {
        Option.none => IO.pure false,
        Option.some conn => do {
            let r <- Ws.send conn m;
            match r {
                Result.ok _ => IO.pure true,
                Result.err e => do {
                    let _ <- WsHub.drop_client hub id;
                    WsHub.emit hub (WsHubEvent.left id (WsHub.code_of e));
                    IO.pure false
                }
            }
        }
    }
}

/// Send to every client; returns how many took it. A client that refuses
/// is dropped.
pub def WsHub.broadcast (hub : WsHub) (m : WsMessage) : IO I64 := do {
    let live <- Ref.get hub.clients;
    WsHub.broadcast_go hub live m 0i64
}

/// One client at a time through `WsHub.send`, so a failed send drops that
/// client here exactly as it does for a targeted send (one `left`, and no
/// further writes to a dead socket).
#[terminating]
def WsHub.broadcast_go (hub : WsHub) (live : List (Pair I64 WsConn)) (m : WsMessage) (sent : I64)
    : IO I64 :=
    match live {
        List.empty => IO.pure sent,
        List.cons p rest =>
            match p {
                Pair.pair cid _conn => do {
                    let ok <- WsHub.send hub cid m;
                    let sent2 := if ok then I64.add sent 1i64 else sent;
                    WsHub.broadcast_go hub rest m sent2
                }
            }
    }

/// Close one client (the hub reports `left` when its reader loop ends).
pub def WsHub.kick (hub : WsHub) (id : I64) (code : I64) (reason : String) : IO Bool := do {
    let live <- Ref.get hub.clients;
    match WsHub.find live id {
        Option.none => IO.pure false,
        Option.some conn => do {
            let r <- Ws.close conn code reason;
            match r { Result.ok _ => IO.pure true, Result.err _ => IO.pure false }
        }
    }
}
