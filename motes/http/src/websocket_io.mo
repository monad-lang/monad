/// WebSocket sessions over an http `Transport` — the IO half of RFC 6455.
///
/// `http::websocket` owns the handshake and the frame codec; this file owns
/// everything that touches a connection: reading and decoding, pings while
/// the peer is quiet, answering pings and the close handshake, and writes
/// serialized so a reader fiber's automatic pong and an application's
/// broadcast never interleave frames.
///
/// A connection may be driven two ways:
///
/// - **two fibers**: one calls `Ws.recv` in a loop, any others call
///   `Ws.send` / `Ws.close`. Writes take the connection's lock, so frames
///   never interleave. This is `moon`'s shape (a reader fiber per socket
///   plus a broadcaster).
/// - **one fiber**: `Ws.drain` (non-blocking; `ok []` when nothing arrived)
///   or `Ws.recv_timeout`, then `Ws.send` when a message is due. This is
///   what a `secure` (TLS) client must use: one `SSL*` must not be read and
///   written from two fibers at once. The reader also holds the lock while
///   it reads on a secure transport, so a TLS session is never read and
///   written concurrently even with two fibers (the read happens only after
///   `wait_read` says bytes are there, so the lock is never held across a
///   blocking wait).
///
/// A protocol violation decodes to the close code RFC 6455 §7.4 names; the
/// session sends that close frame, tears the connection down, and reports it
/// as `WsError.protocol`.
///
/// `Channel` (the write lock) is native-only, so this module is compiled for
/// native targets only; it is therefore not re-exported from `lib`. Import
/// it by module: `use http::websocket_io {WsConn, WsConfig, Ws.open}`.

use std::concurrent::channel {Channel, Channel.new, Channel.put, Channel.take}
use std::ref {Ref, Ref.get, Ref.set}
use http::types {Transport, Transport.close, Transport.read, Transport.read_bytes, Transport.wait_read}
use http::websocket {
    WsClose, WsDecoder, WsDecoder.new, WsInbound, WsMask, WsMessage, WsOpcode, WsFrame,
    Ws.control_frame, Ws.encode_close, Ws.encode_frame, Ws.message_frame, Ws.push,
    Ws.close_going_away, Ws.close_normal, Ws.close_no_status, Ws.close_protocol_error,
    Ws.close_too_big, WsMask.of_bytes,
}

/// The session's limits and timings.
pub struct WsConfig {
    /// The largest message payload accepted; bigger closes with 1009.
    max_message : I64 := 1048576,
    /// Send a ping when nothing has been received for this long.
    ping_interval_ms : I64 := 20000,
    /// Close the connection when nothing at all has been heard for this
    /// long (the peer is gone, not merely quiet).
    idle_timeout_ms : I64 := 60000,
    /// The longest one `wait_read` waits, so a blocked reader notices a
    /// cancel and the idle rules promptly.
    poll_ms : I64 := 1000
}

/// Which end of the connection this is: it decides frame masking (a client
/// masks, a server does not) and must match the handshake that opened it.
pub type WsRole {
    client,
    server
}

/// How a session ended, or why it could not continue.
pub type WsError {
    /// The peer closed (or we closed); carries its code and reason.
    closed (c : WsClose),
    /// The peer broke the protocol; the session has sent this close.
    protocol (c : WsClose),
    /// The transport failed, or the peer vanished without a close frame.
    transport (message : String),
    /// The connection was already closed (a second close, a send after).
    already_closed
}

/// A live session. All fields are Copy handles except the transport, which
/// every operation touches exactly once.
pub struct WsConn {
    t : Ref Transport,
    role : WsRole,
    cfg : WsConfig,
    decoder : Ref WsDecoder,
    pending : Ref (List WsInbound),
    closed : Ref Bool,
    lock : Channel Unit,
    seed : Ref I64
}

/// The error's message, for logging.
pub def WsError.message (e : WsError) : String :=
    match e {
        WsError.closed c => String.concat "closed: " c.reason,
        WsError.protocol c => String.concat "protocol error: " c.reason,
        WsError.transport m => String.concat "transport: " m,
        WsError.already_closed => "already closed"
    }

/// The code a close carried (1005 when it carried none).
pub def WsError.close_code (e : WsError) : I64 :=
    match e {
        WsError.closed c => c.code,
        WsError.protocol c => c.code,
        WsError.transport _ => Ws.close_protocol_error,
        WsError.already_closed => Ws.close_no_status
    }

// ── opening ─────────────────────────────────────────────────────────────

/// Start a session on an upgraded connection. `leftover` is whatever the
/// HTTP reader read past the request head (a client also passes whatever it
/// read past the response head); those bytes are already frame bytes.
pub def Ws.start (cfg : WsConfig) (role : WsRole) (tp : Transport) (leftover : List U8) :
    IO (Result WsError WsConn) := do {
    let d <- Ref.new (WsDecoder.new (Ws.is_server role) cfg.max_message);
    let tc <- Ref.new tp;
    let pending <- Ref.new ([] : List WsInbound);
    let closed <- Ref.new false;
    let seed <- Ref.new 0x2545f4914f6cdd1di64;
    let lock : Channel Unit <- Channel.new;
    let _ <- Channel.put lock unit; // full = unlocked
    let c : WsConn :=
        { t := tc, role := role, cfg := cfg, decoder := d, pending := pending, closed := closed,
            lock := lock, seed := seed };
    match Ws.is_server role {
        true => IO.pure (Result.ok c),
        false => do {
            if List.is_empty leftover then IO.pure (Result.ok c)
            else do {
                let r <- Ws.pump c leftover;
                match r {
                    Result.err e => IO.pure (Result.err e),
                    Result.ok _ => IO.pure (Result.ok c)
                }
            }
        }
    }
}

def Ws.is_server (r : WsRole) : Bool :=
    match r {
        WsRole.server => true,
        WsRole.client => false
    }

// ── writing ─────────────────────────────────────────────────────────────

/// Write one frame, serialized with every other writer on this connection.
def Ws.write_frame (c : WsConn) (f : WsFrame) : IO (Result WsError Unit) := do {
    let mask <- Ws.next_mask c;
    let bytes := Ws.encode_frame mask f;
    let _ <- Channel.take c.lock;
    let tp <- Ref.get c.t;
    let r <- Ws.write_raw tp bytes;
    let _ <- Channel.put c.lock unit;
    return r
}

def Ws.write_raw (t : Transport) (bytes : List U8) : IO (Result WsError Unit) := do {
    let r <- Ws.write_raw_go t bytes;
    match r {
        Result.err m => IO.pure (Result.err (WsError.transport m)),
        Result.ok _ => IO.pure (Result.ok unit)
    }
}

def Ws.write_raw_go (t : Transport) (bytes : List U8) : IO (Result String I64) := do {
    let r <- Transport.write_bytes t bytes;
    match r {
        Result.err m => IO.pure (Result.err m),
        Result.ok n => IO.pure (Result.ok (U64.to_i64 n))
    }
}

/// A fresh mask for the next client frame; `none` for a server.
def Ws.next_mask (c : WsConn) : IO (Option WsMask) := do {
    match Ws.is_server c.role {
        true => IO.pure Option.none,
        false => do {
            let bytes <- Ws.random_bytes c.seed 4i64;
            IO.pure (Option.some (WsMask.of_bytes bytes))
        }
    }
}

/// `n` bytes from a per-connection counter (xorshift64). Masking is an
/// obfuscation the RFC requires, not a security measure (§5.3), so a cheap
/// deterministic source is enough — and it makes a session reproducible.
#[terminating]
def Ws.random_bytes (seed : Ref I64) (n : I64) : IO (List U8) := do {
    let s <- Ref.get seed;
    let s1 := Ws.mix s;
    let _ <- Ref.set seed s1;
    let chunk := [Ws.byte_of (I64.shr s1 0i64), Ws.byte_of (I64.shr s1 8i64),
        Ws.byte_of (I64.shr s1 16i64), Ws.byte_of (I64.shr s1 24i64)];
    if I64.gt n 4 then do {
        let more <- Ws.random_bytes seed (I64.sub n 4i64);
        IO.pure (List.append chunk more)
    }
    else IO.pure (Ws.take_i n chunk)
}

def Ws.mix (x : I64) : I64 :=
    let a := I64.xor x (I64.shl x 13i64) in
    let b := I64.xor a (I64.shr a 7i64) in
    I64.xor b (I64.shl b 17i64)

def Ws.byte_of (x : I64) : U8 :=
    U32.to_u8 (I64.to_u32 (I64.and x 255i64))

#[terminating]
def Ws.take_i (n : I64) (xs : List U8) : List U8 :=
    if Bool.not (I64.gt n 0) then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (Ws.take_i (I64.sub n 1i64) rest)
    }

/// Send a text message.
pub def Ws.send_text (c : WsConn) (s : String) : IO (Result WsError Unit) :=
    Ws.send c (WsMessage.text s)

/// Send a binary message.
pub def Ws.send_binary (c : WsConn) (bytes : List U8) : IO (Result WsError Unit) :=
    Ws.send c (WsMessage.binary bytes)

/// Send a message as one frame.
pub def Ws.send (c : WsConn) (m : WsMessage) : IO (Result WsError Unit) := do {
    let closed <- Ref.get c.closed;
    if closed then IO.pure (Result.err WsError.already_closed)
    else Ws.write_frame c (Ws.message_frame m)
}

/// Send a ping with an empty payload.
pub def Ws.ping (c : WsConn) : IO (Result WsError Unit) :=
    Ws.write_frame c (Ws.control_frame WsOpcode.ping List.empty)

/// Close with `code` and `reason`, then drop the transport. Idempotent: a
/// second call is `already_closed`.
pub def Ws.close (c : WsConn) (code : I64) (reason : String) : IO (Result WsError Unit) :=
    Ws.close_with c (WsClose.of code reason)

def Ws.close_with (c : WsConn) (cl : WsClose) : IO (Result WsError Unit) := do {
    let closed <- Ref.get c.closed;
    if closed then IO.pure (Result.err WsError.already_closed)
    else do {
        let _ <- Ref.set c.closed true;
        let _ <- Ws.write_frame c (Ws.control_frame WsOpcode.close (Ws.encode_close cl));
        Ws.close_raw c;
        IO.pure (Result.ok unit)
    }
}

/// The peer asked to close: answer with its code (or 1000 when it named
/// none), then drop the transport.
def Ws.finish_close (c : WsConn) (cl : WsClose) : IO Unit := do {
    let closed <- Ref.get c.closed;
    if closed then Ws.close_raw c
    else do {
        let _ <- Ref.set c.closed true;
        let code := if cl.code == Ws.close_no_status then Ws.close_normal else cl.code;
        let _ <- Ws.write_frame c (Ws.control_frame WsOpcode.close (Ws.encode_close (WsClose.of code "")));
        Ws.close_raw c
    }
}

// ── reading ─────────────────────────────────────────────────────────────

/// Decode `bytes` into the pending queue; a violation closes the session
/// (sending its close frame here) and is an error.
pub def Ws.pump (c : WsConn) (bytes : List U8) : IO (Result WsError Unit) := do {
    let d <- Ref.get c.decoder;
    match Ws.push d bytes {
        Result.err bad => do {
            let _ <- Ws.close_with c bad;
            IO.pure (Result.err (WsError.protocol bad))
        },
        Result.ok pr => match pr {
            Pair.pair d2 units => do {
                let _ <- Ref.set c.decoder d2;
                let queued <- Ref.get c.pending;
                let _ <- Ref.set c.pending (List.append queued units);
                IO.pure (Result.ok unit)
            }
        }
    }
}

/// One read of at most 64 KiB; end of stream is an empty list.
def Ws.read_chunk (t : Transport) : IO (Result WsError (List U8)) := do {
    let r <- Transport.read_bytes t 65536i64;
    match r {
        Result.err m => IO.pure (Result.err (WsError.transport m)),
        Result.ok bytes => IO.pure (Result.ok bytes)
    }
}

/// Decode a chunk, closing the session on a violation.
def Ws.feed (c : WsConn) (bytes : List U8) : IO (Result WsError Unit) :=
    match bytes {
        List.empty => IO.pure (Result.err (WsError.transport "connection closed")),
        List.cons _ _ => Ws.pump c bytes
    }

/// Wait for readability (0 = do not wait), then read what is there.
def Ws.wait_ready (t : Transport) (ms : I64) : IO (Result WsError Bool) := do {
    let ready <- Transport.wait_read t ms;
    match ready {
        Result.err e => IO.pure (Result.err (WsError.transport e.message)),
        Result.ok is_ready => IO.pure (Result.ok is_ready)
    }
}

/// One non-blocking read: whatever the socket has now, appended to the
/// queue. A read error is a transport error.
def Ws.fill (c : WsConn) : IO (Result WsError Unit) := do {
    let tp <- Ref.get c.t;
    let ready <- Ws.wait_ready tp 0i64;
    match ready {
        Result.err e => IO.pure (Result.err e),
        Result.ok is_ready =>
            if Bool.not is_ready then IO.pure (Result.ok unit)
            else do {
                let r <- Ws.read_chunk tp;
                match r {
                    Result.err e => IO.pure (Result.err e),
                    Result.ok bytes => Ws.feed c bytes
                }
            }
    }
}

/// Take queued units, oldest first.
def Ws.take_pending (c : WsConn) : IO (List WsInbound) := do {
    let queued <- Ref.get c.pending;
    let _ <- Ref.set c.pending List.empty;
    IO.pure queued
}

/// Every unit readable now: the queue plus one non-blocking read. This is
/// the per-frame poll a game loop wants — `ok []` when nothing arrived.
pub def Ws.drain (c : WsConn) : IO (Result WsError (List WsInbound)) := do {
    let r <- Ws.fill c;
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok _ => do {
            let units <- Ws.take_pending c;
            let r2 <- Ws.handle_controls c units;
            match r2 {
                Result.err e => IO.pure (Result.err e),
                Result.ok kept => IO.pure (Result.ok kept)
            }
        }
    }
}

/// Answer pings and finish a close among `units`, keeping only data
/// messages and the close that ended the session.
def Ws.handle_controls (c : WsConn) (units : List WsInbound) : IO (Result WsError (List WsInbound)) := do {
    match units {
        List.empty => IO.pure (Result.ok List.empty),
        List.cons u rest => match u {
            WsInbound.ping payload => do {
                let _ <- Ws.write_frame c (Ws.control_frame WsOpcode.pong payload);
                Ws.handle_controls c rest
            },
            WsInbound.pong _ => Ws.handle_controls c rest,
            WsInbound.close cl => do {
                let _ <- Ws.finish_close c cl;
                IO.pure (Result.err (WsError.closed cl))
            },
            WsInbound.message m => do {
                let r <- Ws.handle_controls c rest;
                match r {
                    Result.err e => IO.pure (Result.err e),
                    Result.ok kept => IO.pure (Result.ok (List.cons (WsInbound.message m) kept))
                }
            }
        }
    }
}

/// Read one message, waiting as long as the session's timeouts allow:
/// pings go out while the peer is quiet, and `idle_timeout_ms` without a
/// byte closes the connection.
pub def Ws.recv (c : WsConn) : IO (Result WsError WsMessage) :=
    Ws.recv_loop c 0i64

#[terminating]
def Ws.recv_loop (c : WsConn) (quiet_ms : I64) : IO (Result WsError WsMessage) := do {
    let r <- Ws.drain c;
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok units => match units {
            List.cons u rest => do {
                let _ <- Ref.set c.pending rest;
                match u {
                    WsInbound.message m => IO.pure (Result.ok m),
                    _ => Ws.recv_loop c 0i64
                }
            },
            List.empty =>
                if I64.gt quiet_ms c.cfg.idle_timeout_ms then do {
                    let _ <- Ws.close c Ws.close_going_away "idle";
                    IO.pure (Result.err (WsError.transport "peer idle past the timeout"))
                }
                else do {
                    let tp <- Ref.get c.t;
                    let ready <- Ws.wait_ready tp c.cfg.poll_ms;
                    match ready {
                        Result.err e => IO.pure (Result.err e),
                        Result.ok is_ready =>
                            if is_ready then Ws.recv_loop c 0i64
                            else do {
                                let quiet := I64.add quiet_ms c.cfg.poll_ms;
                                let _ <- (if I64.gt quiet c.cfg.ping_interval_ms then Ws.ping c
                                    else IO.pure (Result.ok unit));
                                Ws.recv_loop c quiet
                            }
                    }
                }
        }
    }
}

/// `Ws.recv` with a bound: `ok none` when nothing arrived in `ms`. Use this
/// when one fiber must both read and write.
#[terminating] // each turn takes one unit or returns "none"
pub def Ws.recv_timeout (c : WsConn) (ms : I64) : IO (Result WsError (Option WsMessage)) := do {
    let r <- Ws.drain c;
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok units => match units {
            List.cons u rest => do {
                let _ <- Ref.set c.pending rest;
                match u {
                    WsInbound.message m => IO.pure (Result.ok (Option.some m)),
                    _ => Ws.recv_timeout c 0i64
                }
            },
            List.empty => do {
                let tp <- Ref.get c.t;
                let ready <- Ws.wait_ready tp ms;
                match ready {
                    Result.err e => IO.pure (Result.err e),
                    Result.ok is_ready =>
                        if Bool.not is_ready then IO.pure (Result.ok Option.none)
                        else do {
                            let f <- Ws.fill c;
                            match f {
                                Result.err e => IO.pure (Result.err e),
                                Result.ok _ => Ws.recv_timeout c 0i64
                            }
                        }
                }
            }
        }
    }
}

/// The session's transport.
pub def Ws.transport (c : WsConn) : IO Transport :=
    Ref.get c.t

/// Close the underlying socket (idempotent at the OS level).
def Ws.close_raw (c : WsConn) : IO Unit := do {
    let tp <- Ref.get c.t;
    Transport.close tp
}

/// The transport, for internal synchronous reads.
def Ws.transport_of (c : WsConn) : IO Transport :=
    Ref.get c.t
