/// The browser `WebSocket`, imperative and per-frame friendly.
///
/// The JS callbacks never re-enter wasm: they append to the socket's queue,
/// and wasm drains it (`next` one entry, `drain` all of them). `watch` asks
/// the host to wake the app with an `oak_dispatch_event` id from a fresh
/// task when the queue gains entries, which is how `Subscription.websocket`
/// runs without polling.
///
/// Payloads cross as bytes in a caller-owned `ByteBuf`, so a message larger
/// than the 64 KiB scratch string is not truncated; text is its UTF-8.
/// Forge drives `drain` once per frame; oak uses `watch`.

use std::bytebuf {ByteBuf, ByteBuf.alloc, ByteBuf.free, ByteBuf.length, ByteBuf.of_list, ByteBuf.to_list}
use std::list {}
use lib::ffi {
    ws_open_raw, ws_state_raw, ws_peek_raw, ws_read_raw, ws_info_raw, ws_text_raw,
    ws_send_raw, ws_close_raw, ws_watch_raw, ws_unwatch_raw, ws_buffered_raw, ws_free_raw,
}
use lib::types {WebSocket}
use web_event::websocket {WsData, WsEvent}

/// Open `url` with the subprotocols `protocols` (joined with `,`) and
/// return at once: the connection completes in the background and its
/// `WsEvent.opened` (or `failed`) arrives through the queue.
pub def WebSocket.connect (url : String) (protocols : List String) : IO WebSocket := do {
    let joined := WebSocket.join_comma protocols;
    let id <- IO.mk (ws_open_raw url joined);
    IO.pure id
}

#[terminating]
def WebSocket.join_comma (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x rest => WebSocket.join_comma_tail x (WebSocket.join_comma rest)
    }

def WebSocket.join_comma_tail (x : String) (tail : String) : String :=
    if String.beq tail "" then x else String.concat x (String.concat "," tail)

/// `0` connecting, `1` open, `2` closing, `3` closed, `-1` unknown.
pub def WebSocket.state (w : WebSocket) : IO I64 := IO.mk (ws_state_raw w)

/// Close with `code` and `reason` (1000 for a normal close).
pub def WebSocket.close (w : WebSocket) (code : I64) (reason : String) : IO Unit := do {
    let _ <- IO.mk (ws_close_raw w code reason);
    IO.pure unit
}

/// Forget the socket and release its queue (closing it first if needed).
pub def WebSocket.free (w : WebSocket) : IO Unit := do {
    let _ <- IO.mk (ws_free_raw w);
    IO.pure unit
}

/// The queued entries not yet read.
pub def WebSocket.pending (w : WebSocket) : IO I64 := IO.mk (ws_buffered_raw w)

/// Send one message; `Err` when the socket is not open.
pub def WebSocket.send (w : WebSocket) (d : WsData) : IO (Result String Unit) :=
    match d {
        WsData.text s => WebSocket.send_bytes w (String.to_list s) 0i64,
        WsData.binary b => WebSocket.send_bytes w b 1i64
    }

/// Send raw bytes (`is_binary` 0 sends them as the UTF-8 text they are).
pub def WebSocket.send_bytes (w : WebSocket) (bytes : List U8) (is_binary : I64) : IO (Result String Unit) := do {
    let buf <- ByteBuf.of_list bytes;
    let sb := Shared.of buf;
    let ok <- IO.mk (ws_send_raw w (Shared.get sb) is_binary);
    let _ <- ByteBuf.free buf;
    if I64.beq ok 0i64
    then IO.pure (Result.err "websocket is not open")
    else IO.pure (Result.ok unit)
}

/// The queue's next event, `none` when it is empty.
pub def WebSocket.next (w : WebSocket) : IO (Option WsEvent) := do {
    let kind <- IO.mk (ws_peek_raw w 1i64);
    if I64.beq kind 0i64 then IO.pure Option.none
    else if I64.beq kind 1i64 then do {
        let _ <- WebSocket.skip_empty w;
        let protocol <- IO.mk (ws_text_raw w 0i64);
        IO.pure (Option.some (WsEvent.opened protocol))
    }
    else if I64.beq kind 2i64 then do {
        let bytes <- WebSocket.read_bytes w;
        IO.pure (Option.some (WsEvent.message (WsData.text (String.from_list bytes))))
    }
    else if I64.beq kind 3i64 then do {
        let bytes <- WebSocket.read_bytes w;
        IO.pure (Option.some (WsEvent.message (WsData.binary bytes)))
    }
    else if I64.beq kind 4i64 then do {
        let _ <- WebSocket.skip_empty w;
        let code <- IO.mk (ws_info_raw w 0i64);
        let clean <- IO.mk (ws_info_raw w 1i64);
        let reason <- IO.mk (ws_text_raw w 1i64);
        IO.pure (Option.some (WsEvent.closed code reason (I64.beq clean 1i64)))
    }
    else do {
        let _ <- WebSocket.skip_empty w;
        IO.pure (Option.some WsEvent.failed)
    }
}

/// Read the head entry's payload and pop it.
def WebSocket.read_bytes (w : WebSocket) : IO (List U8) := do {
    let n <- IO.mk (ws_peek_raw w 2i64);
    if Bool.not (I64.gt n 0i64) then do {
        let _ <- WebSocket.pop w;
        IO.pure List.empty
    }
    else do {
        let buf <- ByteBuf.alloc n;
        let sb := Shared.of buf;
        let _ <- IO.mk (ws_read_raw w (Shared.get sb));
        let bytes <- ByteBuf.to_list (Shared.get sb) n;
        let _ <- ByteBuf.free buf;
        IO.pure bytes
    }
}

/// Pop a queue entry that carries no payload; `ws_read` does the popping.
def WebSocket.skip_empty (w : WebSocket) : IO Unit :=
    WebSocket.pop w

def WebSocket.pop (w : WebSocket) : IO Unit := do {
    let buf <- ByteBuf.alloc 1i64;
    let sb := Shared.of buf;
    let _ <- IO.mk (ws_read_raw w (Shared.get sb));
    ByteBuf.free buf
}

/// Every queued event, oldest first — the per-frame poll a game loop wants.
#[terminating]
pub def WebSocket.drain (w : WebSocket) : IO (List WsEvent) := do {
    let e <- WebSocket.next w;
    match e {
        Option.none => IO.pure List.empty,
        Option.some ev => do {
            let rest <- WebSocket.drain w;
            IO.pure (List.cons ev rest)
        }
    }
}

/// Have the host dispatch `handler` (an oak handler id) when the queue
/// gains entries. One dispatch drains everything queued.
pub def WebSocket.watch (w : WebSocket) (handler : U32) : IO Unit := do {
    let _ <- IO.mk (ws_watch_raw w handler);
    IO.pure unit
}

/// Stop the wake-ups (the queue keeps filling).
pub def WebSocket.unwatch (w : WebSocket) : IO Unit := do {
    let _ <- IO.mk (ws_unwatch_raw w);
    IO.pure unit
}
