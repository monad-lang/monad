// WebSocket fixture: the oak `Subscription.websocket` and the imperative
// `web_wasm` socket.
//
// `wasm/web/smoke/websocket_smoke.mjs` installs a fake `WebSocket` class and
// then checks: the subscription opened the socket with its protocol list,
// each queued event reached `update` (opened sends a message through
// `Command.ws_send`, a message and a close each bump the model), and the
// imperative path drains a text frame and sends a binary reply.
#![mote { name := "oak_socket", deps := [oak, oak_wasm, web_wasm, web_event] }]

use oak::typed {Oak.Node}
use oak::elements {Html.div, Html.id_, Html.span, Html.text}
use oak::app {Command, Host, Program}
use oak::events {Subscription}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}
use web_wasm::websocket {WebSocket.connect, WebSocket.drain, WebSocket.send, WebSocket.close}
use web_event::websocket {WsData, WsEvent, WsData.text_of}
use web_wasm::console {Console.log}

type Msg {
    ws (ev : WsEvent),
}

def init : I64 := 0i64

def bump (ev : WsEvent) : I64 :=
    match ev {
        WsEvent.opened _protocol => 1i64,
        WsEvent.message _d => 10i64,
        WsEvent.closed _code _reason _clean => 100i64,
        WsEvent.failed => 1000i64,
    }

def update (m : I64) (msg : Msg) : Pair I64 (Command Unit Msg) :=
    match msg {
        Msg.ws ev =>
            match ev {
                WsEvent.opened protocol =>
                    let sent := WsData.text (String.concat "hello " protocol) in
                    Pair.pair (m + bump ev) (Command.ws_send "ws://example.test/game" sent),
                _ => Pair.pair (m + bump ev) Command.none,
            },
    }

def subs (_m : I64) : List (Subscription Msg) :=
    [Subscription.websocket "ws://example.test/game" ["v1"] (fn (ev : WsEvent) => Msg.ws ev)]

def view (m : I64) : Oak.Node Msg :=
    Html.div [Html.id_ "app"] [Html.span [Html.id_ "count"] [Html.text (I64.to_string m)]]

def app : Program I64 Msg Unit := Program.with_subs init update view subs

def host : Host IO Unit Msg := Host.host (fn _effect => IO.pure Option.none)

#[export "c"]
def oak_mount : IO Unit := Runtime.mount app

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

// ── the imperative API, driven directly by the smoke test ──────────────
//
// One socket per call: the fake host opens it, queues a text frame, and
// this drains it, sends a binary reply and closes. The wasm export returns
// what it saw so the harness can assert on it.

def first_text_len (events : List WsEvent) : I64 :=
    match events {
        List.empty => -1i64,
        List.cons e rest =>
            match e {
                WsEvent.message d => String.length (WsData.text_of d),
                _ => first_text_len rest,
            }
    }

#[export "c"]
def imp_probe : IO Unit := do {
    let ws <- WebSocket.connect "ws://example.test/raw" [];
    let events <- WebSocket.drain ws;
    Console.log (String.concat "imp:len=" (I64.to_string (first_text_len events)));
    let _ <- WebSocket.send ws (WsData.binary [1u8, 2u8, 3u8]);
    let _ <- WebSocket.close ws 1000i64 "done";
    IO.pure unit
}
