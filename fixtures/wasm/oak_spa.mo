// A two-message Oak SPA: the smallest program that mounts, dispatches from
// a DOM event, ticks, and patches.
//
// The three `#[export "c"]` thunks are the app's half of the ABI: the
// generated loader calls `oak_mount` once, `oak_dispatch_event(id)` from a
// DOM listener, and `oak_tick` once per animation frame. `oak_wasm` owns the
// runtime; the app owns the message type and binds handlers directly in the
// view (`Html.on_click Msg.increment`), with no decoder.
//
// `scripts/check-wasm-target.sh` builds this for the web profile and
// `wasm/web/spa_smoke.mjs` drives it over a stub DOM.
//
// A FIXTURE, not an `examples/` program: the Rust host's multi-target
// `check` resolves bare top-level names across every target in one scope,
// so an example that imports `Command` (and declares `Msg`) collides with
// `motes/monadup`'s own `Command` and `motes/oak`'s `Msg` type parameter.
// `fixtures/` is not swept by the whole-corpus check; the polished example
// waits on that host scoping fix.
#![mote { name := "oak_spa", deps := [oak, oak_wasm, web_wasm, xml_html] }]

use oak::typed {Oak.Node}
use oak::elements {Html.attr, Html.button, Html.div, Html.span, Html.text}
use oak::events {Html.on_click}
use oak::app {Command, Host, Program}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}

type Msg {
    increment,
    reset,
}

def init : I64 := 0i64

def update (model : I64) (msg : Msg) : Pair I64 (Command Unit Msg) :=
    match msg {
        Msg.increment => Pair.pair (model + 1i64) Command.none,
        Msg.reset => Pair.pair 0i64 Command.none,
    }

def view (model : I64) : Oak.Node Msg :=
    let counter : Oak.Node Msg :=
        Html.span [Html.attr "id" "count"] [Html.text (I64.to_string model)] in
    let add : Oak.Node Msg :=
        Html.button [Html.on_click Msg.increment] [Html.text "add"] in
    let clear : Oak.Node Msg :=
        Html.button [Html.on_click Msg.reset] [Html.text "reset"] in
    let root : Oak.Node Msg :=
        Html.div [Html.attr "class" "counter"] [add, clear, counter] in
    root

def app : Program I64 Msg Unit := Program.app init update view

/// The SPA has no effects; a host that produces no messages is enough.
def host : Host IO Unit Msg := Host.host (fn _effect => IO.pure Option.none)

#[export "c"]
def oak_mount : IO Unit := Runtime.mount app

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

def main : IO Unit := IO.pure unit
