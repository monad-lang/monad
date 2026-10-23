// A two-message Oak SPA: the smallest program that mounts, dispatches from
// a DOM event, ticks, and patches.
//
// The three `#[export "c"]` thunks are the app's half of the ABI: the
// generated loader calls `oak_mount` once, `oak_dispatch_event(id)` from a
// DOM listener, and `oak_tick` once per animation frame. `oak_wasm` owns the
// runtime; the app owns the message type and its decoder.
//
// View handlers are `data-oak-on-<event>` attributes carrying a message id;
// `oak_wasm.Patch` registers the listener instead of setting the attribute.
//
// `scripts/check-wasm-target.sh` builds this for the web profile and
// `wasm/web/spa_smoke.mjs` drives it over a stub DOM.
#![mote { name := "oak_spa", deps := [oak, oak_wasm, web_wasm, xml_html] }]

use xml_html::html {Html.Node}
use oak::elements {Html.attr, Html.button, Html.div, Html.span, Html.text}
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

def view (model : I64) : Html.Node :=
    let counter : Html.Node :=
        Html.span [Html.attr "id" "count"] [Html.text (I64.to_string model)] in
    let add : Html.Node :=
        Html.button [Html.attr "data-oak-on-click" "1"] [Html.text "add"] in
    let clear : Html.Node :=
        Html.button [Html.attr "data-oak-on-click" "2"] [Html.text "reset"] in
    let root : Html.Node :=
        Html.div [Html.attr "class" "counter"] [add, clear, counter] in
    root

def app : Program I64 Msg Unit := Program.app init update view

def decode (handler : I64) : Option Msg :=
    if handler == 1i64 then Option.some Msg.increment
    else if handler == 2i64 then Option.some Msg.reset
    else Option.none

/// The SPA has no effects; a host that produces no messages is enough.
def host : Host IO Unit Msg := Host.host (fn _effect => IO.pure Option.none)

#[export "c"]
def oak_mount : IO Unit := Runtime.mount init view

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch decode handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

def main : IO Unit := IO.pure unit
