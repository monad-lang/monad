// A 256-button view with two handlers per cell: the allocation benchmark for
// the render path. `wasm/web/oak_alloc_smoke.mjs` mounts it, fires one
// click, ticks once, and asserts the committed-memory delta stays below a
// generous ceiling (the pre-fix path measured ~3 MB per render).
#![mote { name := "oak_spa_alloc", deps := [oak, oak_wasm, web_wasm, web_event] }]

use oak::typed {Oak.Node}
use oak::elements {Html.div, Html.button, Html.id_, Html.text}
use oak::events {Html.on_click, Html.on_pointerenter}
use oak::app {Command, Host, Program}
use oak_wasm::program {Runtime.mount, Runtime.dispatch, Runtime.tick}

type Msg {
    tap,
    hover,
}

def init : I64 := 0i64

def update (m : I64) (msg : Msg) : Pair I64 (Command Unit Msg) :=
    match msg {
        Msg.tap => Pair.pair (m + 1i64) Command.none,
        Msg.hover => Pair.pair m Command.none,
    }

#[terminating]
def cells_from (i : I64) (n : I64) (acc : List (Oak.Node Msg)) : List (Oak.Node Msg) :=
    if I64.lt i n
    then
        let cell : Oak.Node Msg :=
            Html.button
                [Html.id_ (String.concat "c" (I64.to_string i)),
                    Html.on_click Msg.tap,
                    Html.on_pointerenter Msg.hover]
                [Html.text "x"] in
        cells_from (i + 1i64) n (List.cons cell acc)
    else List.reverse acc

def view (m : I64) : Oak.Node Msg :=
    Html.div [Html.id_ "app"]
        [Html.text (I64.to_string m),
            Html.div [Html.id_ "board"] (cells_from 0i64 256i64 List.empty)]

def app : Program I64 Msg Unit := Program.app init update view

def host : Host IO Unit Msg := Host.host (fn _effect => IO.pure Option.none)

#[export "c"]
def oak_mount : IO Unit := Runtime.mount app

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

def main : IO Unit := IO.pure unit
