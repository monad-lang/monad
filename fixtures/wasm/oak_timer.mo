// `Command.batch`, `Command.after` (one-shot timer) and `Command.focus`.
//
// The click returns a batch: schedule `later` in 10 ms, dispatch `now` into
// this batch, and focus an input after the patch. `wasm/web/timer_smoke.mjs`
// asserts the immediate message, the post-patch focus, and the delayed
// message after the host timer fires -- with no animation-frame loop.
#![mote { name := "oak_timer", deps := [oak, oak_wasm, web_wasm, web_event] }]

use oak::typed {Oak.Node}
use oak::elements {Html.div, Html.span, Html.button, Html.input, Html.id_, Html.text}
use oak::events {Html.on_click}
use oak::app {Command, Host, Program}
use oak_wasm::program {Runtime.mount, Runtime.dispatch, Runtime.tick}

type Msg {
    go,
    now,
    later,
}

def init : I64 := 0i64

def update (m : I64) (msg : Msg) : Pair I64 (Command Unit Msg) :=
    match msg {
        Msg.go => Pair.pair m (Command.batch [
            Command.after 10i64 Msg.later,
            Command.dispatch Msg.now,
            Command.focus "#target",
        ]),
        Msg.now => Pair.pair (m + 1i64) Command.none,
        Msg.later => Pair.pair (m + 10i64) Command.none,
    }

def view (m : I64) : Oak.Node Msg :=
    Html.div [Html.id_ "app"]
        [Html.span [Html.id_ "count"] [Html.text (I64.to_string m)],
            Html.input [Html.id_ "target"],
            Html.button [Html.id_ "go", Html.on_click Msg.go] [Html.text "go"]]

def app : Program I64 Msg Unit := Program.app init update view

def host : Host IO Unit Msg := Host.host (fn _effect => IO.pure Option.none)

#[export "c"]
def oak_mount : IO Unit := Runtime.mount app

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

def main : IO Unit := IO.pure unit
