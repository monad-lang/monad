// Subscription fixture: window resize, document visibility and the
// animation-frame hook, all declared purely by `Program.with_subs`.
//
// `wasm/web/subs_smoke.mjs` drives it over the stub DOM: it checks the
// listeners were registered from the model, that each fires into update, and
// that the loader's animation-frame loop dispatches the frame message.
#![mote { name := "oak_subs", deps := [oak, oak_wasm, web_wasm, web_event] }]

use oak::typed {Oak.Node}
use oak::elements {Html.div, Html.id_, Html.span, Html.text}
use web_event::event {WebEvent}
use oak::events {Subscription}
use oak::app {Command, Host, Program}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}

type Msg {
    resized,
    hidden,
    frame (stamp : F64),
}

def init : I64 := 0i64

def update (m : I64) (msg : Msg) : Pair I64 (Command Unit Msg) :=
    match msg {
        Msg.resized => Pair.pair (m + 1i64) Command.none,
        Msg.hidden => Pair.pair (m + 10i64) Command.none,
        Msg.frame stamp =>
            if F64.gt stamp 0.0
            then Pair.pair (m + 100i64) Command.none
            else Pair.pair m Command.none,
    }

def subs (_m : I64) : List (Subscription Msg) :=
    [ Subscription.window_msg "resize" Msg.resized,
      Subscription.document_msg "visibilitychange" Msg.hidden,
      Subscription.animation_frame (fn (e : WebEvent) => Msg.frame e.time_stamp) ]

def view (m : I64) : Oak.Node Msg :=
    Html.div [Html.id_ "app"]
        [Html.span [Html.id_ "count"] [Html.text (I64.to_string m)]]

def app : Program I64 Msg Unit := Program.with_subs init update view subs

def host : Host IO Unit Msg := Host.host (fn _effect => IO.pure Option.none)

#[export "c"]
def oak_mount : IO Unit := Runtime.mount app

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

def main : IO Unit := IO.pure unit
