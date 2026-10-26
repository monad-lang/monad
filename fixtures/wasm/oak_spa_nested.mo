// A two-message Oak SPA whose dynamic list is nested one wrapper deep.
//
// Regression fixture for `Patch.drop_last`: the task list sits at patch path
// [0, 0, 1] (container -> root div -> wrapper div -> ul), so replacing it
// exercises a path longer than the depth-2 shapes the older smoke test
// produced. `wasm/web/nested_spa_smoke.mjs` drives it over a stub DOM.
//
// The wrapper exists on purpose: with the buggy drop_last, a replace at
// [0, 0, 1] resolves to the root div and replaces its child 1 -- the footer
// -- so the list never updates and the footer disappears. The smoke test
// asserts both survive.
//
// A FIXTURE, not an `examples/` program: the Rust host's multi-target
// `check` resolves bare top-level names across every target in one scope, so
// an example that imports `Command` (and declares `Msg`) collides with
// `motes/monadup`'s own `Command` and `motes/oak`'s `Msg` type parameter.
#![mote { name := "oak_spa_nested", deps := [oak, oak_wasm, web_wasm, xml_html] }]

use oak::typed {Oak.Node}
use oak::elements {
  Html.attr, Html.button, Html.div, Html.footer, Html.li, Html.p, Html.text, Html.ul,
}
use oak::events {Html.on_click}
use oak::app {Command, Host, Program}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}

type Msg {
    add,
    clear,
}

def init : List String := List.empty

def update (model : List String) (msg : Msg) : Pair (List String) (Command Unit Msg) :=
    match msg {
        Msg.add => Pair.pair (List.append model (List.cons "item" List.empty)) Command.none,
        Msg.clear => Pair.pair List.empty Command.none,
    }

def item_view (label : String) : Oak.Node Msg :=
    Html.li List.empty [Html.text label]

def view (items : List String) : Oak.Node Msg :=
    let list : Oak.Node Msg :=
        Html.ul [Html.attr "id" "items"] (List.map item_view items) in
    let wrapper : Oak.Node Msg :=
        Html.div List.empty [Html.p List.empty [Html.text "nested"], list] in
    let add : Oak.Node Msg :=
        Html.button [Html.on_click Msg.add] [Html.text "add"] in
    let clear : Oak.Node Msg :=
        Html.button [Html.on_click Msg.clear] [Html.text "clear"] in
    let footer : Oak.Node Msg := Html.footer List.empty [add, clear] in
    Html.div [Html.attr "class" "app"] [wrapper, footer]

def app : Program (List String) Msg Unit := Program.app init update view

/// The SPA has no effects; a host that produces no messages is enough.
def host : Host IO Unit Msg := Host.host (fn _effect => IO.pure Option.none)

#[export "c"]
def oak_mount : IO Unit := Runtime.mount app

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

def main : IO Unit := IO.pure unit
