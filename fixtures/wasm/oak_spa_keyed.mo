// A keyed-list Oak SPA: reorder, insert, and delete keep DOM node identity.
//
// `wasm/web/keyed_spa_smoke.mjs` drives it over a stub DOM and asserts the
// SAME `li` objects survive a reorder (not freshly mounted copies), that a
// moved item keeps its click listener, that an insert mounts exactly one new
// element, and that a deleted item is detached.
//
// The `ul` sits at [0, 0], so its children are at [0, 0, i] -- keyed
// reconciliation composes with the same absolute-path model as the rest of
// `Patch`.
//
// A FIXTURE, not an `examples/` program: the Rust host's multi-target
// `check` resolves bare top-level names across every target in one scope, so
// an example that imports `Command` (and declares `Msg`) collides with
// `motes/monadup`'s own `Command` and `motes/oak`'s `Msg` type parameter.
#![mote { name := "oak_spa_keyed", deps := [oak, oak_wasm, web_wasm, xml_html] }]

use std::list {List.length}
use oak::typed {Oak.Node}
use oak::elements {Html.attr, Html.button, Html.div, Html.key, Html.li, Html.text, Html.ul}
use oak::events {Html.on_click}
use oak::app {Command, Host, Program}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}

type Msg {
    reverse,
    add,
    drop,
}

def init : List String := ["a", "b", "c"]

def update (model : List String) (msg : Msg) : Pair (List String) (Command Unit Msg) :=
    match msg {
        Msg.reverse => Pair.pair (List.reverse model) Command.none,
        Msg.add =>
            Pair.pair
                (List.append model
                    (List.cons (String.concat "item" (I64.to_string (List.length model))) List.empty))
                Command.none,
        Msg.drop => Pair.pair (List.tail model) Command.none,
    }

/// Every item is a clickable keyed `<li>`; a listener that survives a move
/// still dispatches.
def item_view (k : String) : Oak.Node Msg :=
    Html.li [Html.key k, Html.on_click Msg.reverse] [Html.text k]

def view (items : List String) : Oak.Node Msg :=
    let list : Oak.Node Msg :=
        Html.ul [Html.attr "id" "items"] (List.map item_view items) in
    let add : Oak.Node Msg :=
        Html.button [Html.on_click Msg.add] [Html.text "add"] in
    let drop : Oak.Node Msg :=
        Html.button [Html.on_click Msg.drop] [Html.text "drop"] in
    Html.div [Html.attr "class" "app"] [list, Html.div List.empty [add, drop]]

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
