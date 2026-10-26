// Oak-level event fixture: typed handlers, drag-and-drop and clipboard,
// all declarative in the view and pure in update.
//
// `wasm/web/oak_event_smoke.mjs` drives it over a stub DOM: it checks the
// lowered `data-oak-on-*` attributes, the drag payload/effect and drop
// effect, the drop/paste payloads reaching update, and the sync copy path.
#![mote { name := "oak_events", deps := [oak, oak_wasm, web_event, web_wasm] }]

use web_event::event {WebEvent}
use oak::typed {Oak.Node}
use oak::elements {Html.div, Html.draggable, Html.id_, Html.input, Html.span, Html.text}
use oak::events {
    Html.copy_text, Html.drag_effect, Html.drag_payload, Html.drop_effect,
    Html.on_copy_msg, Html.on_dragstart_msg, Html.on_dragover, Html.on_drop, Html.on_input,
    Html.on_paste,
}
use oak::app {Command, Host, Program}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}

struct Model {
    payload : String := "payload",
    text : String := "hello",
    dropped : String := "",
    pasted : String := ""
}

type Msg {
    started,
    over,
    copied,
    dropped (text : String),
    set_text (text : String),
    pasted (text : String),
}

def init : Model :=
    let m : Model := { payload := "payload", text := "hello" } in m

def update (m : Model) (msg : Msg) : Pair Model (Command Unit Msg) :=
    match msg {
        Msg.started => Pair.pair m Command.none,
        Msg.over => Pair.pair m Command.none,
        Msg.copied => Pair.pair m Command.none,
        Msg.dropped s => Pair.pair { m with dropped := s } Command.none,
        Msg.set_text s => Pair.pair { m with text := s } Command.none,
        Msg.pasted s => Pair.pair { m with pasted := s } Command.none,
    }

def input_msg (s : String) : Msg := Msg.set_text s

def drop_msg (e : WebEvent) : Msg := Msg.dropped e.data

def paste_msg (e : WebEvent) : Msg := Msg.pasted e.data

def state_text (m : Model) : String :=
    String.concat m.dropped
        (String.concat "/" (String.concat m.text (String.concat "/" m.pasted)))

def view (m : Model) : Oak.Node Msg :=
    let source : Oak.Node Msg :=
        Html.div
            [ Html.id_ "source",
              Html.draggable true,
              Html.drag_payload "text/plain" m.payload,
              Html.drag_effect "copy",
              Html.on_dragstart_msg Msg.started ]
            [Html.text "src"] in
    let target : Oak.Node Msg :=
        Html.div
            [ Html.id_ "target",
              Html.on_dragover Msg.over,
              Html.drop_effect "copy",
              Html.on_drop drop_msg ]
            [Html.text m.dropped] in
    let field : Oak.Node Msg :=
        Html.input [Html.id_ "field", Html.on_input input_msg] in
    let copier : Oak.Node Msg :=
        Html.div
            [Html.id_ "copier", Html.copy_text m.text, Html.on_copy_msg Msg.copied]
            [Html.text m.text] in
    let paster : Oak.Node Msg :=
        Html.div [Html.id_ "paster", Html.on_paste paste_msg] [Html.text m.pasted] in
    let state : Oak.Node Msg :=
        Html.span [Html.id_ "state"] [Html.text (state_text m)] in
    Html.div [Html.id_ "app"] [source, target, field, copier, paster, state]

def app : Program Model Msg Unit := Program.app init update view

def host : Host IO Unit Msg := Host.host (fn _effect => IO.pure Option.none)

#[export "c"]
def oak_mount : IO Unit := Runtime.mount app

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

def main : IO Unit := IO.pure unit
