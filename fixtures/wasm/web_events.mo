// Low-level event transport fixture: no oak, just `web_wasm`.
//
// `setup` mounts a probe and registers one listener per event family with a
// hex handler id. `ev_report` is what the listeners call: it snapshots the
// live event into `web_event::WebEvent`, writes the interesting fields into
// `#report`, and applies preventDefault/stopPropagation for the ids that ask
// for them. `wasm/web/event_smoke.mjs` drives it over a stub DOM.
#![mote { name := "web_events", deps := [web_event, web_wasm] }]

use std::list {List.intercalate, List.length}
use std::ref {Ref, Ref.get}
use web_event::event {WebEvent}
use web_wasm::dom {Dom.append, Dom.create, Dom.on_with, Dom.query, Dom.root, Dom.set_attr, Dom.set_text}
use web_wasm::event {WebEvent.current, WebEvent.prevent_default, WebEvent.stop_propagation}
use web_wasm::clipboard {
    Clipboard.read_begin, Clipboard.write_begin, Clipboard.read_result, Clipboard.write_result,
}
use web_wasm::keep {Keep.load, Keep.save}
use web_wasm::types {ClipboardOp}

def report (e : WebEvent) : String :=
    List.intercalate "|" [
        e.kind,
        F64.to_string e.client_x,
        F64.to_string e.client_y,
        I64.to_string e.modifiers,
        e.key,
        e.code,
        e.value,
        e.data,
        I64.to_string (List.length e.data_types),
        I64.to_string (List.length e.files),
        if e.repeat then "1" else "0",
        e.effect_allowed,
        e.drop_effect,
        I64.to_string e.detail,
        I64.to_string e.pointer_id,
        F64.to_string e.pressure,
        F64.to_string e.delta_x,
        F64.to_string e.delta_y,
        I64.to_string e.delta_mode,
        F64.to_string e.time_stamp,
        if e.checked then "1" else "0",
        I64.to_string e.location,
        if e.is_primary then "1" else "0"
    ]

#[export "c"]
def setup : IO Unit := do {
    let root <- Dom.root;
    let probe <- Dom.create "div";
    let _ <- Dom.set_attr probe "id" "probe";
    let _ <- Dom.append root probe;
    let out <- Dom.create "pre";
    let _ <- Dom.set_attr out "id" "report";
    let _ <- Dom.append root out;
    // ids are hex; the `d` flag prevents default before dispatch.
    let _ <- Dom.on_with probe "pointerdown" "0x1";
    let _ <- Dom.on_with probe "keydown" "0x2";
    let _ <- Dom.on_with probe "input" "0x3";
    let _ <- Dom.on_with probe "dragover" "0x4:d";
    let _ <- Dom.on_with probe "dragstart" "0x5";
    let _ <- Dom.on_with probe "drop" "0x6:d";
    let _ <- Dom.on_with probe "paste" "0x7";
    let _ <- Dom.on_with probe "custom" "0x8:cpso";
    let _ <- Dom.on_with probe "wheel" "0x9";
    return unit
}

def read_text (r : Result String (Option String)) : String :=
    match r {
        Result.ok maybe => read_text_some maybe,
        Result.err name => String.concat "err:" name,
    }

def read_text_some (m : Option String) : String :=
    match m {
        Option.some text => String.concat "ok:" text,
        Option.none => "pending",
    }

def write_text (r : Result String Bool) : String :=
    match r {
        Result.ok done => if done then "ok" else "pending",
        Result.err name => String.concat "err:" name,
    }

#[export "c"]
def clipboard_read_begin_test : IO Unit := do {
    let op <- Clipboard.read_begin;
    let cell : Ref ClipboardOp <- Ref.new op;
    let _ <- Keep.save cell;
    let out <- Dom.query "#report";
    Dom.set_text out "pending"
}

#[export "c"]
def clipboard_read_finish_test : IO Unit := do {
    let cell : Ref ClipboardOp <- Keep.load;
    let op <- Ref.get cell;
    let result <- Clipboard.read_result op;
    let out <- Dom.query "#report";
    Dom.set_text out (read_text result)
}

#[export "c"]
def clipboard_write_begin_test : IO Unit := do {
    let op <- Clipboard.write_begin "written";
    let cell : Ref ClipboardOp <- Ref.new op;
    let _ <- Keep.save cell;
    let out <- Dom.query "#report";
    Dom.set_text out "pending"
}

#[export "c"]
def clipboard_write_finish_test : IO Unit := do {
    let cell : Ref ClipboardOp <- Keep.load;
    let op <- Ref.get cell;
    let result <- Clipboard.write_result op;
    let out <- Dom.query "#report";
    Dom.set_text out (write_text result)
}

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := do {
    let e <- WebEvent.current;
    let _ <- if I64.beq handler 9i64 then WebEvent.prevent_default else IO.pure unit;
    let _ <- if I64.beq handler 10i64 then WebEvent.stop_propagation else IO.pure unit;
    let out <- Dom.query "#report";
    Dom.set_text out (String.concat (report e) (String.concat "|" (I64.to_string handler)))
}

def main : IO Unit := IO.pure unit
