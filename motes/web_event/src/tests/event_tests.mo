/// Pure tests for the event vocabulary. No browser needed.

use lib::event {WebEvent, ListenerFlags, HandlerResult}

#[test]
def test_flags_none_encodes_empty : Bool :=
    String.beq (ListenerFlags.encode ListenerFlags.none) ""

#[test]
def test_flags_encode_all_in_canonical_order : Bool :=
    let f : ListenerFlags :=
        { capture := true, prevent_default := true, stop_propagation := true,
          once := true, passive := true } in
    String.beq (ListenerFlags.encode f) ":cdsop"

#[test]
def test_flags_encode_subset : Bool :=
    let f : ListenerFlags := { prevent_default := true, once := true } in
    String.beq (ListenerFlags.encode f) ":do"

#[test]
def test_modifiers : Bool :=
    let shift : WebEvent := { modifiers := 1i64 } in
    let ctrl : WebEvent := { modifiers := 2i64 } in
    let alt : WebEvent := { modifiers := 4i64 } in
    let meta : WebEvent := { modifiers := 8i64 } in
    WebEvent.mod_shift shift
        && WebEvent.mod_ctrl ctrl
        && WebEvent.mod_alt alt
        && WebEvent.mod_meta meta

#[test]
def test_handler_result_prevent : Bool :=
    match HandlerResult.prevent 7i64 {
        HandlerResult.handler_result msg prevent _stop =>
            match msg {
                Option.some n => prevent && I64.beq n 7i64,
                Option.none => false,
            },
    }

#[test]
def test_handler_result_ignore : Bool :=
    let r : HandlerResult I64 := HandlerResult.ignore in
    match r {
        HandlerResult.handler_result msg prevent stop =>
            match msg {
                Option.none => Bool.not prevent && Bool.not stop,
                Option.some _ => false,
            },
    }
