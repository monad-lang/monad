/// Lowering tests: a typed view becomes the plain markup tree plus the
/// handler table, and SSR lowering drops the handlers.

use std::list {List.length}
use web_event::event {WebEvent, HandlerResult, ListenerFlags}
use lib::typed {Oak.Node, Oak.Lowered, Oak.lower, Oak.to_html, Handler.spec}
use lib::elements {Html.attr, Html.div, Html.text}
use lib::events {Html.on_click}
use xml_html::html {Html.to_string}

#[test]
def test_lower_element : Bool :=
    let n : Oak.Node Unit := Html.div [Html.attr "id" "x"] [Html.text "hi"] in
    match Oak.lower n {
        Oak.Lowered.lowered tree handlers =>
            String.beq (Html.to_string tree) "<div id=\"x\">hi</div>"
                && List.is_empty handlers,
    }

#[test]
def test_lower_handler_attribute : Bool :=
    let n : Oak.Node Unit := Html.div [Html.on_click Unit.unit] List.empty in
    match Oak.lower n {
        Oak.Lowered.lowered tree handlers =>
            String.starts_with "<div data-oak-on-click=\"0x" (Html.to_string tree)
                && I64.beq (List.length handlers) 1i64,
    }

#[test]
def test_to_html_drops_handlers : Bool :=
    let n : Oak.Node Unit := Html.div [Html.on_click Unit.unit, Html.attr "id" "x"] List.empty in
    String.beq (Html.to_string (Oak.to_html n)) "<div id=\"x\"></div>"

#[test]
def test_handler_spec_flags : Bool :=
    let flags : ListenerFlags := { prevent_default := true, once := true } in
    let path : List I64 := [0i64] in
    String.ends_with (Handler.spec path "drop" flags) ":do"
