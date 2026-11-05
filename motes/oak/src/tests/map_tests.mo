/// `Oak.Node.map` / `Oak.Attr.map`: relabelling messages leaves the
/// markup and handler ids alone and maps what the handlers produce.

use web_event::event {WebEvent, HandlerResult}
use lib::typed {Oak.Node, Oak.Node.map, Oak.Lowered, Oak.lower}
use lib::elements {Html.attr, Html.div, Html.button, Html.text}
use lib::events {Html.on_click}
use xml_html::html {Html.to_string}

type MapChildMsg { pressed }

type MapParentMsg { from_child (c : MapChildMsg) }

def child_view : Oak.Node MapChildMsg :=
    Html.div [Html.attr "id" "c"]
        [Html.button [Html.on_click MapChildMsg.pressed] [Html.text "go"]]

def lowered_markup {M : Type} (n : Oak.Node M) : String :=
    match Oak.lower n { Oak.Lowered.lowered tree _ => Html.to_string tree }

def first_handler_msg (n : Oak.Node MapParentMsg) : Option MapParentMsg :=
    match Oak.lower n {
        Oak.Lowered.lowered _ handlers =>
            match handlers {
                List.empty => Option.none,
                List.cons entry _ =>
                    match entry {
                        Pair.pair _ h =>
                            let e : WebEvent := { kind := "click" } in
                            match h e { HandlerResult.handler_result m _ _ => m }
                    },
            },
    }

#[test]
def test_map_preserves_markup : Bool :=
    let mapped : Oak.Node MapParentMsg := Oak.Node.map MapParentMsg.from_child child_view in
    String.beq (lowered_markup child_view) (lowered_markup mapped)

#[test]
def test_map_relabels_handler : Bool :=
    let mapped : Oak.Node MapParentMsg := Oak.Node.map MapParentMsg.from_child child_view in
    match first_handler_msg mapped {
        Option.some p => match p { MapParentMsg.from_child c => match c { MapChildMsg.pressed => true } },
        Option.none => false,
    }
