/// Goldens and behaviour for buttons and icons.

use web_event::event {WebEvent}
use oak::typed {Oak.Node}
use oak::elements {Html.text}
use oak::events {Html.on_click}
use lib::tests::support {ui_renders, ui_has, ui_first_msg}
use lib::vocab {Ui.primary, Ui.danger, Ui.outline, Ui.small, Ui.full, Ui.busy, Ui.inactive, Ui.cls}
use lib::button {Ui.button, Ui.submit_button, Ui.link_button, Ui.icon_button, Ui.button_group, Ui.icon}

type ButtonTestMsg { saved, removed }

#[test]
def test_button_default : Bool :=
    ui_renders (Ui.button List.empty List.empty [Html.text "Go"])
        "<button class=\"oak-btn oak-tone-neutral\" type=\"button\">Go</button>"

#[test]
def test_button_modifiers : Bool :=
    ui_renders (Ui.button [Ui.danger, Ui.outline, Ui.small, Ui.full, Ui.cls ["x"]] List.empty [Html.text "Del"])
        "<button class=\"oak-btn oak-btn--outline oak-btn--sm oak-btn--full oak-tone-danger x\" type=\"button\">Del</button>"

#[test]
def test_button_loading_is_disabled_and_busy : Bool :=
    ui_renders (Ui.button [Ui.primary, Ui.busy] List.empty [Html.text "Save"])
        "<button class=\"oak-btn oak-btn--loading oak-tone-primary\" type=\"button\" disabled aria-busy=\"true\"><span class=\"oak-btn__spinner\" aria-hidden=\"true\"></span>Save</button>"

#[test]
def test_button_disabled : Bool :=
    ui_has (Ui.button [Ui.inactive] List.empty List.empty) "type=\"button\" disabled>"

#[test]
def test_button_click_dispatches : Bool :=
    let b : Oak.Node ButtonTestMsg := Ui.button List.empty [Html.on_click ButtonTestMsg.saved] [Html.text "Save"] in
    let e : WebEvent := { kind := "click" } in
    match ui_first_msg b e {
        Option.some m => match m { ButtonTestMsg.saved => true, ButtonTestMsg.removed => false },
        Option.none => false,
    }

#[test]
def test_submit_button_type : Bool :=
    ui_has (Ui.submit_button [Ui.primary] List.empty List.empty) "type=\"submit\""

#[test]
def test_link_button : Bool :=
    ui_renders (Ui.link_button [Ui.primary] "/new" List.empty [Html.text "New"])
        "<a class=\"oak-btn oak-tone-primary\" href=\"/new\">New</a>"

#[test]
def test_icon_button_is_named : Bool :=
    ui_renders (Ui.icon_button List.empty "Close" (Ui.icon "close") List.empty)
        "<button class=\"oak-btn oak-btn--icon oak-tone-neutral\" type=\"button\" aria-label=\"Close\" title=\"Close\"><span class=\"oak-icon\" aria-hidden=\"true\">\u{00D7}</span></button>"

#[test]
def test_unknown_icon_is_empty : Bool :=
    ui_renders (Ui.icon "nope") "<span class=\"oak-icon\" aria-hidden=\"true\"></span>"

#[test]
def test_button_group : Bool :=
    ui_renders (Ui.button_group List.empty "View" List.empty List.empty)
        "<div class=\"oak-btn-group\" role=\"group\" aria-label=\"View\"></div>"
