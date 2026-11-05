/// Goldens and behaviour for disclosure and overlays.

use web_event::event {WebEvent}
use oak::typed {Oak.Node, Oak.Attr}
use oak::elements {Html.text}
use lib::tests::support {ui_renders, ui_has, ui_first_msg, ui_nth_msg, ui_nth_prevents, ui_handler_count}
use lib::vocab {Ui.large}
use lib::button {Ui.button}
use lib::disclosure {Ui.Section, Ui.section, Ui.accordion, Ui.collapsible, Ui.details}
use lib::overlay {Ui.menu_item, Ui.menu_danger, Ui.menu_divider, Ui.modal, Ui.drawer, Ui.dropdown_menu, Ui.popover, Ui.tooltip}

type OverlayTestMsg { toggled (k : String), closed, renamed, deleted }

def msg_text (m : Option OverlayTestMsg) : String :=
    match m {
        Option.some msg =>
            match msg {
                OverlayTestMsg.toggled k => k,
                OverlayTestMsg.closed => "closed",
                OverlayTestMsg.renamed => "renamed",
                OverlayTestMsg.deleted => "deleted",
            },
        Option.none => "",
    }

def click : WebEvent := { kind := "click" }

def key_event (k : String) : WebEvent := { kind := "keydown", key := k }

def sections : List (Ui.Section OverlayTestMsg) :=
    [Ui.section "a" "First" [Html.text "one"], Ui.section "b" "Second" [Html.text "two"]]

#[test]
def test_accordion_open_and_closed : Bool :=
    let acc : Oak.Node OverlayTestMsg := Ui.accordion List.empty "faq" sections ["b"] OverlayTestMsg.toggled in
    ui_has acc "id=\"faq-header-a\" aria-expanded=\"false\" aria-controls=\"faq-region-a\""
        && ui_has acc "<div class=\"oak-accordion__panel\" id=\"faq-region-a\" role=\"region\" aria-labelledby=\"faq-header-a\" hidden></div>"
        && ui_has acc "aria-labelledby=\"faq-header-b\">two</div>"
        && String.beq (msg_text (ui_nth_msg acc 1 click)) "b"

#[test]
def test_collapsible : Bool :=
    let c : Oak.Node OverlayTestMsg := Ui.collapsible List.empty "more" "More" false OverlayTestMsg.closed [Html.text "x"] in
    ui_has c "<div class=\"oak-accordion oak-accordion--single\" id=\"more\">"
        && String.beq (msg_text (ui_first_msg c click)) "closed"

#[test]
def test_details_native : Bool :=
    ui_renders (Ui.details List.empty "Why?" true [Html.text "Because"] : Oak.Node OverlayTestMsg)
        "<details class=\"oak-details\" open><summary class=\"oak-details__summary\">Why?</summary><div class=\"oak-details__body\">Because</div></details>"

def open_modal : Oak.Node OverlayTestMsg :=
    Ui.modal [Ui.large] "m" true "Edit" OverlayTestMsg.closed [Html.text "body"] [Html.text "foot"]

#[test]
def test_modal_closed_is_empty : Bool :=
    ui_renders (Ui.modal List.empty "m" false "Edit" OverlayTestMsg.closed List.empty List.empty) ""

#[test]
def test_modal_markup : Bool :=
    ui_has open_modal "<div class=\"oak-overlay\"><div class=\"oak-backdrop\"></div><div class=\"oak-modal oak-modal--lg\" id=\"m\" role=\"dialog\" aria-modal=\"true\" aria-labelledby=\"m-title\" tabindex=\"-1\">"
        && ui_has open_modal "<h2 class=\"oak-dialog__title\" id=\"m-title\">Edit</h2>"
        && ui_has open_modal "aria-label=\"Close\" title=\"Close\" autofocus>"
        && ui_has open_modal "<footer class=\"oak-dialog__footer\">foot</footer>"

#[test]
def test_modal_closes_three_ways : Bool :=
    I64.beq (ui_handler_count open_modal) 3
        && String.beq (msg_text (ui_nth_msg open_modal 0 click)) "closed"
        && String.beq (msg_text (ui_nth_msg open_modal 1 (key_event "Escape"))) "closed"
        && ui_nth_prevents open_modal 1 (key_event "Escape")
        && String.beq (msg_text (ui_nth_msg open_modal 1 (key_event "a"))) ""
        && String.beq (msg_text (ui_nth_msg open_modal 2 click)) "closed"

#[test]
def test_drawer_side : Bool :=
    ui_has (Ui.drawer List.empty "d" true "Filters" OverlayTestMsg.closed List.empty List.empty)
        "<div class=\"oak-drawer oak-drawer--end\" id=\"d\" role=\"dialog\""

#[test]
def test_dropdown_menu : Bool :=
    let closed : Oak.Node OverlayTestMsg :=
        Ui.dropdown_menu List.empty "act" "Actions" false (OverlayTestMsg.toggled "menu")
            [Ui.menu_item "Rename" OverlayTestMsg.renamed, Ui.menu_divider, Ui.menu_danger "Delete" OverlayTestMsg.deleted] in
    let opened : Oak.Node OverlayTestMsg :=
        Ui.dropdown_menu List.empty "act" "Actions" true (OverlayTestMsg.toggled "menu")
            [Ui.menu_item "Rename" OverlayTestMsg.renamed, Ui.menu_divider, Ui.menu_danger "Delete" OverlayTestMsg.deleted] in
    ui_has closed "aria-haspopup=\"menu\" aria-expanded=\"false\">"
        && ui_has opened "aria-haspopup=\"menu\" aria-expanded=\"true\" aria-controls=\"act-panel\">"
        && Bool.not (ui_has closed "role=\"menu\"")
        && ui_has opened "<div class=\"oak-menu__panel\" id=\"act-panel\" role=\"menu\" aria-label=\"Actions\">"
        && ui_has opened "<div class=\"oak-menu__divider\" role=\"separator\"></div>"
        && ui_has opened "<button class=\"oak-menu__item oak-menu__item--danger\" type=\"button\" role=\"menuitem\">Delete</button>"
        && String.beq (msg_text (ui_nth_msg opened 1 (key_event "Escape"))) "menu"
        && String.beq (msg_text (ui_nth_msg opened 2 click)) "renamed"
        && String.beq (msg_text (ui_nth_msg opened 3 click)) "deleted"

#[test]
def test_popover : Bool :=
    ui_has (Ui.popover List.empty "p" "Info" true OverlayTestMsg.closed [Html.text "hi"])
        "<div class=\"oak-popover__panel\" id=\"p-panel\" role=\"dialog\" aria-label=\"Info\">hi</div>"

def save_trigger (a : List (Oak.Attr OverlayTestMsg)) : Oak.Node OverlayTestMsg :=
    Ui.button List.empty a [Html.text "Save"]

#[test]
def test_tooltip_wires_describedby : Bool :=
    ui_renders (Ui.tooltip List.empty "tip" "Saves a draft" save_trigger)
        "<span class=\"oak-tooltip\"><button class=\"oak-btn oak-tone-neutral\" type=\"button\" aria-describedby=\"tip\">Save</button><span class=\"oak-tooltip__bubble\" role=\"tooltip\" id=\"tip\">Saves a draft</span></span>"
