/// Goldens and behaviour for navigation.

use web_event::event {WebEvent}
use oak::typed {Oak.Node}
use oak::elements {Html.text}
use lib::tests::support {ui_renders, ui_has, ui_first_msg, ui_first_prevents, ui_nth_msg, ui_handler_count}
use lib::nav {
    Ui.Tab, Ui.NavGroup, Ui.tab, Ui.nav_item, Ui.nav_group, Ui.navbar, Ui.nav_link, Ui.tabs,
    Ui.breadcrumbs, Ui.pagination, Ui.sidebar_nav, Ui.steps,
}

type NavTestMsg { picked (k : String), paged (n : I64), menu }

def picked_text (m : Option NavTestMsg) : String :=
    match m {
        Option.some msg =>
            match msg {
                NavTestMsg.picked k => k,
                NavTestMsg.paged n => String.concat "page " (I64.to_string n),
                NavTestMsg.menu => "menu",
            },
        Option.none => "",
    }

def three_tabs : List (Ui.Tab NavTestMsg) :=
    [Ui.tab "a" "Alpha" (Html.text "A body"), Ui.tab "b" "Beta" (Html.text "B body"),
        Ui.tab "c" "Gamma" (Html.text "C body")]

def tabs_at (active : String) : Oak.Node NavTestMsg := Ui.tabs List.empty "t" three_tabs active NavTestMsg.picked

def key_event (k : String) : WebEvent := { kind := "keydown", key := k }

#[test]
def test_tabs_markup_only_active_panel : Bool :=
    let t : Oak.Node NavTestMsg := tabs_at "b" in
    ui_has t "<div class=\"oak-tabs__list\" role=\"tablist\">"
        && ui_has t "<button class=\"oak-tabs__tab oak-tabs__tab--active\" type=\"button\" role=\"tab\" id=\"t-tab-b\" aria-selected=\"true\" aria-controls=\"t-panel-b\" tabindex=\"0\">Beta</button>"
        && ui_has t "aria-selected=\"false\" aria-controls=\"t-panel-a\" tabindex=\"-1\">Alpha"
        && ui_has t "<div data-oak-key=\"b\" class=\"oak-tabs__panel\" role=\"tabpanel\" id=\"t-panel-b\" aria-labelledby=\"t-tab-b\" tabindex=\"0\">B body</div>"
        && Bool.not (ui_has t "A body")

#[test]
def test_tabs_arrow_keys_wrap : Bool :=
    String.beq (picked_text (ui_first_msg (tabs_at "b") (key_event "ArrowRight"))) "c"
        && String.beq (picked_text (ui_first_msg (tabs_at "c") (key_event "ArrowRight"))) "a"
        && String.beq (picked_text (ui_first_msg (tabs_at "a") (key_event "ArrowLeft"))) "c"
        && String.beq (picked_text (ui_first_msg (tabs_at "b") (key_event "Home"))) "a"
        && String.beq (picked_text (ui_first_msg (tabs_at "a") (key_event "End"))) "c"
        && String.beq (picked_text (ui_first_msg (tabs_at "a") (key_event "x"))) ""
        && ui_first_prevents (tabs_at "a") (key_event "ArrowRight")

#[test]
def test_tab_click_selects : Bool :=
    let e : WebEvent := { kind := "click" } in
    String.beq (picked_text (ui_nth_msg (tabs_at "a") 2 e)) "b"

#[test]
def test_breadcrumbs_last_is_current : Bool :=
    ui_renders (Ui.breadcrumbs List.empty [Pair.pair "Home" "/", Pair.pair "Docs" "/docs"] : Oak.Node NavTestMsg)
        "<nav class=\"oak-breadcrumbs\" aria-label=\"Breadcrumb\"><ol class=\"oak-breadcrumbs__list\"><li class=\"oak-breadcrumbs__item\"><a class=\"oak-link\" href=\"/\">Home</a></li><li class=\"oak-breadcrumbs__item\"><span aria-current=\"page\">Docs</span></li></ol></nav>"

#[test]
def test_pagination_window : Bool :=
    let p : Oak.Node NavTestMsg := Ui.pagination List.empty 5 10 NavTestMsg.paged in
    ui_has p "aria-label=\"Page 1\"" && ui_has p "aria-label=\"Page 4\"" && ui_has p "aria-label=\"Page 6\""
        && ui_has p "aria-label=\"Page 10\"" && Bool.not (ui_has p "aria-label=\"Page 3\"")
        && Bool.not (ui_has p "aria-label=\"Page 7\"")
        && ui_has p "aria-label=\"Page 5\" aria-current=\"page\">5</button>"
        && I64.beq (ui_handler_count p) 7

#[test]
def test_pagination_steps : Bool :=
    let click : WebEvent := { kind := "click" } in
    let first : Oak.Node NavTestMsg := Ui.pagination List.empty 1 3 NavTestMsg.paged in
    ui_has first "aria-label=\"Previous page\" disabled>"
        && String.beq (picked_text (ui_nth_msg first 4 click)) "page 2"

#[test]
def test_sidebar_links_and_select : Bool :=
    let groups : List Ui.NavGroup :=
        [Ui.nav_group "Docs" [Ui.nav_item "intro" "Intro" "/intro", Ui.nav_item "api" "API" "/api"]] in
    let plain : Oak.Node NavTestMsg := Ui.sidebar_nav List.empty "Docs" groups "api" Option.none in
    let routed : Oak.Node NavTestMsg := Ui.sidebar_nav List.empty "Docs" groups "api" (Option.some NavTestMsg.picked) in
    let click : WebEvent := { kind := "click" } in
    ui_has plain "<a class=\"oak-sidenav__link oak-sidenav__link--active\" href=\"/api\" aria-current=\"page\">API</a>"
        && ui_has plain "<p class=\"oak-sidenav__title\">Docs</p>"
        && I64.beq (ui_handler_count plain) 0
        && String.beq (picked_text (ui_first_msg routed click)) "intro"
        && ui_first_prevents routed click

#[test]
def test_steps_states : Bool :=
    let s : Oak.Node NavTestMsg := Ui.steps List.empty ["Cart", "Pay", "Done"] 1 in
    ui_has s "<li class=\"oak-steps__step oak-steps__step--done\">"
        && ui_has s "<li class=\"oak-steps__step oak-steps__step--current\" aria-current=\"step\"><span class=\"oak-steps__marker\">2</span>"
        && ui_has s "oak-steps__step--upcoming"

#[test]
def test_navbar_toggle : Bool :=
    let n : Oak.Node NavTestMsg :=
        Ui.navbar List.empty "top" [Html.text "Brand"] [Ui.nav_link "/" true "Home"] List.empty true NavTestMsg.menu in
    let click : WebEvent := { kind := "click" } in
    ui_has n "<header class=\"oak-navbar oak-navbar--open\" id=\"top\">"
        && ui_has n "aria-expanded=\"true\" aria-controls=\"top-links\""
        && ui_has n "<nav class=\"oak-navbar__links\" id=\"top-links\" aria-label=\"Main\"><a class=\"oak-navbar__link oak-navbar__link--active\" href=\"/\" aria-current=\"page\">Home</a></nav>"
        && String.beq (picked_text (ui_first_msg n click)) "menu"
