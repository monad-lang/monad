// Stories: navigation, disclosure and overlays.

use oak::typed {Oak.Node, Oak.Attr}
use oak::elements {Html.text}
use oak::events {Html.on_click}
use oak_ui::vocab {Ui.Opt, Ui.Align, Ui.primary, Ui.danger, Ui.ghost, Ui.small, Ui.large, Ui.gap, Ui.align}
use oak_ui::layout {Ui.stack, Ui.cluster}
use oak_ui::typography {Ui.text, Ui.muted}
use oak_ui::button {Ui.button, Ui.icon}
use oak_ui::form {Ui.field, Ui.text_input}
use oak_ui::nav {
    Ui.Tab, Ui.tab, Ui.nav_item, Ui.nav_group, Ui.navbar, Ui.nav_link, Ui.tabs, Ui.breadcrumbs, Ui.pagination,
    Ui.sidebar_nav, Ui.steps,
}
use oak_ui::disclosure {Ui.section, Ui.accordion, Ui.collapsible, Ui.details}
use oak_ui::overlay {Ui.menu_item, Ui.menu_danger, Ui.menu_divider, Ui.modal, Ui.drawer, Ui.dropdown_menu, Ui.popover, Ui.tooltip}
use lib::story {
    Book.Story, Book.Ctx, Book.Msg, Book.story, Book.text, Book.flag, Book.int, Book.choice, Book.knob_text,
    Book.knob_bool, Book.knob_int, Book.action, Book.set, Book.set_and_log, Book.setter, Book.state,
    Book.state_bool, Book.state_int,
}

def toggle (ctx : Book.Ctx) (key : String) : Book.Msg :=
    Book.set_and_log key (if Book.state_bool ctx key then "false" else "true") key

def navbar_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.navbar List.empty "story-nav" [Html.text (Book.knob_text ctx "brand")]
        [Ui.nav_link "#" true "Dashboard", Ui.nav_link "#" false "Projects", Ui.nav_link "#" false "Team"]
        [Ui.button [Ui.small, Ui.primary] [Html.on_click (Book.action "new" "")] [Html.text "New"]]
        (Book.state_bool ctx "menu") (toggle ctx "menu")

def tabs_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.tabs List.empty "story-tabs"
        [Ui.tab "overview" "Overview" (Ui.text List.empty List.empty [Html.text "Overview panel. Try the arrow keys."]),
            Ui.tab "activity" "Activity" (Ui.text List.empty List.empty [Html.text "Recent activity."]),
            Ui.tab "settings" "Settings" (Ui.text List.empty List.empty [Html.text "Settings panel."])]
        (Book.state ctx "tab" "overview") (Book.setter "tab")

def page_msg (n : I64) : Book.Msg := Book.set_and_log "page" (I64.to_string n) "page"

def wayfinding_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.stack [Ui.gap 5] List.empty
        [Ui.breadcrumbs List.empty [Pair.pair "Home" "#", Pair.pair "Projects" "#", Pair.pair "Monad" "#"],
            Ui.pagination List.empty (Book.state_int ctx "page" 4) (Book.knob_int ctx "pages") page_msg,
            Ui.steps List.empty ["Account", "Profile", "Billing", "Done"] (Book.knob_int ctx "step")]

def sidebar_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.sidebar_nav List.empty "Docs"
        [Ui.nav_group "Getting started" [Ui.nav_item "intro" "Introduction" "#", Ui.nav_item "install" "Install" "#"],
            Ui.nav_group "Guides" [Ui.nav_item "forms" "Forms" "#", Ui.nav_item "theming" "Theming" "#"]]
        (Book.state ctx "page" "intro") (Option.some (Book.setter "page"))

def disclosure_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    let open_keys : List String := [Book.state ctx "open" "a"] in
    Ui.stack [Ui.gap 4] List.empty
        [Ui.accordion List.empty "story-faq"
            [Ui.section "a" "What is oak_ui?" [Ui.text List.empty List.empty [Html.text "Components for Oak."]],
                Ui.section "b" "Does it need JavaScript?" [Ui.text List.empty List.empty [Html.text "No: everything renders on the server."]],
                Ui.section "c" "Can I restyle it?" [Ui.text List.empty List.empty [Html.text "Swap the theme or override --oak-* variables."]]]
            open_keys (Book.setter "open"),
            Ui.collapsible List.empty "story-more" "Advanced options" (Book.state_bool ctx "more") (toggle ctx "more")
                [Ui.muted List.empty List.empty [Html.text "Hidden until expanded."]],
            Ui.details List.empty "Native details (no state, no runtime)" false
                [Ui.text List.empty List.empty [Html.text "The browser toggles this one."]]]

def modal_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    let size : List Ui.Opt :=
        if String.beq (Book.knob_text ctx "size") "sm" then [Ui.small]
        else if String.beq (Book.knob_text ctx "size") "lg" then [Ui.large] else List.empty in
    Ui.stack [Ui.gap 3] List.empty
        [Ui.cluster List.empty List.empty
            [Ui.button [Ui.primary] [Html.on_click (Book.set_and_log "modal" "true" "open modal")] [Html.text "Open modal"],
                Ui.button List.empty [Html.on_click (Book.set_and_log "drawer" "true" "open drawer")] [Html.text "Open drawer"]],
            Ui.modal size "story-modal" (Book.state_bool ctx "modal") (Book.knob_text ctx "title")
                (Book.set_and_log "modal" "false" "close modal")
                [Ui.text List.empty List.empty [Html.text "Close with the button, the backdrop or Escape."],
                    Ui.field List.empty "story-modal-name" "Project name" "" ""
                        (Ui.text_input List.empty (Book.state ctx "name" "") (Book.setter "name"))]
                [Ui.button [Ui.ghost] [Html.on_click (Book.set_and_log "modal" "false" "cancel")] [Html.text "Cancel"],
                    Ui.button [Ui.primary] [Html.on_click (Book.set_and_log "modal" "false" "save")] [Html.text "Save"]],
            Ui.drawer (if Book.knob_bool ctx "drawer at start" then [Ui.align Ui.Align.align_start] else List.empty)
                "story-drawer" (Book.state_bool ctx "drawer") "Filters"
                (Book.set_and_log "drawer" "false" "close drawer")
                [Ui.muted List.empty List.empty [Html.text "Drawer content."]] List.empty]

def menus_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.cluster [Ui.gap 4] List.empty
        [Ui.dropdown_menu List.empty "story-menu" "Actions" (Book.state_bool ctx "menu") (toggle ctx "menu")
            [Ui.menu_item "Rename" (Book.set_and_log "menu" "false" "rename"),
                Ui.menu_item "Duplicate" (Book.set_and_log "menu" "false" "duplicate"),
                Ui.menu_divider,
                Ui.menu_danger "Delete" (Book.set_and_log "menu" "false" "delete")],
            Ui.popover List.empty "story-pop" "Details" (Book.state_bool ctx "pop") (toggle ctx "pop")
                [Ui.text [Ui.small] List.empty [Html.text "A small non-modal panel."]],
            Ui.tooltip List.empty "story-tip" (Book.knob_text ctx "tooltip") save_trigger]

def save_trigger (a : List (Oak.Attr Book.Msg)) : Oak.Node Book.Msg :=
    Ui.button List.empty (List.cons (Html.on_click (Book.action "save" "")) a) [Html.text "Hover me"]

pub def navigation_stories : List Book.Story :=
    [Book.story "navbar" "Navigation" "Navbar" "Below 768px the links collapse behind the menu button (try the Mobile viewport)."
        [Book.text "brand" "Acme"] navbar_story,
        Book.story "tabs" "Navigation" "Tabs" "Roving tabindex; arrows, Home and End move between tabs." List.empty tabs_story,
        Book.story "wayfinding" "Navigation" "Breadcrumbs, pagination, steps" "Where am I, and where next."
            [Book.int "pages" 12, Book.int "step" 1] wayfinding_story,
        Book.story "sidebar-nav" "Navigation" "Sidebar" "Grouped links that still navigate without the runtime." List.empty sidebar_story,
        Book.story "disclosure" "Disclosure" "Accordion and details" "Controlled accordion and collapsible; native details." List.empty disclosure_story,
        Book.story "modal" "Overlays" "Modal and drawer" "The backdrop is the dialog's sibling, so clicks inside never close it."
            [Book.text "title" "New project", Book.choice "size" ["sm", "md", "lg"] "md", Book.flag "drawer at start" false]
            modal_story,
        Book.story "menus" "Overlays" "Menus, popovers, tooltips" "Escape closes menus and popovers."
            [Book.text "tooltip" "Saves a draft"] menus_story]
