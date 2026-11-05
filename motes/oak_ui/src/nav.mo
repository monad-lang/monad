// Navigation: the top bar, links, tabs, breadcrumbs, pagination, the
// sidebar menu and step indicators.
//
// All of it is controlled. Links stay real `<a href>`s so a server-rendered
// page navigates without the browser runtime; with it, an optional
// `on_select` turns clicks into messages (default prevented).

use std::list {List.length}
use web_event::event {WebEvent, HandlerResult, ListenerFlags}
use oak::typed {Oak.Attr, Oak.Node}
use oak::elements {
    Html.div, Html.span, Html.nav, Html.header, Html.ol, Html.li, Html.a, Html.button, Html.p,
    Html.href, Html.type_, Html.id_, Html.attr, Html.aria, Html.role, Html.class_, Html.class_list,
    Html.text, Html.key, Html.tabindex, Html.disabled,
}
use oak::events {Html.on, Html.on_click}
use lib::vocab {Ui.Opt, Ui.Style, Ui.resolve, Ui.ghost, Ui.cls}
use lib::base {Ui.root_attrs}
use lib::button {Ui.icon_button, Ui.icon}

// ═══ Types ═══

/// One tab: a key, its label and its panel.
pub type Ui.Tab (Msg : Type) {
    ui_tab (key : String) (label : String) (panel : Oak.Node Msg)
}

/// One sidebar entry. Every field is named at each literal.
pub struct Ui.NavItem {
    key : String,
    label : String,
    url : String
}

/// A titled group of sidebar entries (`title` may be `""`).
pub struct Ui.NavGroup {
    title : String,
    items : List Ui.NavItem
}

pub def Ui.tab {Msg : Type} (key : String) (label : String) (panel : Oak.Node Msg) : Ui.Tab Msg :=
    Ui.Tab.ui_tab key label panel

pub def Ui.nav_item (key : String) (label : String) (url : String) : Ui.NavItem :=
    { key := key, label := label, url := url }

pub def Ui.nav_group (title : String) (items : List Ui.NavItem) : Ui.NavGroup :=
    { title := title, items := items }

// ═══ Shared helpers ═══

def prevent_flags : ListenerFlags :=
    { capture := false, prevent_default := true, stop_propagation := false, once := false, passive := false }

def select_click {Msg : Type} (m : Msg) : Oak.Attr Msg :=
    Html.on "click" prevent_flags (fn (_e : WebEvent) => HandlerResult.prevent m)

def current_attrs {Msg : Type} (active : Bool) (value : String) : List (Oak.Attr Msg) :=
    if active then [Html.aria "current" value] else List.empty

// ═══ Tabs ═══

def tab_key {Msg : Type} (t : Ui.Tab Msg) : String := match t { Ui.Tab.ui_tab k _ _ => k }

#[terminating]
def tab_keys {Msg : Type} (ts : List (Ui.Tab Msg)) : List String :=
    match ts {
        List.empty => List.empty,
        List.cons t rest => List.cons (tab_key t) (tab_keys rest),
    }

#[terminating]
def index_of (keys : List String) (k : String) (i : I64) : I64 :=
    match keys {
        List.empty => -1,
        List.cons x rest => if String.beq x k then i else index_of rest k (i + 1),
    }

#[terminating]
def key_at (keys : List String) (i : I64) : String :=
    match keys {
        List.empty => "",
        List.cons x rest => if I64.beq i 0 then x else key_at rest (i - 1),
    }

/// The key `delta` steps from `active`, wrapping around.
def neighbor (keys : List String) (active : String) (delta : I64) : String :=
    let n : I64 := List.length keys in
    let i : I64 := index_of keys active 0 in
    if I64.lt n 1 then active
    else
        let j : I64 := I64.add (if I64.lt i 0 then 0 else i) delta in
        key_at keys (if I64.lt j 0 then n - 1 else if I64.lt j n then j else 0)

/// ArrowLeft/ArrowRight move between tabs, Home/End jump to the ends.
def tab_keydown {Msg : Type} (keys : List String) (active : String) (on_select : String -> Msg)
    : WebEvent -> HandlerResult Msg :=
    fn (e : WebEvent) =>
        if String.beq e.key "ArrowRight" then HandlerResult.prevent (on_select (neighbor keys active 1))
        else if String.beq e.key "ArrowLeft" then HandlerResult.prevent (on_select (neighbor keys active (-1)))
        else if String.beq e.key "Home" then HandlerResult.prevent (on_select (key_at keys 0))
        else if String.beq e.key "End" then HandlerResult.prevent (on_select (key_at keys (List.length keys - 1)))
        else HandlerResult.ignore

def tab_id (id : String) (k : String) : String := String.concat_list [id, "-tab-", k]

def panel_id (id : String) (k : String) : String := String.concat_list [id, "-panel-", k]

def tab_button {Msg : Type} (id : String) (active : String) (on_select : String -> Msg) (t : Ui.Tab Msg)
    : Oak.Node Msg :=
    match t {
        Ui.Tab.ui_tab k label _ =>
            let is_active : Bool := String.beq k active in
            Html.button
                [Html.class_list [Pair.pair "oak-tabs__tab" true, Pair.pair "oak-tabs__tab--active" is_active],
                    Html.type_ "button", Html.role "tab", Html.id_ (tab_id id k),
                    Html.aria "selected" (if is_active then "true" else "false"),
                    Html.aria "controls" (panel_id id k),
                    Html.tabindex (if is_active then 0 else -1),
                    Html.on_click (on_select k)]
                [Html.text label]
    }

#[terminating]
def tab_buttons {Msg : Type} (id : String) (active : String) (on_select : String -> Msg)
    (ts : List (Ui.Tab Msg)) : List (Oak.Node Msg) :=
    match ts {
        List.empty => List.empty,
        List.cons t rest => List.cons (tab_button id active on_select t) (tab_buttons id active on_select rest),
    }

/// Only the active panel is rendered (an inactive panel's view is not
/// computed at all).
#[terminating]
def active_panel {Msg : Type} (id : String) (active : String) (ts : List (Ui.Tab Msg)) : List (Oak.Node Msg) :=
    match ts {
        List.empty => List.empty,
        List.cons t rest =>
            match t {
                Ui.Tab.ui_tab k _ panel =>
                    if String.beq k active
                    then [Html.div
                        [Html.key k, Html.class_ ["oak-tabs__panel"], Html.role "tabpanel",
                            Html.id_ (panel_id id k), Html.aria "labelledby" (tab_id id k), Html.tabindex 0]
                        [panel]]
                    else active_panel id active rest
            },
    }

// ═══ Breadcrumbs, pagination, sidebar, steps ═══

#[terminating]
def crumb_nodes {Msg : Type} (items : List (Pair String String)) : List (Oak.Node Msg) :=
    match items {
        List.empty => List.empty,
        List.cons item rest =>
            match item {
                Pair.pair label url =>
                    let last : Bool := List.is_empty rest in
                    List.cons
                        (Html.li [Html.class_ ["oak-breadcrumbs__item"]]
                            [if last
                                then Html.span [Html.aria "current" "page"] [Html.text label]
                                else Html.a [Html.class_ ["oak-link"], Html.href url] [Html.text label]])
                        (crumb_nodes rest)
            },
    }

/// The page numbers to show: the ends, the current page and its
/// neighbours; 0 marks a gap ("…").
def page_window (page : I64) (total : I64) : List I64 :=
    window_from 1 page total

#[terminating]
def window_from (i : I64) (page : I64) (total : I64) : List I64 :=
    if I64.lt total i then List.empty
    else
        let near : Bool := I64.lt (i - page) 2 && I64.lt (page - i) 2 in
        let edge : Bool := I64.beq i 1 || I64.beq i total in
        if near || edge
        then List.cons i (window_from (i + 1) page total)
        else if I64.lt i page
        then List.cons 0 (window_from (page - 1) page total)
        else List.cons 0 (window_from total page total)

def page_node {Msg : Type} (page : I64) (on_page : I64 -> Msg) (n : I64) : Oak.Node Msg :=
    if I64.beq n 0
    then Html.li [Html.class_ ["oak-pagination__gap"], Html.aria "hidden" "true"] [Html.text "\u{2026}"]
    else
        Html.li List.empty
            [Html.button
                (List.append
                    [Html.class_list [Pair.pair "oak-pagination__page" true, Pair.pair "oak-pagination__page--current" (I64.beq n page)],
                        Html.type_ "button", Html.aria "label" (String.concat "Page " (I64.to_string n)),
                        Html.on_click (on_page n)]
                    (current_attrs (I64.beq n page) "page"))
                [Html.text (I64.to_string n)]]

#[terminating]
def page_nodes {Msg : Type} (page : I64) (on_page : I64 -> Msg) (ns : List I64) : List (Oak.Node Msg) :=
    match ns {
        List.empty => List.empty,
        List.cons n rest => List.cons (page_node page on_page n) (page_nodes page on_page rest),
    }

def step_button {Msg : Type} (label : String) (enabled : Bool) (target : I64) (on_page : I64 -> Msg)
    (glyph : String) : Oak.Node Msg :=
    Html.li List.empty
        [Html.button
            (List.append
                [Html.class_ ["oak-pagination__step"], Html.type_ "button", Html.aria "label" label,
                    Html.on_click (on_page target)]
                (if enabled then List.empty else [Html.disabled]))
            [Ui.icon glyph]]

def nav_item_node {Msg : Type} (active : String) (on_select : Option (String -> Msg)) (item : Ui.NavItem)
    : Oak.Node Msg :=
    match item {
        { key, label, url } =>
            let is_active : Bool := String.beq key active in
            let click : List (Oak.Attr Msg) :=
                match on_select {
                    Option.some f => [select_click (f key)],
                    Option.none => List.empty,
                } in
            Html.li [Html.key key]
                [Html.a
                    (List.append
                        [Html.class_list [Pair.pair "oak-sidenav__link" true, Pair.pair "oak-sidenav__link--active" is_active],
                            Html.href url]
                        (List.append (current_attrs is_active "page") click))
                    [Html.text label]]
    }

#[terminating]
def nav_item_nodes {Msg : Type} (active : String) (on_select : Option (String -> Msg)) (items : List Ui.NavItem)
    : List (Oak.Node Msg) :=
    match items {
        List.empty => List.empty,
        List.cons i rest => List.cons (nav_item_node active on_select i) (nav_item_nodes active on_select rest),
    }

def nav_group_node {Msg : Type} (active : String) (on_select : Option (String -> Msg)) (g : Ui.NavGroup)
    : Oak.Node Msg :=
    match g {
        { title, items } =>
            Html.div [Html.class_ ["oak-sidenav__group"]]
                (List.append
                    (if String.is_empty title then List.empty
                        else [Html.p [Html.class_ ["oak-sidenav__title"]] [Html.text title]])
                    [Html.ol [Html.class_ ["oak-sidenav__list"]] (nav_item_nodes active on_select items)])
    }

#[terminating]
def nav_group_nodes {Msg : Type} (active : String) (on_select : Option (String -> Msg)) (gs : List Ui.NavGroup)
    : List (Oak.Node Msg) :=
    match gs {
        List.empty => List.empty,
        List.cons g rest => List.cons (nav_group_node active on_select g) (nav_group_nodes active on_select rest),
    }

#[terminating]
def step_nodes {Msg : Type} (current : I64) (i : I64) (labels : List String) : List (Oak.Node Msg) :=
    match labels {
        List.empty => List.empty,
        List.cons label rest =>
            let state : String :=
                if I64.lt i current then "done" else if I64.beq i current then "current" else "upcoming" in
            List.cons
                (Html.li
                    (List.append
                        [Html.class_ ["oak-steps__step", String.concat "oak-steps__step--" state]]
                        (current_attrs (I64.beq i current) "step"))
                    [Html.span [Html.class_ ["oak-steps__marker"]]
                        [if I64.lt i current then Ui.icon "check" else Html.text (I64.to_string (i + 1))],
                        Html.span [Html.class_ ["oak-steps__label"]] [Html.text label]])
                (step_nodes current (i + 1) rest),
    }

with Ui {
    /// The top bar: brand, links, actions. Below the `md` breakpoint the
    /// links collapse behind a menu button; `menu_open` and `on_menu` are
    /// the app's toggle.
    pub def navbar {Msg : Type} (opts : List Ui.Opt) (id : String) (brand : List (Oak.Node Msg))
        (links : List (Oak.Node Msg)) (actions : List (Oak.Node Msg)) (menu_open : Bool) (on_menu : Msg)
        : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        let links_id : String := String.concat id "-links" in
        Html.header (Ui.root_attrs "oak-navbar" [if menu_open then "open" else ""] List.empty s [Html.id_ id])
            [Html.div [Html.class_ ["oak-navbar__brand"]] brand,
                Ui.icon_button [Ui.ghost, Ui.cls ["oak-navbar__toggle"]] "Menu" (Ui.icon "menu")
                    [Html.aria "expanded" (if menu_open then "true" else "false"),
                        Html.aria "controls" links_id, Html.on_click on_menu],
                Html.nav [Html.class_ ["oak-navbar__links"], Html.id_ links_id, Html.aria "label" "Main"] links,
                Html.div [Html.class_ ["oak-navbar__actions"]] actions]

    /// A top-bar link; `active` marks the current page.
    pub def nav_link {Msg : Type} (url : String) (active : Bool) (label : String) : Oak.Node Msg :=
        Html.a
            (List.append
                [Html.class_list [Pair.pair "oak-navbar__link" true, Pair.pair "oak-navbar__link--active" active],
                    Html.href url]
                (current_attrs active "page"))
            [Html.text label]

    /// Tabs with arrow-key navigation (roving tabindex). `id` scopes the
    /// tab/panel ids; only the active panel is rendered. Arrow keys change
    /// the selection, but focus stays on the button that had it until Oak
    /// can move focus (no focus command yet).
    pub def tabs {Msg : Type} (opts : List Ui.Opt) (id : String) (tabs : List (Ui.Tab Msg)) (active : String)
        (on_select : String -> Msg) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        let keys : List String := tab_keys tabs in
        Html.div (Ui.root_attrs "oak-tabs" List.empty List.empty s [Html.id_ id])
            (List.cons
                (Html.div
                    [Html.class_ ["oak-tabs__list"], Html.role "tablist",
                        Html.on "keydown" ListenerFlags.none (tab_keydown keys active on_select)]
                    (tab_buttons id active on_select tabs))
                (active_panel id active tabs))

    /// `(label, url)` crumbs; the last one is the current page.
    pub def breadcrumbs {Msg : Type} (opts : List Ui.Opt) (items : List (Pair String String)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.nav (Ui.root_attrs "oak-breadcrumbs" List.empty List.empty s [Html.aria "label" "Breadcrumb"])
            [Html.ol [Html.class_ ["oak-breadcrumbs__list"]] (crumb_nodes items)]

    /// Page `page` of `total` (1-based), with previous/next and a window
    /// of page numbers around the current one.
    pub def pagination {Msg : Type} (opts : List Ui.Opt) (page : I64) (total : I64) (on_page : I64 -> Msg)
        : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.nav (Ui.root_attrs "oak-pagination" List.empty List.empty s [Html.aria "label" "Pagination"])
            [Html.ol [Html.class_ ["oak-pagination__list"]]
                (List.cons (step_button "Previous page" (I64.lt 1 page) (page - 1) on_page "chevron-left")
                    (List.append (page_nodes page on_page (page_window page total))
                        [step_button "Next page" (I64.lt page total) (page + 1) on_page "chevron-right"]))]

    /// A grouped vertical menu. `active` is the current item's key. Items
    /// are links; pass `Option.some on_select` to route clicks through the
    /// app instead (default prevented).
    pub def sidebar_nav {Msg : Type} (opts : List Ui.Opt) (label : String) (groups : List Ui.NavGroup)
        (active : String) (on_select : Option (String -> Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.nav (Ui.root_attrs "oak-sidenav" List.empty List.empty s [Html.aria "label" label])
            (nav_group_nodes active on_select groups)

    /// A step indicator; `current` is the 0-based active step.
    pub def steps {Msg : Type} (opts : List Ui.Opt) (labels : List String) (current : I64) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.ol (Ui.root_attrs "oak-steps" List.empty List.empty s List.empty) (step_nodes current 0 labels)
}
