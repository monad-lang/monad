// Overlays: modal dialogs, drawers, dropdown menus, popovers and tooltips.
//
// Open/closed is controlled by the app. A closed overlay renders an empty
// fragment, so it costs nothing in the tree.
//
// `WebEvent` carries no target node, so a click inside a dialog cannot be
// told apart from a click on its backdrop when one contains the other. The
// backdrop is therefore a SIBLING of the dialog, not its parent: clicking it
// closes, clicks in the dialog never reach it.
//
// Focus: the dialog is focusable (`tabindex=-1`) and carries
// `data-oak-focus-trap`, which the browser runtime turns into a Tab trap
// that restores the previous focus when the dialog leaves the tree. Opening
// a dialog still needs the app to return `Command.focus ("#" ++ id)`; the
// runtime applies it after the patch that inserted the dialog. Escape works
// once focus is inside (the trap focuses the first control).

use web_event::event {WebEvent, HandlerResult, ListenerFlags}
use oak::typed {Oak.Attr, Oak.Node}
use oak::elements {
    Html.div, Html.span, Html.h2, Html.button, Html.header, Html.footer, Html.type_, Html.id_,
    Html.aria, Html.role, Html.class_, Html.class_list, Html.text, Html.fragment, Html.tabindex,
    Html.autofocus, Html.attrs_when, Html.attr,
}
use oak::events {Html.on, Html.on_click}
use lib::vocab {Ui.Opt, Ui.Style, Ui.Size, Ui.Align, Ui.resolve, Ui.ghost, Ui.small}
use lib::base {Ui.root_attrs, Ui.size_mod}
use lib::button {Ui.icon_button, Ui.icon}

/// One dropdown entry.
pub type Ui.MenuItem (Msg : Type) {
    ui_menu_action (label : String) (msg : Msg) (danger : Bool),
    ui_menu_divider
}

pub def Ui.menu_item {Msg : Type} (label : String) (msg : Msg) : Ui.MenuItem Msg :=
    Ui.MenuItem.ui_menu_action label msg false

/// A destructive entry, shown in the danger tone.
pub def Ui.menu_danger {Msg : Type} (label : String) (msg : Msg) : Ui.MenuItem Msg :=
    Ui.MenuItem.ui_menu_action label msg true

pub def Ui.menu_divider {Msg : Type} : Ui.MenuItem Msg := Ui.MenuItem.ui_menu_divider

def on_escape {Msg : Type} (m : Msg) : Oak.Attr Msg :=
    Html.on "keydown" ListenerFlags.none
        (fn (e : WebEvent) => if String.beq e.key "Escape" then HandlerResult.prevent m else HandlerResult.ignore)

def close_button {Msg : Type} (on_close : Msg) : Oak.Node Msg :=
    Ui.icon_button [Ui.ghost, Ui.small] "Close" (Ui.icon "close") [Html.on_click on_close, Html.autofocus]

/// The shared dialog frame for modals and drawers.
def dialog_frame {Msg : Type} (block : String) (mods : List String) (s : Ui.Style) (id : String) (title : String)
    (on_close : Msg) (body : List (Oak.Node Msg)) (foot : List (Oak.Node Msg)) : Oak.Node Msg :=
    let title_id : String := String.concat id "-title" in
    Html.div [Html.class_ ["oak-overlay"]]
        [Html.div [Html.class_ ["oak-backdrop"], Html.on_click on_close] List.empty,
            Html.div
                (Ui.root_attrs block mods List.empty s
                    [Html.id_ id, Html.role "dialog", Html.aria "modal" "true",
                        Html.aria "labelledby" title_id, Html.tabindex (-1),
                        Html.attr "data-oak-focus-trap" "", on_escape on_close])
                (List.append
                    [Html.header [Html.class_ ["oak-dialog__header"]]
                        [Html.h2 [Html.class_ ["oak-dialog__title"], Html.id_ title_id] [Html.text title],
                            close_button on_close],
                        Html.div [Html.class_ ["oak-dialog__body"]] body]
                    (if List.is_empty foot then List.empty
                        else [Html.footer [Html.class_ ["oak-dialog__footer"]] foot]))]

def side_mod (a : Ui.Align) : String :=
    match a {
        Ui.Align.align_start => "start",
        _ => "end",
    }

def menu_item_node {Msg : Type} (item : Ui.MenuItem Msg) : Oak.Node Msg :=
    match item {
        Ui.MenuItem.ui_menu_action label msg danger =>
            Html.button
                [Html.class_list [Pair.pair "oak-menu__item" true, Pair.pair "oak-menu__item--danger" danger],
                    Html.type_ "button", Html.role "menuitem", Html.on_click msg]
                [Html.text label],
        Ui.MenuItem.ui_menu_divider => Html.div [Html.class_ ["oak-menu__divider"], Html.role "separator"] List.empty,
    }

#[terminating]
def menu_item_nodes {Msg : Type} (items : List (Ui.MenuItem Msg)) : List (Oak.Node Msg) :=
    match items {
        List.empty => List.empty,
        List.cons i rest => List.cons (menu_item_node i) (menu_item_nodes rest),
    }

def floating {Msg : Type} (block : String) (id : String) (label : String) (is_open : Bool) (on_toggle : Msg)
    (popup_role : String) (s : Ui.Style) (content : List (Oak.Node Msg)) : Oak.Node Msg :=
    let panel_id : String := String.concat id "-panel" in
    // The trigger names the panel in `aria-controls` only while the panel
    // exists (it is not rendered when closed).
    Html.div (Ui.root_attrs block [if is_open then "open" else ""] List.empty s [Html.id_ id])
        (List.cons
            (Html.button
                (List.append
                    [Html.class_ ["oak-btn", "oak-btn--outline", "oak-tone-neutral", String.concat block "__trigger"],
                        Html.type_ "button", Html.aria "haspopup" (if String.beq popup_role "menu" then "menu" else "dialog"),
                        Html.aria "expanded" (if is_open then "true" else "false")]
                    (List.append (Html.attrs_when is_open [Html.aria "controls" panel_id]) [Html.on_click on_toggle]))
                [Html.text label, Ui.icon "chevron-down"])
            (if is_open
                then [Html.div
                    [Html.class_ [String.concat block "__panel"], Html.id_ panel_id, Html.role popup_role,
                        Html.aria "label" label, on_escape on_toggle]
                    content]
                else List.empty))

with Ui {
    /// A modal dialog. Closes on the backdrop, the close button and
    /// Escape, all via `on_close`. `Ui.small`/`Ui.large` set the width.
    /// The dialog traps Tab and restores the previous focus when it leaves
    /// the tree; the app opens it with `Command.focus ("#" ++ id)` so the
    /// runtime focuses it after the patch that inserted it.
    pub def modal {Msg : Type} (opts : List Ui.Opt) (id : String) (is_open : Bool) (title : String)
        (on_close : Msg) (body : List (Oak.Node Msg)) (foot : List (Oak.Node Msg)) : Oak.Node Msg :=
        if is_open
        then
            let s : Ui.Style := Ui.resolve opts in
            dialog_frame "oak-modal" [Ui.size_mod s.size] s id title on_close body foot
        else Html.fragment List.empty

    /// A panel that slides from the end edge (`Ui.align Ui.Align.align_start`
    /// for the start edge).
    pub def drawer {Msg : Type} (opts : List Ui.Opt) (id : String) (is_open : Bool) (title : String)
        (on_close : Msg) (body : List (Oak.Node Msg)) (foot : List (Oak.Node Msg)) : Oak.Node Msg :=
        if is_open
        then
            let s : Ui.Style := Ui.resolve opts in
            dialog_frame "oak-drawer" [side_mod s.align, Ui.size_mod s.size] s id title on_close body foot
        else Html.fragment List.empty

    /// A button that opens a menu of actions. Each item's click sends its
    /// own message; the app usually closes the menu on it too.
    pub def dropdown_menu {Msg : Type} (opts : List Ui.Opt) (id : String) (label : String) (is_open : Bool)
        (on_toggle : Msg) (items : List (Ui.MenuItem Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        floating "oak-menu" id label is_open on_toggle "menu" s (menu_item_nodes items)

    /// A button that opens a small non-modal panel of arbitrary content.
    pub def popover {Msg : Type} (opts : List Ui.Opt) (id : String) (label : String) (is_open : Bool)
        (on_toggle : Msg) (content : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        floating "oak-popover" id label is_open on_toggle "dialog" s content

    /// A hover/focus tooltip, CSS only. `trigger` receives the
    /// `aria-describedby` wiring (like `Ui.field`'s control):
    /// `Ui.tooltip [] "save-tip" "Saves a draft"
    ///     (fn (a : List (Oak.Attr Msg)) => Ui.button [] a [Html.text "Save"])`.
    pub def tooltip {Msg : Type} (opts : List Ui.Opt) (id : String) (text : String)
        (trigger : List (Oak.Attr Msg) -> Oak.Node Msg) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.span (Ui.root_attrs "oak-tooltip" List.empty List.empty s List.empty)
            [trigger [Html.aria "describedby" id],
                Html.span [Html.class_ ["oak-tooltip__bubble"], Html.role "tooltip", Html.id_ id] [Html.text text]]
}
