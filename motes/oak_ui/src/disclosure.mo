// Disclosure: accordions, a single collapsible, and native `<details>`.
//
// `Ui.accordion`/`Ui.collapsible` are controlled (the app holds which
// sections are open). `Ui.details` needs no state and no browser runtime:
// the browser toggles it, so it suits server-rendered pages.

use oak::typed {Oak.Attr, Oak.Node}
use oak::elements {
    Html.div, Html.h3, Html.button, Html.details, Html.summary, Html.type_, Html.id_, Html.aria,
    Html.role, Html.class_, Html.text, Html.key, Html.hidden, Html.open_,
}
use oak::events {Html.on_click}
use lib::vocab {Ui.Opt, Ui.Style, Ui.resolve}
use lib::base {Ui.root_attrs}
use lib::button {Ui.icon}

/// One accordion section.
pub type Ui.Section (Msg : Type) {
    ui_section (key : String) (title : String) (body : List (Oak.Node Msg))
}

pub def Ui.section {Msg : Type} (key : String) (title : String) (body : List (Oak.Node Msg)) : Ui.Section Msg :=
    Ui.Section.ui_section key title body

#[terminating]
def contains_key (keys : List String) (k : String) : Bool :=
    match keys {
        List.empty => false,
        List.cons x rest => if String.beq x k then true else contains_key rest k,
    }

/// Header button + region. The region is always rendered (hidden when
/// closed) so `aria-controls` always points at an element.
def section_nodes {Msg : Type} (id : String) (key : String) (title : String) (is_open : Bool) (on_toggle : Msg)
    (body : List (Oak.Node Msg)) : List (Oak.Node Msg) :=
    let header_id : String := String.concat_list [id, "-header-", key] in
    let region_id : String := String.concat_list [id, "-region-", key] in
    [Html.h3 [Html.class_ ["oak-accordion__heading"]]
        [Html.button
            [Html.class_ ["oak-accordion__trigger"], Html.type_ "button", Html.id_ header_id,
                Html.aria "expanded" (if is_open then "true" else "false"),
                Html.aria "controls" region_id, Html.on_click on_toggle]
            [Html.text title, Ui.icon (if is_open then "chevron-up" else "chevron-down")]],
        Html.div
            (List.append
                [Html.class_ ["oak-accordion__panel"], Html.id_ region_id, Html.role "region",
                    Html.aria "labelledby" header_id]
                (if is_open then List.empty else [Html.hidden]))
            (if is_open then body else List.empty)]

def accordion_item {Msg : Type} (id : String) (open_keys : List String) (on_toggle : String -> Msg)
    (sec : Ui.Section Msg) : Oak.Node Msg :=
    match sec {
        Ui.Section.ui_section k title body =>
            Html.div [Html.key k, Html.class_ ["oak-accordion__item"]]
                (section_nodes id k title (contains_key open_keys k) (on_toggle k) body)
    }

#[terminating]
def accordion_items {Msg : Type} (id : String) (open_keys : List String) (on_toggle : String -> Msg)
    (secs : List (Ui.Section Msg)) : List (Oak.Node Msg) :=
    match secs {
        List.empty => List.empty,
        List.cons sec rest =>
            List.cons (accordion_item id open_keys on_toggle sec) (accordion_items id open_keys on_toggle rest),
    }

with Ui {
    /// Sections whose keys are in `open_keys` are expanded; a header click
    /// sends `on_toggle key` (the app decides single- or multi-open).
    pub def accordion {Msg : Type} (opts : List Ui.Opt) (id : String) (sections : List (Ui.Section Msg))
        (open_keys : List String) (on_toggle : String -> Msg) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div (Ui.root_attrs "oak-accordion" List.empty List.empty s [Html.id_ id])
            (accordion_items id open_keys on_toggle sections)

    /// One controlled show/hide section.
    pub def collapsible {Msg : Type} (opts : List Ui.Opt) (id : String) (title : String) (is_open : Bool)
        (on_toggle : Msg) (body : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div (Ui.root_attrs "oak-accordion" ["single"] List.empty s [Html.id_ id])
            [Html.div [Html.class_ ["oak-accordion__item"]] (section_nodes id "0" title is_open on_toggle body)]

    /// Native `<details>`: browser-toggled, no state, no runtime.
    pub def details {Msg : Type} (opts : List Ui.Opt) (summary : String) (start_open : Bool)
        (body : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.details (Ui.root_attrs "oak-details" List.empty List.empty s (if start_open then [Html.open_] else List.empty))
            [Html.summary [Html.class_ ["oak-details__summary"]] [Html.text summary],
                Html.div [Html.class_ ["oak-details__body"]] body]
}
