// Feedback: alerts, badges, tags, spinners, progress, skeletons, empty
// states and toasts.
//
// Toned components paint with the shared `oak-tone-*` classes. Live
// announcements use the right ARIA role: `alert` for danger/warning
// (interrupting), `status` for the rest (polite).

use oak::typed {Oak.Attr, Oak.Node}
use oak::elements {
    Html.div, Html.span, Html.p, Html.strong, Html.progress, Html.attr, Html.aria, Html.role,
    Html.class_, Html.text, Html.key,
}
use oak::events {Html.on_click}
use lib::vocab {
    Ui.Opt, Ui.Style, Ui.Tone, Ui.Variant, Ui.Style.default, Ui.resolve, Ui.resolve_from,
    Ui.ghost, Ui.small, Ui.cls,
}
use lib::base {Ui.root_attrs, Ui.tone_class, Ui.size_mod}
use lib::button {Ui.icon_button, Ui.icon}

/// One notification in a `Ui.toast_region`. Every field is named at each
/// literal (or use `Ui.toast`).
pub struct Ui.Toast {
    id : String,
    tone : Ui.Tone,
    title : String,
    body : String
}

def live_role (t : Ui.Tone) : String :=
    match t {
        Ui.Tone.tone_danger => "alert",
        Ui.Tone.tone_warning => "alert",
        _ => "status",
    }

def soft_base : Ui.Style := { Ui.Style.default with variant := Ui.Variant.variant_soft }

def variant_mod (v : Ui.Variant) : String :=
    match v {
        Ui.Variant.variant_solid => "solid",
        Ui.Variant.variant_outline => "outline",
        _ => "",
    }

def dismiss_button {Msg : Type} (label : String) (on_dismiss : Option Msg) : List (Oak.Node Msg) :=
    match on_dismiss {
        Option.none => List.empty,
        Option.some m =>
            [Ui.icon_button [Ui.ghost, Ui.small, Ui.cls ["oak-dismiss"]] label (Ui.icon "close")
                [Html.on_click m]],
    }

def title_node {Msg : Type} (block : String) (title : String) : List (Oak.Node Msg) :=
    if String.is_empty title then List.empty
    else [Html.strong [Html.class_ [String.concat block "__title"]] [Html.text title]]

#[terminating]
def skeleton_lines {Msg : Type} (n : I64) : List (Oak.Node Msg) :=
    if I64.lt n 1 then List.empty
    else List.cons (Html.div [Html.class_ ["oak-skeleton__line"]] List.empty) (skeleton_lines (I64.sub n 1))

def toast_node {Msg : Type} (on_dismiss : String -> Msg) (t : Ui.Toast) : Oak.Node Msg :=
    match t {
        { id, tone, title, body } =>
            Html.div
                [Html.key id, Html.class_ ["oak-toast", Ui.tone_class tone],
                    Html.role (live_role tone)]
                (List.append
                    [Html.div [Html.class_ ["oak-toast__content"]]
                        (List.append (title_node "oak-toast" title)
                            (if String.is_empty body then List.empty
                                else [Html.p [Html.class_ ["oak-toast__body"]] [Html.text body]]))]
                    (dismiss_button "Dismiss notification" (Option.some (on_dismiss id))))
    }

#[terminating]
def toast_nodes {Msg : Type} (on_dismiss : String -> Msg) (ts : List Ui.Toast) : List (Oak.Node Msg) :=
    match ts {
        List.empty => List.empty,
        List.cons t rest => List.cons (toast_node on_dismiss t) (toast_nodes on_dismiss rest),
    }

with Ui {
    /// A message box. `title` may be `""`; `on_dismiss` adds a close
    /// button. Danger/warning alerts use `role="alert"`, others `status`.
    pub def alert {Msg : Type} (opts : List Ui.Opt) (title : String) (on_dismiss : Option Msg)
        (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve_from { Ui.Style.default with tone := Ui.Tone.tone_info } opts in
        Html.div
            (Ui.root_attrs "oak-alert" List.empty [Ui.tone_class s.tone] s
                (List.cons (Html.role (live_role s.tone)) attrs))
            (List.append
                [Html.div [Html.class_ ["oak-alert__content"]]
                    (List.append (title_node "oak-alert" title)
                        [Html.div [Html.class_ ["oak-alert__body"]] children])]
                (dismiss_button "Dismiss" on_dismiss))

    /// A small status label. Soft by default; `Ui.solid`/`Ui.outline`.
    pub def badge {Msg : Type} (opts : List Ui.Opt) (label : String) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve_from soft_base opts in
        Html.span
            (Ui.root_attrs "oak-badge" [variant_mod s.variant, Ui.size_mod s.size] [Ui.tone_class s.tone] s List.empty)
            [Html.text label]

    /// A chip, removable when `on_remove` is given.
    pub def tag {Msg : Type} (opts : List Ui.Opt) (label : String) (on_remove : Option Msg) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve_from soft_base opts in
        Html.span (Ui.root_attrs "oak-tag" [variant_mod s.variant] [Ui.tone_class s.tone] s List.empty)
            (List.cons (Html.span [Html.class_ ["oak-tag__label"]] [Html.text label])
                (dismiss_button (String.concat "Remove " label) on_remove))

    /// A busy indicator. `label` is announced to assistive technology.
    pub def spinner {Msg : Type} (opts : List Ui.Opt) (label : String) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.span (Ui.root_attrs "oak-spinner" [Ui.size_mod s.size] [Ui.tone_class s.tone] s [Html.role "status"])
            [Html.span [Html.class_ ["oak-sr-only"]] [Html.text label]]

    /// A progress bar. `max <= 0` renders an indeterminate bar.
    pub def progress {Msg : Type} (opts : List Ui.Opt) (label : String) (value : I64) (max : I64) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve_from { Ui.Style.default with tone := Ui.Tone.tone_primary } opts in
        let amounts : List (Oak.Attr Msg) :=
            if I64.lt 0 max
            then [Html.attr "value" (I64.to_string value), Html.attr "max" (I64.to_string max)]
            else List.empty in
        Html.progress
            (Ui.root_attrs "oak-progress" [Ui.size_mod s.size] [Ui.tone_class s.tone] s
                (List.cons (Html.aria "label" label) amounts))
            List.empty

    /// A loading placeholder of `lines` shimmering bars.
    pub def skeleton {Msg : Type} (opts : List Ui.Opt) (lines : I64) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div (Ui.root_attrs "oak-skeleton" List.empty List.empty s [Html.aria "hidden" "true"])
            (skeleton_lines lines)

    /// "Nothing here yet": a title, a description and optional actions.
    pub def empty_state {Msg : Type} (opts : List Ui.Opt) (title : String) (description : String)
        (actions : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div (Ui.root_attrs "oak-empty" List.empty List.empty s List.empty)
            (List.append
                [Html.p [Html.class_ ["oak-empty__title"]] [Html.text title],
                    Html.p [Html.class_ ["oak-empty__description"]] [Html.text description]]
                (if List.is_empty actions then List.empty
                    else [Html.div [Html.class_ ["oak-empty__actions"]] actions]))

    /// A toast value.
    pub def toast (id : String) (tone : Ui.Tone) (title : String) (body : String) : Ui.Toast :=
        { id := id, tone := tone, title := title, body := body }

    /// The fixed corner region that shows `toasts` (keyed by id, so
    /// dismissing one keeps the others' DOM). The app owns the list: add
    /// on events, remove in `on_dismiss` (and on a timer, if it wants).
    pub def toast_region {Msg : Type} (opts : List Ui.Opt) (toasts : List Ui.Toast)
        (on_dismiss : String -> Msg) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div
            (Ui.root_attrs "oak-toasts" List.empty List.empty s
                [Html.role "region", Html.aria "label" "Notifications", Html.aria "live" "polite"])
            (toast_nodes on_dismiss toasts)
}
