// Forms: a labelled field wrapper and controlled inputs.
//
// Every control takes its `attrs` LAST, so a partially applied control is a
// `List (Oak.Attr Msg) -> Oak.Node Msg`. `Ui.field` takes exactly that and
// supplies the wiring itself (`id`, `aria-describedby`, `aria-invalid`,
// `required`), so the label, help text and error can never drift from the
// control they describe:
//
//     Ui.field [Ui.required] "email" "Email" "We never share it." model.email_error
//         (Ui.input [] "email" model.email EmailChanged)
//
// Controls are controlled: the caller passes the current value and a
// message constructor; the model is the source of truth. Without the
// browser runtime (SSR), use `Ui.form`'s native `action`/`method` fallback.

use std::list {List.intercalate}
use web_event::event {WebEvent, HandlerResult, ListenerFlags, FileInfo}
use oak::typed {Oak.Attr, Oak.Node}
use oak::elements {
    Html.div, Html.span, Html.p, Html.label, Html.input, Html.textarea, Html.select, Html.option,
    Html.form, Html.id_, Html.for_, Html.type_, Html.value_, Html.name_, Html.checked, Html.selected,
    Html.disabled, Html.required, Html.attr, Html.aria, Html.role, Html.class_, Html.text,
    Html.min_, Html.max_, Html.step,
}
use oak::events {Html.on, Html.on_input, Html.on_change, Html.on_submit_prevent}
use lib::vocab {Ui.Opt, Ui.Style, Ui.resolve}
use lib::base {Ui.root_attrs, Ui.size_mod}

// ═══ Field wiring ═══

def help_id (id : String) : String := String.concat id "-help"

def error_id (id : String) : String := String.concat id "-error"

def described_by (id : String) (help : String) (error : String) : List String :=
    List.append
        (if String.is_empty help then List.empty else [help_id id])
        (if String.is_empty error then List.empty else [error_id id])

/// The attributes `Ui.field` hands its control.
def wiring {Msg : Type} (s : Ui.Style) (id : String) (help : String) (error : String) : List (Oak.Attr Msg) :=
    let ids : List String := described_by id help error in
    List.append [Html.id_ id]
        (List.append
            (if List.is_empty ids then List.empty else [Html.aria "describedby" (List.intercalate " " ids)])
            (List.append
                (if String.is_empty error then List.empty else [Html.aria "invalid" "true"])
                (List.append
                    (if s.required then [Html.required] else List.empty)
                    (if s.disabled then [Html.disabled] else List.empty))))

def required_mark {Msg : Type} (s : Ui.Style) : List (Oak.Node Msg) :=
    if s.required
    then [Html.span [Html.class_ ["oak-field__required"], Html.aria "hidden" "true"] [Html.text "*"]]
    else List.empty

def help_node {Msg : Type} (id : String) (help : String) : List (Oak.Node Msg) :=
    if String.is_empty help then List.empty
    else [Html.p [Html.class_ ["oak-field__help"], Html.id_ (help_id id)] [Html.text help]]

def error_node {Msg : Type} (id : String) (error : String) : List (Oak.Node Msg) :=
    if String.is_empty error then List.empty
    else [Html.p [Html.class_ ["oak-field__error"], Html.id_ (error_id id)] [Html.text error]]

// ═══ Control helpers ═══

def control_mods (s : Ui.Style) : List String :=
    [Ui.size_mod s.size, if s.full_width then "full" else ""]

def checked_handler {Msg : Type} (f : Bool -> Msg) : WebEvent -> HandlerResult Msg :=
    fn (e : WebEvent) => HandlerResult.msg (f e.checked)

def files_handler {Msg : Type} (f : List FileInfo -> Msg) : WebEvent -> HandlerResult Msg :=
    fn (e : WebEvent) => HandlerResult.msg (f e.files)

def option_node {Msg : Type} (current : String) (opt : Pair String String) : Oak.Node Msg :=
    match opt {
        Pair.pair value label =>
            Html.option
                (List.cons (Html.value_ value) (if String.beq value current then [Html.selected] else List.empty))
                [Html.text label]
    }

#[terminating]
def option_nodes {Msg : Type} (current : String) (opts : List (Pair String String)) : List (Oak.Node Msg) :=
    match opts {
        List.empty => List.empty,
        List.cons o rest => List.cons (option_node current o) (option_nodes current rest),
    }

def radio_node {Msg : Type} (s : Ui.Style) (group : String) (current : String) (on_change : String -> Msg)
    (opt : Pair String String) : Oak.Node Msg :=
    match opt {
        Pair.pair value label =>
            Html.label [Html.class_ ["oak-check"]]
                [Html.input
                    (List.append
                        [Html.class_ ["oak-check__box", "oak-check__box--radio"], Html.type_ "radio",
                            Html.name_ group, Html.value_ value, Html.on_change on_change]
                        (List.append
                            (if String.beq value current then [Html.checked] else List.empty)
                            (if s.disabled then [Html.disabled] else List.empty))),
                    Html.span [Html.class_ ["oak-check__label"]] [Html.text label]]
    }

#[terminating]
def radio_nodes {Msg : Type} (s : Ui.Style) (group : String) (current : String) (on_change : String -> Msg)
    (opts : List (Pair String String)) : List (Oak.Node Msg) :=
    match opts {
        List.empty => List.empty,
        List.cons o rest =>
            List.cons (radio_node s group current on_change o) (radio_nodes s group current on_change rest),
    }

def check_like {Msg : Type} (block_mod : String) (extra : List (Oak.Attr Msg)) (opts : List Ui.Opt)
    (label : String) (is_checked : Bool) (on_toggle : Bool -> Msg) (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
    let s : Ui.Style := Ui.resolve opts in
    Html.label (Ui.root_attrs "oak-check" [block_mod] List.empty s List.empty)
        [Html.input
            (List.append
                [Html.class_ ["oak-check__box"], Html.type_ "checkbox",
                    Html.on "change" ListenerFlags.none (checked_handler on_toggle)]
                (List.append extra
                    (List.append
                        (if is_checked then [Html.checked] else List.empty)
                        (List.append (if s.disabled then [Html.disabled] else List.empty) attrs)))),
            Html.span [Html.class_ ["oak-check__label"]] [Html.text label]]

with Ui {
    /// A labelled form field: label, control, help text and error message.
    /// Pass `""` for no help or no error; a non-empty error marks the
    /// control invalid. `Ui.required` adds `required` and a visual marker.
    pub def field {Msg : Type} (opts : List Ui.Opt) (id : String) (label : String) (help : String)
        (error : String) (control : List (Oak.Attr Msg) -> Oak.Node Msg) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        let mods : List String := [if String.is_empty error then "" else "invalid"] in
        Html.div (Ui.root_attrs "oak-field" mods List.empty s List.empty)
            (List.append
                [Html.label [Html.class_ ["oak-field__label"], Html.for_ id]
                    (List.cons (Html.text label) (required_mark s)),
                    control (wiring s id help error)]
                (List.append (help_node id help) (error_node id error)))

    /// A single-line input of HTML type `kind` (`text`, `email`,
    /// `password`, `search`, `url`, `tel`, `number`, `date`, …).
    pub def input {Msg : Type} (opts : List Ui.Opt) (kind : String) (value : String)
        (on_input : String -> Msg) (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.input
            (Ui.root_attrs "oak-input" (control_mods s) List.empty s
                (List.append [Html.type_ kind, Html.value_ value, Html.on_input on_input] attrs))

    /// `Ui.input` with `kind = "text"`.
    pub def text_input {Msg : Type} (opts : List Ui.Opt) (value : String) (on_input : String -> Msg)
        (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        Ui.input opts "text" value on_input attrs

    /// A multi-line text input.
    pub def textarea {Msg : Type} (opts : List Ui.Opt) (value : String) (on_input : String -> Msg)
        (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.textarea
            (Ui.root_attrs "oak-input" (List.cons "textarea" (control_mods s)) List.empty s
                (List.cons (Html.on_input on_input) attrs))
            [Html.text value]

    /// A drop-down over `(value, label)` options; `current` is selected.
    pub def select {Msg : Type} (opts : List Ui.Opt) (options : List (Pair String String)) (current : String)
        (on_change : String -> Msg) (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.select
            (Ui.root_attrs "oak-input" (List.cons "select" (control_mods s)) List.empty s
                (List.cons (Html.on_change on_change) attrs))
            (option_nodes current options)

    /// A checkbox with its label. `on_toggle` receives the new state.
    pub def checkbox {Msg : Type} (opts : List Ui.Opt) (label : String) (is_checked : Bool)
        (on_toggle : Bool -> Msg) (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        check_like "" List.empty opts label is_checked on_toggle attrs

    /// An on/off switch: a checkbox with `role="switch"`.
    pub def switch {Msg : Type} (opts : List Ui.Opt) (label : String) (is_on : Bool)
        (on_toggle : Bool -> Msg) (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        check_like "switch" [Html.role "switch"] opts label is_on on_toggle attrs

    /// Mutually exclusive choices over `(value, label)` options, sharing
    /// the radio `group` name. `legend` labels the group, so do not wrap it
    /// in `Ui.field`: a `<label for>` cannot target the group's `<div>`.
    pub def radio_group {Msg : Type} (opts : List Ui.Opt) (group : String) (legend : String)
        (options : List (Pair String String)) (current : String) (on_change : String -> Msg)
        (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div
            (Ui.root_attrs "oak-radio-group" List.empty List.empty s
                (List.append [Html.role "radiogroup", Html.aria "label" legend] attrs))
            (radio_nodes s group current on_change options)

    /// A slider over `[min, max]` in `step`s. The value arrives as text.
    pub def range {Msg : Type} (opts : List Ui.Opt) (min : I64) (max : I64) (step : I64) (value : I64)
        (on_input : String -> Msg) (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.input
            (Ui.root_attrs "oak-range" List.empty List.empty s
                (List.append
                    [Html.type_ "range", Html.min_ (I64.to_string min), Html.max_ (I64.to_string max),
                        Html.step (I64.to_string step), Html.value_ (I64.to_string value),
                        Html.on_input on_input]
                    attrs))

    /// A file picker. `on_files` receives the chosen files' metadata.
    pub def file_input {Msg : Type} (opts : List Ui.Opt) (accept : String) (on_files : List FileInfo -> Msg)
        (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.input
            (Ui.root_attrs "oak-input" (List.cons "file" (control_mods s)) List.empty s
                (List.append
                    [Html.type_ "file", Html.attr "accept" accept,
                        Html.on "change" ListenerFlags.none (files_handler on_files)]
                    attrs))

    /// A control with leading/trailing addons (a unit, an icon, a button).
    /// Like the controls, it takes the wiring attrs last, so it nests in
    /// `Ui.field`: `Ui.field … (Ui.input_group [] prefix (Ui.text_input …) suffix)`.
    pub def input_group {Msg : Type} (opts : List Ui.Opt) (prefix : List (Oak.Node Msg))
        (control : List (Oak.Attr Msg) -> Oak.Node Msg) (suffix : List (Oak.Node Msg))
        (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div (Ui.root_attrs "oak-input-group" List.empty List.empty s List.empty)
            (List.append (addon prefix) (List.cons (control attrs) (addon suffix)))

    /// A form whose submit becomes `on_submit` (default prevented). Pass
    /// `Html.action`/`Html.method_` in `attrs` so it still posts without
    /// the browser runtime.
    pub def form {Msg : Type} (opts : List Ui.Opt) (on_submit : Msg) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.form (Ui.root_attrs "oak-form" List.empty List.empty s (List.cons (Html.on_submit_prevent on_submit) attrs))
            children
}

def addon {Msg : Type} (nodes : List (Oak.Node Msg)) : List (Oak.Node Msg) :=
    if List.is_empty nodes then List.empty
    else [Html.span [Html.class_ ["oak-input-group__addon"]] nodes]
