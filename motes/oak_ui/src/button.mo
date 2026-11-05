// Buttons and icons.
//
// A button's look is three independent modifiers: tone (colour), variant
// (solid / soft / outline / ghost / plain) and size. `Ui.button` is
// `type="button"` so it never submits a surrounding form by accident;
// `Ui.submit_button` is the one that does.

use oak::typed {Oak.Attr, Oak.Node}
use oak::elements {
    Html.button, Html.a, Html.span, Html.div, Html.href, Html.type_, Html.disabled,
    Html.aria, Html.role, Html.class_, Html.text, Html.title_attr,
}
use lib::vocab {Ui.Opt, Ui.Style, Ui.Variant, Ui.resolve, Ui.Variant.slug}
use lib::base {Ui.root_attrs, Ui.tone_class, Ui.size_mod}

def variant_mod (v : Ui.Variant) : String :=
    match v {
        Ui.Variant.variant_solid => "",
        _ => Ui.Variant.slug v,
    }

def button_mods (s : Ui.Style) : List String :=
    [variant_mod s.variant, Ui.size_mod s.size,
        if s.full_width then "full" else "",
        if s.loading then "loading" else ""]

/// `disabled` + `aria-busy` as the style asks. A loading button is disabled
/// too: a second click must not fire while the first is in flight.
def state_attrs {Msg : Type} (s : Ui.Style) : List (Oak.Attr Msg) :=
    List.append
        (if s.disabled || s.loading then [Html.disabled] else List.empty)
        (if s.loading then [Html.aria "busy" "true"] else List.empty)

def with_spinner {Msg : Type} (s : Ui.Style) (children : List (Oak.Node Msg)) : List (Oak.Node Msg) :=
    if s.loading
    then List.cons (Html.span [Html.class_ ["oak-btn__spinner"], Html.aria "hidden" "true"] List.empty) children
    else children

def button_with_type {Msg : Type} (kind : String) (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
    (children : List (Oak.Node Msg)) : Oak.Node Msg :=
    let s : Ui.Style := Ui.resolve opts in
    Html.button
        (Ui.root_attrs "oak-btn" (button_mods s) [Ui.tone_class s.tone] s
            (List.cons (Html.type_ kind) (List.append (state_attrs s) attrs)))
        (with_spinner s children)

/// Icon name -> glyph. Unicode, not SVG: the browser runtime creates
/// elements without a namespace, so inline SVG would not render.
pub def Ui.icon_glyphs : List (Pair String String) :=
    [Pair.pair "close" "\u{00D7}", Pair.pair "check" "\u{2713}",
        Pair.pair "chevron-down" "\u{25BE}", Pair.pair "chevron-up" "\u{25B4}",
        Pair.pair "chevron-left" "\u{2039}", Pair.pair "chevron-right" "\u{203A}",
        Pair.pair "menu" "\u{2630}", Pair.pair "search" "\u{2315}",
        Pair.pair "plus" "+", Pair.pair "minus" "\u{2212}",
        Pair.pair "info" "\u{2139}", Pair.pair "warning" "\u{26A0}",
        Pair.pair "error" "\u{2716}", Pair.pair "external" "\u{2197}",
        Pair.pair "more" "\u{22EF}", Pair.pair "arrow-up" "\u{2191}",
        Pair.pair "arrow-down" "\u{2193}", Pair.pair "sort" "\u{2195}"]

#[terminating]
def lookup_glyph (name : String) (table : List (Pair String String)) : String :=
    match table {
        List.empty => "",
        List.cons entry rest =>
            match entry {
                Pair.pair k glyph => if String.beq k name then glyph else lookup_glyph name rest
            },
    }

with Ui {
    /// A button. Modifiers: tone (`Ui.primary`…), variant (`Ui.outline`…),
    /// size (`Ui.small`/`Ui.large`), `Ui.full`, `Ui.busy`, `Ui.inactive`.
    pub def button {Msg : Type} (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        button_with_type "button" opts attrs children

    /// A `type="submit"` button for forms.
    pub def submit_button {Msg : Type} (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        button_with_type "submit" opts attrs children

    /// An anchor styled as a button (navigation, not an action).
    pub def link_button {Msg : Type} (opts : List Ui.Opt) (url : String) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.a (Ui.root_attrs "oak-btn" (button_mods s) [Ui.tone_class s.tone] s (List.cons (Html.href url) attrs))
            children

    /// A square button holding only an icon. `label` is required: it is the
    /// button's accessible name (`aria-label`) and its tooltip (`title`).
    pub def icon_button {Msg : Type} (opts : List Ui.Opt) (label : String) (icon : Oak.Node Msg)
        (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.button
            (Ui.root_attrs "oak-btn" (List.cons "icon" (button_mods s)) [Ui.tone_class s.tone] s
                (List.append [Html.type_ "button", Html.aria "label" label, Html.title_attr label]
                    (List.append (state_attrs s) attrs)))
            [icon]

    /// Buttons joined into one control (`role="group"`).
    pub def button_group {Msg : Type} (opts : List Ui.Opt) (label : String) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div (Ui.root_attrs "oak-btn-group" List.empty List.empty s
            (List.append [Html.role "group", Html.aria "label" label] attrs)) children

    /// A decorative icon by name (see `Ui.icon_glyphs`; unknown names
    /// render empty). Hidden from assistive technology: name the control
    /// that holds it instead.
    pub def icon {Msg : Type} (name : String) : Oak.Node Msg :=
        Html.span [Html.class_ ["oak-icon"], Html.aria "hidden" "true"] [Html.text (lookup_glyph name Ui.icon_glyphs)]
}
