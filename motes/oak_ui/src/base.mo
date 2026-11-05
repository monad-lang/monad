// Plumbing every component shares: the root class attribute, tone/size
// modifier slugs, and the `<style>` node for server-rendered heads.
//
// `Ui.root_attrs` is public so an application's own components can follow
// the same `oak-<block>` convention and honour `Ui.cls`.

use oak::typed {Oak.Attr, Oak.Node}
use oak::elements {Html.attr, Html.style}
use lib::vocab {
    Ui.Style, Ui.Tone, Ui.Size, Ui.Align, Ui.class_names,
    Ui.Tone.slug, Ui.Size.slug, Ui.Align.slug,
}
use lib::theme {Ui.Theme}
use lib::css {Ui.stylesheet, Ui.stylesheet_auto}

/// `class="<block> <block>--<mod>… <extra…> <s.classes…>"` followed by the
/// caller's attributes. Caller attributes come last, so a caller `id`,
/// `aria-*` or handler is never shadowed.
pub def Ui.root_attrs {Msg : Type} (block : String) (mods : List String) (extra : List String)
    (s : Ui.Style) (attrs : List (Oak.Attr Msg)) : List (Oak.Attr Msg) :=
    List.cons (Html.attr "class" (Ui.class_names block mods (List.append extra s.classes))) attrs

/// The tone modifier, empty for neutral (the unmarked default).
pub def Ui.tone_mod (t : Ui.Tone) : String :=
    match t {
        Ui.Tone.neutral => "",
        _ => Ui.Tone.slug t,
    }

/// The size modifier, empty for md (the unmarked default).
pub def Ui.size_mod (z : Ui.Size) : String :=
    match z {
        Ui.Size.md => "",
        _ => Ui.Size.slug z,
    }

/// `oak-gap-N`, clamped to the 0-8 scale.
pub def Ui.gap_class (n : I64) : String :=
    let k : I64 := if I64.lt n 0 then 0 else if I64.lt 8 n then 8 else n in
    String.concat "oak-gap-" (I64.to_string k)

pub def Ui.align_class (a : Ui.Align) : String := String.concat "oak-align-" (Ui.Align.slug a)

pub def Ui.justify_class (a : Ui.Align) : String := String.concat "oak-justify-" (Ui.Align.slug a)

/// A `<style>` node with one theme's variables and the whole sheet, for a
/// server-rendered `<head>`.
pub def Ui.style_tag {Msg : Type} (t : Ui.Theme) : Oak.Node Msg :=
    Html.style List.empty (Ui.stylesheet t)

/// As `Ui.style_tag`, with light/dark variables (`Ui.Theme.css_auto`).
pub def Ui.style_tag_auto {Msg : Type} (light : Ui.Theme) (dark : Ui.Theme) : Oak.Node Msg :=
    Html.style List.empty (Ui.stylesheet_auto light dark)
