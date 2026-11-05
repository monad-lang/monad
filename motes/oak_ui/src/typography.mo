// Text: headings, paragraphs, inline code, code blocks, keys and links.

use oak::typed {Oak.Attr, Oak.Node}
use oak::elements {Html.node, Html.p, Html.span, Html.code, Html.pre, Html.kbd, Html.a, Html.href, Html.class_, Html.text}
use lib::vocab {Ui.Opt, Ui.Style, Ui.resolve}
use lib::base {Ui.root_attrs, Ui.tone_mod, Ui.size_mod}

def clamp_level (level : I64) : I64 :=
    if I64.lt level 1 then 1 else if I64.lt 6 level then 6 else level

def text_mods (s : Ui.Style) : List String := [Ui.size_mod s.size, Ui.tone_mod s.tone]

with Ui {
    /// `<h1>`-`<h6>` (the level is clamped). The visual size follows the
    /// level; pass `Ui.cls` to decouple them.
    pub def heading {Msg : Type} (level : I64) (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        let n : String := I64.to_string (clamp_level level) in
        Html.node (String.concat "h" n) (Ui.root_attrs "oak-heading" [n] List.empty s attrs) children

    /// A paragraph. `Ui.small`/`Ui.large` size it; a tone colours it.
    pub def text {Msg : Type} (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.p (Ui.root_attrs "oak-text" (text_mods s) List.empty s attrs) children

    /// Secondary, de-emphasised text.
    pub def muted {Msg : Type} (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.p (Ui.root_attrs "oak-text" (List.cons "muted" (text_mods s)) List.empty s attrs) children

    /// Inline text with the same modifiers as `Ui.text` (a `<span>`).
    pub def inline {Msg : Type} (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.span (Ui.root_attrs "oak-text" (text_mods s) List.empty s attrs) children

    /// Inline code.
    pub def code {Msg : Type} (content : String) : Oak.Node Msg :=
        Html.code [Html.class_ ["oak-code"]] [Html.text content]

    /// A preformatted code block. Whitespace is kept verbatim.
    pub def code_block {Msg : Type} (opts : List Ui.Opt) (content : String) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.pre (Ui.root_attrs "oak-code-block" List.empty List.empty s List.empty)
            [Html.code List.empty [Html.text content]]

    /// A keyboard key (`Ui.kbd "Ctrl"`).
    pub def kbd {Msg : Type} (key : String) : Oak.Node Msg :=
        Html.kbd [Html.class_ ["oak-kbd"]] [Html.text key]

    /// A styled anchor.
    pub def link {Msg : Type} (opts : List Ui.Opt) (url : String) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.a (Ui.root_attrs "oak-link" List.empty List.empty s (List.cons (Html.href url) attrs)) children
}
