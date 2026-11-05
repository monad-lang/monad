// Layout primitives: stacks, rows, grids, containers and the app shell.
//
// Spacing is a step on the theme's scale (`Ui.gap 0`-`Ui.gap 8`), never a
// length, so layouts follow the theme's `--oak-space` unit.

use oak::typed {Oak.Attr, Oak.Node}
use oak::elements {
    Html.div, Html.hr, Html.header, Html.aside, Html.main_, Html.footer, Html.class_,
}
use lib::vocab {
    Ui.Opt, Ui.Style, Ui.Align, Ui.Size, Ui.Style.default, Ui.resolve, Ui.resolve_from,
}
use lib::base {Ui.root_attrs, Ui.gap_class, Ui.align_class, Ui.justify_class}

def flex_extra (s : Ui.Style) : List String :=
    [Ui.gap_class s.gap, Ui.align_class s.align, Ui.justify_class s.justify]

def wrap_mods (s : Ui.Style) : List String :=
    if s.wrap then ["wrap"] else List.empty

def row_base : Ui.Style := { Ui.Style.default with align := Ui.Align.center }

def grid_mod (cols : I64) : String :=
    if I64.beq cols 0 then "auto"
    else if I64.lt cols 2 then ""
    else String.concat "cols-" (I64.to_string (if I64.lt 6 cols then 6 else cols))

def container_mod (z : Ui.Size) : String :=
    match z {
        Ui.Size.sm => "sm",
        Ui.Size.md => "",
        Ui.Size.lg => "lg",
    }

with Ui {
    /// A vertical flex column. Modifiers: `gap`, `align`, `justify`,
    /// `wrapping`, `cls`.
    pub def stack {Msg : Type} (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div (Ui.root_attrs "oak-stack" (wrap_mods s) (flex_extra s) s attrs) children

    /// A horizontal flex row, vertically centred by default.
    pub def row {Msg : Type} (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve_from row_base opts in
        Html.div (Ui.root_attrs "oak-row" (wrap_mods s) (flex_extra s) s attrs) children

    /// A wrapping row: tags, button clusters, toolbars.
    pub def cluster {Msg : Type} (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve_from { row_base with wrap := true, gap := 2 } opts in
        Html.div (Ui.root_attrs "oak-row" (wrap_mods s) (flex_extra s) s attrs) children

    /// An equal-column grid. `Ui.cols n` (2-6) collapses to one column on
    /// narrow screens; `Ui.cols 0` auto-fits columns of at least 16rem.
    pub def grid {Msg : Type} (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div (Ui.root_attrs "oak-grid" [grid_mod s.cols] [Ui.gap_class s.gap] s attrs) children

    /// A centred, max-width page column (`Ui.small`/`Ui.large` for narrow
    /// and wide).
    pub def container {Msg : Type} (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div (Ui.root_attrs "oak-container" [container_mod s.size] List.empty s attrs) children

    /// Centre children on both axes.
    pub def center {Msg : Type} (opts : List Ui.Opt) (attrs : List (Oak.Attr Msg))
        (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div (Ui.root_attrs "oak-center" List.empty List.empty s attrs) children

    /// Takes the free space in a row (pushes later siblings to the end).
    pub def spacer {Msg : Type} : Oak.Node Msg :=
        Html.div [Html.class_ ["oak-spacer"]] List.empty

    /// A horizontal rule.
    pub def divider {Msg : Type} (opts : List Ui.Opt) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.hr (Ui.root_attrs "oak-divider" List.empty List.empty s List.empty)

    /// The application frame: a header bar, an optional sidebar (pass
    /// `List.empty` for none), the main region and a footer. On narrow
    /// screens the sidebar hides unless `nav_open`, which the app toggles
    /// from its own menu button.
    pub def app_shell {Msg : Type} (opts : List Ui.Opt) (nav_open : Bool)
        (header : List (Oak.Node Msg)) (sidebar : List (Oak.Node Msg))
        (content : List (Oak.Node Msg)) (footer : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        let no_sidebar : Bool := List.is_empty sidebar in
        let mods : List String :=
            [if no_sidebar then "no-sidebar" else "", if nav_open then "nav-open" else ""] in
        let sidebar_nodes : List (Oak.Node Msg) :=
            if no_sidebar then List.empty
            else [Html.aside [Html.class_ ["oak-shell__sidebar"]] sidebar] in
        Html.div (Ui.root_attrs "oak-shell" mods List.empty s List.empty)
            (List.append
                [Html.header [Html.class_ ["oak-shell__header"]] header]
                (List.append sidebar_nodes
                    [Html.main_ [Html.class_ ["oak-shell__main"]] content,
                        Html.footer [Html.class_ ["oak-shell__footer"]] footer]))
}
