// Data display: cards, description lists, list groups, avatars, stats and
// tables.
//
// `Ui.table` is column-driven: each `Ui.Column R Msg` names a key, a header
// and a cell renderer for a row of type `R`. Sorting is controlled: the
// table shows `Ui.SortState` (with `aria-sort`) and reports header clicks
// through `on_sort key`; the app reorders its rows (`Ui.SortState.toggle`
// is the usual update).

use oak::typed {Oak.Attr, Oak.Node}
use oak::elements {
    Html.div, Html.span, Html.section, Html.header, Html.footer, Html.p, Html.img, Html.src, Html.alt,
    Html.dl, Html.dt, Html.dd, Html.ul, Html.li,
    Html.table, Html.caption, Html.thead, Html.tbody, Html.tr, Html.th, Html.td, Html.button, Html.type_,
    Html.attr, Html.aria, Html.role, Html.class_, Html.class_list, Html.text, Html.key,
}
use oak::events {Html.on_click}
use lib::vocab {Ui.Opt, Ui.Style, Ui.Tone, Ui.Align, Ui.resolve, Ui.Align.slug, Ui.cls}
use lib::base {Ui.root_attrs, Ui.tone_class, Ui.size_mod}
use lib::button {Ui.icon}

// ═══ Table types ═══

pub type Ui.Column (R : Type) (Msg : Type) {
    ui_column (key : String) (header : String) (cell : R -> Oak.Node Msg) (sortable : Bool) (align : Ui.Align)
}

/// Which column the rows are sorted by (`""` for none) and in which
/// direction. Every field is named at each literal.
pub struct Ui.SortState {
    column : String,
    ascending : Bool
}

pub instance Copy Ui.SortState {
    def copy (s : Ui.SortState) : Pair Ui.SortState Ui.SortState := Pair.pair s s
}

pub def Ui.SortState.none : Ui.SortState := { column := "", ascending := true }

/// The usual header-click update: the same column flips direction, a new
/// column starts ascending.
pub def Ui.SortState.toggle (s : Ui.SortState) (key : String) : Ui.SortState :=
    if String.beq s.column key
    then { column := key, ascending := Bool.not s.ascending }
    else { column := key, ascending := true }

/// A column showing `cell row`, not sortable, start-aligned.
pub def Ui.column {R : Type} {Msg : Type} (key : String) (header : String) (cell : R -> Oak.Node Msg)
    : Ui.Column R Msg :=
    Ui.Column.ui_column key header cell false Ui.Align.align_start

/// The same column, sortable from its header.
pub def Ui.Column.sortable {R : Type} {Msg : Type} (c : Ui.Column R Msg) : Ui.Column R Msg :=
    match c { Ui.Column.ui_column k h cell _ a => Ui.Column.ui_column k h cell true a }

/// The same column, end-aligned (numbers, amounts).
pub def Ui.Column.numeric {R : Type} {Msg : Type} (c : Ui.Column R Msg) : Ui.Column R Msg :=
    match c { Ui.Column.ui_column k h cell s _ => Ui.Column.ui_column k h cell s Ui.Align.align_end }

// ═══ Table rendering ═══

def align_mod (a : Ui.Align) : String :=
    match a {
        Ui.Align.align_start => "",
        _ => Ui.Align.slug a,
    }

/// `class` for a header/body cell: the base class plus the alignment class
/// when the column is not start-aligned.
def cell_class {Msg : Type} (base : String) (a : Ui.Align) : Oak.Attr Msg :=
    let m : String := align_mod a in
    Html.class_list [Pair.pair base true, Pair.pair (String.concat "oak-table__cell--" m) (Bool.not (String.is_empty m))]

def sort_value (sort : Ui.SortState) (key : String) : String :=
    if String.beq sort.column key
    then (if sort.ascending then "ascending" else "descending")
    else "none"

def sort_icon {Msg : Type} (sort : Ui.SortState) (key : String) : Oak.Node Msg :=
    if String.beq sort.column key
    then Ui.icon (if sort.ascending then "arrow-up" else "arrow-down")
    else Ui.icon "sort"

def header_cell {R : Type} {Msg : Type} (sort : Ui.SortState) (on_sort : String -> Msg) (c : Ui.Column R Msg)
    : Oak.Node Msg :=
    match c {
        Ui.Column.ui_column k h _ sortable a =>
            if sortable
            then
                Html.th [cell_class "oak-table__th" a, Html.attr "scope" "col", Html.aria "sort" (sort_value sort k)]
                    [Html.button [Html.class_ ["oak-table__sort"], Html.type_ "button", Html.on_click (on_sort k)]
                        [Html.text h, sort_icon sort k]]
            else Html.th [cell_class "oak-table__th" a, Html.attr "scope" "col"] [Html.text h]
    }

#[terminating]
def header_cells {R : Type} {Msg : Type} (sort : Ui.SortState) (on_sort : String -> Msg)
    (cs : List (Ui.Column R Msg)) : List (Oak.Node Msg) :=
    match cs {
        List.empty => List.empty,
        List.cons c rest => List.cons (header_cell sort on_sort c) (header_cells sort on_sort rest),
    }

def body_cell {R : Type} {Msg : Type} (row : R) (c : Ui.Column R Msg) : Oak.Node Msg :=
    match c {
        Ui.Column.ui_column _ _ cell _ a =>
            Html.td [cell_class "oak-table__td" a]
                [cell row]
    }

#[terminating]
def body_cells {R : Type} {Msg : Type} (row : R) (cs : List (Ui.Column R Msg)) : List (Oak.Node Msg) :=
    match cs {
        List.empty => List.empty,
        List.cons c rest => List.cons (body_cell row c) (body_cells row rest),
    }

#[terminating]
def body_rows {R : Type} {Msg : Type} (row_key : R -> String) (cs : List (Ui.Column R Msg)) (rows : List R)
    : List (Oak.Node Msg) :=
    match rows {
        List.empty => List.empty,
        List.cons row rest =>
            List.cons (Html.tr [Html.key (row_key row), Html.class_ ["oak-table__row"]] (body_cells row cs))
                (body_rows row_key cs rest),
    }

// ═══ Small helpers ═══

def dl_item {Msg : Type} (item : Pair String (Oak.Node Msg)) : List (Oak.Node Msg) :=
    match item {
        Pair.pair term detail =>
            [Html.dt [Html.class_ ["oak-dl__term"]] [Html.text term],
                Html.dd [Html.class_ ["oak-dl__detail"]] [detail]]
    }

#[terminating]
def dl_items {Msg : Type} (items : List (Pair String (Oak.Node Msg))) : List (Oak.Node Msg) :=
    match items {
        List.empty => List.empty,
        List.cons i rest => List.append (dl_item i) (dl_items rest),
    }

#[terminating]
def list_items {Msg : Type} (items : List (Oak.Node Msg)) : List (Oak.Node Msg) :=
    match items {
        List.empty => List.empty,
        List.cons i rest => List.cons (Html.li [Html.class_ ["oak-list__item"]] [i]) (list_items rest),
    }

/// The first byte of each of the first two words, upper-cased by the
/// caller's font (`text-transform`); multi-byte initials stay whole.
def initials (name : String) : String :=
    String.concat (first_char (String.trim name)) (first_char (String.trim (after_space (String.trim name) 0)))

def first_char (s : String) : String :=
    if String.is_empty s then ""
    else
        let one : String := String.slice s 0 1 in
        if String.is_empty one then first_multibyte s 2 else one

#[terminating]
def first_multibyte (s : String) (n : I64) : String :=
    if I64.lt 4 n then ""
    else
        let piece : String := String.slice s 0 n in
        if String.is_empty piece then first_multibyte s (n + 1) else piece

#[terminating]
def after_space (s : String) (i : I64) : String :=
    match String.get s i {
        Option.none => "",
        Option.some b => if U8.beq b 32u8 then String.drop (i + 1) s else after_space s (i + 1),
    }

def delta_tone (delta : String) : String :=
    if String.starts_with "-" delta then Ui.tone_class Ui.Tone.tone_danger
    else if String.starts_with "+" delta then Ui.tone_class Ui.Tone.tone_success
    else ""

with Ui {
    /// Extra table modifiers.
    pub def striped : Ui.Opt := Ui.cls ["oak-table--striped"]
    pub def hoverable : Ui.Opt := Ui.cls ["oak-table--hover"]
    pub def sticky_header : Ui.Opt := Ui.cls ["oak-table--sticky"]

    /// A surface with optional header and footer (pass `List.empty`).
    pub def card {Msg : Type} (opts : List Ui.Opt) (head : List (Oak.Node Msg)) (body : List (Oak.Node Msg))
        (foot : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.section (Ui.root_attrs "oak-card" List.empty List.empty s List.empty)
            (List.append
                (if List.is_empty head then List.empty else [Html.header [Html.class_ ["oak-card__header"]] head])
                (List.cons (Html.div [Html.class_ ["oak-card__body"]] body)
                    (if List.is_empty foot then List.empty else [Html.footer [Html.class_ ["oak-card__footer"]] foot])))

    /// Term/detail pairs (`<dl>`), e.g. a record's properties.
    pub def description_list {Msg : Type} (opts : List Ui.Opt) (items : List (Pair String (Oak.Node Msg)))
        : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.dl (Ui.root_attrs "oak-dl" List.empty List.empty s List.empty) (dl_items items)

    /// A bordered vertical list.
    pub def list_group {Msg : Type} (opts : List Ui.Opt) (items : List (Oak.Node Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.ul (Ui.root_attrs "oak-list" List.empty List.empty s List.empty) (list_items items)

    /// A round avatar: the image when `image_url` is non-empty, initials
    /// otherwise. `name` is the accessible name either way.
    pub def avatar {Msg : Type} (opts : List Ui.Opt) (name : String) (image_url : String) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        if String.is_empty image_url
        then
            Html.span
                (Ui.root_attrs "oak-avatar" [Ui.size_mod s.size] [Ui.tone_class s.tone] s
                    [Html.role "img", Html.aria "label" name])
                [Html.text (initials name)]
        else
            Html.img
                (Ui.root_attrs "oak-avatar" [Ui.size_mod s.size] List.empty s [Html.src image_url, Html.alt name])

    /// A headline number with a label and an optional change (`"+4%"` is
    /// coloured success, `"-2%"` danger, `""` hides it).
    pub def stat {Msg : Type} (opts : List Ui.Opt) (label : String) (value : String) (delta : String)
        : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div (Ui.root_attrs "oak-stat" List.empty List.empty s List.empty)
            (List.append
                [Html.div [Html.class_ ["oak-stat__label"]] [Html.text label],
                    Html.div [Html.class_ ["oak-stat__value"]] [Html.text value]]
                (if String.is_empty delta then List.empty
                    else [Html.div [Html.class_ ["oak-stat__delta", delta_tone delta]] [Html.text delta]]))

    /// A data table over `rows`, keyed by `row_key` (stable DOM rows on
    /// re-sort). `caption` names the table (`""` for none; hide it visually with
    /// `Ui.cls` on a wrapper if the heading already says it). Use
    /// `Ui.small` for dense rows, `Ui.striped`/`Ui.hoverable`/
    /// `Ui.sticky_header` for the rest.
    pub def table {R : Type} {Msg : Type} (opts : List Ui.Opt) (caption : String)
        (columns : List (Ui.Column R Msg)) (rows : List R) (row_key : R -> String)
        (sort : Ui.SortState) (on_sort : String -> Msg) (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        Html.div [Html.class_ ["oak-table-wrap"]]
            [Html.table (Ui.root_attrs "oak-table" [Ui.size_mod s.size] List.empty s attrs)
                (List.append
                    (if String.is_empty caption then List.empty
                        else [Html.caption [Html.class_ ["oak-table__caption"]] [Html.text caption]])
                    [Html.thead List.empty [Html.tr List.empty (header_cells sort on_sort columns)],
                        Html.tbody List.empty (body_rows row_key columns rows)])]
}
