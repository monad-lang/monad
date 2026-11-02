// Terminal UI Library - single-choice picker (a component)
//
// A titled list of names with the current one starred: arrows/Page/Home/
// End move the selection (`handle_list_key`), Enter chooses, Esc or
// Ctrl+C cancels. `Picker.update` answers a `PickerStep` so the parent
// decides what a choice means; `Picker.view` paints a header, the visible
// window and a footer into any height without spilling past it (the
// layout does not clip).

use lib::types {Key, LayoutSize, TextStyle}
use lib::core {style_default}
use lib::widget {Widget, SizedWidget, label, sized, with_style}
use lib::widgets::list {ListState, handle_list_key}
use std::list {List.length}

pub struct PickerModel {
    list : ListState,
    /// The name in effect now; starred in the list.
    current : String,
    title : String,
}

pub type PickerStep {
    stay (p : PickerModel),
    choose (item : String),
    cancel,
}

#[partial]
def index_of (name : String) (xs : List String) (i : I64) : I64 :=
    match xs {
        List.empty => 0 - 1,
        List.cons x rest => if String.beq x name then i else index_of name rest (i + 1),
    }

#[partial]
def nth (i : I64) (xs : List String) : Option String :=
    match xs {
        List.empty => Option.none,
        List.cons x rest => if i < 1 then Option.some x else nth (i - 1) rest,
    }

#[partial]
def take (n : I64) (xs : List String) : List String :=
    if n < 1 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (take (n - 1) rest),
    }

#[partial]
def drop (n : I64) (xs : List String) : List String :=
    if n < 1 then xs
    else match xs {
        List.empty => xs,
        List.cons _ rest => drop (n - 1) rest,
    }

/// A picker over `items` with `current` selected (the first item when
/// `current` is not listed).
pub def Picker.make (title : String) (items : List String) (current : String) : PickerModel :=
    let idx : I64 := index_of current items 0 in
    let st : ListState := { items := items, selected := (if idx < 0 then 0 else idx), offset := 0 } in
    let p : PickerModel := { list := st, current := current, title := title } in
    p

pub def Picker.count (p : PickerModel) : I64 := List.length p.list.items

/// The highlighted name (`current` for an empty list).
pub def Picker.selected (p : PickerModel) : String :=
    match nth p.list.selected p.list.items {
        Option.none => p.current,
        Option.some x => x,
    }

/// The rows the list itself gets out of `avail`: header and footer take one each.
pub def Picker.list_height (avail : I64) : I64 :=
    if avail < 2 then 0 else avail - 2

/// One key: `height` is the list's visible rows (the page size).
pub def Picker.update (height : I64) (p : PickerModel) (k : Key) : PickerStep :=
    match k {
        Key.enter => PickerStep.choose (Picker.selected p),
        Key.escape => PickerStep.cancel,
        Key.ctrl c => if String.beq c "c" then PickerStep.cancel else PickerStep.stay p,
        _ => PickerStep.stay { p with list := handle_list_key (if height < 1 then 1 else height) k p.list },
    }

/// The window's first row for `height` visible rows: the stored offset,
/// moved the least needed to show the selection (a resize can strand it).
pub def Picker.window_offset (height : I64) (p : PickerModel) : I64 :=
    let h : I64 := if height < 1 then 1 else height in
    let sel : I64 := p.list.selected in
    if sel < p.list.offset then sel
    else if p.list.offset + h < sel + 1 then sel + 1 - h
    else p.list.offset

pub def Picker.visible (height : I64) (p : PickerModel) : List String :=
    take height (drop (Picker.window_offset height p) p.list.items)

def footer : String := "↑/↓ move · Enter select · Esc cancel"

#[partial]
def row_widgets (p : PickerModel) (row : I64) (names : List String) : List SizedWidget :=
    match names {
        List.empty => List.empty,
        List.cons name rest =>
            let here : Bool := I64.beq row p.list.selected in
            let cursor : String := if here then "> " else "  " in
            let mark : String := if String.beq name p.current then "*" else " " in
            let style : TextStyle := if here then { style_default with reverse := true } else style_default in
            List.cons (sized (LayoutSize.fixed 1) (with_style style (label (String.concat cursor (String.concat mark (String.concat " " name))))))
                (row_widgets p (row + 1) rest),
    }

/// The picker in `avail` rows: a 1-row space gets the header alone, a
/// 2-row one header and footer, and only 3+ rows list names.
pub def Picker.view (avail : I64) (p : PickerModel) : Widget :=
    let dim : TextStyle := { style_default with dim := true } in
    let head : SizedWidget := sized (LayoutSize.fixed 1) (with_style dim (label (String.concat p.title (String.concat "   current: " p.current)))) in
    let foot : SizedWidget := sized (LayoutSize.fixed 1) (with_style dim (label footer)) in
    if avail < 1 then Widget.column List.empty
    else if I64.beq avail 1 then Widget.column [head]
    else if I64.beq avail 2 then Widget.column [head, foot]
    else
        let h : I64 := Picker.list_height avail in
        let rows : List SizedWidget := row_widgets p (Picker.window_offset h p) (Picker.visible h p) in
        Widget.column (List.append (List.cons head rows) [foot])
