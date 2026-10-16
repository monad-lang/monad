// Terminal UI Library - Widget tree (Phase 5)
//
// The pure-data widget tree the renderer (render.mo) walks. Widgets are sum
// types with no default fields and no `BEq` — the renderer compares `Screen`s,
// not `Widget`s, so deriving equality here would only invite the generic
// `BEq (List A)` dispatch bug. Smart constructors keep call sites terse.
//
// `Widget` is mutually recursive with `DecoratorKind` (a decorator's child is
// a `Widget`) and `SizedWidget` (a sized child wraps a `Widget`). monad allows
// forward type references within a file, so `Widget` is declared first and
// names the two later types in its constructor arguments.

use lib::types { TextStyle, LayoutSize }
use lib::core { style_default }
// The stateful widgets' pure state machines (Phase 5). One-directional:
// those modules never import this one.
use lib::widgets::input { InputState }
use lib::widgets::list { ListState }

/// Box-drawing style for the `border` decorator. The actual glyphs live in
/// `render.mo` (`border_chars`) — this type only carries the choice.
pub type BorderStyle {
    plain,
    rounded,
    double_box,
    thick
}

def BorderStyle.beq (a b : BorderStyle) : Bool :=
    match a {
        plain => match b { plain => true, _ => false },
        rounded => match b { rounded => true, _ => false },
        double_box => match b { double_box => true, _ => false },
        thick => match b { thick => true, _ => false }
    }

instance BEq BorderStyle {
    def beq (a b : BorderStyle) : Bool := BorderStyle.beq a b
}

/// A widget with no children. `label` draws its text; `spacer` reserves a
/// fixed length along the layout axis without painting; `blank` paints
/// nothing (used to clear a region when stacked under others);
/// `text_input`/`list` draw their state machines' current state.
pub type LeafWidget {
    label (text : String),
    spacer (size : I64),
    text_input (state : InputState),
    list (state : ListState),
    blank
}

/// A `Widget` paired with the `LayoutSize` that governs its share of a
/// `row`/`column`. No default fields: every literal names both.
pub struct SizedWidget {
    size : LayoutSize,
    widget : Widget
}

/// What a `decorator` widget does to its single child. `border` draws a box
/// (and insets the child by 1 on every side); `padding` insets by the given
/// amounts; `styled` merges a `TextStyle` into the active style for the subtree.
pub type DecoratorKind {
    border (style : BorderStyle),
    padding (left : I64) (top : I64) (right : I64) (bottom : I64),
    styled (style : TextStyle)
}

/// The widget tree.
//
// `decorator (kind : DecoratorKind) (child : Widget)` references `DecoratorKind`
// (declared above) and `Widget` itself (self-recursive). `column`/`row`
// reference `SizedWidget` (declared above). All curried, space-separated —
// multi-arg constructors are not comma-separated in this language.
pub type Widget {
    leaf (kind : LeafWidget),
    decorator (kind : DecoratorKind) (child : Widget),
    column (children : List SizedWidget),
    row (children : List SizedWidget),
    stack (children : List Widget)
}

// ==================== Smart constructors ====================
//
// Naming the constructor after the widget it builds (e.g. `label`, not
// `mk_label`) matches the design doc's API and keeps call sites readable:
// `border plain (label "hi")`. Only the ones that compose more than one
// constructor earn a name here.

/// A single line of text.
pub def label (text : String) : Widget :=
    Widget.leaf (LeafWidget.label text)

/// Reserve `size` units along the layout axis without painting.
pub def spacer (size : I64) : Widget :=
    Widget.leaf (LeafWidget.spacer size)

/// Paint nothing (transparent; lets a stacked sibling show through).
pub def blank : Widget :=
    Widget.leaf LeafWidget.blank

/// A single-line text field showing `st` (cursor underlined, placeholder
/// dimmed when the value is empty -- render.mo's `text_input` arm).
pub def text_input (st : InputState) : Widget :=
    Widget.leaf (LeafWidget.text_input st)

/// A single-choice list showing `st`'s visible window (selected row
/// marked `"> "` and bolded -- render.mo's `list` arm).
pub def list (st : ListState) : Widget :=
    Widget.leaf (LeafWidget.list st)

/// Draw a box of `bs` around `child` (renderer insets the child by 1).
pub def border (bs : BorderStyle) (child : Widget) : Widget :=
    Widget.decorator (DecoratorKind.border bs) child

/// Inset `child` by the given number of cells on each side.
pub def padding (left : I64) (top : I64) (right : I64) (bottom : I64) (child : Widget) : Widget :=
    Widget.decorator (DecoratorKind.padding left top right bottom) child

/// Merge `s` into the active style for `child`'s subtree.
pub def with_style (s : TextStyle) (child : Widget) : Widget :=
    Widget.decorator (DecoratorKind.styled s) child

/// Attach a `LayoutSize` to `child` for use in a `row`/`column`.
pub def sized (sz : LayoutSize) (child : Widget) : SizedWidget :=
    { size := sz, widget := child }

// `Widget.column`/`Widget.row`/`Widget.stack` are called directly -- a
// same-named forwarder would only give one operation a second name. So would
// `sized_size`/`sized_widget`: read a `SizedWidget`'s halves as `sw.size` and
// `sw.widget`.

// ==================== Tests ====================

#[test]
def test_label_round_trip : Bool :=
    match label "hi" {
        Widget.leaf k => match k { LeafWidget.label t => t == "hi", _ => false },
        _ => false
    }

#[test]
def test_spacer_round_trip : Bool :=
    match spacer 5 {
        Widget.leaf k => match k { LeafWidget.spacer n => n == 5, _ => false },
        _ => false
    }

#[test]
def test_blank_round_trip : Bool :=
    match blank {
        Widget.leaf k => match k { LeafWidget.blank => true, _ => false },
        _ => false
    }

#[test]
def test_border_wraps_child : Bool :=
    match border BorderStyle.plain (label "x") {
        Widget.decorator kind child =>
            match kind {
                DecoratorKind.border bs => bs == BorderStyle.plain
                    && (match child { Widget.leaf k => match k { LeafWidget.label t => t == "x", _ => false }, _ => false }),
                _ => false
            },
        _ => false
    }

#[test]
def test_border_styles_distinct : Bool :=
    Bool.not (BorderStyle.plain == BorderStyle.rounded) && Bool.not (BorderStyle.double_box == BorderStyle.thick) && Bool.not (BorderStyle.plain == BorderStyle.thick)

#[test]
def test_padding_carries_insets : Bool :=
    match padding 1 2 3 4 blank {
        Widget.decorator kind _ =>
            match kind {
                DecoratorKind.padding l t r b => l == 1 && t == 2 && r == 3 && b == 4,
                _ => false
            },
        _ => false
    }

#[test]
def test_styled_carries_style : Bool :=
    let s : TextStyle := { style_default with bold := true } in
    match with_style s blank {
        Widget.decorator kind _ =>
            match kind { DecoratorKind.styled st => st == s, _ => false },
        _ => false
    }

#[test]
def test_column_holds_sized_children : Bool :=
    let ws := [sized (LayoutSize.fill 1) (label "a"), sized (LayoutSize.fill 1) (label "b")] in
    match Widget.column ws {
        Widget.column children =>
            match children {
                empty => false,
                cons first rest =>
                    match rest {
                        empty => false,
                        cons second rest2 =>
                            match rest2 { empty => true, _ => false }
                            && (match first.size { LayoutSize.fill w => w == 1, _ => false })
                            && (match second.size { LayoutSize.fill w => w == 1, _ => false })
                            && (match first.widget { Widget.leaf k => match k { LeafWidget.label t => t == "a", _ => false }, _ => false })
                            && (match second.widget { Widget.leaf k => match k { LeafWidget.label t => t == "b", _ => false }, _ => false })
                    }
            },
        _ => false
    }

#[test]
def test_row_holds_sized_children : Bool :=
    let ws := [sized (LayoutSize.fixed 3) blank] in
    match Widget.row ws {
        Widget.row children =>
            match children {
                empty => false,
                cons first rest =>
                    (match rest { empty => true, _ => false })
                    && (match first.size { LayoutSize.fixed n => n == 3, _ => false })
            },
        _ => false
    }

#[test]
def test_stack_holds_children : Bool :=
    match Widget.stack [label "a", label "b"] {
        Widget.stack children =>
            match children {
                empty => false,
                cons _ rest =>
                    match rest { empty => false, cons _ rest2 => match rest2 { empty => true, _ => false } }
            },
        _ => false
    }

#[test]
def test_sized_accessors : Bool :=
    let sw := sized (LayoutSize.fixed 2) (label "z") in
    (match sw.size { LayoutSize.fixed n => n == 2, _ => false })
    && (match sw.widget { Widget.leaf k => match k { LeafWidget.label t => t == "z", _ => false }, _ => false })

#[test]
def test_nested_decorator : Bool :=
    // border (styled (padding ... (label ...))) — decorators compose.
    let inner := border BorderStyle.rounded (with_style ({ style_default with bold := true } : TextStyle) (padding 1 1 1 1 (label "deep"))) in
    match inner {
        Widget.decorator outer_kind outer_child =>
            (match outer_kind { DecoratorKind.border bs => bs == BorderStyle.rounded, _ => false })
            && (match outer_child {
                Widget.decorator mid_kind mid_child =>
                    match mid_kind { DecoratorKind.styled _ => true, _ => false }
                    && (match mid_child {
                        Widget.decorator inner_kind _ =>
                            match inner_kind {
                                DecoratorKind.padding l t r b => l == 1 && t == 1 && r == 1 && b == 1,
                                _ => false
                            },
                        _ => false
                    }),
                _ => false
            }),
        _ => false
    }
