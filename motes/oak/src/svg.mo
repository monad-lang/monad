// SVG builders: the vector-graphics element and attribute vocabulary as
// plain functions returning `Oak.Node Msg`, in the same call style as
// `Html.*` (`Svg.svg [Svg.view_box 0 0 100 50] [Svg.rect [...] List.empty]`).
//
// Serialization needs nothing new: an SVG element is an ordinary
// `Html.Node` element and inline `<svg>` is valid HTML. The browser runtime
// (`oak_wasm`'s patch) creates every element at or below an `svg` tag in the
// SVG namespace, so the same tree renders live too.
//
// Attribute values that are numbers take `I64`: the layout code that feeds
// these builders works in whole pixels, and an integer never needs a float
// formatter. `Svg.attr` is the escape hatch for everything not curated here.

use std::list {List.intercalate}
use lib::typed {Oak.Attr, Oak.Node}
use lib::elements {Html.attr, Html.node}

def num_list (values : List I64) : String :=
    List.intercalate " " (List.map I64.to_string values)

with Svg {
    // ═══ Elements ═══

    /// The `<svg>` root. Everything below it is created in the SVG namespace
    /// by the browser runtime.
    pub def svg {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Html.node "svg" attrs children

    /// A group: shared transform and styling for its children.
    pub def g {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Html.node "g" attrs children

    pub def path {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Html.node "path" attrs children

    pub def line {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Html.node "line" attrs children

    pub def rect {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Html.node "rect" attrs children

    pub def circle {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Html.node "circle" attrs children

    pub def polyline {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Html.node "polyline" attrs children

    /// SVG `<text>`; the underscore keeps it apart from `Html.text` (a text
    /// node), which is what goes inside it.
    pub def text_ {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Html.node "text" attrs children

    /// SVG `<title>`: the accessible name and hover tooltip of its parent.
    pub def title {Msg : Type} (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Html.node "title" List.empty children

    pub def defs {Msg : Type} (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Html.node "defs" List.empty children

    pub def marker {Msg : Type} (attrs : List (Oak.Attr Msg)) (children : List (Oak.Node Msg)) : Oak.Node Msg :=
        Html.node "marker" attrs children

    // ═══ Attributes ═══

    pub def attr {Msg : Type} (name : String) (value : String) : Oak.Attr Msg :=
        Html.attr name value

    /// `viewBox="min_x min_y width height"`.
    pub def view_box {Msg : Type} (min_x : I64) (min_y : I64) (w : I64) (h : I64) : Oak.Attr Msg :=
        Html.attr "viewBox" (num_list [min_x, min_y, w, h])

    /// Path data, already formatted (`M 0 0 C 10 0 ...`).
    pub def d {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "d" value

    pub def x {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "x" (I64.to_string value)
    pub def y {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "y" (I64.to_string value)
    pub def x1 {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "x1" (I64.to_string value)
    pub def y1 {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "y1" (I64.to_string value)
    pub def x2 {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "x2" (I64.to_string value)
    pub def y2 {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "y2" (I64.to_string value)
    pub def cx {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "cx" (I64.to_string value)
    pub def cy {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "cy" (I64.to_string value)
    pub def r {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "r" (I64.to_string value)
    pub def rx {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "rx" (I64.to_string value)
    pub def width {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "width" (I64.to_string value)
    pub def height {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "height" (I64.to_string value)

    /// Space-separated points for `polyline`: `[x0, y0, x1, y1, ...]`.
    pub def points {Msg : Type} (coords : List I64) : Oak.Attr Msg := Html.attr "points" (num_list coords)

    pub def transform {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "transform" value

    /// `transform="translate(dx dy)"`.
    pub def translate {Msg : Type} (dx : I64) (dy : I64) : Oak.Attr Msg :=
        Html.attr "transform" (String.concat_list ["translate(", I64.to_string dx, " ", I64.to_string dy, ")"])

    pub def fill {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "fill" value
    pub def stroke {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "stroke" value
    pub def stroke_width {Msg : Type} (value : I64) : Oak.Attr Msg := Html.attr "stroke-width" (I64.to_string value)

    /// `marker-end="url(#id)"`.
    pub def marker_end {Msg : Type} (marker_id : String) : Oak.Attr Msg :=
        Html.attr "marker-end" (String.concat_list ["url(#", marker_id, ")"])

    /// `start`, `middle` or `end`.
    pub def text_anchor {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "text-anchor" value

    /// `auto`, `middle`, `central`, ... (vertical text alignment).
    pub def dominant_baseline {Msg : Type} (value : String) : Oak.Attr Msg := Html.attr "dominant-baseline" value
}
