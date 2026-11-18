// The graph widget: a laid-out `Ui.GraphLayout` drawn as SVG, with
// selection, panning and zooming.
//
// Controlled like every interactive oak_ui component: the caller owns a
// `Ui.GraphView` (pan, zoom, selection, highlighted ids, drag state) and
// routes the widget's `Ui.GraphMsg`s through its own message type. Most
// apps hand them straight to `Ui.GraphView.update`, and look at
// `graph_select` themselves when a selection should do more (open a detail
// panel, refocus a query).
//
// Layout is separate (`Ui.graph_layout`, `graph_layout.mo`) so an app
// recomputes it only when the graph changes, not on every pan or zoom.
//
// Interaction:
// - click a node, or focus it and press Enter/Space: `graph_select id`;
//   clicking a group's label selects the group id;
// - drag the background: `graph_drag_start`/`_move`/`_end` (pan);
// - wheel over the drawing, or the toolbar's +/-: `graph_zoom`;
// - the toolbar's reset: `graph_reset`.
//
// With a selection, everything not adjacent to it is dimmed and the
// selection's own edges are emphasised; highlighted ids (search matches)
// get `oak-graph__node--match`.

use std::list {List.contains_by, List.filter, List.intercalate}
use oak::typed {Oak.Attr, Oak.Node}
use oak::elements {
    Html.div, Html.button, Html.type_, Html.attr, Html.aria, Html.role, Html.class_, Html.text,
    Html.tabindex, Html.title_attr,
}
use oak::events {Html.on, Html.on_click}
use oak::svg {
    Svg.svg, Svg.g, Svg.path, Svg.rect, Svg.text_, Svg.title, Svg.defs, Svg.marker,
    Svg.attr, Svg.x, Svg.y, Svg.width, Svg.height, Svg.rx, Svg.d, Svg.translate, Svg.transform,
    Svg.text_anchor, Svg.dominant_baseline, Svg.marker_end, Svg.stroke_width,
}
use web_event::event {WebEvent, ListenerFlags, HandlerResult, HandlerResult.prevent, HandlerResult.ignore,
    ListenerFlags.none}
use lib::vocab {Ui.Opt, Ui.Style, Ui.resolve}
use lib::base {Ui.root_attrs}
use lib::graph_layout {
    Ui.GraphLayout, Ui.PlacedNode, Ui.PlacedGroup, Ui.PlacedEdge,
}

// ═══ State and messages ═══

/// What the widget reports. Coordinates are client pixels.
pub type Ui.GraphMsg {
    graph_select (id : String),
    graph_zoom (steps : I64),
    graph_reset,
    graph_drag_start (x : I64) (y : I64),
    graph_drag_move (x : I64) (y : I64),
    graph_drag_end,
}

/// The caller-owned view state. `zoom` is a percentage; `selected` is `""`
/// for no selection.
pub struct Ui.GraphView {
    pan_x : I64,
    pan_y : I64,
    zoom : I64,
    selected : String,
    highlighted : List String,
    dragging : Bool,
    drag_x : I64,
    drag_y : I64,
}

pub def Ui.GraphView.initial : Ui.GraphView :=
    { pan_x := 0, pan_y := 0, zoom := 100, selected := "", highlighted := List.empty,
        dragging := false, drag_x := 0, drag_y := 0 }

/// The zoom ladder, in percent; `graph_zoom n` moves `n` rungs.
def zoom_levels : List I64 := [10, 20, 33, 50, 67, 80, 100, 125, 150, 200, 300]

#[terminating]
def rung_of (z : I64) (levels : List I64) (i : I64) (best : I64) : I64 :=
    match levels {
        List.empty => best,
        List.cons l rest => if l <= z then rung_of z rest (i + 1) i else best,
    }

#[terminating]
def level_at (i : I64) (levels : List I64) (last : I64) : I64 :=
    match levels {
        List.empty => last,
        List.cons l rest => if i <= 0 then l else level_at (i - 1) rest l,
    }

/// `z` moved `steps` rungs along the ladder, clamped at both ends.
pub def Ui.graph_zoom_step (z : I64) (steps : I64) : I64 :=
    let rung : I64 := rung_of z zoom_levels 0 0 + steps in
    level_at (if rung < 0 then 0 else rung) zoom_levels 300

/// The usual update: pan on drag, zoom along the ladder, select (selecting
/// the selected id again clears the selection), reset pan and zoom.
pub def Ui.GraphView.update (v : Ui.GraphView) (m : Ui.GraphMsg) : Ui.GraphView :=
    match m {
        Ui.GraphMsg.graph_select id =>
            { v with selected := if String.beq v.selected id then "" else id },
        Ui.GraphMsg.graph_zoom steps => { v with zoom := Ui.graph_zoom_step v.zoom steps },
        Ui.GraphMsg.graph_reset => { v with pan_x := 0, pan_y := 0, zoom := 100 },
        Ui.GraphMsg.graph_drag_start x y => { v with dragging := true, drag_x := x, drag_y := y },
        Ui.GraphMsg.graph_drag_move x y =>
            if v.dragging
            then { v with pan_x := v.pan_x + x - v.drag_x, pan_y := v.pan_y + y - v.drag_y, drag_x := x, drag_y := y }
            else v,
        Ui.GraphMsg.graph_drag_end => { v with dragging := false },
    }

// ═══ Helpers ═══

/// The integer part of a pixel coordinate. `F64` has no integer
/// conversion, so this reads the shortest decimal rendering; event
/// coordinates are small, so it never has an exponent.
pub def Ui.graph_whole_px (f : F64) : I64 :=
    let s : String := F64.to_string f in
    if String.starts_with "-" s then 0 - digits_of (String.drop 1 s) 0 else digits_of s 0

#[terminating]
def digit_in (c : String) (ds : List String) (i : I64) : I64 :=
    match ds {
        List.empty => 0 - 1,
        List.cons d rest => if String.beq c d then i else digit_in c rest (i + 1),
    }

def digit (c : String) : I64 := digit_in c ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"] 0

#[terminating]
def digits_of (s : String) (acc : I64) : I64 :=
    if String.is_empty s then acc
    else
        let d : I64 := digit (String.slice s 0 1) in
        if d < 0 then acc else digits_of (String.drop 1 s) (acc * 10 + d)

def has (id : String) (ids : List String) : Bool := List.contains_by String.beq id ids

/// `1.25` for 125: the scale factor CSS reads.
def scale_of (percent : I64) : String :=
    let whole : I64 := percent / 100 in
    let frac : I64 := percent - whole * 100 in
    String.concat_list [I64.to_string whole, ".", if frac < 10 then "0" else "", I64.to_string frac]

def max_chars : I64 := 40

/// A label cut to the width the layout reserved for it.
def shown_label (label : String) : String :=
    if String.length label > max_chars
    then String.concat (String.slice label 0 (max_chars - 1)) "\u{2026}"
    else label

/// The selection's neighbourhood: the selected id and every id one edge
/// away from it.
#[terminating]
def neighbours (sel : String) (es : List Ui.PlacedEdge) : List String :=
    match es {
        List.empty => List.empty,
        List.cons e rest =>
            if String.beq e.from sel then List.cons e.to (neighbours sel rest)
            else if String.beq e.to sel then List.cons e.from (neighbours sel rest)
            else neighbours sel rest,
    }

def classes (parts : List String) : String :=
    List.intercalate " " (List.filter (fn (p : String) => Bool.not (String.is_empty p)) parts)

// ═══ Drawing ═══

def activate_key {Msg : Type} (m : Msg) : Oak.Attr Msg :=
    Html.on "keydown" ListenerFlags.none
        (fn (e : WebEvent) =>
            if String.beq e.key "Enter" || String.beq e.key " " then HandlerResult.prevent m else HandlerResult.ignore)

def draw_node {Msg : Type} (v : Ui.GraphView) (near : List String) (on_msg : Ui.GraphMsg -> Msg)
    (n : Ui.PlacedNode) : Oak.Node Msg :=
    let selected : Bool := String.beq v.selected n.id in
    let dim : Bool := Bool.not (String.is_empty v.selected) && Bool.not selected && Bool.not (has n.id near) in
    let cls : String := classes ["oak-graph__node", n.cls,
        if selected then "oak-graph__node--selected" else "",
        if has n.id v.highlighted then "oak-graph__node--match" else "",
        if dim then "oak-graph__node--dim" else ""] in
    let tip : String := if String.is_empty n.tip then n.label else n.tip in
    let pick : Msg := on_msg (Ui.GraphMsg.graph_select n.id) in
    Svg.g [Svg.attr "class" cls, Svg.translate n.x n.y, Html.tabindex 0, Html.role "button",
        Html.aria "label" tip, Html.aria "pressed" (if selected then "true" else "false"),
        Html.on_click pick, activate_key (on_msg (Ui.GraphMsg.graph_select n.id))]
        [Svg.title [Html.text tip],
            Svg.rect [Svg.width n.w, Svg.height n.h, Svg.rx 6] List.empty,
            Svg.text_ [Svg.x (n.w / 2), Svg.y (n.h / 2), Svg.text_anchor "middle", Svg.dominant_baseline "central"]
                [Html.text (shown_label n.label)]]

def draw_group {Msg : Type} (v : Ui.GraphView) (on_msg : Ui.GraphMsg -> Msg) (gr : Ui.PlacedGroup) : Oak.Node Msg :=
    let cls : String := classes ["oak-graph__group", gr.cls,
        String.concat "oak-graph__group--depth-" (I64.to_string (if gr.depth > 3 then 3 else gr.depth)),
        if String.beq v.selected gr.id then "oak-graph__group--selected" else ""] in
    Svg.g [Svg.attr "class" cls, Svg.translate gr.x gr.y]
        [Svg.rect [Svg.width gr.w, Svg.height gr.h, Svg.rx 8] List.empty,
            Svg.text_ [Svg.attr "class" "oak-graph__group-label", Svg.x 10, Svg.y 15,
                Html.on_click (on_msg (Ui.GraphMsg.graph_select gr.id))]
                [Svg.title [Html.text gr.label], Html.text (shown_label gr.label)]]

def edge_width (weight : I64) : I64 := if weight >= 8 then 4 else if weight >= 3 then 2 else 1

def draw_edge {Msg : Type} (v : Ui.GraphView) (e : Ui.PlacedEdge) : Oak.Node Msg :=
    let touches : Bool := String.beq v.selected e.from || String.beq v.selected e.to in
    let dim : Bool := Bool.not (String.is_empty v.selected) && Bool.not touches in
    let cls : String := classes ["oak-graph__edge", e.cls,
        if touches then "oak-graph__edge--active" else "",
        if dim then "oak-graph__edge--dim" else ""] in
    Svg.path [Svg.attr "class" cls, Svg.d e.d, Svg.stroke_width (edge_width e.weight),
        Svg.marker_end "oak-graph-arrow"]
        [Svg.title [Html.text (String.concat_list [e.from, " \u{2192} ", e.to,
            if e.weight > 1 then String.concat_list [" (", I64.to_string e.weight, ")"] else ""])]]

def arrow_marker {Msg : Type} : Oak.Node Msg :=
    Svg.defs [Svg.marker [Svg.attr "id" "oak-graph-arrow", Svg.attr "viewBox" "0 0 10 10",
        Svg.attr "refX" "9", Svg.attr "refY" "5", Svg.attr "markerWidth" "7", Svg.attr "markerHeight" "7",
        Svg.attr "orient" "auto-start-reverse", Svg.attr "markerUnits" "userSpaceOnUse"]
        [Svg.path [Svg.attr "class" "oak-graph__arrow", Svg.d "M 0 0 L 10 5 L 0 10 z"] List.empty]]

def wheel_zoom {Msg : Type} (on_msg : Ui.GraphMsg -> Msg) : Oak.Attr Msg :=
    Html.on "wheel" ListenerFlags.none
        (fn (e : WebEvent) =>
            HandlerResult.prevent (on_msg (Ui.GraphMsg.graph_zoom (if F64.gt e.delta_y 0.0 then 0 - 1 else 1))))

def drag_start {Msg : Type} (on_msg : Ui.GraphMsg -> Msg) : Oak.Attr Msg :=
    Html.on "pointerdown" ListenerFlags.none
        (fn (e : WebEvent) =>
            HandlerResult.prevent (on_msg (Ui.GraphMsg.graph_drag_start (Ui.graph_whole_px e.client_x)
                (Ui.graph_whole_px e.client_y))))

def drag_move {Msg : Type} (on_msg : Ui.GraphMsg -> Msg) : Oak.Attr Msg :=
    Html.on "pointermove" ListenerFlags.none
        (fn (e : WebEvent) =>
            HandlerResult.prevent (on_msg (Ui.GraphMsg.graph_drag_move (Ui.graph_whole_px e.client_x)
                (Ui.graph_whole_px e.client_y))))

/// The listeners on the drawing: wheel always; move/up/leave only while a
/// drag is in progress, so an idle pointer dispatches nothing.
def surface_attrs {Msg : Type} (v : Ui.GraphView) (on_msg : Ui.GraphMsg -> Msg) : List (Oak.Attr Msg) :=
    if v.dragging
    then [wheel_zoom on_msg, drag_move on_msg,
        Html.on_click (on_msg Ui.GraphMsg.graph_drag_end),
        Html.on "pointerup" ListenerFlags.none (fn (_e : WebEvent) => HandlerResult.prevent
            (on_msg Ui.GraphMsg.graph_drag_end)),
        Html.on "pointerleave" ListenerFlags.none (fn (_e : WebEvent) => HandlerResult.prevent
            (on_msg Ui.GraphMsg.graph_drag_end))]
    else [wheel_zoom on_msg]

def tool {Msg : Type} (label : String) (glyph : String) (m : Msg) : Oak.Node Msg :=
    Html.button [Html.type_ "button", Html.class_ ["oak-graph__tool"], Html.aria "label" label,
        Html.title_attr label, Html.on_click m]
        [Html.text glyph]

def toolbar {Msg : Type} (v : Ui.GraphView) (on_msg : Ui.GraphMsg -> Msg) : Oak.Node Msg :=
    Html.div [Html.class_ ["oak-graph__toolbar"], Html.role "toolbar", Html.aria "label" "Graph view"]
        [tool "Zoom in" "+" (on_msg (Ui.GraphMsg.graph_zoom 1)),
            tool "Zoom out" "\u{2212}" (on_msg (Ui.GraphMsg.graph_zoom (0 - 1))),
            tool "Reset view" "\u{21BA}" (on_msg Ui.GraphMsg.graph_reset),
            Html.div [Html.class_ ["oak-graph__zoom"], Html.aria "live" "polite"]
                [Html.text (String.concat (I64.to_string v.zoom) "%")]]

with Ui {
    /// A graph drawing. `label` is the accessible name of the drawing;
    /// `layout` comes from `Ui.graph_layout`; `view` is the caller's state.
    pub def graph {Msg : Type} (opts : List Ui.Opt) (label : String) (layout : Ui.GraphLayout)
        (view : Ui.GraphView) (on_msg : Ui.GraphMsg -> Msg) (attrs : List (Oak.Attr Msg)) : Oak.Node Msg :=
        let s : Ui.Style := Ui.resolve opts in
        let near : List String := neighbours view.selected layout.edges in
        let content : String := String.concat_list [
            "translate(", I64.to_string view.pan_x, " ", I64.to_string view.pan_y, ") scale(", scale_of view.zoom,
                ")"] in
        Html.div (Ui.root_attrs "oak-graph" (if view.dragging then ["dragging"] else List.empty) List.empty s attrs)
            [toolbar view on_msg,
                Svg.svg (List.append
                    [Svg.attr "class" "oak-graph__canvas", Html.role "group", Html.aria "label" label,
                        Svg.attr "width" "100%", Svg.attr "height" "100%"]
                    (surface_attrs view on_msg))
                    [arrow_marker,
                        Svg.rect [Svg.attr "class" "oak-graph__surface", Svg.attr "width" "100%",
                            Svg.attr "height" "100%",
                            drag_start on_msg] List.empty,
                        Svg.g [Svg.transform content]
                            [Svg.g [Svg.attr "class" "oak-graph__groups"] (List.map
                                (draw_group view on_msg) layout.groups),
                                Svg.g [Svg.attr "class" "oak-graph__edges"] (List.map (draw_edge view) layout.edges),
                                Svg.g [Svg.attr "class" "oak-graph__nodes"] (List.map
                                    (draw_node view near on_msg) layout.nodes)]]]
}
