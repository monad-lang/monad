/// Rendering and behaviour of `Ui.graph`, and the `Ui.GraphView` update.

use web_event::event {WebEvent}
use oak::typed {Oak.Node}
use lib::tests::support {ui_has, ui_nth_msg, ui_handler_count}
use lib::graph_layout {Ui.GraphSpec, Ui.GraphNode, Ui.GraphEdge, Ui.GraphGroup, Ui.GraphLayout, Ui.graph_layout}
use lib::graph {
    Ui.GraphMsg, Ui.GraphView, Ui.GraphView.initial, Ui.GraphView.update,
    Ui.graph_zoom_step, Ui.graph_whole_px, Ui.graph,
}
use lib::css {Ui.css_all}

type GraphTestMsg { from_graph (m : Ui.GraphMsg) }

def wrap (m : Ui.GraphMsg) : GraphTestMsg := GraphTestMsg.from_graph m

def spec : Ui.GraphSpec :=
    let a : Ui.GraphNode := { id := "a", label := "alpha", group := "g", cls := "kind-def", tip := "lib::alpha" } in
    let b : Ui.GraphNode := { id := "b", label := "beta", group := "g", cls := "", tip := "" } in
    let c : Ui.GraphNode := { id := "c", label := "gamma", group := "", cls := "", tip := "" } in
    let ab : Ui.GraphEdge := { from := "a", to := "b", weight := 1, cls := "" } in
    let bc : Ui.GraphEdge := { from := "b", to := "c", weight := 9, cls := "" } in
    let g : Ui.GraphGroup := { id := "g", label := "lib::m", parent := "", cls := "" } in
    { nodes := [a, b, c], edges := [ab, bc], groups := [g] }

def layout : Ui.GraphLayout := Ui.graph_layout spec

def view_of (v : Ui.GraphView) : Oak.Node GraphTestMsg := Ui.graph List.empty "Calls" layout v wrap List.empty

def plain : Oak.Node GraphTestMsg := view_of Ui.GraphView.initial

def selected_b : Ui.GraphView := { Ui.GraphView.initial with selected := "b", highlighted := ["c"] }

#[test]
def test_graph_draws_an_svg_canvas : Bool :=
    ui_has plain "<svg class=\"oak-graph__canvas\" role=\"group\" aria-label=\"Calls\""

#[test]
def test_graph_draws_every_node_with_its_tip : Bool :=
    ui_has plain "<title>lib::alpha</title>" && ui_has plain ">beta</text>" && ui_has plain ">gamma</text>"

#[test]
def test_graph_draws_groups_and_edges : Bool :=
    ui_has plain "oak-graph__group oak-graph__group--depth-0" && ui_has plain "marker-end=\"url(#oak-graph-arrow)\""

#[test]
def test_heavy_edge_draws_thicker : Bool := ui_has plain "stroke-width=\"4\""

#[test]
def test_node_carries_its_kind_class : Bool := ui_has plain "class=\"oak-graph__node kind-def\""

#[test]
def test_selection_marks_dims_and_activates : Bool :=
    let n : Oak.Node GraphTestMsg := view_of selected_b in
    ui_has n "oak-graph__node--selected" && ui_has n "oak-graph__node--match"
        && ui_has n "oak-graph__edge--active" && Bool.not (ui_has n "oak-graph__node--dim")

#[test]
def test_unrelated_node_dims : Bool :=
    let v : Ui.GraphView := { Ui.GraphView.initial with selected := "a" } in
    ui_has (view_of v) "oak-graph__node--dim"

#[test]
def test_transform_follows_pan_and_zoom : Bool :=
    let v : Ui.GraphView := { Ui.GraphView.initial with pan_x := 5, pan_y := 0 - 3, zoom := 125 } in
    ui_has (view_of v) "transform=\"translate(5 -3) scale(1.25)\""

#[test]
def test_idle_surface_only_listens_for_the_wheel : Bool :=
    // wheel + 3 tools + surface pointerdown + group label + 3 nodes x (click, keydown)
    ui_handler_count plain == 12

#[test]
def test_dragging_adds_move_and_end_listeners : Bool :=
    let v : Ui.GraphView := { Ui.GraphView.initial with dragging := true } in
    ui_handler_count (view_of v) == 16

#[test]
def test_wheel_down_zooms_out : Bool :=
    let e : WebEvent := { kind := "wheel", valid := true, delta_y := 3.0 } in
    // Handlers in document order: the three toolbar buttons, then the canvas's wheel.
    match ui_nth_msg plain 3 e {
        Option.some m => match m { GraphTestMsg.from_graph g => match g { Ui.GraphMsg.graph_zoom n => n == 0 - 1,
            _ => false } },
        Option.none => false,
    }

#[test]
def test_update_selects_and_toggles_off : Bool :=
    let v1 : Ui.GraphView := Ui.GraphView.update Ui.GraphView.initial (Ui.GraphMsg.graph_select "a") in
    let v2 : Ui.GraphView := Ui.GraphView.update v1 (Ui.GraphMsg.graph_select "a") in
    String.beq v1.selected "a" && String.is_empty v2.selected

#[test]
def test_update_pans_while_dragging : Bool :=
    let v1 : Ui.GraphView := Ui.GraphView.update Ui.GraphView.initial (Ui.GraphMsg.graph_drag_start 10 10) in
    let v2 : Ui.GraphView := Ui.GraphView.update v1 (Ui.GraphMsg.graph_drag_move 25 4) in
    let v3 : Ui.GraphView := Ui.GraphView.update v2 Ui.GraphMsg.graph_drag_end in
    let v4 : Ui.GraphView := Ui.GraphView.update v3 (Ui.GraphMsg.graph_drag_move 99 99) in
    v2.pan_x == 15 && v2.pan_y == 0 - 6 && Bool.not v3.dragging && v4.pan_x == 15

#[test]
def test_zoom_ladder_clamps : Bool :=
    Ui.graph_zoom_step 100 1 == 125 && Ui.graph_zoom_step 100 (0 - 1) == 80
        && Ui.graph_zoom_step 300 5 == 300 && Ui.graph_zoom_step 10 (0 - 5) == 10

#[test]
def test_whole_px : Bool :=
    Ui.graph_whole_px 12.75 == 12 && Ui.graph_whole_px (0.0 - 3.5) == 0 - 3 && Ui.graph_whole_px 0.0 == 0

#[test]
def test_stylesheet_includes_graph : Bool := String.contains Ui.css_all ".oak-graph__node"
