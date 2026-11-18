// The layout's contract: deterministic, edges flow left to right where the
// graph allows, cycles terminate, and group boxes contain their members and
// never overlap their siblings.

use std::list {List.all, List.any}
use lib::graph_layout {
    Ui.GraphSpec, Ui.GraphNode, Ui.GraphEdge, Ui.GraphGroup, Ui.GraphLayout,
    Ui.PlacedNode, Ui.PlacedGroup, Ui.PlacedEdge, Ui.graph_layout, Ui.graph_node_width,
}

def node (id : String) (group : String) : Ui.GraphNode :=
    { id := id, label := id, group := group, cls := "", tip := "" }

def edge (a : String) (b : String) : Ui.GraphEdge :=
    { from := a, to := b, weight := 1, cls := "" }

def group (id : String) (parent : String) : Ui.GraphGroup :=
    { id := id, label := id, parent := parent, cls := "" }

#[terminating]
def find_node (id : String) (ns : List Ui.PlacedNode) : Option Ui.PlacedNode :=
    match ns {
        List.empty => Option.none,
        List.cons n rest => if String.beq n.id id then Option.some n else find_node id rest,
    }

#[terminating]
def find_group (id : String) (gs : List Ui.PlacedGroup) : Option Ui.PlacedGroup :=
    match gs {
        List.empty => Option.none,
        List.cons g rest => if String.beq g.id id then Option.some g else find_group id rest,
    }

def x_of (id : String) (l : Ui.GraphLayout) : I64 :=
    match find_node id l.nodes { Option.some n => n.x, Option.none => 0 - 1 }

def chain : Ui.GraphSpec :=
    { nodes := [node "a" "", node "b" "", node "c" ""],
        edges := [edge "a" "b", edge "b" "c"], groups := List.empty }

#[test]
def test_chain_flows_left_to_right : Bool :=
    let l : Ui.GraphLayout := Ui.graph_layout chain in
    x_of "a" l < x_of "b" l && x_of "b" l < x_of "c" l

#[test]
def test_every_node_and_edge_is_placed : Bool :=
    let l : Ui.GraphLayout := Ui.graph_layout chain in
    List.length l.nodes == 3 && List.length l.edges == 2

#[test]
def test_cycle_terminates_and_places_all : Bool :=
    let spec : Ui.GraphSpec :=
        { nodes := [node "a" "", node "b" "", node "c" ""],
            edges := [edge "a" "b", edge "b" "c", edge "c" "a"], groups := List.empty } in
    let l : Ui.GraphLayout := Ui.graph_layout spec in
    List.length l.nodes == 3 && List.length l.edges == 3

#[test]
def test_self_loop_is_not_drawn : Bool :=
    let spec : Ui.GraphSpec := { nodes := [node "a" ""], edges := [edge "a" "a"], groups := List.empty } in
    let l : Ui.GraphLayout := Ui.graph_layout spec in
    List.is_empty l.edges

#[test]
def test_layout_is_deterministic : Bool :=
    let a : Ui.GraphLayout := Ui.graph_layout chain in
    let b : Ui.GraphLayout := Ui.graph_layout chain in
    a.width == b.width && a.height == b.height && x_of "c" a == x_of "c" b

def inside (n : Ui.PlacedNode) (g : Ui.PlacedGroup) : Bool :=
    n.x >= g.x && n.y >= g.y && n.x + n.w <= g.x + g.w && n.y + n.h <= g.y + g.h

def disjoint (a : Ui.PlacedGroup) (b : Ui.PlacedGroup) : Bool :=
    a.x + a.w <= b.x || b.x + b.w <= a.x || a.y + a.h <= b.y || b.y + b.h <= a.y

def grouped : Ui.GraphSpec :=
    { nodes := [node "m1.f" "m1", node "m1.g" "m1", node "m2.h" "m2", node "m3.k" "m3", node "loose" ""],
        edges := [edge "m1.f" "m1.g", edge "m1.g" "m2.h", edge "m2.h" "m3.k", edge "loose" "m1.f"],
        groups := [group "mote" "", group "m1" "mote", group "m2" "mote", group "m3" ""] }

def contained (node_id : String) (group_id : String) (l : Ui.GraphLayout) : Bool :=
    match find_node node_id l.nodes {
        Option.none => false,
        Option.some n => match find_group group_id l.groups { Option.none => false, Option.some g => inside n g },
    }

#[test]
def test_members_sit_inside_their_groups : Bool :=
    let l : Ui.GraphLayout := Ui.graph_layout grouped in
    contained "m1.f" "m1" l && contained "m1.g" "m1" l && contained "m2.h" "m2" l
        && contained "m1.f" "mote" l && contained "m2.h" "mote" l && contained "m3.k" "m3" l

def groups_disjoint (a : String) (b : String) (l : Ui.GraphLayout) : Bool :=
    match find_group a l.groups {
        Option.none => false,
        Option.some ga => match find_group b l.groups { Option.none => false, Option.some gb => disjoint ga gb },
    }

#[test]
def test_sibling_groups_do_not_overlap : Bool :=
    let l : Ui.GraphLayout := Ui.graph_layout grouped in
    groups_disjoint "m1" "m2" l && groups_disjoint "mote" "m3" l

#[test]
def test_outer_groups_draw_first : Bool :=
    let l : Ui.GraphLayout := Ui.graph_layout grouped in
    match l.groups {
        List.cons g _ => g.depth == 0,
        List.empty => false,
    }

#[test]
def test_unknown_group_falls_back_to_top : Bool :=
    let spec : Ui.GraphSpec := { nodes := [node "a" "nope"], edges := List.empty, groups := List.empty } in
    let l : Ui.GraphLayout := Ui.graph_layout spec in
    List.length l.nodes == 1

#[test]
def test_node_width_is_clamped : Bool :=
    Ui.graph_node_width "" == 44 && Ui.graph_node_width (String.repeat "x" 200) == Ui.graph_node_width
        (String.repeat "x" 40)
