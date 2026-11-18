/// Projection: levels aggregate edges, filters hide externals and tests,
/// focus keeps a neighbourhood, groupings nest, and the cap refuses a
/// hairball.

use std::list {List.any, List.filter}
use oak_ui::graph_layout {Ui.GraphSpec, Ui.GraphNode, Ui.GraphEdge, Ui.GraphGroup}
use lib::project {
    Trellis.Level, Trellis.Grouping, Trellis.Direction, Trellis.Settings, Trellis.Settings.initial,
    Trellis.Projection, Trellis.project, Trellis.neighbours, Trellis.lift_key, Trellis.effective_grouping,
}
use lib::tests::support {fixture}

def at (level : Trellis.Level) : Trellis.Settings := { Trellis.Settings.initial with level := level }

def spec_of (p : Trellis.Projection) : Ui.GraphSpec :=
    match p {
        Trellis.Projection.projected spec _ _ => spec,
        _ => { nodes := List.empty, edges := List.empty, groups := List.empty },
    }

def has_node (id : String) (s : Ui.GraphSpec) : Bool := List.any (fn (n : Ui.GraphNode) => String.beq n.id id) s.nodes

def edge_weight (a : String) (b : String) (s : Ui.GraphSpec) : I64 :=
    match List.filter (fn (e : Ui.GraphEdge) => String.beq e.from a && String.beq e.to b) s.edges {
        List.cons e _ => e.weight,
        List.empty => 0,
    }

#[test]
def test_module_level_aggregates_edges : Bool :=
    let s : Ui.GraphSpec := spec_of (Trellis.project fixture (at Trellis.Level.at_module)) in
    // check->unify and infer->unify: two references, one edge.
    edge_weight "lang::typecheck::infer" "lang::typecheck::unify" s == 2
        && List.length s.nodes == 4

#[test]
def test_mote_level_hides_externals_by_default : Bool :=
    let s : Ui.GraphSpec := spec_of (Trellis.project fixture (at Trellis.Level.at_mote)) in
    has_node "lang" s && has_node "proofs" s && Bool.not (has_node "std" s)

#[test]
def test_externals_on_request : Bool :=
    let base : Trellis.Settings := at Trellis.Level.at_mote in
    let st : Trellis.Settings := { base with external := true } in
    let s : Ui.GraphSpec := spec_of (Trellis.project fixture st) in
    has_node "std" s && edge_weight "lang" "std" s == 1

#[test]
def test_tests_hidden_by_default : Bool :=
    let s : Ui.GraphSpec := spec_of (Trellis.project fixture (at Trellis.Level.at_decl)) in
    Bool.not (has_node "lang::typecheck::infer::check_tests" s) && has_node "lang::typecheck::infer::check" s

#[test]
def test_axis_filter_drops_signature_edges : Bool :=
    let base : Trellis.Settings := at Trellis.Level.at_decl in
    let st : Trellis.Settings := { base with signature := false } in
    let s : Ui.GraphSpec := spec_of (Trellis.project fixture st) in
    edge_weight "lang::typecheck::infer::infer" "lang::typecheck::infer::Ty" s == 0
        && edge_weight "lang::typecheck::infer::infer" "lang::typecheck::unify::unify" s == 1

#[test]
def test_focus_callees_depth_one : Bool :=
    let base : Trellis.Settings := at Trellis.Level.at_decl in
    let st : Trellis.Settings :=
        { base with focus := ["lang::typecheck::infer::infer"], depth := 1, direction := Trellis.Direction.callees } in
    let s : Ui.GraphSpec := spec_of (Trellis.project fixture st) in
    has_node "lang::typecheck::infer::infer" s && has_node "lang::typecheck::unify::unify" s
        && Bool.not (has_node "lang::typecheck::infer::check" s) && Bool.not (has_node "lang::typecheck::unify::whnf" s)

#[test]
def test_focus_callers_follows_edges_backwards : Bool :=
    let base : Trellis.Settings := at Trellis.Level.at_decl in
    let st : Trellis.Settings :=
        { base with focus := ["lang::typecheck::unify::unify"], depth := 1, direction := Trellis.Direction.callers } in
    let s : Ui.GraphSpec := spec_of (Trellis.project fixture st) in
    has_node "lang::typecheck::infer::check" s && has_node "lang::typecheck::infer::infer" s
        && has_node "lang::typecheck::unify::whnf" s && List.length s.nodes == 4

#[test]
def test_focus_depth_two_reaches_further : Bool :=
    let base : Trellis.Settings := at Trellis.Level.at_decl in
    let st : Trellis.Settings :=
        { base with focus := ["lang::typecheck::infer::check"], depth := 2, direction := Trellis.Direction.callees } in
    has_node "lang::typecheck::unify::whnf" (spec_of (Trellis.project fixture st))

#[test]
def test_decl_level_groups_nest_modules_in_motes : Bool :=
    let base : Trellis.Settings := at Trellis.Level.at_decl in
    let st : Trellis.Settings := { base with grouping := Trellis.Grouping.by_module } in
    let s : Ui.GraphSpec := spec_of (Trellis.project fixture st) in
    List.any (fn
        (g : Ui.GraphGroup) => String.beq g.id "module:lang::typecheck::unify"
            && String.beq g.parent "mote:lang") s.groups
        && List.any (fn (g : Ui.GraphGroup) => String.beq g.id "mote:lang" && String.is_empty g.parent) s.groups
        && List.any (fn (n : Ui.GraphNode) => String.beq n.group "module:lang::typecheck::unify") s.nodes

#[test]
def test_grouping_is_never_finer_than_the_level : Bool :=
    match Trellis.effective_grouping Trellis.Level.at_module Trellis.Grouping.by_module {
        Trellis.Grouping.by_mote => true,
        _ => false,
    }

#[test]
def test_cap_refuses_large_views : Bool :=
    let base : Trellis.Settings := at Trellis.Level.at_decl in
    let st : Trellis.Settings := { base with cap := 3 } in
    match Trellis.project fixture st {
        Trellis.Projection.too_many n => n > 3,
        _ => false,
    }

#[test]
def test_proof_lens_marks_props : Bool :=
    let base : Trellis.Settings := at Trellis.Level.at_decl in
    let st : Trellis.Settings := { base with lens := "proofs" } in
    let s : Ui.GraphSpec := spec_of (Trellis.project fixture st) in
    List.any (fn
        (n : Ui.GraphNode) => String.beq n.id "proofs::nat::add_zero" && String.contains n.cls "trellis-proof") s.nodes
        && List.any (fn
            (n : Ui.GraphNode) => String.beq n.id "proofs::nat::plus"
                && String.contains n.cls "trellis-nonproof") s.nodes

#[test]
def test_neighbours_both_ways : Bool :=
    List.length (Trellis.neighbours fixture "lang::typecheck::unify::unify" false) == 3
        && List.length (Trellis.neighbours fixture "lang::typecheck::unify::unify" true) == 1

#[test]
def test_lift_key : Bool :=
    match Trellis.lift_key fixture Trellis.Level.at_decl Trellis.Level.at_mote "lang::typecheck::infer::infer" {
        Option.some k => String.beq k "lang",
        Option.none => false,
    }
