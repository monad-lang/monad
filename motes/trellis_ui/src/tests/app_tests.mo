/// The app's update: loading, searching, picking, drilling and level
/// switches, driven with a fixture graph (no browser).

use std::list {List.any}
use oak::typed {Oak.to_html}
use xml_html::html {Html.to_string}
use oak_ui::graph_layout {Ui.PlacedNode}
use oak_ui::graph {Ui.GraphMsg}
use lib::model {Trellis.Graph.encode}
use lib::project {Trellis.Level, Trellis.Level.slug}
use lib::app {Trellis.Model, Trellis.Msg, Trellis.Model.initial, Trellis.update, Trellis.view, Trellis.selected_key}
use lib::tests::support {fixture}

def step (m : Trellis.Model) (msg : Trellis.Msg) : Trellis.Model :=
    match Trellis.update m msg { Pair.pair next _ => next }

def ready : Trellis.Model := step (Trellis.Model.initial "graph.tsv") (Trellis.Msg.loaded
    (Trellis.Graph.encode fixture))

def node_ids (m : Trellis.Model) : List String := List.map (fn (n : Ui.PlacedNode) => n.id) m.layout.nodes

def shows (id : String) (m : Trellis.Model) : Bool := List.any (fn (n : String) => String.beq n id) (node_ids m)

def html (m : Trellis.Model) : String := Html.to_string (Oak.to_html (Trellis.view m))

#[test]
def test_load_projects_the_module_level : Bool :=
    String.beq ready.status "ready" && shows "lang::typecheck::infer" ready && ready.shown == 4

#[test]
def test_bad_file_fails_with_reason : Bool :=
    let m : Trellis.Model := step (Trellis.Model.initial "graph.tsv") (Trellis.Msg.loaded "<html>") in
    String.beq m.status "failed" && String.contains (html m) "Could not load the graph"

#[test]
def test_search_highlights_and_enter_picks : Bool :=
    let searched : Trellis.Model := step ready (Trellis.Msg.search "whnf") in
    let picked : Trellis.Model := step searched (Trellis.Msg.search_key "Enter") in
    List.length searched.hits >= 1
        && String.beq (Trellis.Level.slug picked.settings.level) "decl"
        && String.beq picked.view.selected "lang::typecheck::unify::whnf"
        && shows "lang::typecheck::unify::unify" picked && Bool.not (shows "lang::module::load" picked)

#[test]
def test_drill_into_a_module_shows_its_decls : Bool :=
    let sel : Trellis.Model := step ready (Trellis.Msg.pick "module" "lang::typecheck::unify") in
    let drilled : Trellis.Model := step sel Trellis.Msg.drill_selected in
    shows "lang::typecheck::unify::unify" drilled && shows "lang::typecheck::unify::whnf" drilled
        && Bool.not (shows "lang::typecheck::infer::check" drilled)

#[test]
def test_level_up_lifts_the_focus : Bool :=
    let picked : Trellis.Model := step ready (Trellis.Msg.pick "decl" "lang::typecheck::infer::infer") in
    let up : Trellis.Model := step picked (Trellis.Msg.set_level "module") in
    List.any (fn (f : String) => String.beq f "lang::typecheck::infer") up.settings.focus

#[test]
def test_group_selection_names_the_module : Bool :=
    let m : Trellis.Model := step ready (Trellis.Msg.graph (Ui.GraphMsg.graph_select "module:lang::module")) in
    match Trellis.selected_key m { Pair.pair level key => String.beq level "module" && String.beq key "lang::module" }

#[test]
def test_detail_lists_uses_and_used_by : Bool :=
    let m : Trellis.Model := step ready (Trellis.Msg.pick "decl" "lang::typecheck::unify::unify") in
    let page : String := html m in
    String.contains page "Used by (3)" && String.contains page "Uses (1)"

#[test]
def test_clear_focus_restores_the_level : Bool :=
    let picked : Trellis.Model := step ready (Trellis.Msg.pick "decl" "lang::typecheck::unify::whnf") in
    let cleared : Trellis.Model := step picked Trellis.Msg.clear_focus in
    cleared.shown > picked.shown

#[test]
def test_toggling_externals_adds_std : Bool :=
    let m : Trellis.Model := step ready (Trellis.Msg.toggle "external" true) in
    shows "std::list" m
