/// The app's update: loading, searching, picking, drilling and level
/// switches, driven with a fixture graph (no browser).

use std::list {List.any}
use oak::typed {Oak.to_html}
use xml_html::html {Html.to_string}
use oak_ui::graph_layout {Ui.PlacedNode}
use oak_ui::graph {Ui.GraphMsg}
use lib::model {Trellis.Graph.encode, Trellis.DeclNode}
use lib::project {Trellis.Level, Trellis.Level.slug}
use oak::app {Command}
use lib::app {Trellis.Model, Trellis.Msg, Trellis.Effect, Trellis.Model.initial, Trellis.update, Trellis.view,
    Trellis.selected_key, Trellis.source_url}
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
    let m : Trellis.Model := ready in
    String.beq m.status "ready" && shows "lang::typecheck::infer" ready && m.shown == 4

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

/// The fixture at the decl level with a cap of 3: three sections, infer
/// alone, unify packed with module (2 + 1), then nat.
def over_cap : Trellis.Model :=
    step (step ready (Trellis.Msg.set_level "decl")) (Trellis.Msg.set_cap "3")

#[test]
def test_over_the_cap_shows_the_section_browser : Bool :=
    let m : Trellis.Model := over_cap in
    m.over == 8 && List.length m.sections == 3 && m.shown == 0
        && String.contains (html over_cap) "too many to draw at once"
        && String.contains (html over_cap) "lang::typecheck::unify"

#[test]
def test_opening_a_section_draws_it : Bool :=
    let m : Trellis.Model := step over_cap (Trellis.Msg.open_section "+lang::typecheck::unify") in
    m.shown == 3 && shows "lang::typecheck::unify::whnf" m && shows "lang::module::load" m
        && String.contains (html m) "Section 2 of 3"

#[test]
def test_section_steps_clamp_at_the_ends : Bool :=
    let first : Trellis.Model := step over_cap (Trellis.Msg.open_section "+lang::typecheck::infer") in
    let back : Trellis.Model := step first (Trellis.Msg.section_step (0 - 1)) in
    let next : Trellis.Model := step first (Trellis.Msg.section_step 1) in
    let last : Trellis.Model := step next (Trellis.Msg.section_step 9) in
    String.beq back.settings.section "+lang::typecheck::infer"
        && String.beq next.settings.section "+lang::typecheck::unify"
        && String.beq last.settings.section "+proofs::nat"

#[test]
def test_close_section_returns_to_the_list : Bool :=
    let opened : Trellis.Model := step over_cap (Trellis.Msg.open_section "+proofs::nat") in
    let closed : Trellis.Model := step opened Trellis.Msg.close_section in
    closed.shown == 0 && String.contains (html closed) "too many to draw at once"

#[test]
def test_level_switch_clears_the_section : Bool :=
    let opened : Trellis.Model := step over_cap (Trellis.Msg.open_section "+proofs::nat") in
    let up : Trellis.Model := step opened (Trellis.Msg.set_level "module") in
    // Still over the cap of 3 at the module level (4 modules): back to the
    // list, now by mote (lang, proofs), with no section open.
    String.is_empty up.settings.section && up.over == 4 && up.shown == 0 && List.length up.sections == 2

#[test]
def test_filter_narrows_the_section_list : Bool :=
    let m : Trellis.Model := step over_cap (Trellis.Msg.filter_sections "nat") in
    String.contains (html m) "proofs::nat" && Bool.not (String.contains (html m) "lang::typecheck::infer")

#[test]
def test_theme_follows_the_os_until_picked : Bool :=
    let auto_html : String := html ready in
    let dark : Trellis.Model := step ready (Trellis.Msg.set_theme "dark") in
    String.contains auto_html "oak-root" && Bool.not (String.contains auto_html "data-theme")
        && String.contains (html dark) "data-theme=\"dark\""

#[test]
def test_signature_links_the_types_it_names : Bool :=
    let m : Trellis.Model := step ready (Trellis.Msg.pick "decl" "lang::typecheck::infer::infer") in
    let page : String := html m in
    String.contains page "trellis-sig__text" && String.contains page "title=\"lang::typecheck::infer::Ty\""
        && String.contains page "trellis-types__module"
        && List.any (fn (d : Trellis.DeclNode) => String.beq d.id "lang::typecheck::infer::Ty") m.sig_types

#[terminating]
def fetches_source (module : String) (cmd : Command Trellis.Effect Trellis.Msg) : Bool :=
    match cmd {
        Command.batch cmds => List.any (fetches_source module) cmds,
        Command.perform e =>
            match e { Trellis.Effect.fx_fetch_source mo url => String.beq mo module
                && String.beq url (Trellis.source_url module), _ => false },
        _ => false,
    }

def unify_picked : Pair Trellis.Model (Command Trellis.Effect Trellis.Msg) :=
    Trellis.update ready (Trellis.Msg.pick "decl" "lang::typecheck::unify::whnf")

#[test]
def test_selecting_a_decl_fetches_its_module_once : Bool :=
    match unify_picked {
        Pair.pair m cmd =>
            let again : Pair Trellis.Model (Command Trellis.Effect Trellis.Msg) :=
                Trellis.update m (Trellis.Msg.pick "decl" "lang::typecheck::unify::unify") in
            fetches_source "lang::typecheck::unify" cmd
                && (match again { Pair.pair _ cmd2 => Bool.not (fetches_source "lang::typecheck::unify" cmd2) })
                && String.contains (html m) "Loading the source",
    }

#[test]
def test_loaded_source_shows_the_decl_lines : Bool :=
    match unify_picked {
        Pair.pair m _ =>
            let src : String := "pub def whnf (t : Term) : Term := t\npub def unify (a : Term) : Bool := true" in
            let shown : Trellis.Model := step m (Trellis.Msg.source_loaded "lang::typecheck::unify" src) in
            let page : String := html shown in
            String.contains page "trellis-source__line" && String.contains page "whnf"
                && Bool.not (String.contains page "(a : Term)") && List.length shown.code == 1,
    }

#[test]
def test_a_failed_source_says_so : Bool :=
    match unify_picked {
        Pair.pair m _ =>
            String.contains (html (step m (Trellis.Msg.source_failed "lang::typecheck::unify" "HTTP 404")))
                "Source not available",
    }
