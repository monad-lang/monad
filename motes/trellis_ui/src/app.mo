// The trellis app: an Oak program over a loaded `Trellis.Graph`.
//
// The model keeps the whole graph and the current view settings; every
// change to the settings re-projects (`Trellis.project`) and re-lays out
// (`Ui.graph_layout`) once, and pan/zoom/selection touch only the cached
// layout's `Ui.GraphView`.
//
// Loading is the host's job: `fx_fetch` starts a request for the graph
// file and the update polls it (`fx_poll`) from a short timer until the body
// is in. The wasm entry (`main.mo`) runs the effects; tests drive `update`
// with `loaded` directly.

use std::list {List.filter, List.any, List.intercalate, List.filter_map}
use oak::typed {Oak.Node, Oak.Attr}
use oak::app {Program, Program.with_subs, Command}
use oak::events {Html.on, Html.on_click, Subscription, Subscription.animation_frame_msg}
use oak::elements {
    Html.div, Html.span, Html.p, Html.ul, Html.li, Html.a, Html.h2, Html.h3, Html.button, Html.type_,
    Html.class_, Html.text, Html.href, Html.attr, Html.aria, Html.role, Html.id_, Html.target, Html.rel,
    Html.placeholder, Html.title_attr, Html.aside,
}
use web_event::event {WebEvent, ListenerFlags, ListenerFlags.none, HandlerResult, HandlerResult.prevent,
    HandlerResult.ignore}
use web_wasm::types {RequestId}
use oak_ui::vocab {Ui.Opt, Ui.primary, Ui.small, Ui.ghost, Ui.soft, Ui.outline, Ui.gap, Ui.full, Ui.neutral, Ui.info,
    Ui.warning, Ui.cls}
use oak_ui::layout {Ui.stack, Ui.cluster, Ui.app_shell}
use oak_ui::typography {Ui.heading, Ui.text, Ui.muted, Ui.code}
use oak_ui::button {Ui.button, Ui.button_group}
use oak_ui::form {Ui.field, Ui.input, Ui.select, Ui.checkbox, Ui.switch, Ui.range}
use oak_ui::feedback {Ui.badge, Ui.spinner, Ui.empty_state, Ui.alert}
use oak_ui::data {Ui.description_list}
use oak_ui::graph_layout {Ui.GraphLayout, Ui.GraphSpec, Ui.graph_layout}
use oak_ui::graph {Ui.GraphMsg, Ui.GraphView, Ui.GraphView.initial, Ui.GraphView.update, Ui.graph}
use lib::model {Trellis.Graph, Trellis.Graph.empty, Trellis.Graph.decode, Trellis.DeclNode, Trellis.ModuleNode,
    Trellis.DeclNode.is_proof}
use lib::fuzzy {Fuzzy.Hit, Fuzzy.search}
use lib::seq {Seq.map, Seq.filter, Seq.length}
use lib::project {
    Trellis.Level, Trellis.Grouping, Trellis.Direction, Trellis.Settings, Trellis.Settings.initial,
    Trellis.Level.slug, Trellis.Level.of_slug, Trellis.Grouping.slug, Trellis.Grouping.of_slug,
    Trellis.Direction.slug, Trellis.Direction.of_slug, Trellis.Projection, Trellis.project,
    Trellis.neighbours, Trellis.find_decl, Trellis.find_module, Trellis.lift_key,
}
use lib::model {Trellis.parse_nat}

// ═══ Model, messages, effects ═══

pub struct Trellis.Model {
    /// `idle` (before the first frame), `loading`, `ready` or `failed`.
    status : String,
    error : String,
    url : String,
    graph : Trellis.Graph,
    settings : Trellis.Settings,
    query : String,
    hits : List Fuzzy.Hit,
    cursor : I64,
    view : Ui.GraphView,
    layout : Ui.GraphLayout,
    shown : I64,
    total : I64,
    /// The node count of a refused view (`Trellis.Projection.too_many`), else 0.
    over : I64,
    /// The selected declaration with its uses and users, computed when the
    /// selection changes (not on every render: a drag re-renders per move).
    detail : Option Trellis.DeclNode,
    uses : List String,
    used_by : List String,
}

pub type Trellis.Msg {
    start,
    fetch_started (req : RequestId),
    fetch_poll (req : RequestId),
    loaded (text : String),
    failed (why : String),
    search (query : String),
    search_key (key : String),
    pick (level : String) (key : String),
    set_level (slug : String),
    set_grouping (slug : String),
    set_direction (slug : String),
    set_depth (text : String),
    toggle (name : String) (on : Bool),
    graph (msg : Ui.GraphMsg),
    focus_selected,
    drill_selected,
    clear_focus,
}

pub type Trellis.Effect {
    fx_fetch (url : String),
    fx_poll (req : RequestId),
}

def empty_layout : Ui.GraphLayout :=
    { nodes := List.empty, groups := List.empty, edges := List.empty, width := 0, height := 0 }

/// The model before anything is loaded; `url` is where the graph file is.
pub def Trellis.Model.initial (url : String) : Trellis.Model :=
    { status := "idle", error := "", url := url, graph := Trellis.Graph.empty, settings := Trellis.Settings.initial,
        query := "", hits := List.empty, cursor := 0, view := Ui.GraphView.initial, layout := empty_layout,
        shown := 0, total := 0, over := 0, detail := Option.none, uses := List.empty, used_by := List.empty }

// ═══ Update ═══

def stay (m : Trellis.Model) : Pair Trellis.Model (Command Trellis.Effect Trellis.Msg) := Pair.pair m Command.none

def hit_keys (hits : List Fuzzy.Hit) : List String := List.map (fn (h : Fuzzy.Hit) => h.key) hits

/// Re-project and re-lay out after a settings or graph change. Search hits
/// that are nodes at this level are highlighted.
pub def Trellis.refresh (m : Trellis.Model) : Trellis.Model :=
    let v : Ui.GraphView := m.view in
    let marked : Ui.GraphView := { v with highlighted := hit_keys m.hits } in
    match Trellis.project m.graph m.settings {
        Trellis.Projection.projected spec shown total =>
            { m with layout := Ui.graph_layout spec, shown := shown, total := total, over := 0, view := marked },
        Trellis.Projection.too_many n => { m with layout := empty_layout, shown := 0, over := n, view := marked },
        Trellis.Projection.nothing => { m with layout := empty_layout, shown := 0, total := 0, over := 0,
            view := marked },
    }

def with_settings (m : Trellis.Model) (s : Trellis.Settings) : Trellis.Model := Trellis.refresh { m with settings := s }

def search_limit : I64 := 12

def hit_at (hits : List Fuzzy.Hit) (i : I64) : Option Fuzzy.Hit :=
    match hits {
        List.empty => Option.none,
        List.cons h rest => if i <= 0 then Option.some h else hit_at rest (i - 1),
    }

/// Show `key` (a mote, module or decl, by `level`) as the focus: switch to
/// its level, focus on it and select it.
pub def Trellis.pick (m : Trellis.Model) (level : String) (key : String) : Trellis.Model :=
    let s : Trellis.Settings := m.settings in
    let lvl : Trellis.Level := Trellis.Level.of_slug level in
    let grouping : Trellis.Grouping :=
        match lvl { Trellis.Level.at_decl => Trellis.Grouping.by_module, _ => Trellis.Grouping.by_mote } in
    let ns : Trellis.Settings := { s with level := lvl, grouping := grouping, focus := [key] } in
    let v : Ui.GraphView := m.view in
    let nv : Ui.GraphView := { v with selected := key, pan_x := 0, pan_y := 0 } in
    with_settings { m with view := nv } ns

def level_of_hit (h : Fuzzy.Hit) : String := h.level

/// The key under the selection, at the current level. A group's id
/// (`mote:`/`module:`) names the mote or module it boxes.
pub def Trellis.selected_key (m : Trellis.Model) : Pair String String :=
    let sel : String := m.view.selected in
    if String.starts_with "mote:" sel then Pair.pair "mote" (String.drop 5 sel)
    else if String.starts_with "module:" sel then Pair.pair "module" (String.drop 7 sel)
    else Pair.pair (Trellis.Level.slug m.settings.level) sel

def decls_of_module (g : Trellis.Graph) (path : String) : List String :=
    Seq.map (fn (d : Trellis.DeclNode) => d.id) (Seq.filter (fn
        (d : Trellis.DeclNode) => String.beq d.module path) g.decls)

def modules_of_mote (g : Trellis.Graph) (mote : String) : List String :=
    List.map (fn (mo : Trellis.ModuleNode) => mo.path) (List.filter (fn
        (mo : Trellis.ModuleNode) => String.beq mo.mote mote) g.modules)

/// One level down from the selection: a mote's modules, a module's
/// declarations (depth 0, so only them; raise the depth to see neighbours).
def drill (m : Trellis.Model) : Trellis.Model :=
    let s : Trellis.Settings := m.settings in
    match Trellis.selected_key m {
        Pair.pair level key =>
            if String.beq level "mote"
            then with_settings m { s with level := Trellis.Level.at_module, grouping := Trellis.Grouping.by_mote,
                focus := modules_of_mote m.graph key, depth := 0 }
            else if String.beq level "module"
            then with_settings m { s with level := Trellis.Level.at_decl, grouping := Trellis.Grouping.by_module,
                focus := decls_of_module m.graph key, depth := 0 }
            else m,
    }

def focus_selection (m : Trellis.Model) : Trellis.Model :=
    match Trellis.selected_key m {
        Pair.pair level key => if String.is_empty key then m else Trellis.pick m level key,
    }

/// A level switch keeps the focus when it can be lifted (a decl to its
/// module, a module to its mote) and drops it otherwise.
def switch_level (m : Trellis.Model) (slug : String) : Trellis.Model :=
    let s : Trellis.Settings := m.settings in
    let to : Trellis.Level := Trellis.Level.of_slug slug in
    let lifted : List String :=
        List.filter_map (fn (k : String) => Trellis.lift_key m.graph s.level to k) s.focus in
    let v : Ui.GraphView := m.view in
    let nv : Ui.GraphView := { v with selected := "" } in
    with_settings { m with view := nv } { s with level := to, focus := lifted }

def toggle (m : Trellis.Model) (name : String) (on : Bool) : Trellis.Model :=
    let s : Trellis.Settings := m.settings in
    if String.beq name "external" then with_settings m { s with external := on }
    else if String.beq name "tests" then with_settings m { s with tests := on }
    else if String.beq name "signature" then with_settings m { s with signature := on }
    else if String.beq name "body" then with_settings m { s with body := on }
    else if String.beq name "proofs" then with_settings m { s with lens := if on then "proofs" else "calls" }
    else m

def search_key (m : Trellis.Model) (key : String) : Trellis.Model :=
    let n : I64 := List.length m.hits in
    if String.beq key "ArrowDown" then { m with cursor := if m.cursor + 1 >= n then 0 else m.cursor + 1 }
    else if String.beq key "ArrowUp" then { m with cursor := if m.cursor <= 0 then
        (if n > 0 then n - 1 else 0) else m.cursor - 1 }
    else if String.beq key "Escape" then Trellis.refresh { m with query := "", hits := List.empty, cursor := 0 }
    else if String.beq key "Enter" then
        match hit_at m.hits m.cursor {
            Option.none => m,
            Option.some h => Trellis.pick m h.level h.key,
        }
    else m

def loaded (m : Trellis.Model) (text : String) : Trellis.Model :=
    match Trellis.Graph.decode text {
        Result.err why => { m with status := "failed", error := why },
        Result.ok g => Trellis.refresh { m with status := "ready", graph := g },
    }

def poll_delay : I64 := 30

/// Recompute the detail cache for the current selection.
def with_detail (m : Trellis.Model) : Trellis.Model :=
    match Trellis.selected_key m {
        Pair.pair level key =>
            if String.beq level "decl" && Bool.not (String.is_empty key)
            then { m with detail := Trellis.find_decl m.graph.decls key,
                uses := Trellis.neighbours m.graph key true, used_by := Trellis.neighbours m.graph key false }
            else { m with detail := Option.none, uses := List.empty, used_by := List.empty },
    }

def keep_detail (before : String) (step : Pair Trellis.Model
    (Command Trellis.Effect Trellis.Msg)) : Pair Trellis.Model (Command Trellis.Effect Trellis.Msg) :=
    match step {
        Pair.pair m cmd => if String.beq before m.view.selected then step else Pair.pair (with_detail m) cmd,
    }

pub def Trellis.update (m : Trellis.Model) (msg : Trellis.Msg) : Pair Trellis.Model
    (Command Trellis.Effect Trellis.Msg) :=
    keep_detail m.view.selected (update_step m msg)

def update_step (m : Trellis.Model) (msg : Trellis.Msg) : Pair Trellis.Model (Command Trellis.Effect Trellis.Msg) :=
    match msg {
        Trellis.Msg.start => Pair.pair { m with status := "loading" } (Command.perform (Trellis.Effect.fx_fetch m.url)),
        Trellis.Msg.fetch_started req => Pair.pair m (Command.after poll_delay (Trellis.Msg.fetch_poll req)),
        Trellis.Msg.fetch_poll req => Pair.pair m (Command.perform (Trellis.Effect.fx_poll req)),
        Trellis.Msg.loaded text => stay (loaded m text),
        Trellis.Msg.failed why => stay { m with status := "failed", error := why },
        Trellis.Msg.search q =>
            let hits : List Fuzzy.Hit := Fuzzy.search m.graph q search_limit m.settings.external in
            let v : Ui.GraphView := m.view in
            stay { m with query := q, hits := hits, cursor := 0, view := { v with highlighted := hit_keys hits } },
        Trellis.Msg.search_key key => stay (search_key m key),
        Trellis.Msg.pick level key => stay (Trellis.pick m level key),
        Trellis.Msg.set_level slug => stay (switch_level m slug),
        Trellis.Msg.set_grouping slug =>
            let s : Trellis.Settings := m.settings in
            stay (with_settings m { s with grouping := Trellis.Grouping.of_slug slug }),
        Trellis.Msg.set_direction slug =>
            let s : Trellis.Settings := m.settings in
            stay (with_settings m { s with direction := Trellis.Direction.of_slug slug }),
        Trellis.Msg.set_depth text =>
            let s : Trellis.Settings := m.settings in
            stay (with_settings m { s with depth := Trellis.parse_nat text }),
        Trellis.Msg.toggle name on => stay (toggle m name on),
        Trellis.Msg.graph gm => stay { m with view := Ui.GraphView.update m.view gm },
        Trellis.Msg.focus_selected => stay (focus_selection m),
        Trellis.Msg.drill_selected => stay (drill m),
        Trellis.Msg.clear_focus =>
            let s : Trellis.Settings := m.settings in
            stay (with_settings m { s with focus := List.empty }),
    }

/// Load on the first frame (the runtime has no init command).
pub def Trellis.subscriptions (m : Trellis.Model) : List (Subscription Trellis.Msg) :=
    if String.beq m.status "idle" then [Subscription.animation_frame_msg Trellis.Msg.start] else List.empty

// ═══ View ═══

def search_keys (e : WebEvent) : HandlerResult Trellis.Msg :=
    if String.beq e.key "ArrowDown" || String.beq e.key "ArrowUp" || String.beq e.key "Enter"
        || String.beq e.key "Escape"
    then HandlerResult.prevent (Trellis.Msg.search_key e.key)
    else HandlerResult.ignore

def hit_row (cursor : I64) (i : I64) (h : Fuzzy.Hit) : Oak.Node Trellis.Msg :=
    let active : Bool := i == cursor in
    Html.li [Html.role "option", Html.aria "selected" (if active then "true" else "false"),
        Html.class_ (if active then ["trellis-hit", "trellis-hit--active"] else ["trellis-hit"])]
        [Html.button [Html.type_ "button", Html.class_ ["trellis-hit__button"], Html.on_click
            (Trellis.Msg.pick h.level h.key)]
            [Html.span [Html.class_ ["trellis-hit__name"]] [Html.text h.label],
                Html.span [Html.class_ ["trellis-hit__kind"]] [Html.text h.kind],
                Html.span [Html.class_ ["trellis-hit__detail"]] [Html.text h.detail]]]

#[terminating]
def hit_rows (cursor : I64) (i : I64) (hits : List Fuzzy.Hit) : List (Oak.Node Trellis.Msg) :=
    match hits {
        List.empty => List.empty,
        List.cons h rest => List.cons (hit_row cursor i h) (hit_rows cursor (i + 1) rest),
    }

def search_box (m : Trellis.Model) : Oak.Node Trellis.Msg :=
    Ui.stack [Ui.gap 2] List.empty
        [Ui.field List.empty "trellis-search" "Search"
            "Motes, modules and declarations; \u{2191}\u{2193} and Enter pick." ""
            (fn (wiring : List (Oak.Attr Trellis.Msg)) =>
                Ui.input [Ui.full] "search" m.query Trellis.Msg.search
                    (List.append wiring [Html.placeholder "unify, infer::check, typecheck\u{2026}",
                        Html.on "keydown" ListenerFlags.none search_keys, Html.aria "controls" "trellis-hits",
                        Html.attr "autocomplete" "off"])),
            if List.is_empty m.hits
            then (if String.is_empty m.query then Html.span List.empty List.empty
                else Ui.muted [Ui.small] List.empty [Html.text "No matches."])
            else Html.ul [Html.id_ "trellis-hits", Html.class_ ["trellis-hits"], Html.role "listbox",
                Html.aria "label" "Search results"]
                (hit_rows m.cursor 0 m.hits)]

def level_button (current : Trellis.Level) (slug : String) (label : String) : Oak.Node Trellis.Msg :=
    let on : Bool := String.beq (Trellis.Level.slug current) slug in
    Ui.button (if on then [Ui.small, Ui.primary] else [Ui.small, Ui.outline])
        [Html.aria "pressed" (if on then "true" else "false"), Html.on_click (Trellis.Msg.set_level slug)]
        [Html.text label]

def grouping_options (level : Trellis.Level) : List (Pair String String) :=
    match level {
        Trellis.Level.at_mote => [Pair.pair "none" "None"],
        Trellis.Level.at_module => [Pair.pair "none" "None", Pair.pair "mote" "By mote"],
        Trellis.Level.at_decl => [Pair.pair "none" "None", Pair.pair "mote" "By mote", Pair.pair "module" "By module"],
    }

def labelled (id : String) (label : String) (control : List
    (Oak.Attr Trellis.Msg) -> Oak.Node Trellis.Msg) : Oak.Node Trellis.Msg :=
    Ui.field [Ui.small] id label "" "" control

def focus_summary (m : Trellis.Model) : Oak.Node Trellis.Msg :=
    let n : I64 := List.length m.settings.focus in
    if n == 0 then Ui.muted [Ui.small] List.empty [Html.text "No focus: the whole level is shown."]
    else Ui.stack [Ui.gap 1] List.empty
        [Ui.text [Ui.small] List.empty
            [Html.text (if n == 1 then String.concat "Focus: " (List.intercalate "" m.settings.focus)
                else String.concat_list ["Focus: ", I64.to_string n, " items"])],
            Ui.button [Ui.small, Ui.ghost] [Html.on_click Trellis.Msg.clear_focus] [Html.text "Clear focus"]]

def controls (m : Trellis.Model) : Oak.Node Trellis.Msg :=
    let s : Trellis.Settings := m.settings in
    Ui.stack [Ui.gap 3] List.empty
        [Ui.button_group [Ui.small] "Level" List.empty
            [level_button s.level "mote" "Motes", level_button s.level "module" "Modules",
                level_button s.level "decl" "Declarations"],
            labelled "trellis-grouping" "Grouping"
                (Ui.select [Ui.small, Ui.full] (grouping_options s.level)
                    (Trellis.Grouping.slug s.grouping) Trellis.Msg.set_grouping),
            labelled "trellis-direction" "Follow"
                (Ui.select [Ui.small, Ui.full]
                    [Pair.pair "both" "Callers and callees", Pair.pair "callees" "Callees",
                        Pair.pair "callers" "Callers"]
                    (Trellis.Direction.slug s.direction) Trellis.Msg.set_direction),
            labelled "trellis-depth" (String.concat "Depth: " (I64.to_string s.depth))
                (Ui.range [Ui.full] 0 6 1 s.depth Trellis.Msg.set_depth),
            focus_summary m,
            Ui.checkbox [Ui.small] "Signature references" s.signature (Trellis.Msg.toggle "signature") List.empty,
            Ui.checkbox [Ui.small] "Body references" s.body (Trellis.Msg.toggle "body") List.empty,
            Ui.checkbox [Ui.small] "Dependencies (init, std, \u{2026})" s.external
                (Trellis.Msg.toggle "external") List.empty,
            Ui.checkbox [Ui.small] "Tests" s.tests (Trellis.Msg.toggle "tests") List.empty,
            Ui.switch [Ui.small] "Proof lens" (String.beq s.lens "proofs") (Trellis.Msg.toggle "proofs") List.empty]

// ─── Detail panel ───

def ref_button (id : String) : Oak.Node Trellis.Msg :=
    Html.li List.empty
        [Html.button [Html.type_ "button", Html.class_ ["trellis-ref"], Html.title_attr id, Html.on_click
            (Trellis.Msg.pick "decl" id)]
            [Html.text id]]

def max_refs : I64 := 40

#[terminating]
def take_ids (n : I64) (xs : List String) : List String :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => if n <= 0 then List.empty else List.cons x (take_ids (n - 1) rest),
    }

def ref_list (title : String) (ids : List String) : Oak.Node Trellis.Msg :=
    let n : I64 := List.length ids in
    Html.div [Html.class_ ["trellis-refs"]]
        [Html.h3 [Html.class_ ["trellis-refs__title"]] [Html.text (String.concat_list [title, " (", I64.to_string n,
            ")"])],
            if n == 0 then Ui.muted [Ui.small] List.empty [Html.text "None."]
            else Html.ul [Html.class_ ["trellis-refs__list"]] (List.map ref_button (take_ids max_refs ids)),
            if n > max_refs then Ui.muted [Ui.small] List.empty [Html.text (String.concat_list ["\u{2026} and ",
                I64.to_string (n - max_refs), " more"])]
            else Html.span List.empty List.empty]

def file_of (g : Trellis.Graph) (module : String) : String :=
    match Trellis.find_module g.modules module { Option.some mo => mo.file, Option.none => "" }

def actions (drillable : Bool) : Oak.Node Trellis.Msg :=
    Ui.cluster [Ui.gap 2] List.empty
        (List.append [Ui.button [Ui.small, Ui.primary] [Html.on_click Trellis.Msg.focus_selected] [Html.text "Focus"]]
            (if drillable then [Ui.button [Ui.small,
                Ui.outline] [Html.on_click Trellis.Msg.drill_selected] [Html.text "Show contents"]]
                else List.empty))

def decl_detail (g : Trellis.Graph) (d : Trellis.DeclNode) (uses : List String)
    (used_by : List String) : Oak.Node Trellis.Msg :=
    let file : String := file_of g d.module in
    let where_ : String := if String.is_empty file then d.module else String.concat_list [file, ":",
        I64.to_string d.line] in
    Ui.stack [Ui.gap 3] List.empty
        [Html.h2 [Html.class_ ["trellis-detail__title"]] [Html.text d.name],
            Ui.cluster [Ui.gap 1] List.empty
                (List.append [Ui.badge [Ui.info] d.kind, Ui.badge [Ui.neutral] d.vis]
                    (List.append (if Trellis.DeclNode.is_proof d then [Ui.badge [Ui.warning] "proof"] else List.empty)
                        (List.map (fn (a : String) => Ui.badge [Ui.neutral, Ui.soft] (String.concat "#" a)) d.attrs))),
            Ui.description_list [Ui.small]
                [Pair.pair "Module" (Ui.code d.module), Pair.pair "Source" (Ui.code where_),
                    Pair.pair "Sort" (Html.text (if String.is_empty d.sort then "\u{2014}" else d.sort))],
            if String.is_empty d.doc
            then Ui.muted [Ui.small] List.empty [Html.text "No docs link (extract with --docs-base)."]
            else Html.a [Html.href d.doc, Html.target "_blank", Html.rel "noopener"] [Html.text "Open documentation"],
            actions false,
            ref_list "Uses" uses,
            ref_list "Used by" used_by]

def module_detail (g : Trellis.Graph) (path : String) : Oak.Node Trellis.Msg :=
    Ui.stack [Ui.gap 3] List.empty
        [Html.h2 [Html.class_ ["trellis-detail__title"]] [Html.text path],
            Ui.cluster [Ui.gap 1] List.empty [Ui.badge [Ui.info] "module"],
            Ui.description_list [Ui.small]
                [Pair.pair "File" (Ui.code (file_of g path)),
                    Pair.pair "Declarations" (Html.text (I64.to_string (List.length (decls_of_module g path))))],
            actions true]

def mote_detail (g : Trellis.Graph) (mote : String) : Oak.Node Trellis.Msg :=
    Ui.stack [Ui.gap 3] List.empty
        [Html.h2 [Html.class_ ["trellis-detail__title"]] [Html.text mote],
            Ui.cluster [Ui.gap 1] List.empty [Ui.badge [Ui.info] "mote"],
            Ui.description_list [Ui.small]
                [Pair.pair "Modules" (Html.text (I64.to_string (List.length (modules_of_mote g mote))))],
            actions true]

def detail (m : Trellis.Model) : Oak.Node Trellis.Msg :=
    match Trellis.selected_key m {
        Pair.pair level key =>
            if String.is_empty key
            then Ui.muted [Ui.small] List.empty [Html.text "Select a node to see what it uses and what uses it."]
            else if String.beq level "mote" then mote_detail m.graph key
            else if String.beq level "module" then module_detail m.graph key
            else match m.detail {
                Option.some d => decl_detail m.graph d m.uses m.used_by,
                Option.none => Ui.muted [Ui.small] List.empty [Html.text key],
            },
    }

// ─── Main area ───

def stats_line (m : Trellis.Model) : String :=
    String.concat_list [I64.to_string m.shown, " of ", I64.to_string m.total, " ", Trellis.Level.slug m.settings.level,
        " nodes \u{00B7} ", I64.to_string (Seq.length m.graph.decls), " declarations \u{00B7} ",
        I64.to_string (Seq.length m.graph.edges), " references (", I64.to_string m.graph.unresolved, " unresolved)"]

def main_area (m : Trellis.Model) : Oak.Node Trellis.Msg :=
    if String.beq m.status "failed"
    then Ui.alert [Ui.cls ["trellis-error"]] "Could not load the graph" Option.none List.empty [Html.text m.error]
    else if Bool.not (String.beq m.status "ready")
    then Ui.spinner List.empty "Loading the graph\u{2026}"
    else if m.over > 0
    then Ui.empty_state List.empty (String.concat_list [I64.to_string m.over, " nodes is too many to draw"])
        "Search for a declaration, pick a module, or lower the depth to narrow the view." List.empty
    else if m.shown == 0
    then Ui.empty_state List.empty "Nothing to show" "The filters hide every declaration." List.empty
    else Ui.graph List.empty "Reference graph" m.layout m.view Trellis.Msg.graph [Html.class_ ["trellis-graph"]]

pub def Trellis.view (m : Trellis.Model) : Oak.Node Trellis.Msg :=
    Ui.app_shell [Ui.cls ["trellis"]] false
        [Ui.cluster [Ui.gap 3] List.empty
            [Html.span [Html.class_ ["trellis-brand"]] [Html.text "trellis"],
                Ui.muted [Ui.small] List.empty [Html.text (List.intercalate ", " m.graph.roots)]]]
        [Ui.stack [Ui.gap 4] List.empty [search_box m, controls m]]
        [Html.div [Html.class_ ["trellis-main"]]
            [Html.div [Html.class_ ["trellis-canvas"]] [main_area m],
                Html.aside [Html.class_ ["trellis-detail"], Html.aria "label" "Selection"] [detail m]]]
        [Ui.muted [Ui.small] List.empty [Html.text (stats_line m)]]

pub def Trellis.program (url : String) : Program Trellis.Model Trellis.Msg Trellis.Effect :=
    Program.with_subs (Trellis.Model.initial url) Trellis.update Trellis.view Trellis.subscriptions

/// The app's own styles: layout of the main area and the search results,
/// on top of `Ui.css_all`. Variables only, like oak_ui's sheet.
pub def Trellis.css : String := r#"
.trellis .oak-shell__main { padding: 0; }
.trellis-brand { font-weight: 700; letter-spacing: 0.02em; }
.trellis-main { display: grid; grid-template-columns: minmax(0, 1fr) 22rem; height: calc(100vh - 7rem); }
.trellis-canvas { position: relative; min-width: 0; padding: calc(var(--oak-space) * 2); }
.trellis-graph { height: 100%; }
.trellis-detail { border-left: 1px solid var(--oak-border); padding: calc(var(--oak-space) * 4); overflow-y: auto; }
.trellis-detail__title { font-size: 1.05rem; margin: 0; word-break: break-all; font-family: var(--oak-font-mono); }
.trellis-hits { list-style: none; margin: 0; padding: 0; border: 1px solid var(--oak-border);
  border-radius: var(--oak-radius-sm); max-height: 22rem; overflow-y: auto; }
.trellis-hit__button { display: grid; grid-template-columns: 1fr auto; gap: 0 var(--oak-space); width: 100%;
  text-align: left; border: 0; background: transparent;
  padding: calc(var(--oak-space) * 1.5) calc(var(--oak-space) * 2); font: inherit; color: inherit; cursor: pointer; }
.trellis-hit--active .trellis-hit__button, .trellis-hit__button:hover { background: var(--oak-primary-soft); }
.trellis-hit__name { font-family: var(--oak-font-mono); font-weight: 600; overflow: hidden; text-overflow: ellipsis; }
.trellis-hit__kind { font-size: 0.75em; color: var(--oak-muted); }
.trellis-hit__detail { grid-column: 1 / -1; font-size: 0.75em; color: var(--oak-muted); overflow: hidden;
  text-overflow: ellipsis; white-space: nowrap; }
.trellis-refs__title { font-size: 0.875rem; margin: 0 0 var(--oak-space); }
.trellis-refs__list { list-style: none; margin: 0; padding: 0; }
.trellis-ref { border: 0; background: transparent; color: var(--oak-primary); font-family: var(--oak-font-mono);
  font-size: 0.8125em; padding: 2px 0; cursor: pointer; text-align: left; word-break: break-all; }
.trellis-ref:hover { text-decoration: underline; }
.oak-graph__node.trellis-kind-type > rect, .oak-graph__node.trellis-kind-struct > rect { fill: var(--oak-info-soft); }
.oak-graph__node.trellis-kind-class > rect,
.oak-graph__node.trellis-kind-instance > rect { fill: var(--oak-success-soft); }
.oak-graph__node.trellis-kind-module > rect { fill: var(--oak-surface); }
.oak-graph__node.trellis-external > rect { stroke-dasharray: 3 2; }
.oak-graph__node.trellis-external > text { fill: var(--oak-muted); }
.oak-graph__node.trellis-proof > rect { fill: var(--oak-warning-soft); stroke: var(--oak-warning); }
.oak-graph__node.trellis-nonproof { opacity: 0.45; }
"#
