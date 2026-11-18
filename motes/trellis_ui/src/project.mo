// Projection: the whole graph plus the view settings, down to one
// `Ui.GraphSpec` the widget can lay out.
//
// 1. Visible declarations: externals (init/std/... -- any mote not
//    extracted as a root) only when asked for, tests only when asked for,
//    hidden kinds dropped.
// 2. Each visible declaration maps to a NODE KEY at the current level: its
//    mote, its module path, or its own id.
// 3. Edges between two different keys are aggregated, counting the
//    references each one stands for; the signature/body axes can be turned
//    off separately.
// 4. A focus (a set of keys) keeps only the keys within `depth` edges of it,
//    following callees, callers or both.
// 5. A view over `cap` nodes is refused (`too_many`) instead of drawn: a
//    5,000-node hairball helps nobody, and searching or focusing narrows it.
//
// Grouping draws boxes around nodes: by mote at the module level; by mote
// or by module (nested in its mote) at the declaration level. A grouping no
// coarser than the level is ignored.
//
// `lens` is the hook for other readings of the same graph. `calls` styles
// nodes by kind; `proofs` additionally marks proof-shaped declarations
// (`Trellis.DeclNode.is_proof`) and dims the rest -- the first step of the proof
// inspector, which needs no other extraction.

use std::list {List.filter, List.any, List.intercalate}
use std::map {HashMap}
use oak_ui::graph_layout {Ui.GraphSpec, Ui.GraphNode, Ui.GraphEdge, Ui.GraphGroup}
use lib::seq {Seq.fold, Seq.reverse, Seq.filter, Seq.length, Seq.find}
use lib::smap {Smap.empty, Smap.insert, Smap.get, Smap.has, Smap.get_i64, Smap.get_str}
use lib::model {Trellis.Graph, Trellis.DeclNode, Trellis.Edge, Trellis.ModuleNode, Trellis.DeclNode.is_proof,
    Trellis.DeclNode.is_test}

pub type Trellis.Level { at_mote, at_module, at_decl }

pub type Trellis.Grouping { by_none, by_mote, by_module }

pub type Trellis.Direction { callees, callers, both_ways }

pub struct Trellis.Settings {
    level : Trellis.Level,
    grouping : Trellis.Grouping,
    focus : List String,
    depth : I64,
    direction : Trellis.Direction,
    external : Bool,
    tests : Bool,
    signature : Bool,
    body : Bool,
    hidden_kinds : List String,
    lens : String,
    cap : I64,
}

pub def Trellis.Settings.initial : Trellis.Settings :=
    { level := Trellis.Level.at_module, grouping := Trellis.Grouping.by_mote, focus := List.empty,
        depth := 1, direction := Trellis.Direction.both_ways, external := false, tests := false,
        signature := true, body := true, hidden_kinds := List.empty, lens := "calls", cap := 250 }

pub def Trellis.Level.slug (l : Trellis.Level) : String :=
    match l { Trellis.Level.at_mote => "mote", Trellis.Level.at_module => "module", Trellis.Level.at_decl => "decl" }

pub def Trellis.Level.of_slug (s : String) : Trellis.Level :=
    if String.beq s "mote" then Trellis.Level.at_mote
    else if String.beq s "decl" then Trellis.Level.at_decl
    else Trellis.Level.at_module

pub def Trellis.Grouping.slug (g : Trellis.Grouping) : String :=
    match g { Trellis.Grouping.by_none => "none", Trellis.Grouping.by_mote => "mote",
        Trellis.Grouping.by_module => "module" }

pub def Trellis.Grouping.of_slug (s : String) : Trellis.Grouping :=
    if String.beq s "mote" then Trellis.Grouping.by_mote
    else if String.beq s "module" then Trellis.Grouping.by_module
    else Trellis.Grouping.by_none

pub def Trellis.Direction.slug (d : Trellis.Direction) : String :=
    match d { Trellis.Direction.callees => "callees", Trellis.Direction.callers => "callers",
        Trellis.Direction.both_ways => "both" }

pub def Trellis.Direction.of_slug (s : String) : Trellis.Direction :=
    if String.beq s "callees" then Trellis.Direction.callees
    else if String.beq s "callers" then Trellis.Direction.callers
    else Trellis.Direction.both_ways

/// What a projection produced.
pub type Trellis.Projection {
    /// A drawable spec; `shown` nodes out of `total` keys at this level.
    projected (spec : Ui.GraphSpec) (shown : I64) (total : I64),
    /// More than `cap` nodes would be drawn.
    too_many (count : I64),
    /// Nothing is visible (an empty graph, or filters that hide everything).
    nothing,
}

// ═══ Keys ═══

/// The key of a declaration at a level.
pub def Trellis.key_at (level : Trellis.Level) (d : Trellis.DeclNode) : String :=
    match level {
        Trellis.Level.at_mote => d.mote,
        Trellis.Level.at_module => d.module,
        Trellis.Level.at_decl => d.id,
    }

/// What a node key is called on screen: a mote by name, a module by its
/// path inside its mote, a declaration by its own name.
def label_at (level : Trellis.Level) (d : Trellis.DeclNode) : String :=
    match level {
        Trellis.Level.at_mote => d.mote,
        Trellis.Level.at_module =>
            if String.starts_with (String.concat d.mote "::") d.module
            then String.drop (String.length d.mote + 2) d.module
            else d.module,
        Trellis.Level.at_decl => d.name,
    }

/// The grouping that applies at a level (never as fine as the level).
pub def Trellis.effective_grouping (level : Trellis.Level) (g : Trellis.Grouping) : Trellis.Grouping :=
    match level {
        Trellis.Level.at_mote => Trellis.Grouping.by_none,
        Trellis.Level.at_module =>
            match g { Trellis.Grouping.by_module => Trellis.Grouping.by_mote, _ => g },
        Trellis.Level.at_decl => g,
    }

def mote_group (mote : String) : String := String.concat "mote:" mote
def module_group (module : String) : String := String.concat "module:" module

// ═══ Visible declarations ═══

def visible (s : Trellis.Settings) (d : Trellis.DeclNode) : Bool :=
    (s.external || Bool.not d.external)
        && (s.tests || Bool.not (Trellis.DeclNode.is_test d))
        && Bool.not (List.any (fn (k : String) => String.beq k d.kind) s.hidden_kinds)

/// One node per key, built from the first visible declaration with that key.
struct NodeInfo {
    key : String,
    label : String,
    mote : String,
    module : String,
    kind : String,
    external : Bool,
    proof : Bool,
    members : I64,
}

/// Every visible decl's key (`decl id -> key`), and the node table in first
/// appearance order.
struct Keys {
    of_decl : HashMap String String,
    nodes : HashMap String NodeInfo,
    order : List String,
}

def node_info (level : Trellis.Level) (d : Trellis.DeclNode) : NodeInfo :=
    { key := Trellis.key_at level d, label := label_at level d, mote := d.mote, module := d.module,
        kind := match level { Trellis.Level.at_decl => d.kind, Trellis.Level.at_module => "module",
            Trellis.Level.at_mote => "mote" },
        external := d.external, proof := Trellis.DeclNode.is_proof d, members := 1 }

def key_step (s : Trellis.Settings) (k : Keys) (d : Trellis.DeclNode) : Keys :=
    if Bool.not (visible s d) then k
    else
        let key : String := Trellis.key_at s.level d in
        let with_decl : Keys := { k with of_decl := Smap.insert d.id key k.of_decl } in
        match Smap.get key k.nodes {
            Option.some info =>
                let grown : NodeInfo := { info with members := info.members + 1,
                    proof := info.proof || Trellis.DeclNode.is_proof d } in
                { with_decl with nodes := Smap.insert key grown k.nodes },
            Option.none =>
                { with_decl with nodes := Smap.insert key (node_info s.level d) k.nodes,
                    order := List.cons key k.order },
        }

def collect_keys (s : Trellis.Settings) (ds : List Trellis.DeclNode) (k : Keys) : Keys :=
    let done : Keys := Seq.fold (key_step s) k ds in
    { done with order := Seq.reverse done.order }

// ═══ Aggregated edges ═══

struct Agg {
    counts : HashMap String I64,
    pairs : List (Pair String String),
}

def axis_on (s : Trellis.Settings) (axis : String) : Bool :=
    if String.beq axis "s" then s.signature else s.body

def pair_key (a : String) (b : String) : String := String.concat_list [a, "\t", b]

def agg_step (s : Trellis.Settings) (keys : HashMap String String) (agg : Agg) (e : Trellis.Edge) : Agg :=
    if Bool.not (axis_on s e.axis) then agg
    else
        match Smap.get e.from keys {
            Option.none => agg,
            Option.some a =>
                match Smap.get e.to keys {
                    Option.none => agg,
                    Option.some b =>
                        if String.beq a b then agg
                        else
                            let pk : String := pair_key a b in
                            let n : I64 := Smap.get_i64 pk 0 agg.counts in
                            let pairs : List (Pair String String) := if n == 0 then List.cons
                                (Pair.pair a b) agg.pairs else agg.pairs in
                            { counts := Smap.insert pk (n + 1) agg.counts, pairs := pairs },
                },
        }

def aggregate (s : Trellis.Settings) (keys : HashMap String String) (es : List Trellis.Edge) (agg : Agg) : Agg :=
    let done : Agg := Seq.fold (agg_step s keys) agg es in
    { done with pairs := Seq.reverse done.pairs }

// ═══ Focus ═══

def pfst (p : Pair String String) : String := match p { Pair.pair a _ => a }
def psnd (p : Pair String String) : String := match p { Pair.pair _ b => b }

/// The keys one step from `frontier` along the chosen direction.
def step_one (dir : Trellis.Direction) (frontier : HashMap String Bool) (acc : List String)
    (p : Pair String String) : List String :=
    let a : String := pfst p in
    let b : String := psnd p in
    let fwd : Bool := match dir { Trellis.Direction.callers => false, _ => Smap.has a frontier } in
    let back : Bool := match dir { Trellis.Direction.callees => false, _ => Smap.has b frontier } in
    let acc1 : List String := if fwd then List.cons b acc else acc in
    if back then List.cons a acc1 else acc1

def step (dir : Trellis.Direction) (frontier : HashMap String Bool) (pairs : List (Pair String String)) : List String :=
    Seq.fold (step_one dir frontier) List.empty pairs

def mark_all (ks : List String) (m : HashMap String Bool) : HashMap String Bool :=
    Seq.fold (fn (acc : HashMap String Bool) (k : String) => Smap.insert k true acc) m ks

def unseen (ks : List String) (seen : HashMap String Bool) : List String :=
    Seq.filter (fn (k : String) => Bool.not (Smap.has k seen)) ks

/// Breadth-first from the focus, `depth` steps.
#[terminating]
def reach (dir : Trellis.Direction) (pairs : List (Pair String String)) (frontier : List String)
    (seen : HashMap String Bool) (depth : I64) : HashMap String Bool :=
    if depth <= 0 || List.is_empty frontier then seen
    else
        let next : List String := unseen (step dir (mark_all frontier Smap.empty) pairs) seen in
        reach dir pairs next (mark_all next seen) (depth - 1)

// ═══ The spec ═══

def node_cls (lens : String) (info : NodeInfo) : String :=
    List.intercalate " " (List.filter (fn (c : String) => Bool.not (String.is_empty c))
        [String.concat "trellis-kind-" info.kind,
            if info.external then "trellis-external" else "",
            if String.beq lens "proofs" then (if info.proof then "trellis-proof" else "trellis-nonproof") else ""])

def node_tip (level : Trellis.Level) (info : NodeInfo) : String :=
    match level {
        Trellis.Level.at_decl => String.concat_list [info.key, " (", info.kind, ")"],
        _ => String.concat_list [info.key, " \u{2014} ", I64.to_string info.members, " declarations"],
    }

def group_of (g : Trellis.Grouping) (info : NodeInfo) : String :=
    match g {
        Trellis.Grouping.by_none => "",
        Trellis.Grouping.by_mote => mote_group info.mote,
        Trellis.Grouping.by_module => module_group info.module,
    }

def spec_node (s : Trellis.Settings) (g : Trellis.Grouping) (info : NodeInfo) : Ui.GraphNode :=
    { id := info.key, label := info.label, group := group_of g info, cls := node_cls s.lens info,
        tip := node_tip s.level info }

def spec_nodes (s : Trellis.Settings) (g : Trellis.Grouping) (order : List String) (nodes : HashMap String NodeInfo)
    (keep : HashMap String Bool) (focused : Bool) : List Ui.GraphNode :=
    Seq.reverse (Seq.fold (fn (acc : List Ui.GraphNode) (k : String) =>
        if focused && Bool.not (Smap.has k keep) then acc
        else match Smap.get k nodes {
            Option.none => acc,
            Option.some info => List.cons (spec_node s g info) acc,
        }) List.empty order)

def spec_edge (counts : HashMap String I64) (keep : HashMap String Bool) (focused : Bool) (acc : List Ui.GraphEdge)
    (p : Pair String String) : List Ui.GraphEdge :=
    let a : String := pfst p in
    let b : String := psnd p in
    if focused && Bool.not (Smap.has a keep && Smap.has b keep) then acc
    else
        let e : Ui.GraphEdge := { from := a, to := b, weight := Smap.get_i64 (pair_key a b) 1 counts, cls := "" } in
        List.cons e acc

/// Only edges between drawn nodes: with no focus, every node is drawn.
def spec_edges (pairs : List (Pair String String)) (counts : HashMap String I64) (keep : HashMap String Bool)
    (focused : Bool) : List Ui.GraphEdge :=
    Seq.reverse (Seq.fold (spec_edge counts keep focused) List.empty pairs)

/// The groups the drawn nodes need, outer first: a mote box for every mote,
/// and (by module) a module box nested in it.
#[terminating]
def spec_groups (g : Trellis.Grouping) (ns : List Ui.GraphNode) (nodes : HashMap String NodeInfo)
    (seen : HashMap String Bool) (acc : List Ui.GraphGroup) : List Ui.GraphGroup :=
    match ns {
        List.empty => List.reverse acc,
        List.cons n rest =>
            match Smap.get n.id nodes {
                Option.none => spec_groups g rest nodes seen acc,
                Option.some info =>
                    let mg : String := mote_group info.mote in
                    let with_mote : Pair (HashMap String Bool) (List Ui.GraphGroup) :=
                        if Smap.has mg seen then Pair.pair seen acc
                        else
                            let box : Ui.GraphGroup := { id := mg, label := info.mote, parent := "",
                                cls := "trellis-group-mote" } in
                            Pair.pair (Smap.insert mg true seen) (List.cons box acc) in
                    match with_mote {
                        Pair.pair seen1 acc1 =>
                            match g {
                                Trellis.Grouping.by_module =>
                                    let modg : String := module_group info.module in
                                    if Smap.has modg seen1 then spec_groups g rest nodes seen1 acc1
                                    else
                                        let box : Ui.GraphGroup :=
                                            { id := modg, label := info.module, parent := mg,
                                                cls := "trellis-group-module" } in
                                        spec_groups g rest nodes (Smap.insert modg true seen1) (List.cons box acc1),
                                _ => spec_groups g rest nodes seen1 acc1,
                            },
                    },
            },
    }

/// Project the graph.
pub def Trellis.project (g : Trellis.Graph) (s : Trellis.Settings) : Trellis.Projection :=
    let empty_keys : Keys := { of_decl := Smap.empty, nodes := Smap.empty, order := List.empty } in
    let k : Keys := collect_keys s g.decls empty_keys in
    let total : I64 := Seq.length k.order in
    if total == 0 then Trellis.Projection.nothing
    else
        let agg0 : Agg := { counts := Smap.empty, pairs := List.empty } in
        let agg : Agg := aggregate s k.of_decl g.edges agg0 in
        let focus : List String := List.filter (fn (f : String) => Smap.has f k.nodes) s.focus in
        let focused : Bool := Bool.not (List.is_empty focus) in
        let keep : HashMap String Bool :=
            if focused then reach s.direction agg.pairs focus (mark_all focus Smap.empty) s.depth else Smap.empty in
        let grouping : Trellis.Grouping := Trellis.effective_grouping s.level s.grouping in
        let nodes : List Ui.GraphNode := spec_nodes s grouping k.order k.nodes keep focused in
        let shown : I64 := Seq.length nodes in
        if shown > s.cap then Trellis.Projection.too_many shown
        else
            let groups : List Ui.GraphGroup :=
                match grouping {
                    Trellis.Grouping.by_none => List.empty,
                    _ => spec_groups grouping nodes k.nodes Smap.empty List.empty,
                } in
            let spec : Ui.GraphSpec := { nodes := nodes, edges := spec_edges agg.pairs agg.counts keep focused,
                groups := groups } in
            Trellis.Projection.projected spec shown total

// ═══ Neighbours (the detail panel) ═══

/// The distinct declarations `id` references (`outgoing`) or that reference
/// it (incoming), in edge order.
pub def Trellis.neighbours (g : Trellis.Graph) (id : String) (outgoing : Bool) : List String :=
    let step : Pair (HashMap String Bool) (List String) -> Trellis.Edge -> Pair (HashMap String Bool) (List String) :=
        fn (acc : Pair (HashMap String Bool) (List String)) (e : Trellis.Edge) =>
            let mine : Bool := if outgoing then String.beq e.from id else String.beq e.to id in
            if Bool.not mine then acc
            else
                let other : String := if outgoing then e.to else e.from in
                match acc {
                    Pair.pair seen out => if Smap.has other seen then acc else Pair.pair
                        (Smap.insert other true seen) (List.cons other out),
                } in
    match Seq.fold step (Pair.pair Smap.empty List.empty) g.edges { Pair.pair _ out => Seq.reverse out }

pub def Trellis.find_decl (ds : List Trellis.DeclNode) (id : String) : Option Trellis.DeclNode :=
    Seq.find (fn (d : Trellis.DeclNode) => String.beq d.id id) ds

pub def Trellis.find_module (ms : List Trellis.ModuleNode) (path : String) : Option Trellis.ModuleNode :=
    Seq.find (fn (m : Trellis.ModuleNode) => String.beq m.path path) ms

/// The key `key` (at `from`) maps to one level up, or `key` itself when the
/// target level is not coarser: a decl's module, a module's mote.
pub def Trellis.lift_key (g : Trellis.Graph) (from : Trellis.Level) (to : Trellis.Level)
    (key : String) : Option String :=
    match from {
        Trellis.Level.at_decl =>
            match Trellis.find_decl g.decls key {
                Option.none => Option.none,
                Option.some d => match to { Trellis.Level.at_decl => Option.some key, _ => Option.some
                    (Trellis.key_at to d) },
            },
        Trellis.Level.at_module =>
            match to {
                Trellis.Level.at_mote =>
                    match Trellis.find_module g.modules key { Option.none => Option.none,
                        Option.some m => Option.some m.mote },
                Trellis.Level.at_module => Option.some key,
                Trellis.Level.at_decl => Option.none,
            },
        Trellis.Level.at_mote => match to { Trellis.Level.at_mote => Option.some key, _ => Option.none },
    }
