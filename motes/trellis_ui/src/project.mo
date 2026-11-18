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
// 5. A view over `cap` nodes is split into SECTIONS instead of drawn whole
//    (a 5,000-node hairball helps nobody): the nodes are partitioned by the
//    next-coarser key -- a declaration by its module, a module by its mote --
//    and a part bigger than `cap` is cut into pieces of at most `cap`, in
//    source order. `section` picks one to draw; with none picked (or a stale
//    id) the projection is the section list (`sectioned`). Searching or
//    focusing narrows a view below the cap instead.
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
    /// The section drawn when the view is over `cap` (`""` for none).
    section : String,
}

pub def Trellis.Settings.initial : Trellis.Settings :=
    { level := Trellis.Level.at_module, grouping := Trellis.Grouping.by_mote, focus := List.empty,
        depth := 1, direction := Trellis.Direction.both_ways, external := false, tests := false,
        signature := true, body := true, hidden_kinds := List.empty, lens := "calls", cap := 500,
        section := "" }

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

/// One piece of a view too big to draw at once.
pub struct Trellis.Section {
    /// `<parent key>#<part>`: stable while the settings that shape the view are.
    id : String,
    label : String,
    count : I64,
}

/// A drawable view: `shown` nodes out of `total` keys at this level. When the
/// view was over the cap, `sections` lists every piece and `section` is the
/// one drawn; under the cap both are empty.
pub struct Trellis.Drawn {
    spec : Ui.GraphSpec,
    shown : I64,
    total : I64,
    sections : List Trellis.Section,
    section : String,
}

/// What a projection produced.
pub type Trellis.Projection {
    drawn (d : Trellis.Drawn),
    /// `count` nodes is over the cap and no section is picked: the pieces to
    /// browse.
    sectioned (count : I64) (sections : List Trellis.Section),
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

// ═══ Sections ═══

/// What a node's section is cut from: the next-coarser key.
def parent_key (level : Trellis.Level) (info : NodeInfo) : String :=
    match level {
        Trellis.Level.at_decl => info.module,
        Trellis.Level.at_module => info.mote,
        Trellis.Level.at_mote => "",
    }

/// Per parent: its node count, and the parents in first-appearance order.
struct Parents {
    counts : HashMap String I64,
    order : List String,
}

def count_parent (level : Trellis.Level) (nodes : HashMap String NodeInfo) (ps : Parents)
    (n : Ui.GraphNode) : Parents :=
    match Smap.get n.id nodes {
        Option.none => ps,
        Option.some info =>
            let p : String := parent_key level info in
            let c : I64 := Smap.get_i64 p 0 ps.counts in
            { counts := Smap.insert p (c + 1) ps.counts, order := if c == 0 then List.cons p ps.order else ps.order },
    }

def section_id (parent : String) (part : I64) : String := String.concat_list [parent, "#", I64.to_string part]

def sec_min (a : I64) (b : I64) : I64 := if a < b then a else b

/// The label of part `part` of `parts` of `parent`.
def section_label (parent : String) (part : I64) (parts : I64) (cap : I64) (count : I64) : String :=
    if String.is_empty parent
    then String.concat_list ["Nodes ", I64.to_string (part * cap + 1), "\u{2013}",
        I64.to_string (sec_min count ((part + 1) * cap))]
    else if parts > 1 then String.concat_list [parent, " (", I64.to_string (part + 1), "/", I64.to_string parts, ")"]
    else parent

/// The sections of one parent, appended to `acc` (reversed).
#[terminating]
def parent_sections (parent : String) (count : I64) (cap : I64) (parts : I64) (part : I64)
    (acc : List Trellis.Section) : List Trellis.Section :=
    if part >= parts then acc
    else
        let sec : Trellis.Section := { id := section_id parent part,
            label := section_label parent part parts cap count,
            count := sec_min cap (count - part * cap) } in
        parent_sections parent count cap parts (part + 1) (List.cons sec acc)

def sections_of (cap : I64) (ps : Parents) : List Trellis.Section :=
    Seq.reverse (Seq.fold (fn (acc : List Trellis.Section) (p : String) =>
        let count : I64 := Smap.get_i64 p 0 ps.counts in
        parent_sections p count cap ((count + cap - 1) / cap) 0 acc) List.empty (Seq.reverse ps.order))

/// The nodes in section `id`: each node's part is its index within its
/// parent, divided by `cap`.
struct Picking {
    seen : HashMap String I64,
    kept : List Ui.GraphNode,
}

def pick_step (level : Trellis.Level) (nodes : HashMap String NodeInfo) (cap : I64) (id : String) (st : Picking)
    (n : Ui.GraphNode) : Picking :=
    match Smap.get n.id nodes {
        Option.none => st,
        Option.some info =>
            let p : String := parent_key level info in
            let i : I64 := Smap.get_i64 p 0 st.seen in
            let mine : Bool := String.beq (section_id p (i / cap)) id in
            { seen := Smap.insert p (i + 1) st.seen, kept := if mine then List.cons n st.kept else st.kept },
    }

def nodes_in_section (level : Trellis.Level) (nodes : HashMap String NodeInfo) (cap : I64) (id : String)
    (ns : List Ui.GraphNode) : List Ui.GraphNode :=
    let st0 : Picking := { seen := Smap.empty, kept := List.empty } in
    let done : Picking := Seq.fold (pick_step level nodes cap id) st0 ns in
    Seq.reverse done.kept

def has_section (id : String) (secs : List Trellis.Section) : Bool :=
    List.any (fn (sec : Trellis.Section) => String.beq sec.id id) secs

// ═══ Projecting ═══

def node_ids (ns : List Ui.GraphNode) : HashMap String Bool :=
    Seq.fold (fn (acc : HashMap String Bool) (n : Ui.GraphNode) => Smap.insert n.id true acc) Smap.empty ns

/// The spec for exactly `nodes`: their groups and the edges between them.
def spec_for (grouping : Trellis.Grouping) (k : Keys) (agg : Agg) (nodes : List Ui.GraphNode) : Ui.GraphSpec :=
    let groups : List Ui.GraphGroup :=
        match grouping {
            Trellis.Grouping.by_none => List.empty,
            _ => spec_groups grouping nodes k.nodes Smap.empty List.empty,
        } in
    { nodes := nodes, edges := spec_edges agg.pairs agg.counts (node_ids nodes) true, groups := groups }

def drawn_view (spec : Ui.GraphSpec) (total : I64) (sections : List Trellis.Section)
    (section : String) : Trellis.Projection :=
    let d : Trellis.Drawn := { spec := spec, shown := Seq.length spec.nodes, total := total, sections := sections,
        section := section } in
    Trellis.Projection.drawn d

/// The expensive half of a projection: the visible keys, the aggregated
/// edges and the nodes the focus keeps. It depends on every setting except
/// `cap` and `section`, so the app keeps it and re-runs only `Trellis.cut`
/// while the user pages through sections or changes the cap (aggregating
/// the type checker's 64k edges is most of a projection's cost).
pub struct Trellis.Prepared {
    level : Trellis.Level,
    grouping : Trellis.Grouping,
    keys : Keys,
    agg : Agg,
    nodes : List Ui.GraphNode,
    total : I64,
}

pub def Trellis.Prepared.empty : Trellis.Prepared :=
    let k : Keys := { of_decl := Smap.empty, nodes := Smap.empty, order := List.empty } in
    let a : Agg := { counts := Smap.empty, pairs := List.empty } in
    { level := Trellis.Level.at_module, grouping := Trellis.Grouping.by_none, keys := k, agg := a,
        nodes := List.empty, total := 0 }

/// Everything but the cap and the section.
pub def Trellis.prepare (g : Trellis.Graph) (s : Trellis.Settings) : Trellis.Prepared :=
    let empty_keys : Keys := { of_decl := Smap.empty, nodes := Smap.empty, order := List.empty } in
    let k : Keys := collect_keys s g.decls empty_keys in
    let agg0 : Agg := { counts := Smap.empty, pairs := List.empty } in
    let agg : Agg := aggregate s k.of_decl g.edges agg0 in
    let focus : List String := List.filter (fn (f : String) => Smap.has f k.nodes) s.focus in
    let focused : Bool := Bool.not (List.is_empty focus) in
    let keep : HashMap String Bool :=
        if focused then reach s.direction agg.pairs focus (mark_all focus Smap.empty) s.depth else Smap.empty in
    let grouping : Trellis.Grouping := Trellis.effective_grouping s.level s.grouping in
    { level := s.level, grouping := grouping, keys := k, agg := agg,
        nodes := spec_nodes s grouping k.order k.nodes keep focused, total := Seq.length k.order }

/// The cheap half: draw the prepared view whole, or cut it into sections
/// of at most `cap` nodes and draw `section` (or list them).
pub def Trellis.cut (p : Trellis.Prepared) (cap0 : I64) (section : String) : Trellis.Projection :=
    if p.total == 0 then Trellis.Projection.nothing
    else
        let shown : I64 := Seq.length p.nodes in
        let cap : I64 := if cap0 < 1 then 1 else cap0 in
        if shown <= cap then drawn_view (spec_for p.grouping p.keys p.agg p.nodes) p.total List.empty ""
        else
            let ps0 : Parents := { counts := Smap.empty, order := List.empty } in
            let sections : List Trellis.Section :=
                sections_of cap (Seq.fold (count_parent p.level p.keys.nodes) ps0 p.nodes) in
            if has_section section sections
            then
                let picked : List Ui.GraphNode := nodes_in_section p.level p.keys.nodes cap section p.nodes in
                drawn_view (spec_for p.grouping p.keys p.agg picked) p.total sections section
            else Trellis.Projection.sectioned shown sections

/// Project the graph: `Trellis.cut` of `Trellis.prepare`.
pub def Trellis.project (g : Trellis.Graph) (s : Trellis.Settings) : Trellis.Projection :=
    Trellis.cut (Trellis.prepare g s) s.cap s.section

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
