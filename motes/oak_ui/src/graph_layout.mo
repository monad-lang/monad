// Graph layout: a pure, deterministic compound layered layout for
// `Ui.graph`.
//
// Input is a `Ui.GraphSpec`: nodes, directed edges, and (optionally nested)
// groups a node or group belongs to. Output is a `Ui.GraphLayout` in whole
// pixels: every node and group box placed, every edge as SVG path data.
//
// The layout is COMPOUND and computed bottom-up. Each group's members are
// laid out on their own first, which sizes the group's box; the boxes are
// then laid out at the parent level as ordinary items, with every edge that
// crosses between two of them standing in for an edge between the boxes. So
// groups never overlap, and a member never leaves its group.
//
// Within one container the layout is the classic layered (Sugiyama-style)
// pipeline, flowing left to right:
//   1. cycle breaking: a DFS drops back edges for layering only (they are
//      still drawn);
//   2. layering: longest path from the sources;
//   3. ordering: barycenter sweeps, forward then backward;
//   4. coordinates: a column per layer, stacked and centred.
// Long edges are drawn as cubic curves; there are no dummy nodes.
//
// Everything is `I64`: SVG takes integer user units and the widget never
// needs a float formatter.

use std::list {List.sort_by, List.filter, List.any}
use std::map {
    HashMap, HashMap.bucket_insert_str, HashMap.bucket_lookup_str,
    HashMap.bucket_of, HashMap.empty_buckets, HashMap.get_bucket,
    HashMap.set_bucket, map,
}

// ═══ Public types ═══

/// One node to draw. `group` is the id of the group it sits in (`""` for
/// none, or an id that names no group); `cls` is extra CSS classes for the
/// node and `tip` its hover text (`""` for the label).
pub struct Ui.GraphNode {
    id : String,
    label : String,
    group : String,
    cls : String,
    tip : String,
}

/// A directed edge. `weight` is how many underlying references it stands for
/// (an aggregated edge draws thicker).
pub struct Ui.GraphEdge {
    from : String,
    to : String,
    weight : I64,
    cls : String,
}

/// A box drawn around its members. `parent` nests it in another group
/// (`""` for the top level).
pub struct Ui.GraphGroup {
    id : String,
    label : String,
    parent : String,
    cls : String,
}

pub struct Ui.GraphSpec {
    nodes : List Ui.GraphNode,
    edges : List Ui.GraphEdge,
    groups : List Ui.GraphGroup,
}

pub struct Ui.PlacedNode {
    id : String,
    label : String,
    cls : String,
    tip : String,
    x : I64,
    y : I64,
    w : I64,
    h : I64,
}

/// A group box; `depth` is its nesting level (0 for the top).
pub struct Ui.PlacedGroup {
    id : String,
    label : String,
    cls : String,
    x : I64,
    y : I64,
    w : I64,
    h : I64,
    depth : I64,
}

/// An edge as SVG path data from its source's edge to its target's.
pub struct Ui.PlacedEdge {
    from : String,
    to : String,
    weight : I64,
    cls : String,
    d : String,
}

pub struct Ui.GraphLayout {
    nodes : List Ui.PlacedNode,
    groups : List Ui.PlacedGroup,
    edges : List Ui.PlacedEdge,
    width : I64,
    height : I64,
}

// ═══ Metrics ═══

def node_h : I64 := 26
def col_gap : I64 := 56
def row_gap : I64 := 14
def group_pad : I64 := 12
def group_header : I64 := 22
def margin : I64 := 16
def char_w : I64 := 7
def max_label_chars : I64 := 40

/// A node's width from its label: about one character cell per byte,
/// clamped so a long qualified name cannot stretch a whole column.
pub def Ui.graph_node_width (label : String) : I64 :=
    let n : I64 := String.length label in
    let shown : I64 := if n > max_label_chars then max_label_chars else n in
    let w : I64 := shown * char_w + 20 in
    if w < 44 then 44 else w

def imax (a : I64) (b : I64) : I64 := if a > b then a else b

// ═══ String-keyed maps ═══
//
// The bucket helpers from `std::map`, keyed by `String.hash`/`String.beq`,
// so no class dispatch is involved (the same reason `llvm::strmap` exists;
// that mote is not a dependency here).

def smap_empty {V : Type} : HashMap String V := HashMap.map HashMap.empty_buckets

def smap_insert {V : Type} (key : String) (val : V) (m : HashMap String V) : HashMap String V :=
    match m {
        HashMap.map buckets =>
            let idx := HashMap.bucket_of (String.hash key) in
            HashMap.map (HashMap.set_bucket buckets idx
                (HashMap.bucket_insert_str key val (HashMap.get_bucket buckets idx)))
    }

def smap_get {V : Type} (key : String) (m : HashMap String V) : Option V :=
    match m {
        HashMap.map buckets =>
            HashMap.bucket_lookup_str key (HashMap.get_bucket buckets (HashMap.bucket_of (String.hash key)))
    }

def smap_get_i64 (key : String) (fallback : I64) (m : HashMap String I64) : I64 :=
    match smap_get key m { Option.some v => v, Option.none => fallback }

def smap_get_str (key : String) (m : HashMap String String) : String :=
    match smap_get key m { Option.some v => v, Option.none => "" }

def smap_has_str (key : String) (m : HashMap String String) : Bool :=
    match smap_get key m { Option.some _ => true, Option.none => false }

/// Both values, or none.
def both {A : Type} {B : Type} (a : Option A) (b : Option B) : Option (Pair A B) :=
    match a {
        Option.none => Option.none,
        Option.some x => match b { Option.none => Option.none, Option.some y => Option.some (Pair.pair x y) },
    }

def pfst {A : Type} {B : Type} (p : Pair A B) : A := match p { Pair.pair a _ => a }
def psnd {A : Type} {B : Type} (p : Pair A B) : B := match p { Pair.pair _ b => b }

// ═══ The containment tree ═══

/// What the layout knows about the spec, indexed once.
struct LayoutIndex {
    /// group id -> parent group id (`""` at the top).
    parent : HashMap String String,
    /// node id -> the group it is laid out in (`""` at the top).
    home : HashMap String String,
    groups : List Ui.GraphGroup,
    nodes : List Ui.GraphNode,
    edges : List Ui.GraphEdge,
}

#[terminating]
def index_groups (gs : List Ui.GraphGroup) (m : HashMap String String) : HashMap String String :=
    match gs {
        List.empty => m,
        List.cons g rest => index_groups rest (smap_insert g.id g.parent m),
    }

/// A group whose parent names no group is a top-level group; so is a group
/// that would contain itself.
#[terminating]
def fix_parents (gs : List Ui.GraphGroup) (known : HashMap String String) : List Ui.GraphGroup :=
    match gs {
        List.empty => List.empty,
        List.cons g rest =>
            let ok : Bool := smap_has_str g.parent known && Bool.not (String.beq g.parent g.id) in
            let fixed : Ui.GraphGroup := { g with parent := if ok then g.parent else "" } in
            List.cons fixed (fix_parents rest known),
    }

#[terminating]
def index_homes (ns : List Ui.GraphNode) (groups : HashMap String String)
    (m : HashMap String String) : HashMap String String :=
    match ns {
        List.empty => m,
        List.cons n rest =>
            let home : String := if smap_has_str n.group groups then n.group else "" in
            index_homes rest groups (smap_insert n.id home m),
    }

def build_index (spec : Ui.GraphSpec) : LayoutIndex :=
    let raw : HashMap String String := index_groups spec.groups smap_empty in
    let groups : List Ui.GraphGroup := fix_parents spec.groups raw in
    let parent : HashMap String String := index_groups groups smap_empty in
    { parent := parent, home := index_homes spec.nodes parent smap_empty,
        groups := groups, nodes := spec.nodes, edges := spec.edges }

/// The item that stands for `id` (a node or group id) inside container `c`:
/// `id` itself when it sits directly in `c`, else the ancestor group that
/// does. `none` when `id` is not below `c` at all. `fuel` bounds the walk so
/// a malformed parent cycle cannot loop.
#[terminating]
def item_in (idx : LayoutIndex) (c : String) (id : String) (container : String) (fuel : I64) : Option String :=
    if String.beq container c then Option.some id
    else if String.is_empty container || fuel <= 0 then Option.none
    else item_in idx c container (smap_get_str container idx.parent) (fuel - 1)

def node_item_in (idx : LayoutIndex) (c : String) (node_id : String) : Option String :=
    match smap_get node_id idx.home {
        Option.none => Option.none,
        Option.some home => item_in idx c node_id home 64,
    }

// ═══ One container ═══

/// An item laid out in a container: a node or a child group's box.
struct LayoutItem {
    id : String,
    w : I64,
    h : I64,
}

/// A laid-out container, in coordinates relative to its own origin.
struct LayoutBox {
    w : I64,
    h : I64,
    nodes : List Ui.PlacedNode,
    groups : List Ui.PlacedGroup,
}

/// The container's edges between two of its own items, deduplicated and
/// without self loops, in first-seen order.
#[terminating]
def container_edges (idx : LayoutIndex) (c : String) (es : List Ui.GraphEdge) (seen : HashMap String Bool)
    (acc : List (Pair String String)) : List (Pair String String) :=
    match es {
        List.empty => List.reverse acc,
        List.cons e rest =>
            match both (node_item_in idx c e.from) (node_item_in idx c e.to) {
                Option.none => container_edges idx c rest seen acc,
                Option.some ab =>
                    let key : String := String.concat_list [pfst ab, "\t", psnd ab] in
                    let fresh : Bool := match smap_get key seen { Option.some _ => false, Option.none => true } in
                    if fresh && Bool.not (String.beq (pfst ab) (psnd ab))
                    then container_edges idx c rest (smap_insert key true seen) (List.cons ab acc)
                    else container_edges idx c rest seen acc,
            },
    }

// ─── Step 1: cycle breaking ───

#[terminating]
def succs_of (v : String) (es : List (Pair String String)) : List String :=
    match es {
        List.empty => List.empty,
        List.cons e rest =>
            match e {
                Pair.pair a b => if String.beq a v then List.cons b (succs_of v rest) else succs_of v rest,
            },
    }

#[terminating]
def preds_of (v : String) (es : List (Pair String String)) : List String :=
    match es {
        List.empty => List.empty,
        List.cons e rest =>
            match e {
                Pair.pair a b => if String.beq b v then List.cons a (preds_of v rest) else preds_of v rest,
            },
    }

/// DFS state: colour per item (0 white, 1 on the stack, 2 done) and the
/// edges kept for layering.
struct LayoutDfs {
    colour : HashMap String I64,
    kept : List (Pair String String),
}

#[terminating]
def dfs_visit (es : List (Pair String String)) (v : String) (st : LayoutDfs) : LayoutDfs :=
    let entered : LayoutDfs := { st with colour := smap_insert v 1 st.colour } in
    let after : LayoutDfs := dfs_succs es v (succs_of v es) entered in
    { after with colour := smap_insert v 2 after.colour }

#[partial]
def dfs_succs (es : List (Pair String String)) (v : String) (ws : List String) (st : LayoutDfs) : LayoutDfs :=
    match ws {
        List.empty => st,
        List.cons w rest =>
            let c : I64 := smap_get_i64 w 0 st.colour in
            if c == 1 then dfs_succs es v rest st
            else
                let kept : LayoutDfs := { st with kept := List.cons (Pair.pair v w) st.kept } in
                if c == 0
                then dfs_succs es v rest (dfs_visit es w kept)
                else dfs_succs es v rest kept,
    }

#[partial]
def dfs_all (es : List (Pair String String)) (items : List LayoutItem) (st : LayoutDfs) : LayoutDfs :=
    match items {
        List.empty => st,
        List.cons it rest =>
            if smap_get_i64 it.id 0 st.colour == 0
            then dfs_all es rest (dfs_visit es it.id st)
            else dfs_all es rest st,
    }

/// The edges with every DFS back edge removed: an acyclic subgraph.
def acyclic_edges (es : List (Pair String String)) (items : List LayoutItem) : List (Pair String String) :=
    let start : LayoutDfs := { colour := smap_empty, kept := List.empty } in
    let done : LayoutDfs := dfs_all es items start in
    List.reverse done.kept

// ─── Step 2: layering ───

/// Longest path from the sources, memoised. The edges are acyclic, so the
/// recursion through predecessors terminates.
#[terminating]
def layer_of (dag : List (Pair String String)) (v : String) (memo : HashMap String I64) : Pair I64
    (HashMap String I64) :=
    match smap_get v memo {
        Option.some l => Pair.pair l memo,
        Option.none =>
            match layer_of_preds dag (preds_of v dag) 0 memo {
                Pair.pair l m => Pair.pair l (smap_insert v l m),
            },
    }

#[partial]
def layer_of_preds (dag : List (Pair String String)) (ps : List String) (best : I64)
    (memo : HashMap String I64) : Pair I64 (HashMap String I64) :=
    match ps {
        List.empty => Pair.pair best memo,
        List.cons p rest =>
            match layer_of dag p memo {
                Pair.pair l m => layer_of_preds dag rest (imax best (l + 1)) m,
            },
    }

#[partial]
def assign_layers (dag : List (Pair String String)) (items : List LayoutItem)
    (memo : HashMap String I64) : HashMap String I64 :=
    match items {
        List.empty => memo,
        List.cons it rest =>
            match layer_of dag it.id memo {
                Pair.pair _ m => assign_layers dag rest m,
            },
    }

#[terminating]
def max_layer (items : List LayoutItem) (layers : HashMap String I64) (best : I64) : I64 :=
    match items {
        List.empty => best,
        List.cons it rest => max_layer rest layers (imax best (smap_get_i64 it.id 0 layers)),
    }

#[terminating]
def items_in_layer (items : List LayoutItem) (layers : HashMap String I64) (l : I64) : List String :=
    match items {
        List.empty => List.empty,
        List.cons it rest =>
            if smap_get_i64 it.id 0 layers == l
            then List.cons it.id (items_in_layer rest layers l)
            else items_in_layer rest layers l,
    }

#[terminating]
def build_columns (items : List LayoutItem) (layers : HashMap String I64) (l : I64) (top : I64) : List (List String) :=
    if l > top then List.empty
    else List.cons (items_in_layer items layers l) (build_columns items layers (l + 1) top)

// ─── Step 3: ordering ───

#[terminating]
def index_positions (col : List String) (i : I64) (m : HashMap String I64) : HashMap String I64 :=
    match col {
        List.empty => m,
        List.cons v rest => index_positions rest (i + 1) (smap_insert v i m),
    }

#[terminating]
def all_positions (cols : List (List String)) (m : HashMap String I64) : HashMap String I64 :=
    match cols {
        List.empty => m,
        List.cons col rest => all_positions rest (index_positions col 0 m),
    }

#[terminating]
def sum_positions (vs : List String) (pos : HashMap String I64) (acc : I64) : I64 :=
    match vs {
        List.empty => acc,
        List.cons v rest => sum_positions rest pos (acc + smap_get_i64 v 0 pos),
    }

/// A sort key per item: the mean position (x1000) of its neighbours on the
/// side being swept; an item with none keeps its current position.
def bary_key (neighbours : List String) (pos : HashMap String I64) (own : I64) : I64 :=
    let n : I64 := List.length neighbours in
    if n == 0 then own * 1000 else (sum_positions neighbours pos 0 * 1000) / n

#[terminating]
def keyed_column (col : List String) (es : List (Pair String String)) (forward : Bool)
    (pos : HashMap String I64) : List (Pair I64 String) :=
    match col {
        List.empty => List.empty,
        List.cons v rest =>
            let ns : List String := if forward then preds_of v es else succs_of v es in
            List.cons (Pair.pair (bary_key ns pos (smap_get_i64 v 0 pos)) v) (keyed_column rest es forward pos),
    }

def key_lt (a : Pair I64 String) (b : Pair I64 String) : Bool :=
    match a { Pair.pair ka _ => match b { Pair.pair kb _ => ka < kb } }

def snd_str (p : Pair I64 String) : String := match p { Pair.pair _ v => v }

def reorder_column (col : List String) (es : List (Pair String String)) (forward : Bool)
    (pos : HashMap String I64) : List String :=
    List.map snd_str (List.sort_by key_lt (keyed_column col es forward pos))

/// One sweep over the columns in list order, re-indexing positions after
/// each column so the next one sees the new order.
#[partial]
def sweep (cols : List (List String)) (es : List (Pair String String)) (forward : Bool)
    (pos : HashMap String I64) : List (List String) :=
    match cols {
        List.empty => List.empty,
        List.cons col rest =>
            let col2 : List String := reorder_column col es forward pos in
            List.cons col2 (sweep rest es forward (index_positions col2 0 pos)),
    }

#[partial]
def order_columns (cols : List (List String)) (es : List (Pair String String)) (rounds : I64) : List (List String) :=
    if rounds <= 0 then cols
    else
        let fwd : List (List String) := sweep cols es true (all_positions cols smap_empty) in
        let back : List (List String) := List.reverse (sweep (List.reverse fwd) es false
            (all_positions fwd smap_empty)) in
        order_columns back es (rounds - 1)

// ─── Step 4: coordinates ───

#[terminating]
def item_sizes (items : List LayoutItem) (m : HashMap String LayoutItem) : HashMap String LayoutItem :=
    match items {
        List.empty => m,
        List.cons it rest => item_sizes rest (smap_insert it.id it m),
    }

def size_of (id : String) (sizes : HashMap String LayoutItem) : LayoutItem :=
    match smap_get id sizes { Option.some it => it, Option.none => { id := id, w := 0, h := 0 } }

#[terminating]
def column_width (col : List String) (sizes : HashMap String LayoutItem) (best : I64) : I64 :=
    match col {
        List.empty => best,
        List.cons v rest =>
            let it : LayoutItem := size_of v sizes in
            column_width rest sizes (imax best it.w),
    }

#[terminating]
def column_height (col : List String) (sizes : HashMap String LayoutItem) (acc : I64) (first : Bool) : I64 :=
    match col {
        List.empty => acc,
        List.cons v rest =>
            let gap : I64 := if first then 0 else row_gap in
            let it : LayoutItem := size_of v sizes in
            column_height rest sizes (acc + gap + it.h) false,
    }

#[terminating]
def tallest (cols : List (List String)) (sizes : HashMap String LayoutItem) (best : I64) : I64 :=
    match cols {
        List.empty => best,
        List.cons col rest => tallest rest sizes (imax best (column_height col sizes 0 true)),
    }

/// LayoutItem id -> its top-left corner (x, y) in the container.
#[terminating]
def place_column (col : List String) (sizes : HashMap String LayoutItem) (x : I64) (colw : I64) (y : I64)
    (m : HashMap String (Pair I64 I64)) : HashMap String (Pair I64 I64) :=
    match col {
        List.empty => m,
        List.cons v rest =>
            let it : LayoutItem := size_of v sizes in
            // Centre a narrower item in its column.
            let ix : I64 := x + (colw - it.w) / 2 in
            place_column rest sizes x colw (y + it.h + row_gap) (smap_insert v (Pair.pair ix y) m),
    }

/// Returns the placements and the total width.
#[terminating]
def place_columns (cols : List (List String)) (sizes : HashMap String LayoutItem) (height : I64) (x : I64)
    (m : HashMap String (Pair I64 I64)) : Pair (HashMap String (Pair I64 I64)) I64 :=
    match cols {
        List.empty => Pair.pair m (imax 0 (x - col_gap)),
        List.cons col rest =>
            let colw : I64 := column_width col sizes 0 in
            let top : I64 := (height - column_height col sizes 0 true) / 2 in
            place_columns rest sizes height (x + colw + col_gap) (place_column col sizes x colw top m),
    }

// ─── Assembling a container ───

#[terminating]
def shift_nodes (ns : List Ui.PlacedNode) (dx : I64) (dy : I64) : List Ui.PlacedNode :=
    match ns {
        List.empty => List.empty,
        List.cons n rest => List.cons { n with x := n.x + dx, y := n.y + dy } (shift_nodes rest dx dy),
    }

#[terminating]
def shift_groups (gs : List Ui.PlacedGroup) (dx : I64) (dy : I64) : List Ui.PlacedGroup :=
    match gs {
        List.empty => List.empty,
        List.cons g rest => List.cons { g with x := g.x + dx, y := g.y + dy } (shift_groups rest dx dy),
    }

#[terminating]
def child_groups (gs : List Ui.GraphGroup) (c : String) : List Ui.GraphGroup :=
    match gs {
        List.empty => List.empty,
        List.cons g rest =>
            if String.beq g.parent c then List.cons g (child_groups rest c) else child_groups rest c,
    }

#[terminating]
def child_nodes (idx : LayoutIndex) (ns : List Ui.GraphNode) (c : String) : List Ui.GraphNode :=
    match ns {
        List.empty => List.empty,
        List.cons n rest =>
            if String.beq (smap_get_str n.id idx.home) c
            then List.cons n (child_nodes idx rest c)
            else child_nodes idx rest c,
    }

#[terminating]
def node_items (ns : List Ui.GraphNode) : List LayoutItem :=
    match ns {
        List.empty => List.empty,
        List.cons n rest =>
            let it : LayoutItem := { id := n.id, w := Ui.graph_node_width n.label, h := node_h } in
            List.cons it (node_items rest),
    }

/// A laid-out child group: its spec, and its contents' box.
struct LayoutInner {
    group : Ui.GraphGroup,
    box : LayoutBox,
}

def inner_item (inner : LayoutInner) : LayoutItem :=
    let w : I64 := imax (inner.box.w + 2 * group_pad) (Ui.graph_node_width inner.group.label) in
    { id := inner.group.id, w := w, h := inner.box.h + 2 * group_pad + group_header }

#[terminating]
def inner_items (inners : List LayoutInner) : List LayoutItem :=
    match inners {
        List.empty => List.empty,
        List.cons i rest => List.cons (inner_item i) (inner_items rest),
    }

def at (id : String) (placed : HashMap String (Pair I64 I64)) : Pair I64 I64 :=
    match smap_get id placed { Option.some p => p, Option.none => Pair.pair 0 0 }

def px (p : Pair I64 I64) : I64 := match p { Pair.pair x _ => x }
def py (p : Pair I64 I64) : I64 := match p { Pair.pair _ y => y }

#[terminating]
def place_nodes (ns : List Ui.GraphNode) (placed : HashMap String (Pair I64 I64)) : List Ui.PlacedNode :=
    match ns {
        List.empty => List.empty,
        List.cons n rest =>
            let p : Pair I64 I64 := at n.id placed in
            let pn : Ui.PlacedNode :=
                { id := n.id, label := n.label, cls := n.cls, tip := n.tip,
                    x := px p, y := py p, w := Ui.graph_node_width n.label, h := node_h } in
            List.cons pn (place_nodes rest placed),
    }

/// Every child group's box, plus its contents shifted under its header.
#[terminating]
def place_inners (inners : List LayoutInner) (placed : HashMap String (Pair I64 I64)) (depth : I64)
    (acc : LayoutBox) : LayoutBox :=
    match inners {
        List.empty => acc,
        List.cons inner rest =>
            let p : Pair I64 I64 := at inner.group.id placed in
            let it : LayoutItem := inner_item inner in
            let gx : I64 := px p in
            let gy : I64 := py p in
            let own : Ui.PlacedGroup :=
                { id := inner.group.id, label := inner.group.label, cls := inner.group.cls,
                    x := gx, y := gy, w := it.w, h := it.h, depth := depth } in
            let cx : I64 := gx + (it.w - inner.box.w) / 2 in
            let cy : I64 := gy + group_header + group_pad in
            let next : LayoutBox :=
                { acc with
                    nodes := List.append (shift_nodes inner.box.nodes cx cy) acc.nodes,
                    groups := List.cons own (List.append (shift_groups inner.box.groups cx cy) acc.groups) } in
            place_inners rest placed depth next,
    }

/// Groups get a relative `depth` while nested; the top call fixes it up.
#[terminating]
def deepen (gs : List Ui.PlacedGroup) : List Ui.PlacedGroup :=
    match gs {
        List.empty => List.empty,
        List.cons g rest => List.cons { g with depth := g.depth + 1 } (deepen rest),
    }

#[terminating]
def layout_container (idx : LayoutIndex) (c : String) : LayoutBox :=
    let inners : List LayoutInner := layout_children idx (child_groups idx.groups c) in
    let nodes : List Ui.GraphNode := child_nodes idx idx.nodes c in
    let items : List LayoutItem := List.append (node_items nodes) (inner_items inners) in
    if List.is_empty items
    then { w := 0, h := 0, nodes := List.empty, groups := List.empty }
    else
        let es : List (Pair String String) := container_edges idx c idx.edges smap_empty List.empty in
        let dag : List (Pair String String) := acyclic_edges es items in
        let layers : HashMap String I64 := assign_layers dag items smap_empty in
        let cols0 : List (List String) := build_columns items layers 0 (max_layer items layers 0) in
        let cols : List (List String) := order_columns cols0 es 3 in
        let sizes : HashMap String LayoutItem := item_sizes items smap_empty in
        let height : I64 := tallest cols sizes 0 in
        match place_columns cols sizes height 0 smap_empty {
            Pair.pair placed width =>
                let base : LayoutBox := { w := width, h := height, nodes := place_nodes nodes placed,
                    groups := List.empty } in
                place_inners inners placed 0 base,
        }

#[partial]
def layout_children (idx : LayoutIndex) (gs : List Ui.GraphGroup) : List LayoutInner :=
    match gs {
        List.empty => List.empty,
        List.cons g rest =>
            let b : LayoutBox := layout_container idx g.id in
            let inner : LayoutInner := { group := g, box := { b with groups := deepen b.groups } } in
            List.cons inner (layout_children idx rest),
    }

// ═══ Edges ═══

#[terminating]
def node_table (ns : List Ui.PlacedNode) (m : HashMap String Ui.PlacedNode) : HashMap String Ui.PlacedNode :=
    match ns {
        List.empty => m,
        List.cons n rest => node_table rest (smap_insert n.id n m),
    }

def num (v : I64) : String := I64.to_string v

/// A cubic from the right edge of `a` to the left edge of `b` when `b` is to
/// the right; otherwise a loop that leaves `a`'s right edge and comes back
/// into `b`'s right edge, so a back edge never cuts through a column.
pub def Ui.graph_edge_path (a : Ui.PlacedNode) (b : Ui.PlacedNode) : String :=
    let sx : I64 := a.x + a.w in
    let sy : I64 := a.y + a.h / 2 in
    let ty : I64 := b.y + b.h / 2 in
    if b.x >= sx
    then
        let tx : I64 := b.x in
        let bend : I64 := imax 20 ((tx - sx) / 2) in
        String.concat_list ["M ", num sx, " ", num sy, " C ", num (sx + bend), " ", num sy, " ",
            num (tx - bend), " ", num ty, " ", num tx, " ", num ty]
    else
        let tx : I64 := b.x + b.w in
        let reach : I64 := imax sx tx + col_gap / 2 in
        String.concat_list ["M ", num sx, " ", num sy, " C ", num reach, " ", num sy, " ",
            num reach, " ", num ty, " ", num tx, " ", num ty]

#[terminating]
def place_edges (es : List Ui.GraphEdge) (table : HashMap String Ui.PlacedNode) : List Ui.PlacedEdge :=
    match es {
        List.empty => List.empty,
        List.cons e rest =>
            match both (smap_get e.from table) (smap_get e.to table) {
                Option.none => place_edges rest table,
                Option.some ab =>
                    if String.beq e.from e.to then place_edges rest table
                    else
                        let pe : Ui.PlacedEdge :=
                            { from := e.from, to := e.to, weight := e.weight, cls := e.cls,
                                d := Ui.graph_edge_path (pfst ab) (psnd ab) } in
                        List.cons pe (place_edges rest table),
            },
    }

// ═══ Entry point ═══

def depth_lt (a : Ui.PlacedGroup) (b : Ui.PlacedGroup) : Bool := a.depth < b.depth

/// Lay out a graph. Deterministic: the same spec always gives the same
/// layout, and items keep their spec order wherever the edges leave the
/// choice open. The result is offset by a small margin.
pub def Ui.graph_layout (spec : Ui.GraphSpec) : Ui.GraphLayout :=
    let idx : LayoutIndex := build_index spec in
    let b : LayoutBox := layout_container idx "" in
    let nodes : List Ui.PlacedNode := shift_nodes b.nodes margin margin in
    // Outer boxes first, so an inner box draws on top of its parent's.
    let groups : List Ui.PlacedGroup := List.sort_by depth_lt (shift_groups b.groups margin margin) in
    { nodes := nodes, groups := groups,
        edges := place_edges spec.edges (node_table nodes smap_empty),
        width := b.w + 2 * margin, height := b.h + 2 * margin }
