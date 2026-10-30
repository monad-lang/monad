// Balanced dispatch trees over a sorted leaf list.
//
// A linear `if`/`else if` chain nests one level per leaf; at ~1,500 arms
// that overflowed CI's 8 MB stack while the corpus was checked, which is
// why the generated tables are trees of small functions instead. Depth is
// log2(n), and every function makes at most one call.
//
// The `else` branch of a node calls the OTHER node's function, not its
// own, so no function here is self-recursive.

use lang::construct {
    Vis, app, apps, attr, def_text, global, if_, param, u32, var,
}
use lang::types {Term}
use std::list {List.length}

/// One leaf: the key the tree routes on and the body its function
/// returns. Both are terms, so a caller decides what "matches" means
/// (`String.beq`, `U32.beq`, or a range test).
pub struct Leaf {
    key : Term,
    body : Term,
}

pub def leaf (key : Term) (body : Term) : Leaf := { key := key, body := body }

/// Everything about a tree that does not vary per leaf.
pub struct Spec {
    /// Function base name, e.g. `Markdown.entity_raw`; helpers are
    /// `base_0`, `base_1`, ...
    base : String,
    /// The parameter name every function in the tree takes.
    param : String,
    key_type : Term,
    result_type : Term,
    /// Strict less-than on the key, e.g. `String.lt`.
    less_than : String,
    /// What an EMPTY tree's entry point returns.
    fallback : Term,
}

pub def spec (base : String) (param : String) (key_type : Term) (result_type : Term)
    (less_than : String) (fallback : Term) : Spec :=
    { base := base, param := param, key_type := key_type, result_type := result_type,
      less_than := less_than, fallback := fallback }

/// A built node: its id is its position in the emitted list, and a fork
/// names its children by id.
type Node {
    leaf_node (key : Term) (body : Term),
    fork_node (pivot : Term) (left : I64) (right : I64),
}

/// The whole tree, as source. Leaves must arrive sorted by the key the
/// tree compares (`less_than`), and every `Leaf.key` must be a literal
/// term, since a parent compares against it.
pub def Gen.emit (spec : Spec) (leaves : List Leaf) : String :=
    match build leaves List.empty {
        Pair.pair nodes_rev root =>
            let nodes : List Node := List.reverse nodes_rev in
            String.concat (render_nodes spec nodes 0) (entry_text spec root),
    }

/// Nodes, children before parents, so a parent's children already have
/// their ids. The second half is this subtree's root id (-1 when empty).
#[partial]
def build (leaves : List Leaf) (acc : List Node) : Pair (List Node) I64 :=
    if I64.lt (List.length leaves) 2
    then build_small leaves acc
    else build_halves (split_at (I64.div (List.length leaves) 2) leaves List.empty) acc

#[partial]
def build_small (leaves : List Leaf) (acc : List Node) : Pair (List Node) I64 :=
    match leaves {
        List.empty => Pair.pair acc (I64.sub 0 1),
        List.cons only _ =>
            Pair.pair (List.cons (Node.leaf_node only.key only.body) acc) (List.length acc),
    }

#[partial]
def build_halves (halves : Pair (List Leaf) (List Leaf)) (acc : List Node)
    : Pair (List Node) I64 :=
    match halves {
        Pair.pair left right =>
            match build left acc {
                Pair.pair after_left left_id =>
                    match build right after_left {
                        Pair.pair after_right right_id =>
                            Pair.pair
                                (List.cons (Node.fork_node (pivot_of right) left_id right_id)
                                    after_right)
                                (List.length after_right),
                    },
            },
    }

/// A fork's pivot is the FIRST leaf of its right half: every key in the
/// left subtree sorts below it and every key in the right subtree is at or
/// above it, which is what makes `< pivot then left else right` a partition.
/// Using the left half's last key instead would route that key's own leaf
/// out of the subtree that contains it.
def pivot_of (right : List Leaf) : Term :=
    match right {
        List.cons hd _ => hd.key,
        // Unreachable: a fork always has two non-empty halves.
        List.empty => u32 0,
    }

/// Split at `n`, keeping the order of both halves.
#[partial]
def split_at (n : I64) (leaves : List Leaf) (acc : List Leaf)
    : Pair (List Leaf) (List Leaf) :=
    if I64.lt n 1
    then Pair.pair (List.reverse acc) leaves
    else
        match leaves {
            List.empty => Pair.pair (List.reverse acc) List.empty,
            List.cons hd tl => split_at (I64.sub n 1) tl (List.cons hd acc),
        }

/// One helper declaration per node, in id order.
#[partial]
def render_nodes (spec : Spec) (nodes : List Node) (id : I64) : String :=
    match nodes {
        List.empty => "",
        List.cons hd tl =>
            String.concat (render_node spec hd id) (render_nodes spec tl (I64.add id 1)),
    }

def render_node (spec : Spec) (node : Node) (id : I64) : String :=
    def_text [attr "partial"] Vis.vis_package (helper_name spec id)
        [param spec.param spec.key_type] spec.result_type (node_body spec node)

def node_body (spec : Spec) (node : Node) : Term :=
    match node {
        Node.leaf_node _ body => body,
        Node.fork_node pivot_key left right =>
            if_ (apps (global spec.less_than) [var 0 spec.param, pivot_key])
                (app (global (helper_name spec left)) (var 0 spec.param))
                (app (global (helper_name spec right)) (var 0 spec.param)),
    }

def helper_name (spec : Spec) (id : I64) : String :=
    String.concat (String.concat spec.base "_") (I64.to_string id)

/// The `pub def` a generator calls: the root helper, or the fallback value
/// for an empty leaf list.
def entry_text (spec : Spec) (root : I64) : String :=
    if I64.lt root 0
    then def_text [] Vis.vis_public spec.base [param spec.param spec.key_type]
            spec.result_type spec.fallback
    else def_text [] Vis.vis_public spec.base [param spec.param spec.key_type]
            spec.result_type (app (global (helper_name spec root)) (var 0 spec.param))
