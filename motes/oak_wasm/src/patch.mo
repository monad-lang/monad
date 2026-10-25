/// Diff two rendered `Html.Node` trees into a patch list, and apply it to a
/// live DOM.
///
/// Attributes diff by name. Children reconcile one of two ways: a list
/// whose children all carry a distinct `data-oak-key` (`Html.key`) is
/// matched BY KEY, so a reorder moves the existing DOM nodes; any other
/// list diffs positionally when the child count is unchanged, and any
/// other change (different tag, different child count, text/raw-text
/// content, a comment) replaces that node. That is exact, cheap to reason
/// about, and covers the Elm-loop shapes.
///
/// Paths are `childNodes` indices from the mount container: the top-level
/// node is `[0]`, its i-th child `[0, i]`, and so on. `childNodes` counts text
/// nodes, and `Patch.mount_node` appends every text node, so an index means
/// the same thing on both sides.
///
/// Event handlers ride in attributes: `data-oak-on-<event>` whose value is a
/// numeric message id. The JS host owns that convention: setting such an
/// attribute registers (or REPLACES) the listener, removing it unregisters,
/// and the listener calls the exported `oak_dispatch_event(id)`. Keeping the
/// rule in one place is what stops a re-render from stacking listeners.
use std::list {List.length}
use xml_html::html {Html.Attr, Html.Node, Html.beq}
use oak::elements {Html.key_attr}
use web_wasm::types {Node}
use web_wasm::dom {
  Dom.append, Dom.child, Dom.child_count, Dom.comment, Dom.create, Dom.insert_before,
  Dom.remove, Dom.remove_attr, Dom.replace, Dom.set_attr, Dom.set_text, Dom.text_node,
}

pub type Patch {
    replace (path : List I64) (node : Html.Node),
    set_text (path : List I64) (text : String),
    set_attr (path : List I64) (name : String) (value : String),
    remove_attr (path : List I64) (name : String),
    insert (path : List I64) (node : Html.Node),
    remove (path : List I64),
    move (from : List I64) (to : List I64)
}

/// The patch list that turns `old` into `new` under the mount container.
pub def Patch.diff (old : Html.Node) (new : Html.Node) : List Patch :=
    Patch.diff_at (List.cons 0i64 List.empty) old new

#[terminating]
def Patch.diff_at (path : List I64) (old : Html.Node) (new : Html.Node) : List Patch :=
    if Html.beq old new then List.empty else Patch.diff_changed path old new

#[partial]
def Patch.diff_changed (path : List I64) (old : Html.Node) (new : Html.Node) : List Patch :=
    match new {
        Html.Node.node_text content => Patch.diff_text path old content,
        Html.Node.node_element tag attrs children => Patch.diff_element path old tag attrs children,
        Html.Node.node_void tag attrs => Patch.diff_void path old tag attrs,
        _ => Patch.replace_at path new,
    }

def Patch.replace_at (path : List I64) (node : Html.Node) : List Patch :=
    List.cons (Patch.replace path node) List.empty

#[partial]
def Patch.diff_text (path : List I64) (old : Html.Node) (content : String) : List Patch :=
    match old {
        Html.Node.node_text _ => List.cons (Patch.set_text path content) List.empty,
        _ => Patch.replace_at path (Html.Node.node_text content),
    }

#[partial]
def Patch.diff_element (path : List I64) (old : Html.Node) (tag : String) (attrs : List Html.Attr) (children : List Html.Node) : List Patch :=
    match old {
        Html.Node.node_element old_tag old_attrs old_children =>
            Patch.diff_same_element path old_tag old_attrs old_children tag attrs children,
        _ => Patch.replace_at path (Html.Node.node_element tag attrs children),
    }

#[partial]
def Patch.diff_same_element (path : List I64) (old_tag : String) (old_attrs : List Html.Attr) (old_children : List Html.Node) (tag : String) (attrs : List Html.Attr) (children : List Html.Node) : List Patch :=
    if Bool.not (String.beq old_tag tag)
    then Patch.replace_at path (Html.Node.node_element tag attrs children)
    else if Patch.keyed_mode old_children children
    then List.append (Patch.attr_patches path old_attrs attrs) (Patch.keyed_patches path old_children children)
    else if Bool.not (List.length old_children == List.length children)
    then Patch.replace_at path (Html.Node.node_element tag attrs children)
    else List.append (Patch.attr_patches path old_attrs attrs) (Patch.child_patches path old_children children)

#[partial]
def Patch.diff_void (path : List I64) (old : Html.Node) (tag : String) (attrs : List Html.Attr) : List Patch :=
    match old {
        Html.Node.node_void old_tag old_attrs =>
            if String.beq old_tag tag
            then Patch.attr_patches path old_attrs attrs
            else Patch.replace_at path (Html.Node.node_void tag attrs),
        _ => Patch.replace_at path (Html.Node.node_void tag attrs),
    }

#[terminating]
def Patch.child_patches (path : List I64) (old_children : List Html.Node) (children : List Html.Node) : List Patch :=
    Patch.child_patches_at path old_children children 0i64

#[terminating]
#[partial]
def Patch.child_patches_at (path : List I64) (old_children : List Html.Node) (children : List Html.Node) (index : I64) : List Patch :=
    match old_children {
        List.empty => List.empty,
        List.cons old_child old_rest =>
            match children {
                List.empty => List.empty,
                List.cons child rest =>
                    let child_path : List I64 := List.append path (List.cons index List.empty) in
                    List.append
                        (Patch.diff_at child_path old_child child)
                        (Patch.child_patches_at path old_rest rest (index + 1i64)),
            },
    }

// ─── Keyed children ──────────────────────────────────────────────────
//
// A list whose children all carry a distinct `data-oak-key` (see
// `Html.key`) is reconciled by key: a reorder moves the existing DOM nodes,
// an insertion mounts one node, a deletion removes one. A node therefore
// keeps its identity -- focus, scroll, listeners, CSS transitions -- across
// a reorder. Unkeyed lists, and lists with a duplicate key, keep the
// positional behavior above.
//
// Apply-order invariant: every patch is interpreted against the DOM as left
// by all preceding patches, and the generator performs the identical splice
// on `model`, so `model[i]` is `parent.childNodes[i]` when its patch runs.
// Each apply operation mutates the DOM once and resolves every index before
// mutating.

/// `path ++ [index]`.
def Patch.child_path (path : List I64) (index : I64) : List I64 :=
    List.append path (List.cons index List.empty)

#[terminating]
#[partial]
def Patch.attr_lookup (name : String) (attrs : List Html.Attr) : Option String := match attrs {
    List.empty => Option.none,
    List.cons a rest =>
        if String.beq (Patch.attr_name a) name
        then Option.some (Patch.attr_value a)
        else Patch.attr_lookup name rest,
}

/// A child's key, when it is an element/void carrying `data-oak-key`.
#[partial]
def Patch.key_of (node : Html.Node) : Option String := match node {
    Html.Node.node_element _tag attrs _children => Patch.attr_lookup Html.key_attr attrs,
    Html.Node.node_void _tag attrs => Patch.attr_lookup Html.key_attr attrs,
    _ => Option.none,
}

/// How many times `key` occurs in `nodes` (duplicate detection).
#[terminating]
def Patch.key_count (key : String) (nodes : List Html.Node) : I64 := match nodes {
    List.empty => 0i64,
    List.cons node rest => I64.add (Patch.key_is key node) (Patch.key_count key rest),
}

def Patch.key_is (key : String) (node : Html.Node) : I64 :=
    Patch.key_is_opt key (Patch.key_of node)

def Patch.key_is_opt (key : String) (found : Option String) : I64 := match found {
    Option.none => 0i64,
    Option.some k => if String.beq k key then 1i64 else 0i64,
}

/// Every child is keyed and no key repeats. `[]` is vacuously true, which
/// is what lets empty -> keyed (all inserts) and keyed -> empty (all
/// removes) work without replacing the parent. Uniqueness is also what
/// guarantees a match is never behind the cursor during the walk.
#[terminating]
def Patch.keys_unique (nodes : List Html.Node) : Bool := match nodes {
    List.empty => true,
    List.cons node rest => Patch.key_unique_child node rest && Patch.keys_unique rest,
}

def Patch.key_unique_child (node : Html.Node) (rest : List Html.Node) : Bool :=
    Patch.key_unique_opt (Patch.key_of node) rest

def Patch.key_unique_opt (found : Option String) (rest : List Html.Node) : Bool := match found {
    Option.none => false,
    Option.some k => I64.beq (Patch.key_count k rest) 0i64,
}

def Patch.keyed_mode (old_children : List Html.Node) (children : List Html.Node) : Bool :=
    Patch.keys_unique old_children && Patch.keys_unique children

/// Is `key` present in `nodes`?
#[terminating]
def Patch.key_in (key : String) (nodes : List Html.Node) : Bool := match nodes {
    List.empty => false,
    List.cons node rest => Patch.key_in_step key node rest,
}

#[terminating]
def Patch.key_in_step (key : String) (node : Html.Node) (rest : List Html.Node) : Bool :=
    Patch.key_in_opt key (Patch.key_of node) rest

#[terminating]
def Patch.key_in_opt (key : String) (found : Option String) (rest : List Html.Node) : Bool := match found {
    Option.none => Patch.key_in key rest,
    Option.some k => if String.beq k key then true else Patch.key_in key rest,
}

/// `remove` patches for old children whose key is gone, in DESCENDING index
/// order: deleting a higher index never shifts a lower one, so every path
/// is still valid when its patch runs, and no surviving node is moved to
/// express a pure deletion.
#[terminating]
def Patch.keyed_removals (path : List I64) (rev : List Html.Node) (children : List Html.Node) (index : I64) : List Patch := match rev {
    List.empty => List.empty,
    List.cons node rest =>
        List.append
            (Patch.keyed_removal path node children index)
            (Patch.keyed_removals path rest children (index - 1i64)),
}

def Patch.keyed_removal (path : List I64) (node : Html.Node) (children : List Html.Node) (index : I64) : List Patch :=
    Patch.keyed_removal_opt path (Patch.key_of node) children index

def Patch.keyed_removal_opt (path : List I64) (found : Option String) (children : List Html.Node) (index : I64) : List Patch := match found {
    Option.none => List.empty,
    Option.some key =>
        if Patch.key_in key children
        then List.empty
        else List.cons (Patch.remove (Patch.child_path path index)) List.empty,
}

/// The old children whose key survives, in their original order: the model
/// the walk starts from, i.e. the DOM after the removals.
#[terminating]
def Patch.keyed_kept (nodes : List Html.Node) (children : List Html.Node) : List Html.Node := match nodes {
    List.empty => List.empty,
    List.cons node rest =>
        if Patch.keyed_kept_child node children
        then List.cons node (Patch.keyed_kept rest children)
        else Patch.keyed_kept rest children,
}

def Patch.keyed_kept_child (node : Html.Node) (children : List Html.Node) : Bool :=
    Patch.keyed_kept_opt (Patch.key_of node) children

def Patch.keyed_kept_opt (found : Option String) (children : List Html.Node) : Bool := match found {
    Option.none => false,
    Option.some key => Patch.key_in key children,
}

/// Where `key` sits in the model, with the node to diff against.
#[terminating]
def Patch.key_locate (key : String) (model : List Html.Node) (index : I64) : Option (Pair I64 Html.Node) := match model {
    List.empty => Option.none,
    List.cons head rest => Patch.key_locate_head key head rest index,
}

#[terminating]
def Patch.key_locate_head (key : String) (head : Html.Node) (rest : List Html.Node) (index : I64) : Option (Pair I64 Html.Node) :=
    Patch.key_locate_opt key (Patch.key_of head) head rest index

#[terminating]
def Patch.key_locate_opt (key : String) (found : Option String) (head : Html.Node) (rest : List Html.Node) (index : I64) : Option (Pair I64 Html.Node) := match found {
    Option.none => Patch.key_locate key rest (index + 1i64),
    Option.some k =>
        if String.beq k key
        then Option.some (Pair.pair index head)
        else Patch.key_locate key rest (index + 1i64),
}

#[terminating]
def Patch.model_insert (index : I64) (node : Html.Node) (model : List Html.Node) : List Html.Node := match model {
    List.empty => List.cons node List.empty,
    List.cons head rest =>
        if index == 0i64
        then List.cons node (List.cons head rest)
        else List.cons head (Patch.model_insert (index - 1i64) node rest),
}

#[terminating]
def Patch.model_remove (index : I64) (model : List Html.Node) : List Html.Node := match model {
    List.empty => List.empty,
    List.cons head rest =>
        if index == 0i64
        then rest
        else List.cons head (Patch.model_remove (index - 1i64) rest),
}

def Patch.model_move (from : I64) (to : I64) (node : Html.Node) (model : List Html.Node) : List Html.Node :=
    Patch.model_insert to node (Patch.model_remove from model)

/// Reconcile the new children against the model, left to right.
#[terminating]
def Patch.keyed_walk (path : List I64) (model : List Html.Node) (children : List Html.Node) (index : I64) : List Patch := match children {
    List.empty => List.empty,
    List.cons child rest => Patch.keyed_step path model child rest index,
}

#[terminating]
def Patch.keyed_step (path : List I64) (model : List Html.Node) (child : Html.Node) (rest : List Html.Node) (index : I64) : List Patch :=
    Patch.keyed_step_opt path model child rest index (Patch.key_of child)

#[terminating]
def Patch.keyed_step_opt (path : List I64) (model : List Html.Node) (child : Html.Node) (rest : List Html.Node) (index : I64) (found : Option String) : List Patch := match found {
    Option.none => List.empty,
    Option.some key => Patch.keyed_continue path key model child rest index,
}

#[terminating]
def Patch.keyed_continue (path : List I64) (key : String) (model : List Html.Node) (child : Html.Node) (rest : List Html.Node) (index : I64) : List Patch :=
    let step : Pair (List Patch) (List Html.Node) :=
        Patch.keyed_match path key model child index (Patch.key_locate key model 0i64) in
    Patch.keyed_append path step rest index

def Patch.keyed_append (path : List I64) (step : Pair (List Patch) (List Html.Node)) (rest : List Html.Node) (index : I64) : List Patch :=
    match step {
        Pair.pair patches next_model =>
            List.append patches (Patch.keyed_walk path next_model rest (index + 1i64)),
    }

#[terminating]
def Patch.keyed_match (path : List I64) (key : String) (model : List Html.Node) (child : Html.Node) (target : I64) (found : Option (Pair I64 Html.Node)) : Pair (List Patch) (List Html.Node) := match found {
    Option.none =>
        Pair.pair
            (List.cons (Patch.insert (Patch.child_path path target) child) List.empty)
            (Patch.model_insert target child model),
    Option.some located => Patch.keyed_located path model child target located,
}

#[terminating]
def Patch.keyed_located (path : List I64) (model : List Html.Node) (child : Html.Node) (target : I64) (located : Pair I64 Html.Node) : Pair (List Patch) (List Html.Node) := match located {
    Pair.pair from old_node => Patch.keyed_move path model child old_node target from,
}

/// A matched key: `from == target` diffs in place; `from > target` moves the
/// node left first. `from < target` cannot happen -- keys are unique and the
/// prefix `0..target-1` already holds the new keys.
#[terminating]
def Patch.keyed_move (path : List I64) (model : List Html.Node) (child : Html.Node) (old_node : Html.Node) (target : I64) (from : I64) : Pair (List Patch) (List Html.Node) :=
    if from == target
    then Pair.pair
            (Patch.diff_at (Patch.child_path path target) old_node child)
            model
    else Pair.pair
            (List.cons
                (Patch.move (Patch.child_path path from) (Patch.child_path path target))
                (Patch.diff_at (Patch.child_path path target) old_node child))
            (Patch.model_move from target old_node model)

#[terminating]
def Patch.keyed_patches (path : List I64) (old_children : List Html.Node) (children : List Html.Node) : List Patch :=
    let rev : List Html.Node := List.reverse old_children in
    let last_index : I64 := List.length old_children - 1i64 in
    let removals : List Patch := Patch.keyed_removals path rev children last_index in
    let kept : List Html.Node := Patch.keyed_kept old_children children in
    List.append removals (Patch.keyed_walk path kept children 0i64)

// ─── Attributes ──────────────────────────────────────────────────────

def Patch.attr_name (a : Html.Attr) : String := match a {
    Html.Attr.attr name _value => name,
    Html.Attr.bool_attr name => name,
}

def Patch.attr_value (a : Html.Attr) : String := match a {
    Html.Attr.attr _name value => value,
    Html.Attr.bool_attr _name => "",
}

#[terminating]
def Patch.attr_patches (path : List I64) (old_attrs : List Html.Attr) (attrs : List Html.Attr) : List Patch :=
    List.append (Patch.attr_sets path old_attrs attrs) (Patch.attr_removes path old_attrs attrs)

#[terminating]
#[partial]
def Patch.attr_sets (path : List I64) (old_attrs : List Html.Attr) (attrs : List Html.Attr) : List Patch := match attrs {
    List.empty => List.empty,
    List.cons a rest =>
        let name := Patch.attr_name a in
        let value := Patch.attr_value a in
        if Patch.attr_has name value old_attrs
        then Patch.attr_sets path old_attrs rest
        else List.cons (Patch.set_attr path name value) (Patch.attr_sets path old_attrs rest),
}

#[terminating]
#[partial]
def Patch.attr_removes (path : List I64) (old_attrs : List Html.Attr) (attrs : List Html.Attr) : List Patch := match old_attrs {
    List.empty => List.empty,
    List.cons a rest =>
        let name := Patch.attr_name a in
        if Patch.attr_contains name attrs
        then Patch.attr_removes path rest attrs
        else List.cons (Patch.remove_attr path name) (Patch.attr_removes path rest attrs),
}

#[terminating]
#[partial]
def Patch.attr_has (name : String) (value : String) (attrs : List Html.Attr) : Bool := match attrs {
    List.empty => false,
    List.cons a rest =>
        if Bool.not (String.beq (Patch.attr_name a) name)
        then Patch.attr_has name value rest
        else String.beq (Patch.attr_value a) value,
}

#[terminating]
#[partial]
def Patch.attr_contains (name : String) (attrs : List Html.Attr) : Bool := match attrs {
    List.empty => false,
    List.cons a rest =>
        if String.beq (Patch.attr_name a) name then true else Patch.attr_contains name rest,
}

// ─── Applying ────────────────────────────────────────────────────────

/// Apply every patch. `root` is the mount container (what `Dom.root`
/// returned); paths resolve from it.
pub def Patch.apply (root : Node) (patches : List Patch) : IO Unit :=
    Patch.apply_each root patches

#[terminating]
def Patch.apply_each (root : Node) (patches : List Patch) : IO Unit := match patches {
    List.empty => IO.pure unit,
    List.cons p rest => do {
        let _ <- Patch.apply_one root p;
        Patch.apply_each root rest
    },
}

#[partial]
def Patch.apply_one (root : Node) (p : Patch) : IO Unit :=
    match p {
        Patch.replace path node => Patch.apply_replace root path node,
        Patch.set_text path text => Patch.apply_set_text root path text,
        Patch.set_attr path name value => Patch.apply_set_attr root path name value,
        Patch.remove_attr path name => Patch.apply_remove_attr root path name,
        Patch.insert path node => Patch.apply_insert root path node,
        Patch.remove path => Patch.apply_remove root path,
        Patch.move from to => Patch.apply_move root from to,
    }

def Patch.apply_insert (root : Node) (path : List I64) (node : Html.Node) : IO Unit := do {
    let parent <- Patch.resolve root (Patch.drop_last path);
    let fresh <- Patch.mount_node node;
    let anchor <- Dom.child parent (Patch.last_or_zero path);
    Dom.insert_before parent fresh anchor
}

def Patch.apply_remove (root : Node) (path : List I64) : IO Unit := do {
    let victim <- Patch.resolve root path;
    Dom.remove victim
}

/// Move the node at `from` to sit at `to`. Both endpoints are resolved
/// before the mutation, and they share a parent by construction (a keyed
/// child list): `insert_before` detaches and reinserts the node, which is
/// the splice the generator modelled.
def Patch.apply_move (root : Node) (from : List I64) (to : List I64) : IO Unit := do {
    let parent <- Patch.resolve root (Patch.drop_last from);
    let moved <- Dom.child parent (Patch.last_or_zero from);
    let anchor <- Dom.child parent (Patch.last_or_zero to);
    Dom.insert_before parent moved anchor
}

def Patch.apply_replace (root : Node) (path : List I64) (node : Html.Node) : IO Unit := do {
    let parent <- Patch.resolve root (Patch.drop_last path);
    let old <- Dom.child parent (Patch.last_or_zero path);
    let fresh <- Patch.mount_node node;
    let _ <- Dom.replace old fresh;
    return unit
}

def Patch.apply_set_text (root : Node) (path : List I64) (text : String) : IO Unit := do {
    let node <- Patch.resolve root path;
    let _ <- Dom.set_text node text;
    return unit
}

def Patch.apply_set_attr (root : Node) (path : List I64) (name : String) (value : String) : IO Unit := do {
    let node <- Patch.resolve root path;
    let _ <- Patch.set_attribute node name value;
    return unit
}

def Patch.apply_remove_attr (root : Node) (path : List I64) (name : String) : IO Unit := do {
    let node <- Patch.resolve root path;
    let _ <- Dom.remove_attr node name;
    return unit
}

#[terminating]
pub def Patch.resolve (root : Node) (path : List I64) : IO Node := match path {
    List.empty => IO.pure root,
    List.cons index rest => do {
        let child <- Dom.child root index;
        Patch.resolve child rest
    },
}

/// Everything but the last index.
#[terminating]
def Patch.drop_last (path : List I64) : List I64 :=
    List.reverse (List.tail (List.reverse path))

#[terminating]
def Patch.last_or_zero (path : List I64) : I64 := match path {
    List.empty => 0i64,
    List.cons index rest =>
        match rest {
            List.empty => index,
            List.cons _ _ => Patch.last_or_zero rest,
        },
}

// ─── Mounting ─────────────────────────────────────────────────────────

/// Empty a mount container. v1 hydration: a server-rendered page puts its
/// own content under the root, and the SPA replaces it wholesale rather
/// than adopting nodes (`data-oak` markers exist for the adopting version).
pub def Patch.clear (root : Node) : IO Unit := do {
    let count <- Dom.child_count root;
    Patch.clear_n root count
}

#[terminating]
def Patch.clear_n (root : Node) (remaining : I64) : IO Unit :=
    if I64.gt remaining 0i64
    then do {
        let child <- Dom.child root 0i64;
        let _ <- Dom.remove child;
        Patch.clear_n root (remaining - 1i64)
    }
    else IO.pure unit

/// Build the DOM for one rendered node.
#[partial]
pub def Patch.mount_node (node : Html.Node) : IO Node :=
    match node {
        Html.Node.node_element tag attrs children => Patch.mount_element tag attrs children,
        Html.Node.node_void tag attrs => Patch.mount_void tag attrs,
        Html.Node.node_text content => Dom.text_node content,
        Html.Node.node_raw_text tag attrs content => Patch.mount_raw tag attrs content,
        Html.Node.node_comment content => Dom.comment content,
        // A doctype has no place inside an element; a comment keeps the
        // path model intact and renders nothing.
        Html.Node.node_doctype declaration => Dom.comment (String.concat "DOCTYPE " declaration),
        Html.Node.node_fragment children => Patch.mount_fragment children,
    }

#[terminating]
#[partial]
def Patch.mount_element (tag : String) (attrs : List Html.Attr) (children : List Html.Node) : IO Node := do {
    let element <- Dom.create tag;
    let _ <- Patch.apply_attrs element attrs;
    let _ <- Patch.append_children element children;
    return element
}

def Patch.mount_void (tag : String) (attrs : List Html.Attr) : IO Node := do {
    let element <- Dom.create tag;
    let _ <- Patch.apply_attrs element attrs;
    return element
}

def Patch.mount_raw (tag : String) (attrs : List Html.Attr) (content : String) : IO Node := do {
    let element <- Dom.create tag;
    let _ <- Patch.apply_attrs element attrs;
    let _ <- Dom.set_text element content;
    return element
}

/// A fragment has no element of its own; v1 wraps it in a plain container so
/// every rendered tree maps onto exactly one DOM node and paths stay
/// positional. Hydration that ADOPTS server nodes is the follow-up.
#[terminating]
#[partial]
def Patch.mount_fragment (children : List Html.Node) : IO Node := do {
    let element <- Dom.create "div";
    let _ <- Dom.set_attr element "data-oak-fragment" "";
    let _ <- Patch.append_children element children;
    return element
}

#[terminating]
def Patch.append_children (parent : Node) (children : List Html.Node) : IO Unit := match children {
    List.empty => IO.pure unit,
    List.cons child rest => do {
        let node <- Patch.mount_node child;
        let _ <- Dom.append parent node;
        Patch.append_children parent rest
    },
}

#[terminating]
def Patch.apply_attrs (element : Node) (attrs : List Html.Attr) : IO Unit := match attrs {
    List.empty => IO.pure unit,
    List.cons a rest => do {
        let _ <- Patch.set_attribute element (Patch.attr_name a) (Patch.attr_value a);
        Patch.apply_attrs element rest
    },
}

/// Set one attribute. `data-oak-on-<event>` values are ordinary attributes
/// to Monad: `web_runtime.js`'s `dom_set_attr` sees the prefix and keeps the
/// DOM listener in step (replace on change, unregister on removal).
pub def Patch.set_attribute (element : Node) (name : String) (value : String) : IO Unit :=
    Dom.set_attr element name value
