/// Diff two rendered `Html.Node` trees into a patch list, and apply it to a
/// live DOM.
///
/// v1 scope, deliberately: attributes diff by name, children diff
/// positionally when the child COUNT is unchanged, and any other change
/// (different tag, different child count, text/raw-text content, a comment)
/// replaces that node. That is exact, cheap to reason about, and covers the
/// Elm-loop shapes; keyed list reordering is the follow-up in
/// `plans/library-ideas/oak.md`.
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
use web_wasm::types {Node}
use web_wasm::dom {
  Dom.append, Dom.child, Dom.child_count, Dom.comment, Dom.create, Dom.remove,
  Dom.remove_attr, Dom.replace, Dom.set_attr, Dom.set_text, Dom.text_node,
}

pub type Patch {
    replace (path : List I64) (node : Html.Node),
    set_text (path : List I64) (text : String),
    set_attr (path : List I64) (name : String) (value : String),
    remove_attr (path : List I64) (name : String)
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
    Patch.drop_last_go (List.reverse path) List.empty

#[terminating]
def Patch.drop_last_go (rev : List I64) (acc : List I64) : List I64 := match rev {
    List.empty => List.reverse acc,
    List.cons _index rest =>
        match rest {
            List.empty => List.reverse acc,
            List.cons index tail => Patch.drop_last_go tail (List.cons index acc),
        },
}

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
