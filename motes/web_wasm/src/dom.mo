/// DOM operations. Thin `IO` wrappers over the `RawIO` externs; the node
/// table lives on the JS side, so a `Node` here is just its id.

use lib::types {Node}
use lib::ffi {
  dom_create_raw, dom_create_text_raw, dom_create_comment_raw, dom_root_raw, dom_append_raw,
  dom_insert_before_raw, dom_remove_raw, dom_replace_raw, dom_set_attr_raw,
  dom_remove_attr_raw, dom_set_text_raw, dom_add_listener_raw, dom_child_raw,
  dom_child_count_raw, dom_node_type_raw, dom_tag_name_raw, dom_value_raw, dom_query_raw,
}

pub def Dom.create (tag : String) : IO Node := IO.mk (dom_create_raw tag)

pub def Dom.text_node (text : String) : IO Node := IO.mk (dom_create_text_raw text)

/// A comment node -- what an `Html.Node.node_comment` mounts as (a text
/// node would render its `<!--...-->` markup to the user).
pub def Dom.comment (text : String) : IO Node := IO.mk (dom_create_comment_raw text)

pub def Dom.root : IO Node := IO.mk dom_root_raw

pub def Dom.append (parent : Node) (child : Node) : IO Unit := IO.mk (dom_append_raw parent child)

pub def Dom.insert_before (parent : Node) (child : Node) (before : Node) : IO Unit :=
  IO.mk (dom_insert_before_raw parent child before)

pub def Dom.remove (node : Node) : IO Unit := IO.mk (dom_remove_raw node)

pub def Dom.replace (old : Node) (new_ : Node) : IO Unit := IO.mk (dom_replace_raw old new_)

pub def Dom.set_attr (n : Node) (key : String) (value : String) : IO Unit :=
  IO.mk (dom_set_attr_raw n key value)

pub def Dom.remove_attr (n : Node) (key : String) : IO Unit := IO.mk (dom_remove_attr_raw n key)

pub def Dom.set_text (n : Node) (text : String) : IO Unit := IO.mk (dom_set_text_raw n text)

/// Register `handler_id` for `event`; the JS side calls the exported
/// `oak_dispatch_event(handler_id)` when it fires.
pub def Dom.on (n : Node) (event : String) (handler_id : I64) : IO Unit :=
  IO.mk (dom_add_listener_raw n event handler_id)

/// The indexed child of `n` (text nodes included, matching `childNodes`).
/// Returns a null handle (`0`) when the index is out of range; patch
/// application never asks for one, so the caller can treat it as a bug.
pub def Dom.child (n : Node) (index : I64) : IO Node := IO.mk (dom_child_raw n index)

/// How many children `n` has, text nodes included -- what clearing a mount
/// container needs (a null handle is not comparable in Monad).
pub def Dom.child_count (n : Node) : IO I64 := IO.mk (dom_child_count_raw n)

// ─── Read-only introspection ─────────────────────────────────────────
//
// `Node` is opaque, so these are the only way to ask what a handle points
// at. A null handle (`Dom.child` past the end, `Dom.query` with no match)
// reads `node_type = 0` and an empty `tag_name`.

/// The DOM `nodeType`: 1 element, 3 text, 8 comment, 10 doctype fragment;
/// 0 for the null handle.
pub def Dom.node_type (n : Node) : IO I64 := IO.mk (dom_node_type_raw n)

/// The element's tag name, LOWERCASE (the host folds the case). Empty for
/// non-element nodes and the null handle.
pub def Dom.tag_name (n : Node) : IO String := IO.mk (dom_tag_name_raw n)

/// The live form value (`input.value`, `textarea.value`, `select.value`),
/// empty when the node has none. This reads the property, not the `value`
/// attribute, so it sees what the user typed.
pub def Dom.value (n : Node) : IO String := IO.mk (dom_value_raw n)

/// The first element matching `selector` (`#id` or a tag name), or the null
/// handle. An SPA handler only carries a message id, so this is how it
/// addresses a node it did not create in this turn.
pub def Dom.query (selector : String) : IO Node := IO.mk (dom_query_raw selector)
