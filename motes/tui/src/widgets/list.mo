// Terminal UI Library - Selection list state (Phase 5)
//
// The pure state machine for a single-choice scrollable list: `ListState`
// plus `handle_list_key`. The widget half (`list`, in widget.mo) renders
// this state through render.mo's `LeafWidget.list` arm. Like
// widgets/input.mo, this file does not import widget.mo -- the state is
// pure data, keeping the widget.mo -> widgets/list.mo dependency
// one-directional. `BEq` is hand-rolled for the same meta-capture reason
// input.mo's header records, and `items` is compared by hand because
// generic `BEq (List A)` dispatch through a custom element type's
// instance is the unreliable path this mote avoids throughout.

use lib::types { Key }
use lib::core { clamp }
use std::list { List.length }

/// A single-choice list's state: the full item list, the selected index,
/// and `offset` -- the index of the first visible row. `offset` is
/// bookkeeping the renderer trusts: `handle_list_key` keeps both it and
/// `selected` inside `[0, length items)`. No default fields (a literal
/// that omits one panics the checker today); `list_state` is the builder.
pub struct ListState {
    items : List String,
    selected : I64,
    offset : I64
}

/// A list over `items` with the first item selected, window at the top.
pub def list_state (items : List String) : ListState :=
    { items := items, selected := 0, offset := 0 }

def string_list_beq (a b : List String) : Bool :=
    match a {
        empty => match b { empty => true, _ => false },
        cons ha ta => match b {
            cons hb tb => ha == hb && string_list_beq ta tb,
            _ => false
        }
    }

def ListState.beq (a b : ListState) : Bool :=
    string_list_beq a.items b.items && a.selected == b.selected && a.offset == b.offset

instance BEq ListState {
    def beq (a b : ListState) : Bool := ListState.beq a b
}

/// Move the selection to `target` (already clamped), scrolling `offset`
/// the minimum needed to keep the selection inside a `height`-row window.
def list_scroll_to (target : I64) (height : I64) (st : ListState) : ListState :=
    let offset :=
        if target < st.offset
        then target
        // `>=` has no infix entry in the host lowering pass -- the negated
        // `<` is this mote's spelling (see core.mo's bounds checks).
        else if Bool.not (target < st.offset + height)
        then target - height + 1
        else st.offset in
    { st with selected := target, offset := offset }

/// Move the selection by `delta`, clamped to the list, keeping it visible
/// in the `height`-row window. No-op on an empty list.
def list_select (delta : I64) (height : I64) (st : ListState) : ListState :=
    let count := List.length st.items in
    if count < 1
    then st
    else list_scroll_to (clamp (st.selected + delta) 0 (count - 1)) height st

/// One keypress's worth of state transition. `up`/`down` move by one,
/// `page_up`/`page_down` by a window, `home`/`end` jump to the ends;
/// every other key leaves the state alone. `height` is the viewport's
/// row count -- it lives with the caller (the widget tree sizes the
/// window), not in the state, so one state serves any layout.
pub def handle_list_key (height : I64) (k : Key) (st : ListState) : ListState :=
    match k {
        Key.up => list_select (0 - 1) height st,
        Key.down => list_select 1 height st,
        Key.page_up => list_select (0 - height) height st,
        Key.page_down => list_select height height st,
        Key.home => list_scroll_to 0 height st,
        Key.end =>
            let count := List.length st.items in
            if count < 1
            then st
            else list_scroll_to (count - 1) height st,
        _ => st
    }
