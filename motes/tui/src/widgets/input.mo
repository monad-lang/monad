// Terminal UI Library - Text input state (Phase 5)
//
// The pure state machine for a single-line text field: `InputState` plus
// `handle_input_key`. The widget half (`text_input`, in widget.mo beside
// `label`) renders this state through render.mo's `LeafWidget.text_input`
// arm. This file deliberately does not import widget.mo -- the state is
// pure data, and keeping it that way makes the widget.mo ->
// widgets/input.mo dependency one-directional.
//
// `BEq` is hand-rolled (not `#[derive BEq]`) for the same reason
// widget.mo's own types are: a derive in a file whose defs use dot
// access and struct literals trips the Rust host's meta-capture re-check
// (`cannot infer the type of { .. }`).

use lib::types { Key }
use lib::core { clamp }

/// A single-line text field's state. `cursor` is a BYTE offset into
/// `value`: `String.slice`/`String.drop` -- the only string primitives --
/// are byte-oriented, so a multi-byte code point moves the cursor by its
/// byte length and may slice mid-code-point at the field's edge. v1
/// assumes single-byte input, the normal case for a terminal sending
/// keypresses one at a time. No default fields: a struct literal that
/// omits one panics the checker today, so every literal names all three
/// (`SizedWidget`'s convention).
pub struct InputState {
    value : String,
    cursor : I64,
    placeholder : String
}

/// A field holding `value` with the cursor at its end, showing
/// `placeholder` when the value is empty.
pub def input_state (value : String) (placeholder : String) : InputState :=
    { value := value, cursor := String.length value, placeholder := placeholder }

def InputState.beq (a b : InputState) : Bool :=
    a.value == b.value && a.cursor == b.cursor && a.placeholder == b.placeholder

instance BEq InputState {
    def beq (a b : InputState) : Bool := InputState.beq a b
}

/// Insert `c` at the cursor and step the cursor past it.
def input_insert (c : String) (st : InputState) : InputState :=
    let len := String.length st.value in
    let cur := clamp st.cursor 0 len in
    let before := String.slice st.value 0 cur in
    let after := String.drop cur st.value in
    { st with value := before ++ c ++ after, cursor := cur + 1 }

/// Delete the byte before the cursor. No-op at the start of the value.
def input_backspace (st : InputState) : InputState :=
    let len := String.length st.value in
    let cur := clamp st.cursor 0 len in
    if cur < 1
    then st
    else
        let before := String.slice st.value 0 (cur - 1) in
        let after := String.drop cur st.value in
        { st with value := before ++ after, cursor := cur - 1 }

/// Move the cursor `delta` bytes, clamped to `[0, length value]`.
def input_move (delta : I64) (st : InputState) : InputState :=
    let len := String.length st.value in
    let cur := clamp st.cursor 0 len in
    { st with cursor := clamp (cur + delta) 0 len }

/// One keypress's worth of state transition. `char` inserts at the
/// cursor; `backspace` deletes before it; `left`/`right` move by one;
/// `home`/`end` jump to the ends. Every other key leaves the state
/// alone -- an input field never claims keys it does not interpret.
pub def handle_input_key (k : Key) (st : InputState) : InputState :=
    match k {
        Key.char c => input_insert c st,
        Key.backspace => input_backspace st,
        Key.left => input_move (0 - 1) st,
        Key.right => input_move 1 st,
        Key.home => { st with cursor := 0 },
        Key.end => { st with cursor := String.length st.value },
        _ => st
    }
