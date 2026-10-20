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
use lib::text {Text.col_of_byte, Text.byte_at_col, Text.prev_boundary, Text.next_boundary}

/// A single-line text field's state. `cursor` is a BYTE offset into
/// `value` (`String.slice`/`String.drop` are byte-oriented), but every
/// movement and deletion snaps to a code-point boundary, so a multi-byte
/// character moves and deletes as one unit. No default fields: a struct
/// literal that omits one panics the checker today, so every literal names
/// all three (`SizedWidget`'s convention).
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
    { st with value := before ++ c ++ after, cursor := cur + String.length c }

/// Insert a whole string (a paste) at the cursor, advancing by its
/// length; CRLF/CR become `\n`, the input state's own newline spelling.
/// The cursor is snapped to a character boundary first: `String.slice`/
/// `String.drop` off a boundary return `""`, which would otherwise
/// replace the whole field with the pasted text.
pub def insert_text (text : String) (st : InputState) : InputState :=
    let t : String := normalize_newlines text in
    let cur := clamp_to_boundary st.value st.cursor in
    let before := String.slice st.value 0 cur in
    let after := String.drop cur st.value in
    { st with value := before ++ t ++ after, cursor := cur + String.length t }

#[terminating]
def boundary_below (s : String) (i : I64) : I64 :=
    if i < 1 then 0
    else if Bool.not (String.slice s i 1 == "") then i
    else boundary_below s (i - 1)

/// `i`, clamped to `[0, len]` and then walked back to a character
/// boundary (a mid-code-point slice reads as empty in both runtimes).
def clamp_to_boundary (s : String) (i : I64) : I64 :=
    let len : I64 := String.length s in
    let c : I64 := if i < 0 then 0 else if len < i then len else i in
    if c == len then c else boundary_below s c

/// CRLF -> LF, a lone CR -> LF. Byte-wise: the input state is
/// byte-offset based and v1 is ASCII.
#[terminating]
def norm_bytes (bs : List U8) (acc : List U8) : List U8 :=
    match bs {
        List.empty => List.reverse acc,
        List.cons b rest =>
            if U8.beq b 13u8
            then match rest {
                List.cons b2 r2 => if U8.beq b2 10u8 then norm_bytes r2 (List.cons 10u8 acc) else norm_bytes rest (List.cons 10u8 acc),
                List.empty => norm_bytes List.empty (List.cons 10u8 acc),
            }
            else norm_bytes rest (List.cons b acc),
    }

def normalize_newlines (s : String) : String :=
    if Bool.not (String.contains s "\r") then s
    else String.from_list (norm_bytes (String.to_list s) List.empty)

/// Delete the code point before the cursor. No-op at the start.
def input_backspace (st : InputState) : InputState :=
    let len := String.length st.value in
    let cur := clamp st.cursor 0 len in
    if cur < 1
    then st
    else
        let start : I64 := Text.prev_boundary st.value cur in
        let before := String.slice st.value 0 start in
        let after := String.drop cur st.value in
        { st with value := before ++ after, cursor := start }

/// Move the cursor one code point left (negative) or right.
def input_move (delta : I64) (st : InputState) : InputState :=
    let len := String.length st.value in
    let cur := clamp st.cursor 0 len in
    if delta < 0
    then { st with cursor := Text.prev_boundary st.value cur }
    else { st with cursor := Text.next_boundary st.value cur }

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

// ==================== multiline (Phase 11b, the input pass) ====================

/// A line's geometry: its byte START in the value and its own byte
/// LENGTH (without the newline). The multiline cursor maps a byte
/// offset onto these.
struct InputLine {
    start : I64,
    len : I64,
}

/// Hand-rolled (not `#[derive BEq]`), the file's own recorded reason.
pub def InputLine.beq (a b : InputLine) : Bool :=
    a.start == b.start && a.len == b.len

instance BEq InputLine {
    def beq (a b : InputLine) : Bool := InputLine.beq a b
}

/// The value's lines, split at newlines, each with its start offset. A
/// trailing newline produces a final empty line -- the cursor's
/// resting place after it.
#[terminating]
pub def input_lines (s : String) (start : I64) : List InputLine :=
    if Bool.not (start < String.length s)
    then List.cons ({ start := start, len := 0 } : InputLine) List.empty
    else
        match index_of_newline s start {
            Option.none => List.cons ({ start := start, len := String.length s - start } : InputLine) List.empty,
            Option.some at =>
                List.cons ({ start := start, len := at - start } : InputLine) (input_lines s (at + 1)),
        }

#[terminating]
def index_of_newline (s : String) (i : I64) : Option I64 :=
    if Bool.not (i < String.length s)
    then Option.none
    else if String.slice s i 1 == "\n"
    then Option.some i
    else index_of_newline s (i + 1)

/// Whether byte `i` of the value lies within line `l` (a cursor at a
/// line's end -- on the newline itself -- belongs to that line).
#[terminating]
def in_this_line (l : InputLine) (i : I64) : Bool := Bool.and (Bool.not (i < l.start)) (Bool.not (l.start + l.len < i))

/// The (index, line) the cursor byte sits on.
#[terminating]
pub def cursor_line (lines : List InputLine) (i : I64) (cur : I64) : Option (Pair I64 InputLine) :=
    match lines {
        List.empty => Option.none,
        List.cons l rest =>
            if in_this_line l cur
            then Option.some (Pair.pair i l)
            else cursor_line rest (i + 1) cur,
    }

/// The list's tail from index `i` (0-based), for InputLine lists.
#[terminating]
def nth_lines (xs : List InputLine) (i : I64) : List InputLine :=
    if i < 1
    then xs
    else match xs { List.empty => List.empty, List.cons _ rest => nth_lines rest (i - 1) }

/// `up`/`down`: move to the PREVIOUS/NEXT line, keeping the column
/// when it fits (clamped to the target line's length).
#[partial]
pub def input_line_move (delta : I64) (st : InputState) : InputState :=
    let lines : List InputLine := input_lines st.value 0 in
    match cursor_line lines 0 st.cursor {
        Option.none => st,
        Option.some found =>
            match found {
                Pair.pair idx l =>
                    let target : I64 := idx + delta in
                    if target < 0
                    then st
                    else match nth_lines lines target {
                        List.empty => st,
                        List.cons t _ =>
                            let here : String := String.slice st.value l.start l.len in
                            let there : String := String.slice st.value t.start t.len in
                            let col : I64 := Text.col_of_byte here (clamp (st.cursor - l.start) 0 l.len) in
                            { st with cursor := t.start + Text.byte_at_col there col },
                    },
            },
    }

/// The multiline key handler: `Alt+Enter` (`Key.alt "\n"` -- ICRNL
/// stays on in cbreak, so a terminal's Enter arrives as `\n`; a line
/// that does not convert gives `Key.alt "\r"`, accepted too; Ctrl+J IS
/// `\r`/`\n` on this wire, i.e. plain Enter) inserts a newline; `up`/`down` cross lines. Everything else
/// falls to the single-line handler, so a one-line value still has the
/// plain up/down no-op it always had (Weaver routes history through
/// its own `update_key` only when the input is empty, before this).
#[partial]
pub def handle_input_multiline_key (k : Key) (st : InputState) : InputState :=
    match k {
        Key.alt c =>
            if Bool.or (c == "\r") (c == "\n")
            then input_insert "\n" st
            else handle_input_key k st,
        Key.up => input_line_move (0 - 1) st,
        Key.down => input_line_move 1 st,
        _ => handle_input_key k st,
    }
