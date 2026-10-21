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
use std::list { List.intercalate }
use lib::text {
    Text.col_of_byte, Text.byte_at_col, Text.prev_boundary, Text.next_boundary,
    Text.width, Text.drop_cols, Text.take_width, Text.slice_cols, Text.snap_span,
}

/// A mouse selection over the input's LOGICAL lines (0-based) and DISPLAY
/// columns within the full line. Display coordinates mean rendering and
/// hit-testing share one geometry; edits clear the selection, so the
/// coordinates cannot go stale.
pub struct InputSel {
    anchor_line : I64,
    anchor_col : I64,
    focus_line : I64,
    focus_col : I64,
    moved : Bool
}

/// A single-line text field's state. `cursor` is a BYTE offset into
/// `value` (`String.slice`/`String.drop` are byte-oriented), but every
/// movement and deletion snaps to a code-point boundary, so a multi-byte
/// character moves and deletes as one unit. No default fields: a struct
/// literal that omits one panics the checker today, so every literal names
/// all four (`SizedWidget`'s convention).
pub struct InputState {
    value : String,
    cursor : I64,
    placeholder : String,
    /// The transient mouse selection; never part of value equality.
    sel : Option InputSel
}

/// A field holding `value` with the cursor at its end, showing
/// `placeholder` when the value is empty.
pub def input_state (value : String) (placeholder : String) : InputState :=
    { value := value, cursor := String.length value, placeholder := placeholder, sel := Option.none }

def InputState.beq (a b : InputState) : Bool :=
    a.value == b.value && a.cursor == b.cursor && a.placeholder == b.placeholder

instance BEq InputState {
    def beq (a b : InputState) : Bool := InputState.beq a b
}

/// Insert `c` at the cursor and step the cursor past it. An active
/// selection is replaced by the insertion.
def input_insert (c : String) (st : InputState) : InputState :=
    let s0 : InputState := InputState.drop_selection st in
    let len := String.length s0.value in
    let cur := clamp s0.cursor 0 len in
    let before := String.slice s0.value 0 cur in
    let after := String.drop cur s0.value in
    { s0 with value := before ++ c ++ after, cursor := cur + String.length c, sel := Option.none }

/// Insert a whole string (a paste) at the cursor, advancing by its
/// length; CRLF/CR become `\n`, the input state's own newline spelling.
/// The cursor is snapped to a character boundary first: `String.slice`/
/// `String.drop` off a boundary return `""`, which would otherwise
/// replace the whole field with the pasted text.
pub def insert_text (text : String) (st : InputState) : InputState :=
    let s0 : InputState := InputState.drop_selection st in
    let t : String := normalize_newlines text in
    let cur := clamp_to_boundary s0.value s0.cursor in
    let before := String.slice s0.value 0 cur in
    let after := String.drop cur s0.value in
    { s0 with value := before ++ t ++ after, cursor := cur + String.length t, sel := Option.none }

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

/// Delete the selection when there is one, otherwise the code point before
/// the cursor. No-op at the start.
def input_backspace (st : InputState) : InputState :=
    match selection_byte_range st {
        Option.some _ => InputState.drop_selection st,
        Option.none =>
            let len := String.length st.value in
            let cur := clamp st.cursor 0 len in
            if cur < 1
            then { st with sel := Option.none }
            else
                let start : I64 := Text.prev_boundary st.value cur in
                let before := String.slice st.value 0 start in
                let after := String.drop cur st.value in
                { st with value := before ++ after, cursor := start, sel := Option.none },
    }

/// Move the cursor one code point left (negative) or right; movement
/// clears the selection.
def input_move (delta : I64) (st : InputState) : InputState :=
    let s0 : InputState := InputState.clear_selection st in
    let len := String.length s0.value in
    let cur := clamp s0.cursor 0 len in
    if delta < 0
    then { s0 with cursor := Text.prev_boundary s0.value cur }
    else { s0 with cursor := Text.next_boundary s0.value cur }

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
        Key.home => { st with cursor := 0, sel := Option.none },
        Key.end => { st with cursor := String.length st.value, sel := Option.none },
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
                            { st with cursor := t.start + Text.byte_at_col there col, sel := Option.none },
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

// ==================== mouse selection ====================

pub def InputState.clear_selection (st : InputState) : InputState :=
    { st with sel := Option.none }

/// Whether the anchor and focus name different cells (a press without a
/// drag is not a selection).
pub def InputState.selection_active (st : InputState) : Bool :=
    match st.sel {
        Option.none => false,
        Option.some s =>
            Bool.or (Bool.not (s.anchor_line == s.focus_line))
                (Bool.not (s.anchor_col == s.focus_col)),
    }

/// The selection normalized to reading order: (top, bottom) positions.
def input_sel_span (s : InputSel) : Pair (Pair I64 I64) (Pair I64 I64) :=
    let forward : Bool := Bool.or (s.anchor_line < s.focus_line)
        (Bool.and (s.anchor_line == s.focus_line) (Bool.not (s.focus_col < s.anchor_col))) in
    let a : Pair I64 I64 := Pair.pair s.anchor_line s.anchor_col in
    let f : Pair I64 I64 := Pair.pair s.focus_line s.focus_col in
    if forward then Pair.pair a f else Pair.pair f a

#[terminating]
def line_count (ls : List InputLine) : I64 :=
    match ls {
        List.empty => 0,
        List.cons _ rest => 1 + line_count rest,
    }

/// The byte offset at `(line, display column)`, clamped to the line.
def byte_of_pos (lines : List InputLine) (value : String) (li : I64) (col : I64) : Option I64 :=
    match nth_lines lines li {
        List.empty => Option.none,
        List.cons l _ =>
            let text : String := String.slice value l.start l.len in
            Option.some (l.start + Text.byte_at_col text (clamp col 0 (Text.width text))),
    }

/// The byte range of the selection, or none for a click with no movement.
def selection_byte_range (st : InputState) : Option (Pair I64 I64) :=
    match st.sel {
        Option.none => Option.none,
        Option.some s =>
            if Bool.not (InputState.selection_active st)
            then Option.none
            else
                let lines : List InputLine := input_lines st.value 0 in
                match input_sel_span s {
                    Pair.pair top bottom =>
                        match top {
                            Pair.pair tl tc => match bottom {
                                Pair.pair bl bc =>
                                    match byte_of_pos lines st.value tl tc {
                                        Option.none => Option.none,
                                        Option.some a =>
                                            // The focus cell is INCLUSIVE in the
                                            // highlight; the byte range's end is
                                            // the next column (clamped to the line).
                                            match byte_of_pos lines st.value bl (bc + 1) {
                                                Option.none => Option.none,
                                                Option.some b => Option.some (Pair.pair a b),
                                            },
                                    },
                            },
                        },
                },
    }

/// Delete the selected text and put the caret at its start.
pub def InputState.drop_selection (st : InputState) : InputState :=
    match selection_byte_range st {
        Option.none => { st with sel := Option.none },
        Option.some pr => match pr {
            Pair.pair a b =>
                let before : String := String.slice st.value 0 a in
                let after : String := String.drop b st.value in
                { st with value := before ++ after, cursor := a, sel := Option.none },
        },
    }

/// The horizontal window one input line shows: `(visible text, dropped
/// display columns)`. The SINGLE rule render.mo and the hit-test share, so
/// a click on the visible tail of a long line lands on the right cell.
pub def input_line_window (text : String) (caret_byte : I64) (width : I64) : Pair String I64 :=
    let w : I64 := if width < 1 then 1 else width in
    let cur_col : I64 := Text.col_of_byte text caret_byte in
    let win_col : I64 := if cur_col < w then 0 else cur_col - w + 1 in
    match Text.drop_cols text win_col {
        Pair.pair rest start => Pair.pair (Text.take_width rest w) start,
    }

def window_dropped (text : String) (caret_byte : I64) (width : I64) : I64 :=
    match input_line_window text caret_byte width {
        Pair.pair _ d => d,
    }

/// The logical line and full-line display column under a content-relative
/// `(row, col)`. Rows past the visible line window clamp to its edge.
pub def InputState.hit (st : InputState) (width : I64) (height : I64) (row : I64) (col : I64) : Pair I64 I64 :=
    let lines : List InputLine := input_lines st.value 0 in
    let h : I64 := if height < 1 then 1 else height in
    match cursor_line lines 0 (clamp st.cursor 0 (String.length st.value)) {
        Option.none => Pair.pair 0 0,
        Option.some found => match found {
            Pair.pair cidx _ =>
                let first : I64 := if cidx - (h - 1) < 0 then 0 else cidx - (h - 1) in
                let n : I64 := line_count lines in
                let li : I64 := clamp (first + row) 0 (if n < 1 then 0 else n - 1) in
                match nth_lines lines li {
                    List.empty => Pair.pair li 0,
                    List.cons l _ =>
                        let text : String := String.slice st.value l.start l.len in
                        let dropped : I64 :=
                            if li == cidx
                            then window_dropped text (clamp (st.cursor - l.start) 0 l.len) width
                            else 0 in
                        Pair.pair li (clamp (col + dropped) 0 (Text.width text)),
                },
        },
    }

/// A left press: put the caret at the hit and anchor a selection there.
pub def InputState.press (st : InputState) (width : I64) (height : I64) (row : I64) (col : I64) : InputState :=
    match InputState.hit st width height row col {
        Pair.pair li c =>
            let lines : List InputLine := input_lines st.value 0 in
            match byte_of_pos lines st.value li c {
                Option.none => st,
                Option.some byte =>
                    let sel : InputSel := { anchor_line := li, anchor_col := c, focus_line := li, focus_col := c, moved := false } in
                    { st with cursor := byte, sel := Option.some sel },
            },
    }

/// A drag: extend the anchor to the hit and move the caret with it.
pub def InputState.drag (st : InputState) (width : I64) (height : I64) (row : I64) (col : I64) : InputState :=
    match st.sel {
        Option.none => st,
        Option.some s =>
            match InputState.hit st width height row col {
                Pair.pair li c =>
                    let lines : List InputLine := input_lines st.value 0 in
                    match byte_of_pos lines st.value li c {
                        Option.none => st,
                        Option.some byte =>
                            let moved : Bool := Bool.or s.moved
                                (Bool.or (Bool.not (li == s.anchor_line)) (Bool.not (c == s.anchor_col))) in
                            let s2 : InputSel := { s with focus_line := li, focus_col := c, moved := moved } in
                            { st with cursor := byte, sel := Option.some s2 },
                    },
            },
    }

/// The half-open display-column span to highlight on `line_idx`.
pub def InputState.selection_cols (st : InputState) (line_idx : I64) (line_text : String) : Option (Pair I64 I64) :=
    match st.sel {
        Option.none => Option.none,
        Option.some s =>
            if Bool.not (InputState.selection_active st)
            then Option.none
            else
                let width : I64 := Text.width line_text in
                match input_sel_span s {
                    Pair.pair top bottom =>
                        match top {
                            Pair.pair tl tc => match bottom {
                                Pair.pair bl bc =>
                                    if Bool.or (line_idx < tl) (bl < line_idx)
                                    then Option.none
                                    else
                                        let a : I64 := if line_idx == tl then tc else 0 in
                                        let b : I64 := if line_idx == bl then bc + 1 else width in
                                        Option.some (Text.snap_span line_text a b),
                            },
                        },
                },
    }

#[terminating]
def selection_text_go (st : InputState) (lines : List InputLine) (idx : I64)
        (top : I64) (bottom : I64) (acc : List String) : List String :=
    match lines {
        List.empty => List.reverse acc,
        List.cons l rest =>
            if bottom < idx
            then List.reverse acc
            else
                let text : String := String.slice st.value l.start l.len in
                let piece : String :=
                    if idx < top
                    then ""
                    else match InputState.selection_cols st idx text {
                        Option.none => "",
                        Option.some pr => match pr {
                            Pair.pair a b => Text.slice_cols text a b,
                        },
                    } in
                selection_text_go st rest (idx + 1) top bottom
                    (if idx < top then acc else List.cons piece acc),
    }

/// The selected text: lines joined with `\n`, exact (no trailing-space
/// trim). None for a click or an empty span.
pub def InputState.selection_text (st : InputState) : Option String :=
    match st.sel {
        Option.none => Option.none,
        Option.some s =>
            if Bool.not (InputState.selection_active st)
            then Option.none
            else
                match input_sel_span s {
                    Pair.pair top bottom =>
                        match top {
                            Pair.pair tl _ => match bottom {
                                Pair.pair bl _ =>
                                    let pieces : List String :=
                                        selection_text_go st (input_lines st.value 0) 0 tl bl List.empty in
                                    let joined : String := List.intercalate "\n" pieces in
                                    if String.is_empty joined then Option.none else Option.some joined,
                            },
                        },
                },
    }

/// Drop the selection and return its text (the copy is the caller's).
pub def InputState.finish_selection (st : InputState) : Pair InputState (Option String) :=
    let text : Option String := InputState.selection_text st in
    Pair.pair { st with sel := Option.none } text
