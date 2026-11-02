/// The prompt: the multiline input box and its submit history. A
/// component -- `PromptModel`, `PromptMsg`, `Prompt.update`, `Prompt.view`.
/// Enter is the parent's (submitting depends on whether a turn runs); the
/// prompt owns editing, the up/down history walk, paste, and mouse
/// selection inside its own box.
use tui::types {Key}
use tui::widget {Widget, text_input, padding}
use tui::widgets::input {
    InputState, input_state, insert_text, handle_input_multiline_key,
    InputState.press, InputState.drag, InputState.finish_selection, InputState.clear_selection,
}

pub struct PromptModel {
    input : InputState,
    /// Submitted non-empty lines, most recent first.
    hist : List String,
    /// Where the history walk stands (-1 = live edit, not browsing).
    hist_idx : I64,
}

/// Where the box sits on screen: content rows/columns, for mouse hits.
pub struct PromptBox {
    top : I64,
    left : I64,
    width : I64,
    height : I64,
}

pub type PromptMsg {
    key (k : Key),
    paste (text : String),
    /// Mouse gestures in SCREEN cells; the box maps them.
    press (row : I64) (col : I64),
    drag (row : I64) (col : I64),
    release (row : I64) (col : I64),
}

pub def Prompt.placeholder : String := "type a message, or /help"

/// History is capped: an unbounded list was a per-process growth.
pub def Prompt.hist_cap : I64 := 200

pub def Prompt.empty : PromptModel :=
    let p : PromptModel := { input := input_state "" Prompt.placeholder, hist := List.empty, hist_idx := 0 - 1 } in
    p

pub def Prompt.text (p : PromptModel) : String := p.input.value

/// Replace the text (a plan revision's note, a recalled line).
pub def Prompt.set_text (p : PromptModel) (text : String) : PromptModel :=
    { p with input := input_state text Prompt.placeholder }

pub def Prompt.clear (p : PromptModel) : PromptModel := Prompt.set_text p ""

#[partial]
def take (n : I64) (xs : List String) : List String :=
    if n < 1 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (take (n - 1) rest),
    }

#[partial]
def count (xs : List String) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _ rest => 1 + count rest,
    }

#[partial]
def nth (xs : List String) (i : I64) : String :=
    match xs {
        List.empty => "",
        List.cons h rest => if i < 1 then h else nth rest (i - 1),
    }

/// A submitted line: the box clears, the line joins the history (deduped
/// against the newest entry) and the walk returns to the live edit.
pub def Prompt.submitted (p : PromptModel) (text : String) : PromptModel :=
    let pushed : List String :=
        match p.hist {
            List.cons h _ => if h == text then p.hist else List.cons text p.hist,
            List.empty => List.cons text List.empty,
        } in
    let cleared : PromptModel := Prompt.clear p in
    { cleared with hist := take Prompt.hist_cap pushed, hist_idx := 0 - 1 }

def browsing (p : PromptModel) : Bool := Bool.not (p.hist_idx < 0)

def show (p : PromptModel) (idx : I64) : PromptModel :=
    { p with hist_idx := idx, input := input_state (nth p.hist idx) Prompt.placeholder }

def edit (p : PromptModel) (k : Key) : PromptModel :=
    { p with input := handle_input_multiline_key k p.input }

/// Up recalls history from an EMPTY box or while a walk is open (a
/// recalled value is not empty); otherwise it is the multiline cursor's.
def up (p : PromptModel) : PromptModel :=
    if Bool.or (browsing p) (String.is_empty p.input.value)
    then
        let next : I64 := p.hist_idx + 1 in
        if next < count p.hist then show p next else p
    else edit p Key.up

/// Down walks younger while browsing; past the newest entry it returns to
/// an empty live edit.
def down (p : PromptModel) : PromptModel :=
    if browsing p
    then
        if p.hist_idx < 1
        then { (Prompt.clear p) with hist_idx := 0 - 1 }
        else show p (p.hist_idx - 1)
    else edit p Key.down

pub def Prompt.box_contains (b : PromptBox) (row : I64) (col : I64) : Bool :=
    Bool.and (Bool.not (row < b.top))
        (Bool.and (row < b.top + b.height)
            (Bool.and (Bool.not (col < b.left)) (col < b.left + b.width)))

pub def Prompt.selecting (p : PromptModel) : Bool :=
    match p.input.sel {
        Option.none => false,
        Option.some _ => true,
    }

pub def Prompt.clear_selection (p : PromptModel) : PromptModel :=
    { p with input := InputState.clear_selection p.input }

def dragged (b : PromptBox) (p : PromptModel) (row : I64) (col : I64) : PromptModel :=
    { p with input := InputState.drag p.input b.width b.height (row - b.top) (col - b.left) }

/// One message. The second half is text a finished drag selected (the
/// parent copies it; a pure update cannot write the clipboard).
pub def Prompt.update (b : PromptBox) (p : PromptModel) (msg : PromptMsg) : Pair PromptModel (Option String) :=
    match msg {
        PromptMsg.key k => match k {
            Key.up => Pair.pair (up p) Option.none,
            Key.down => Pair.pair (down p) Option.none,
            _ => Pair.pair (edit p k) Option.none,
        },
        PromptMsg.paste text => Pair.pair { p with input := insert_text text p.input } Option.none,
        PromptMsg.press row col =>
            Pair.pair { p with input := InputState.press p.input b.width b.height (row - b.top) (col - b.left) } Option.none,
        PromptMsg.drag row col => Pair.pair (dragged b p row col) Option.none,
        PromptMsg.release row col =>
            let d : PromptModel := dragged b p row col in
            match InputState.finish_selection d.input {
                Pair.pair input2 text => Pair.pair { d with input := input2 } text,
            },
    }

/// The box's content, inset one column on each side.
pub def Prompt.view (p : PromptModel) : Widget :=
    padding 1 0 1 0 (text_input p.input)
