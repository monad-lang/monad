/// Weaver's TUI model -- weaver.md Phase 4: the Elm `Model`/`view` half
/// over `tui`'s generalized `App`/`Cmd` (see `tui_app.mo`'s header for
/// why `update` itself lives there instead of here). `WeaverMsg` is the
/// message type the loop folds: a lifted terminal `Event`, or the
/// result of a turn/command that ran through `Cmd.perform`.
///
/// `TuiModel` carries its own `rows`/`cols` (kept in step by `Event.resize`
/// in `tui_app.mo`'s `update`) because `view : TuiModel -> Widget` has no
/// other way to know how many transcript lines fit -- the widget tree
/// does not auto-clip oversized content, and `List`'s own
/// `ListState.offset` bookkeeping is the wrong tool here (it drives a
/// single-selection menu's highlight, not a scrolling transcript).
use shuttle::agent {RunState}
use weaver::commands {WeaverState, Effect}
use weaver::dumb {Dumb.status_fields}
use tui::types {Event, LayoutSize}
use tui::widgets::input {InputState, input_state}
use tui::widget {Widget, SizedWidget, BorderStyle, border, label, text_input, sized}

/// The loop's message type: a raw terminal event not yet interpreted, or
/// the folded-back result of a `Cmd.perform`'d turn or slash command.
pub type WeaverMsg {
    key_event (e : Event),
    turn_result (run : RunState) (lines : List String),
    command_result (effect : Effect),
}

/// `tui::App`'s `on_event : Event -> WeaverMsg` -- every raw event is a
/// `key_event` until `update` decides otherwise; `turn_result`/
/// `command_result` only ever arrive via `Cmd.perform`, never from the
/// terminal.
pub def on_event (e : Event) : WeaverMsg :=
    WeaverMsg.key_event e

pub struct TuiModel {
    state : WeaverState,
    input : InputState,
    transcript : List String,
    rows : I64,
    cols : I64,
}

/// The initial model: an empty input box with a hint placeholder, no
/// transcript yet, and the terminal size `Tui.run` probed before the
/// first frame.
pub def init_tui_model (st : WeaverState) (rows : I64) (cols : I64) : TuiModel :=
    { state := st, input := input_state "" "type a message, or /help", transcript := List.empty, rows := rows, cols := cols }

// ── view ─────────────────────────────────────────────────────────────────

/// Three rows: a bordered transcript panel (fills whatever is left), a
/// one-line status bar, and the input box. Named `Model.view`, not bare
/// `view` -- `init::optics` already owns that name for applying a
/// `Lens`, and a whole-program check loads both (a real collision,
/// caught by checking the whole corpus, not just this mote).
pub def Model.view (m : TuiModel) : Widget :=
    Widget.column [
        sized (LayoutSize.fill 1) (border BorderStyle.plain (transcript_column m)),
        sized (LayoutSize.fixed 1) (label (status_line m)),
        sized (LayoutSize.fixed 1) (text_input m.input),
    ]

/// The transcript panel's content: the last lines that fit, one `label`
/// row each. `rows - 4` is the fill share's height (`rows` minus the
/// status and input's one row each) minus the border's own top/bottom
/// lines; clamped so a tiny or not-yet-known terminal never asks for a
/// negative slice.
def transcript_column (m : TuiModel) : Widget :=
    Widget.column (List.map transcript_row (visible_transcript m))

def transcript_row (line : String) : SizedWidget :=
    sized (LayoutSize.fixed 1) (label line)

def visible_transcript (m : TuiModel) : List String :=
    take_last (panel_height m) m.transcript

def panel_height (m : TuiModel) : I64 :=
    let h := m.rows - 4 in
    if h < 0 then 0 else h

/// The last `n` elements of `xs`, in their original order. `#[partial]`:
/// every clause terminates on `xs`, but the checker's totality pass
/// does not see `length` as a measure here -- the same shape
/// `diff.mo`'s `take_lines`/`drop_lines` already use.
#[partial]
def take_last (n : I64) (xs : List String) : List String :=
    drop_n (list_length xs - n) xs

#[partial]
def drop_n (n : I64) (xs : List String) : List String :=
    if n < 1 then xs
    else match xs {
        List.empty => xs,
        List.cons _ rest => drop_n (n - 1) rest,
    }

#[partial]
def list_length (xs : List String) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _ rest => 1 + list_length rest,
    }

// ── status line ─────────────────────────────────────────────────────────

/// The TUI's status bar: the dumb-mode twin minus the trailing `"> "`
/// prompt (the input box itself is the prompt here).
pub def status_line (m : TuiModel) : String :=
    Dumb.status_fields m.state
