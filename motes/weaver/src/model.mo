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
use weaver::theme {theme_line_style, theme_status_style}
use tui::types {Event, LayoutSize}
use tui::widgets::input {InputState, input_state}
use tui::widget {Widget, SizedWidget, BorderStyle, border, label, text_input, sized, with_style, padding}

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
    /// Consecutive Ctrl+C presses since the last other event (the
    /// double-press exit; a pure update has no clock, so no timed
    /// window -- any other key or message resets the streak).
    ctrl_c_streak : I64 := 0,
    /// Lines above the pinned bottom; 0 = pinned to the latest output
    /// (Phase 11's scroll state machine).
    scroll : I64 := 0,
}

/// The initial model: an empty input box with a hint placeholder, no
/// transcript yet, and the terminal size `Tui.run` probed before the
/// first frame. New fields are spelled even though they default --
/// a struct literal whose new field is omitted has been seen to check
/// clean and fill GARBAGE at runtime (the two-host divergence note).
pub def init_tui_model (st : WeaverState) (rows : I64) (cols : I64) : TuiModel :=
    { state := st, input := input_state "" "type a message, or /help", transcript := List.empty, rows := rows, cols := cols, ctrl_c_streak := 0, scroll := 0 }

// ── view ─────────────────────────────────────────────────────────────────

/// Three rows: a bordered transcript panel (fills whatever is left), a
/// one-line status bar, and the input box. Named `Model.view`, not bare
/// `view` -- `init::optics` already owns that name for applying a
/// `Lens`, and a whole-program check loads both (a real collision,
/// caught by checking the whole corpus, not just this mote).
pub def Model.view (m : TuiModel) : Widget :=
    Widget.column [
        sized (LayoutSize.fill 1) (border BorderStyle.plain (padding 1 0 1 0 (transcript_column m))),
        sized (LayoutSize.fixed 1) (with_style (theme_status_style m.state.mode) (label (status_line m))),
        sized (LayoutSize.fixed 1) (text_input m.input),
    ]

/// The transcript panel's content: the window of lines that fit, one
/// `label` row each. `rows - 4` is the fill share's height (`rows`
/// minus the status and input's one row each) minus the border's own
/// top/bottom lines; clamped so a tiny or not-yet-known terminal never
/// asks for a negative slice. Scrolled up (scroll > 0), the panel's
/// first row shows the count indicator.
def transcript_column (m : TuiModel) : Widget :=
    Widget.column (List.map transcript_row (visible_transcript m))

/// One row, class-styled through the theme's palette (diff marks,
/// errors, running rows, the you: prefix).
def transcript_row (line : String) : SizedWidget :=
    sized (LayoutSize.fixed 1) (with_style (theme_line_style line) (label line))

/// The visible window: when pinned to the bottom (scroll = 0), the
/// last lines that fit; scrolled up, the block of lines that ends
/// `scroll` lines above the bottom, with the indicator row in front.
/// The scroll is clamped here too -- a shrink (`rows` collapsed) can
/// leave the state above the new top, and the view never lies.
pub def visible_transcript (m : TuiModel) : List String :=
    let eff : I64 := scroll_clamp m.scroll m.transcript (panel_height m) in
    if eff > 0
    then List.cons (scroll_indicator eff)
        (transcript_window m.transcript (panel_height m - 1) eff)
    else transcript_window m.transcript (panel_height m) eff

/// `N lines above -- PgDn for latest`: the row the scrolled-up panel
/// spends one of its rows on (the count is the scroll itself).
pub def scroll_indicator (n : I64) : String :=
    String.concat (I64.to_string n) " lines above -- PgDn for latest"

/// The lines that fit, ending `scroll` above the bottom: the last
/// `height + scroll` lines, minus their LAST scroll lines.
#[partial]
def transcript_window (all : List String) (height : I64) (scroll : I64) : List String :=
    drop_last_n scroll (take_last (height + scroll) all)

/// The FIRST `n` lines of the last-window slice (drop the last n).
#[partial]
def drop_last_n (n : I64) (xs : List String) : List String :=
    take_n (list_length xs - n) xs

#[partial]
def take_n (n : I64) (xs : List String) : List String :=
    if n < 1 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (take_n (n - 1) rest),
    }

/// The top scroll still allows: at most `len - height`, never less
/// than 0.
#[partial]
def scroll_clamp (scroll : I64) (all : List String) (height : I64) : I64 :=
    let len : I64 := list_length all in
    let headroom : I64 := len - height in
    let room : I64 := if headroom < 0 then 0 else headroom in
    if scroll > room then room
    else if scroll < 0 then 0
    else scroll

pub def panel_height (m : TuiModel) : I64 :=
    let h := m.rows - 4 in
    if h < 0 then 0 else h

/// The scroll state machine: `scroll` counts lines above the pinned
/// bottom. The delta moves the window (PageUp/Ctrl+U positive, i.e.
/// older; PageDown/Ctrl+D negative), clamped at both ends.
#[partial]
pub def Model.scroll_step (m : TuiModel) (delta : I64) : TuiModel :=
    { m with scroll := scroll_clamp (m.scroll + delta) m.transcript (panel_height m) }

/// A new block of transcript lines: the blank separator row in front
/// (Phase 11's spacing, skipped on an empty transcript), and a
/// scrolled view HELD in place -- the scroll grows by the block's own
/// size, so the visible lines do not slide (auto-pin only happens
/// when the user was already at the bottom, i.e. scroll = 0: it stays
/// 0 and the tail keeps riding).
#[partial]
pub def Model.append_block (m : TuiModel) (lines : List String) : TuiModel :=
    let gap : List String :=
        match m.transcript {
            List.empty => List.empty,
            _ => List.singleton "",
        } in
    let block : List String := List.append gap lines in
    { m with transcript := List.append m.transcript block,
             scroll := if m.scroll > 0 then m.scroll + list_length block else 0 }

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
pub def list_length (xs : List String) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _ rest => 1 + list_length rest,
    }

// ── status line ─────────────────────────────────────────────────────────

/// The TUI's status bar: the dumb-mode twin minus the trailing `"> "`
/// prompt (the input box itself is the prompt here).
pub def status_line (m : TuiModel) : String :=
    Dumb.status_fields m.state
