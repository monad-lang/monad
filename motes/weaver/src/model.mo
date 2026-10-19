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
use shuttle::message {Message}
use weaver::commands {WeaverState, Effect}
use weaver::error {WeaverError}
use weaver::dumb {Dumb.status_fields}
use weaver::theme {theme_line_style, theme_status_style, theme_border_style}
use weaver::store {
    Transcript, TranscriptPage, Store.page_lines,
    Transcript.empty, Transcript.next_block, Transcript.append, Transcript.slice,
}
use tui::types {Event, LayoutSize}
use tui::widgets::input {InputState, input_state}
use tui::widget {Widget, SizedWidget, BorderStyle, border, label, text_input, sized, with_style, padding}

/// The loop's message type: a raw terminal event not yet interpreted, or
/// the folded-back result of a `Cmd.perform`'d turn or slash command.
/// The `*_failed` variants carry the failure CLASS, so the update can
/// apply the one recoverable/fatal classification (dumb mode's
/// `failed_step` contract: fatal ends the run, recoverable leaves the
/// session intact) -- the earlier shape folded every error into a plain
/// transcript line and both the state's fatal slot and the
/// classification were lost (a TUI session never exited nonzero).
pub type WeaverMsg {
    key_event (e : Event),
    /// `delta` is the turn's FULL history delta (the user message
    /// included); `lines` is the rendered display block.
    turn_result (run : RunState) (lines : List String) (delta : List Message),
    turn_failed (run : RunState) (e : WeaverError),
    command_result (effect : Effect),
    command_failed (e : WeaverError),
    /// A page of older transcript lines came back from disk.
    page_loaded (page : TranscriptPage),
    page_failed (e : String),
    /// `/clear` or `/resume` switched sessions.
    transcript_reset (t : Transcript),
    /// A store write reported a problem (none = success).
    store_result (e : Option String),
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
    /// The bounded window into the session's transcript: the last
    /// `Store.tail_lines` lines plus at most one older page read from disk.
    transcript : Transcript,
    rows : I64,
    cols : I64,
    /// Consecutive Ctrl+C presses since the last other event (the
    /// double-press exit; a pure update has no clock, so no timed
    /// window -- any other key or message resets the streak).
    ctrl_c_streak : I64 := 0,
    /// Lines above the pinned bottom; 0 = pinned to the latest output
    /// (Phase 11's scroll state machine).
    scroll : I64 := 0,
    /// Submitted non-empty lines, most recent first (the up-arrow
    /// history; ArrowUp recalls only from an empty input).
    hist : List String := List.empty,
    /// Where the history walk stands (-1 = live edit, not browsing).
    hist_idx : I64 := 0 - 1,
    /// A turn is running on its own fiber (`Cmd.perform_async`): the
    /// spinner shows and the status row carries its glyph. Keys typed
    /// meanwhile buffer in the tty and drain when the turn completes --
    /// tui.mo's header carries the whole reason.
    turn_pending : Bool := false,
    /// The spinner's tick counter (bumped only while `turn_pending`, so
    /// idle ticks are zero-diff draws).
    spinner_frame : I64 := 0,
    /// A page read is in flight; only the synchronous `Cmd.perform`
    /// pager sets it, so it clears in the same fold.
    page_pending : Bool := false,
}

/// The initial model: an empty input box with a hint placeholder, no
/// transcript yet, and the terminal size `Tui.run` probed before the
/// first frame. New fields are spelled even though they default --
/// a struct literal whose new field is omitted has been seen to check
/// clean and fill GARBAGE at runtime (the two-host divergence note).
pub def init_tui_model (st : WeaverState) (rows : I64) (cols : I64) : TuiModel :=
    init_tui_model_with st rows cols Transcript.empty

/// The startup tail loaded from the session store.
pub def init_tui_model_with (st : WeaverState) (rows : I64) (cols : I64) (tr : Transcript) : TuiModel :=
    { state := st, input := input_state "" input_placeholder, transcript := tr, rows := rows, cols := cols, ctrl_c_streak := 0, scroll := 0, hist := List.empty, hist_idx := 0 - 1, turn_pending := false, spinner_frame := 0, page_pending := false }

/// The input box's placeholder, shared by the live edit and a history
/// walk's return-to-live.
pub def input_placeholder : String := "type a message, or /help" 

// ── view ─────────────────────────────────────────────────────────────────

/// Three rows: a bordered transcript panel (fills whatever is left), a
/// one-line status bar, and the input box. Named `Model.view`, not bare
/// `view` -- `init::optics` already owns that name for applying a
/// `Lens`, and a whole-program check loads both (a real collision,
/// caught by checking the whole corpus, not just this mote).
pub def Model.view (m : TuiModel) : Widget :=
    Widget.column [
        sized (LayoutSize.fill 1) (with_style theme_border_style (border BorderStyle.rounded (padding 1 0 1 0 (transcript_column m)))),
        sized (LayoutSize.fixed 1) (with_style (theme_status_style m.state.mode) (label (status_line m))),
        sized (LayoutSize.fixed 3) (padding 1 0 1 0 (text_input m.input)),
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

/// The absolute window the panel shows. `eff` is the clamped scroll; the
/// scrolled panel spends ONE row on the indicator, so the content window
/// is `panel_height - 1` rows ending `eff` lines above the bottom.
pub struct Window {
    start : I64,
    count : I64,
    eff : I64,
}

pub def Model.window (m : TuiModel) : Window :=
    let total : I64 := m.transcript.total in
    let eff : I64 := scroll_clamp m.scroll total (panel_height m) in
    let h : I64 := if eff > 0 then panel_height m - 1 else panel_height m in
    let endp : I64 := total - eff in
    let start : I64 := if endp - h < 0 then 0 else endp - h in
    let count : I64 := if endp - start < 0 then 0 else endp - start in
    let w : Window := { start := start, count := count, eff := eff } in
    w

/// `visible_transcript`'s absolute range still needs a page: its start
/// is above the loaded tail and no loaded page covers the pre-tail part.
pub def Model.needs_page (m : TuiModel) (w : Window) : Bool :=
    let ts : I64 := m.transcript.tail_start in
    if Bool.not (w.start < ts) then false
    else Bool.not (covered_by_page m w)

def covered_by_page (m : TuiModel) (w : Window) : Bool :=
    let ts : I64 := m.transcript.tail_start in
    let upto : I64 := if w.start + w.count < ts then w.start + w.count else ts in
    match m.transcript.page {
        Option.none => false,
        Option.some p =>
            let pe : I64 := p.start + list_length p.lines in
            Bool.and (Bool.not (w.start < p.start)) (Bool.not (pe < upto)),
    }

/// The absolute range to load: ends at the top of the tail (or the
/// window's top, whichever is lower) and reaches back one page.
pub def Model.page_request (m : TuiModel) (w : Window) : Option (Pair I64 I64) :=
    let ts : I64 := m.transcript.tail_start in
    let upto : I64 := if w.start + w.count < ts then w.start + w.count else ts in
    let req_start : I64 := if upto - Store.page_lines < 0 then 0 else upto - Store.page_lines in
    if Bool.not (req_start < upto)
    then Option.none
    else Option.some (Pair.pair req_start (upto - req_start))

/// The visible window. The scrolled panel spends ONE of its rows on
/// the indicator; a requested range the loaded window does not cover
/// renders `""` placeholders until the page loads.
pub def visible_transcript (m : TuiModel) : List String :=
    let w : Window := Model.window m in
    let content : List String := Transcript.slice m.transcript w.start w.count in
    if w.eff > 0 then List.cons (scroll_indicator w.start) content else content

/// `N lines above -- PgDn for latest`: the row the scrolled-up panel
/// spends one of its rows on; `n` is the count of lines STILL above
/// the window's top.
pub def scroll_indicator (n : I64) : String :=
    let lines_word : String := if n == 1 then "line above -- PgDn for latest" else "lines above -- PgDn for latest" in
    String.concat (String.concat (I64.to_string n) " ") lines_word

#[partial]
def take_n (n : I64) (xs : List String) : List String :=
    if n < 1 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (take_n (n - 1) rest),
    }

/// The top scroll still allows: at most `len - (height - 1)` (the
/// scrolled window shows `height - 1` content rows and an indicator
/// row), never less than 0 -- so the transcript's FIRST line is
/// reachable at max scroll.
#[partial]
def scroll_clamp (scroll : I64) (len : I64) (height : I64) : I64 :=
    let headroom : I64 := if height < 1 then 0 else len - (height - 1) in
    let room : I64 := if headroom < 0 then 0 else headroom in
    if scroll > room then room
    else if scroll < 0 then 0
    else scroll

/// `rows` minus the 3-row input box and the status row, minus the
/// transcript border's own top/bottom lines.
pub def panel_height (m : TuiModel) : I64 :=
    let h := m.rows - 6 in
    if h < 0 then 0 else h

/// The scroll state machine: `scroll` counts lines above the pinned
/// bottom, in absolute transcript coordinates. The delta moves the
/// window (PageUp/Ctrl+U positive, i.e. older; PageDown/Ctrl+D
/// negative), clamped at both ends.
#[partial]
pub def Model.scroll_step (m : TuiModel) (delta : I64) : TuiModel :=
    let total : I64 := m.transcript.total in
    let m2 : TuiModel := { m with scroll := scroll_clamp (m.scroll + delta) total (panel_height m) } in
    m2

/// A new block of transcript lines: the blank separator row in front
/// (skipped on an empty transcript), and a scrolled view HELD in place
/// -- the scroll grows by the block's own size, so the visible lines do
/// not slide (auto-pin only happens when the user was already at the
/// bottom, i.e. scroll = 0: it stays 0 and the tail keeps riding).
#[partial]
pub def Model.append_block (m : TuiModel) (lines : List String) : TuiModel :=
    let block : List String := Transcript.next_block m.transcript lines in
    let tr2 : Transcript := Transcript.append m.transcript block in
    let m2 : TuiModel := { m with transcript := tr2,
        scroll := if m.scroll > 0 then m.scroll + list_length block else 0 } in
    m2

/// A gapless append (the Ctrl+C hint): no separator row, and no scroll
/// adjustment -- the line joins the tail like any other output.
#[partial]
pub def Model.append_lines (m : TuiModel) (lines : List String) : TuiModel :=
    let tr2 : Transcript := Transcript.append m.transcript lines in
    let m2 : TuiModel := { m with transcript := tr2 } in
    m2

pub def Model.transcript_count (m : TuiModel) : I64 := m.transcript.total

/// Prompt history is capped: an unbounded `List String` was the other
/// per-process growth.
pub def Model.hist_cap : I64 := 200

pub def Model.hist_keep (xs : List String) : List String :=
    take_n Model.hist_cap xs

#[partial]
pub def list_length (xs : List String) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _ rest => 1 + list_length rest,
    }

// ── status line ─────────────────────────────────────────────────────────

/// The TUI's status bar: the dumb-mode twin minus the trailing `"> "`
/// prompt (the input box itself is the prompt here), with the
/// turn-spinner glyph riding at the end while a turn runs. The glyph is
/// deliberately the ONLY cell of this row that changes mid-turn
/// (`spinner_frame` bumps per tick, everything else is static), so the
/// diff pipeline rewrites exactly that one cell each frame and the raw
/// `TuiApp.progress` fragment on the transcript's last row survives.
pub def status_line (m : TuiModel) : String :=
    if m.turn_pending
    then String.concat (String.concat (Dumb.status_fields m.state) " ") (spinner_glyph m.spinner_frame)
    else Dumb.status_fields m.state

/// The spinner's four frames, cycling on the tick count.
pub def spinner_glyph (frame : I64) : String :=
    let idx : I64 := frame - (frame / 4) * 4 in
    if I64.beq idx 0 then "|"
    else if I64.beq idx 1 then "/"
    else if I64.beq idx 2 then "-"
    else "\\"
