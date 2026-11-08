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
use std::list {List.length}
use weaver::commands {WeaverState, Effect}
use weaver::overlay {OverlayState}
use log::logger {Logger}
use weaver::error {WeaverError}
use weaver::dumb {Dumb.status_fields}
use weaver::theme {theme_status_style_with, theme_border_style_with, theme_thinking_style_with}
use weaver::todo {TodoItem, Todo.summary, Todo.lines, Todo.is_running}
use weaver::tasks {TaskEntry}
use tui::text {Text.take_width}
use weaver::policy {Mode}
use weaver::store {TLine, Transcript, TranscriptPage, Transcript.empty}
use tui::types {Event, LayoutSize}
use tui::widget {Widget, SizedWidget, BorderStyle, border_with, border_titled, label, sized, with_style, padding}
use weaver::ui::banner {BannerModel, BannerMsg, BannerView, Banner.shown, Banner.rows, Banner.height, Banner.view}
use weaver::ui::prompt {PromptModel, PromptBox, Prompt.empty, Prompt.view}
use tui::widgets::picker {PickerModel, Picker.list_height, Picker.view}
use weaver::ui::live {LiveModel, LiveMsg, LiveView, Live.idle, Live.rows, Live.height}
use weaver::ui::rows {DisplayRow, Rows.widget}
use weaver::ui::pane {
    PaneModel, PaneMsg, PaneView, Pane.make, Pane.update, Pane.refresh,
    Pane.append_block, Pane.append_lines, Pane.row_widgets, Pane.bar_view,
}

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
    /// `last_context` is the real prompt size of the turn's last model
    /// call; `plan` is the assistant text captured while the turn ran in
    /// plan mode (none otherwise).
    turn_result (run : RunState) (lines : List TLine) (delta : List Message)
        (last_context : I64) (plan : Option String),
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
    /// Fill the input box (the plan dialog's "revise with a note").
    input_set (text : String),
    /// Submit a line as a new turn (the plan dialog's "approve and
    /// execute"): the update starts the same fiber path as Enter.
    submit (st : WeaverState) (text : String),
    /// The Esc stop request's signal write completed; a no-op fold.
    stop_sent,
    /// The background session-title call finished: the pair it wrote
    /// (none when it was skipped or failed). Display state only.
    title_result (title : Option (Pair String String)),
    /// The running turn's live display (`ui/live.mo`).
    live (msg : LiveMsg),
    /// The launch banner's sweep (`ui/banner.mo`).
    banner (msg : BannerMsg),
    /// The dialog-ownership handshake, polled every frame.
    overlay_polled (overlay : Option OverlayState),
    /// The session's todo list, polled from `todos.json`.
    todos_polled (todos : List TodoItem),
    /// Background processes and subagent runs, polled for the footer
    /// count and the exit notes.
    tasks_polled (tasks : List TaskEntry),
    /// The `/tasks` monitor closed; `notes` are what it did (a kill).
    monitor_closed (notes : List String),
    /// One tick's subscription results, folded in order.
    batch (msgs : List WeaverMsg),
    /// `repaint_cmd` ran: the terminal was erased and repainted.
    repainted,
    /// A side command's dialog (`/help`, `/todos`, ...) closed.
    side_closed,
    /// A `/btw` question's answer, or why there is none.
    btw_result (question : String) (answer : Result String String),
}

/// `tui::App`'s `on_event : Event -> WeaverMsg` -- every raw event is a
/// `key_event` until `update` decides otherwise; `turn_result`/
/// `command_result` only ever arrive via `Cmd.perform`, never from the
/// terminal.
pub def on_event (e : Event) : WeaverMsg :=
    WeaverMsg.key_event e

pub struct TuiModel {
    state : WeaverState,
    /// The input box and its submit history.
    prompt : PromptModel := Prompt.empty,
    /// The transcript pane: the loaded window, its rows, scroll,
    /// selection and scrollbar.
    pane : PaneModel,
    rows : I64,
    cols : I64,
    /// Consecutive Ctrl+C presses since the last other event (the
    /// double-press exit; a pure update has no clock, so no timed
    /// window -- any other key or message resets the streak).
    ctrl_c_streak : I64 := 0,
    /// The same streak for Ctrl+D. Kept apart from `ctrl_c_streak` so
    /// each gesture arms only itself: Ctrl+C then Ctrl+D is two FIRST
    /// presses, never an exit.
    ctrl_d_streak : I64 := 0,
    /// A turn is running on its own fiber (`Cmd.perform_async`): the
    /// spinner shows and the status row carries its glyph. Keys typed
    /// meanwhile reach the input box (they are read mid-turn unless a
    /// dialog owns stdin); Esc asks the turn to stop.
    turn_pending : Bool := false,
    /// Ticks since startup: the subscriptions' cadence clock.
    frame : I64 := 0,
    /// The launch banner, until the first submit.
    banner : BannerModel := Banner.shown,
    /// The running turn's streamed text, spend and spinner (reset at
    /// submit; shown only while `turn_pending`).
    live : LiveModel := Live.idle,
    /// The submitted line opened a full-screen modal that owns the
    /// terminal: the main loop must not tick-redraw over it (interleaved
    /// writes corrupt the modal's paint).
    modal : Bool := false,
    /// A clean plan-mode turn produced a plan: the persistence
    /// continuation opens the "Plan ready" dialog once the turn folds.
    plan_ready : Bool := false,
    /// This turn warrants an agent-generated session title (the first
    /// turn, or one that produced a plan): the next frame tick forks the
    /// title call, so it never blocks the turn's persistence or its
    /// dialog.
    title_due : Bool := false,
    /// The submitted turn's generation (the stop signal's stale-request
    /// guard).
    turn_gen : I64 := 0,
    /// A dialog on the turn's fiber owns stdin and the terminal: the tick
    /// poll sets it, `reads_input` acks once after that, and the poll
    /// that sees the close clears it and forces a repaint.
    overlay_open : Bool := false,
    /// The last dialog-close sequence folded into the model.
    dialog_seq : I64 := 0,
    /// The model picker, while `/model` with no argument
    /// has one open. The app loop still owns stdin; keys route here.
    picker : Option PickerModel := Option.none,
    /// Instructions typed while a turn runs, in submit order. Enter
    /// queues instead of dropping them; the head starts when the running
    /// turn's result folds in.
    queued : List String := List.empty,
    /// A running turn's store write is in flight and an instruction is
    /// queued behind it: `store_result` starts the head when the write
    /// lands (one `Cmd` per fold, so the two cannot share a fold).
    queued_ready : Bool := false,
    /// The run's debug logger (none when WEAVER_LOG=off).
    log : Option Logger := Option.none,
    /// The model's todo list (`todo_write`), shown above the status row.
    todos : List TodoItem := List.empty,
    /// Ctrl+T: the whole list, or its one-line summary.
    todos_open : Bool := true,
    /// Tasks running at the last poll (the footer's count).
    tasks_running : I64 := 0,
    /// Their ids: the next poll's exit notes compare against them.
    tasks_seen : List String := List.empty,
    /// A dialog closed and the terminal still shows it. A batch keeps only
    /// its first command, so a close beside another command could lose its
    /// repaint: `TuiApp.update` pays the debt on the spot (a repaint, or an
    /// erase before the update's own perform/inspect) and the flag outlives
    /// the update only when that command is a fork, dispatch or quit.
    repaint_due : Bool := false,
    /// `/btw` answers that arrived while a turn's dialog owned the screen:
    /// (question, answer), shown when it closes.
    btw_ready : List (Pair String String) := List.empty,
}

/// The initial model: an empty input box with a hint placeholder, no
/// transcript yet, and the terminal size `Tui.run` probed before the
/// first frame. New fields are spelled even though they default --
/// a struct literal whose new field is omitted has been seen to check
/// clean and fill GARBAGE at runtime (the two-host divergence note).
pub def init_tui_model (log : Option Logger) (st : WeaverState) (rows : I64) (cols : I64) : TuiModel :=
    init_tui_model_with log st rows cols Transcript.empty

/// The startup tail loaded from the session store.
pub def init_tui_model_with (log : Option Logger) (st : WeaverState) (rows : I64) (cols : I64) (tr : Transcript) : TuiModel :=
    let m : TuiModel := { state := st, prompt := Prompt.empty, pane := Pane.make tr, rows := rows, cols := cols, ctrl_c_streak := 0, ctrl_d_streak := 0, turn_pending := false, frame := 0, banner := Banner.shown, live := Live.idle, modal := false, plan_ready := false, title_due := false, turn_gen := 0, overlay_open := false, dialog_seq := 0, picker := Option.none, queued := List.empty, queued_ready := false, log := log, todos := List.empty, todos_open := true, tasks_running := 0, tasks_seen := List.empty, repaint_due := false, btw_ready := List.empty } in
    Model.refresh_rows m

pub def Model.banner_view (m : TuiModel) : BannerView :=
    let v : BannerView := { colors := m.state.colors, cols := m.cols, provider := m.state.provider, model := m.state.run.session.config.model } in
    v

// ── view ─────────────────────────────────────────────────────────────────

/// Three rows: a bordered transcript panel (fills whatever is left), a
/// one-line status bar, and the input box. Named `Model.view`, not bare
/// `view` -- `init::optics` already owns that name for applying a
/// `Lens`, and a whole-program check loads both (a real collision,
/// caught by checking the whole corpus, not just this mote).
pub def Model.picker_height (m : TuiModel) : I64 :=
    Picker.list_height (panel_height m)

pub def Model.view (m : TuiModel) : Widget :=
    let colors : Bool := m.state.colors in
    let mode : Mode := m.state.mode in
    let body : Widget := match m.picker {
        Option.none => transcript_column m,
        Option.some p => Picker.view (panel_height m) p,
    } in
    // `border_with`, not `with_style (border ...)`: the frame is dim, the
    // rows inside it are not (with_style merges into the whole subtree).
    let inner : Widget :=
        if I64.lt m.cols 5
        then body
        else Widget.row [sized (LayoutSize.fill 1) body, sized (LayoutSize.fixed 1) (Pane.bar_view (Model.pane_view m) m.pane)] in
    let framed : Widget := padding 1 0 0 0 inner in
    // The session's name sits in the frame's top edge: it costs no row.
    let frame : Widget := match m.state.name {
        Option.some n => border_titled (theme_border_style_with colors) BorderStyle.rounded n framed,
        Option.none => border_with (theme_border_style_with colors) BorderStyle.rounded framed,
    } in
    let transcript : SizedWidget := sized (LayoutSize.fill 1) frame in
    let status : SizedWidget := sized (LayoutSize.fixed 1) (with_style (theme_status_style_with colors mode) (label (status_line m))) in
    let input : SizedWidget := sized (LayoutSize.fixed 3) (Prompt.view m.prompt) in
    let head : List SizedWidget := if m.banner.shown then [sized (LayoutSize.fixed Banner.rows) (Banner.view (Model.banner_view m) m.banner)] else List.empty in
    let todo_rows : List String := Model.todo_rows m in
    let todos : List SizedWidget := if List.is_empty todo_rows then List.empty
        else [sized (LayoutSize.fixed (List.length todo_rows)) (Widget.column (List.map (fn (r : String) =>
            sized (LayoutSize.fixed 1) (with_style (theme_thinking_style_with colors) (label r))) todo_rows))] in
    Widget.column (List.append head (List.append [transcript] (List.append todos [status, input])))

// ── the todo panel ───────────────────────────────────────────────────────

/// The most todo rows shown open; a longer list keeps the in-progress item
/// and its neighbours in view.
pub def Model.todo_max_rows : I64 := 8

/// The panel above the status row: nothing without todos; folded (Ctrl+T),
/// the one-line summary; open, the summary and the items, each clipped to
/// the width.
pub def Model.todo_rows (m : TuiModel) : List String :=
    if List.is_empty m.todos then List.empty
    else
        let width : I64 := if m.cols - 2 < 1 then 1 else m.cols - 2 in
        let head : String := String.concat " " (Todo.summary m.todos) in
        let all : List String := if m.todos_open
            then List.cons head (List.map (fn (l : String) => String.concat "   " l) (todo_window m.todos))
            else [String.concat head "  (ctrl+t)"] in
        List.map (fn (r : String) => Text.take_width r width) all

/// At most `todo_max_rows - 1` items, starting a little before the one in
/// progress so it stays visible.
def todo_window (ts : List TodoItem) : List String :=
    let cap : I64 := Model.todo_max_rows - 1 in
    let lines : List String := Todo.lines ts in
    let n : I64 := List.length lines in
    if Bool.not (I64.lt cap n) then lines
    else
        let at : I64 := running_index ts 0 in
        let start0 : I64 := if at < 1 then 0 else at - 1 in
        let start : I64 := if I64.lt (n - cap) start0 then n - cap else start0 in
        take_n cap (drop_n start lines)

#[partial]
def running_index (ts : List TodoItem) (i : I64) : I64 :=
    match ts {
        List.empty => 0,
        List.cons t rest => if Todo.is_running t then i else running_index rest (i + 1),
    }

#[partial]
def take_n (n : I64) (xs : List String) : List String :=
    if n < 1 then List.empty
    else match xs {
        List.empty => xs,
        List.cons x rest => List.cons x (take_n (n - 1) rest),
    }

#[partial]
def drop_n (n : I64) (xs : List String) : List String :=
    if n < 1 then xs
    else match xs {
        List.empty => xs,
        List.cons _ rest => drop_n (n - 1) rest,
    }

// ── the transcript pane ─────────────────────────────────────────────────
// Screen -> pane mapping is the panel's border (1) plus its left padding
// (1); the scrollbar takes the old right padding column.

/// The transcript content's first screen row/column. The row depends on
/// the launch banner: while it shows, the panel starts four rows lower.
pub def Model.panel_top : I64 := 1
pub def Model.panel_top_of (m : TuiModel) : I64 :=
    Banner.height m.banner + Model.panel_top
pub def Model.panel_left : I64 := 2

// ── input-box geometry and mouse selection ──────────────────────────────
// The input is `sized (fixed 3) (padding 1 0 1 0 …)`: content starts at
// column 1 and row rows-3, three rows tall (single-line text on the first,
// multiline down to the third). Banner-independent.

pub def Model.prompt_box (m : TuiModel) : PromptBox :=
    let top : I64 := if m.rows - 3 < 0 then 0 else m.rows - 3 in
    let width : I64 := if m.cols - 2 < 1 then 1 else m.cols - 2 in
    let b : PromptBox := { top := top, left := 1, width := width, height := 3 } in
    b

/// The panel's content width: the terminal minus the rounded border (2)
/// and the horizontal padding (2).
pub def Model.content_width (m : TuiModel) : I64 :=
    let w : I64 := m.cols - 4 in
    if w < 1 then 1 else w

/// The pane's geometry: below the banner, above the live rows; no bar
/// while the picker covers the panel.
pub def Model.pane_view (m : TuiModel) : PaneView :=
    let no_picker : Bool := match m.picker { Option.none => true, Option.some _ => false } in
    let v : PaneView := { colors := m.state.colors, width := Model.content_width m, height := Model.body_height m,
        top := Model.panel_top_of m, left := Model.panel_left, bar := Bool.and no_picker (I64.lt 4 m.cols) } in
    v

/// One pane message; a finished selection's text rides along.
pub def Model.pane_step (m : TuiModel) (msg : PaneMsg) : Pair TuiModel (Option String) :=
    match Pane.update (Model.pane_view m) m.pane msg {
        Pair.pair p text => Pair.pair { m with pane := p } text,
    }

/// Recompute the pane's rows when the transcript, geometry or scroll moved.
pub def Model.refresh_rows (m : TuiModel) : TuiModel :=
    { m with pane := Pane.refresh (Model.pane_view m) m.pane }

pub def Model.display_rows (m : TuiModel) : List DisplayRow :=
    m.pane.rows

def transcript_column (m : TuiModel) : Widget :=
    let body : List SizedWidget := Pane.row_widgets (Model.pane_view m) m.pane in
    // The live row is painted AFTER the cached rows (it is not part of
    // them), so ticks update it without re-wrapping the transcript.
    if m.turn_pending
    then
        Widget.column (List.append body (List.map Rows.widget (Live.rows (Model.live_view m) m.live)))
    else Widget.column body

/// `rows` minus the 3-row input box and the status row, minus the
/// transcript border's own top/bottom lines.
pub def panel_height (m : TuiModel) : I64 :=
    let h := m.rows - 6 - Banner.height m.banner - List.length (Model.todo_rows m) in
    if h < 0 then 0 else h

/// The transcript body's height: while a turn is pending, one panel row is
/// reserved for the live thinking row appended under the last prompt.
pub def Model.body_height (m : TuiModel) : I64 :=
    let live : I64 := Model.live_rows_height m in
    let h : I64 := panel_height m - live in
    if h < 0 then 0 else h

/// The rows the in-flight display owns below the transcript: the spinner
/// row plus the reasoning and answer tails (separate blocks, so reasoning
/// can never evict the answer).
pub def Model.live_rows_height (m : TuiModel) : I64 :=
    if Bool.not m.turn_pending then 0
    else Live.height (Model.live_view m) m.live

pub def Model.live_view (m : TuiModel) : LiveView :=
    let v : LiveView := { colors := m.state.colors, width := Model.content_width m, panel := panel_height m } in
    v

/// Rows toward older output (negative: toward the latest).
pub def Model.scroll_step (m : TuiModel) (delta : I64) : TuiModel :=
    match Model.pane_step m (PaneMsg.scroll delta) {
        Pair.pair m2 _ => m2,
    }

/// A new block of transcript lines (a blank separator row in front; a
/// scrolled view is held in place).
pub def Model.append_block (m : TuiModel) (lines : List TLine) : TuiModel :=
    { m with pane := Pane.append_block (Model.pane_view m) m.pane lines }

/// A gapless append (the Ctrl+C hint).
pub def Model.append_lines (m : TuiModel) (lines : List TLine) : TuiModel :=
    { m with pane := Pane.append_lines (Model.pane_view m) m.pane lines }

// ── status line ─────────────────────────────────────────────────────────

/// The TUI's status bar: the dumb-mode twin minus the trailing `"> "`
/// prompt (the input box itself is the prompt here). It is STATIC
/// mid-turn: the spinner now lives on the thinking row under the prompt.
pub def status_line (m : TuiModel) : String :=
    let base : String := Dumb.status_fields m.state in
    // In front: the fields already fill an 80-column row, and a clipped
    // count would hide the one thing still running.
    if m.tasks_running < 1 then base
    else String.concat (I64.to_string m.tasks_running)
        (String.concat (if m.tasks_running == 1 then " task running · " else " tasks running · ") base)
