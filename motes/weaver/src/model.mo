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
use shuttle::message {Message, Usage}
use shuttle::context {usage_zero}
use weaver::usage {Usage.delta}
use weaver::commands {WeaverState, Effect}
use weaver::overlay {OverlayState}
use weaver::format {format_tokens, format_elapsed}
use log::logger {Logger}
use weaver::error {WeaverError}
use weaver::dumb {Dumb.status_fields}
use weaver::theme {
    theme_line_style_with, theme_tline_style_with, theme_status_style_with,
    theme_border_style_with, theme_banner_style_with, theme_running_style_with,
    theme_thinking_style_with,
    theme_scrollbar_thumb_style_with,
    theme_markdown_span_style_with,
    BannerPart, theme_split_lines,
}
use markdown::parse {Markdown.parse}
use markdown::render {
    Markdown.to_lines, Markdown.to_plain_lines,
    Markdown.StyledLine, Markdown.StyledSpan,
}
use weaver::policy {Mode}
use weaver::store {
    TLine, TLineKind, Transcript, TranscriptPage, Store.page_lines,
    Transcript.empty, Transcript.next_block, Transcript.append, Transcript.slice,
}
use tui::types {Event, LayoutSize, TextStyle, TextSegment}
use tui::core {clamp, style_default, mk_text_segment}
use tui::widgets::input {
    InputState, input_state, InputState.press, InputState.drag,
    InputState.finish_selection, InputState.clear_selection,
}
use tui::widget {Widget, SizedWidget, BorderStyle, border_with, label, spans, text_input, sized, with_style, padding}
use tui::render {wrap_text}
use tui::text {
    Text.width, Text.take_width, Text.slice_cols, Text.padded_slice_cols, Text.snap_span,
    Text.width_spans, Text.wrap_spans, Text.slice_spans,
}
use std::list {List.intercalate}

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
    /// A pending tick's poll: the live usage (only every tenth frame),
    /// the dialog-ownership state (every frame), and -- every third
    /// frame -- the streamed-text delta.
    polled (usage : Option Usage) (overlay : Option OverlayState) (live : Option LiveDelta),
}

/// One live poll's streamed-text delta: the new assistant text and
/// reasoning since the given offsets, the offsets after the read, and
/// the tool currently dispatching (none when nothing is).
pub struct LiveDelta {
    text : String,
    thinking : String,
    text_seen : I64,
    thinking_seen : I64,
    activity : Option String,
}

/// `tui::App`'s `on_event : Event -> WeaverMsg` -- every raw event is a
/// `key_event` until `update` decides otherwise; `turn_result`/
/// `command_result` only ever arrive via `Cmd.perform`, never from the
/// terminal.
pub def on_event (e : Event) : WeaverMsg :=
    WeaverMsg.key_event e

/// What the cached display rows were computed for. Any transcript,
/// viewport or scroll change invalidates them.
pub struct RowsKey {
    total : I64,
    tail_start : I64,
    cols : I64,
    rows : I64,
    scroll : I64,
    page_start : I64,
    /// The startup banner spends four rows of the panel while it shows.
    banner : Bool,
    /// A pending turn spends one panel row on the live thinking row.
    pending : Bool,
    /// Ctrl+O's detail-line filter.
    details : Bool,
    /// The two streamed blocks' heights: `body_height` shrinks as they
    /// grow, so the cache must rebuild on either change.
    think_stream : I64,
    text_stream : I64,
}

/// The model picker: the fetched list, the session's current name,
/// and the selected row. Pure -- the TUI draws it in the transcript
/// panel and routes keys to it while it is open; no dialog machinery.
pub struct PickerState {
    models : List String,
    current : String,
    selected : I64,
    offset : I64,
}

#[partial]
def picker_index_of (model : String) (models : List String) (i : I64) : I64 :=
    match models {
        List.empty => 0i64 - 1i64,
        List.cons m rest =>
            if String.beq m model then i else picker_index_of model rest (i + 1i64),
    }

#[partial]
def picker_count (models : List String) : I64 :=
    match models {
        List.empty => 0i64,
        List.cons _ rest => 1i64 + picker_count rest,
    }

#[partial]
def picker_at (i : I64) (models : List String) : Option String :=
    match models {
        List.empty => Option.none,
        List.cons m rest => if i < 1i64 then Option.some m else picker_at (i - 1i64) rest,
    }

#[partial]
def picker_take (n : I64) (xs : List String) : List String :=
    if n < 1i64 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (picker_take (n - 1i64) rest),
    }

#[partial]
def picker_drop (n : I64) (xs : List String) : List String :=
    if n < 1i64 then xs
    else match xs {
        List.empty => xs,
        List.cons _ rest => picker_drop (n - 1i64) rest,
    }

pub def Picker.init (models : List String) (current : String) : PickerState :=
    let idx : I64 := picker_index_of current models 0i64 in
    let sel : I64 := if idx < 0i64 then 0i64 else idx in
    { models := models, current := current, selected := sel, offset := 0i64 }

pub def Picker.count (p : PickerState) : I64 := picker_count p.models

pub def Picker.selected_model (p : PickerState) : String :=
    match picker_at p.selected p.models {
        Option.none => p.current,
        Option.some m => m,
    }

/// Clamp the selection and scroll `offset` so it stays inside a window
/// of `visible` rows.
pub def Picker.adjust (visible : I64) (p : PickerState) : PickerState :=
    let n : I64 := Picker.count p in
    if n < 1i64 then p
    else
        let sel : I64 := clamp p.selected 0i64 (n - 1i64) in
        let v : I64 := if visible < 1i64 then 1i64 else visible in
        let off : I64 :=
            if sel < p.offset then sel
            else if p.offset + v < sel + 1i64 then sel + 1i64 - v
            else p.offset in
        { p with selected := sel, offset := off }

pub def Picker.move (delta : I64) (visible : I64) (p : PickerState) : PickerState :=
    let sel : I64 := p.selected + delta in
    Picker.adjust visible { p with selected := sel }

/// The adjusted top row for a `visible`-row window (the view's read
/// side; `adjust` is what key handling writes).
pub def Picker.window_offset (visible : I64) (p : PickerState) : I64 :=
    let adjusted : PickerState := Picker.adjust visible p in
    adjusted.offset

pub def Picker.visible (visible : I64) (p : PickerState) : List String :=
    let v : I64 := if visible < 1i64 then 1i64 else visible in
    let start : I64 := Picker.window_offset v p in
    picker_take v (picker_drop start p.models)

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
    /// The same streak for Ctrl+D. Kept apart from `ctrl_c_streak` so
    /// each gesture arms only itself: Ctrl+C then Ctrl+D is two FIRST
    /// presses, never an exit.
    ctrl_d_streak : I64 := 0,
    /// WRAPPED DISPLAY ROWS above the pinned bottom; 0 = pinned to the
    /// latest output. A row unit (not a logical line) is what makes every
    /// row of a message taller than the panel reachable.
    scroll : I64 := 0,
    /// The wrapped row count of the loaded window (page + tail) plus one
    /// row for each placeholder line before it. Recomputed with the rows
    /// cache; `scroll` clamps against it.
    row_total : I64 := 0,
    /// Where the pointer grabbed the scrollbar thumb (rows below its top);
    /// none when no scrollbar drag is in progress. Kept out of `sel` so a
    /// bar drag never becomes a text selection.
    scroll_drag : Option I64 := Option.none,
    /// Submitted non-empty lines, most recent first (the up-arrow
    /// history; ArrowUp recalls only from an empty input).
    hist : List String := List.empty,
    /// Where the history walk stands (-1 = live edit, not browsing).
    hist_idx : I64 := 0 - 1,
    /// A turn is running on its own fiber (`Cmd.perform_async`): the
    /// spinner shows and the status row carries its glyph. Keys typed
    /// meanwhile reach the input box (they are read mid-turn unless a
    /// dialog owns stdin); Esc asks the turn to stop.
    turn_pending : Bool := false,
    /// The spinner's tick counter (bumped only while `turn_pending`, so
    /// idle ticks are zero-diff draws).
    spinner_frame : I64 := 0,
    /// A page read is in flight; only the synchronous `Cmd.perform`
    /// pager sets it, so it clears in the same fold.
    page_pending : Bool := false,
    /// The wrapped rows last computed, and the state they were computed
    /// for. Wrapping a long line every 100 ms tick was the TUI's other
    /// allocation hot spot; a tick reuses this.
    rows_cache : List DisplayRow := List.empty,
    rows_key : Option RowsKey := Option.none,
    /// The mouse selection over DISPLAY rows (cleared whenever the rows
    /// cache is rebuilt: scroll, append, page load, resize).
    sel : Option TextSelection := Option.none,
    /// The launch banner shows until the first submit.
    banner : Bool := true,
    /// The one-time shuttle sweep's tick counter (stops at 12).
    banner_frame : I64 := 0,
    /// The cumulative spend reported by the turn's `on_usage` hook. The
    /// session in `state.run` is the PRE-turn snapshot, so this is the
    /// live token count the thinking row shows.
    live_spent : Option Usage := Option.none,
    /// The cumulative spend at submit: `live_spent` minus this is the
    /// TURN's delta (the file carries cumulative billing).
    live_base : Option Usage := Option.none,
    /// The submitted line opened a full-screen modal that owns the
    /// terminal: the main loop must not tick-redraw over it (interleaved
    /// writes corrupt the modal's paint).
    /// The in-flight turn's streamed text and reasoning, painted below
    /// the transcript and cleared at turn end; `live_seen`/
    /// `live_thinking_seen` are byte offsets into the turn files.
    live_text : String := "",
    live_seen : I64 := 0,
    live_thinking : String := "",
    live_thinking_seen : I64 := 0,
    /// The tool currently dispatching, from the activity feed.
    live_activity : Option String := Option.none,
    /// Ctrl+O: show detail lines (tool output, completed thinking).
    show_details : Bool := false,
    modal : Bool := false,
    /// A clean plan-mode turn produced a plan: the persistence
    /// continuation opens the "Plan ready" dialog once the turn folds.
    plan_ready : Bool := false,
    /// Esc asked the running turn to stop; the live row says so and the
    /// fiber ends at its next model/tool boundary.
    stop_requested : Bool := false,
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
    picker : Option PickerState := Option.none,
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
    let m : TuiModel := { state := st, input := input_state "" input_placeholder, transcript := tr, rows := rows, cols := cols, ctrl_c_streak := 0, ctrl_d_streak := 0, scroll := 0, row_total := 0, scroll_drag := Option.none, hist := List.empty, hist_idx := 0 - 1, turn_pending := false, spinner_frame := 0, page_pending := false, rows_cache := List.empty, rows_key := Option.none, sel := Option.none, banner := true, banner_frame := 0, live_spent := Option.none, live_base := Option.none, live_text := "", live_seen := 0, live_thinking := "", live_thinking_seen := 0, live_activity := Option.none, show_details := false, modal := false, plan_ready := false, stop_requested := false, turn_gen := 0, overlay_open := false, dialog_seq := 0, picker := Option.none, queued := List.empty, queued_ready := false, log := log } in
    Model.refresh_rows m

/// The input box's placeholder, shared by the live edit and a history
/// walk's return-to-live.
pub def input_placeholder : String := "type a message, or /help" 

// ── the launch banner ────────────────────────────────────────────────────

pub def Model.banner_height : I64 := 4

def banner_seg (style : TextStyle) (text : String) : SizedWidget :=
    sized (LayoutSize.fixed (Text.width text)) (with_style style (label text))

def banner_pad (m : TuiModel) (w : I64) : I64 :=
    let room : I64 := m.cols - w in
    if room < 1 then 0 else room / 2

/// `w e a v e r`, each letter in a cyan -> blue -> magenta gradient.
#[partial]
def banner_word_go (colors : Bool) (letters : List String) (i : I64) (acc : List SizedWidget) : List SizedWidget :=
    match letters {
        List.empty => List.reverse acc,
        List.cons l rest =>
            let part : BannerPart :=
                if i < 2 then BannerPart.word_cyan
                else if i < 4 then BannerPart.word_blue
                else BannerPart.word_magenta in
            // The separator belongs BETWEEN letters: in the reversed
            // accumulator it is pushed before the newer letter.
            let acc1 : List SizedWidget :=
                if i < 1 then acc
                else List.cons (banner_seg (theme_banner_style_with colors BannerPart.warp) " ") acc in
            banner_word_go colors rest (i + 1) (List.cons (banner_seg (theme_banner_style_with colors part) l) acc1),
    }

def banner_word (colors : Bool) : SizedWidget :=
    sized (LayoutSize.fixed 11) (Widget.row (banner_word_go colors ["w", "e", "a", "v", "e", "r"] 0 List.empty))

/// The shuttle row: frame + 14-cell warp, the shuttle one cell further
/// right per tick (a one-time sweep), frame.
def banner_art_mid (m : TuiModel) : List SizedWidget :=
    let colors : Bool := m.state.colors in
    let frame := theme_banner_style_with colors BannerPart.frame in
    let warp := theme_banner_style_with colors BannerPart.warp in
    let shuttle := theme_banner_style_with colors BannerPart.shuttle in
    let p : I64 := if m.banner_frame < 14 then m.banner_frame else 13 in
    let before : String := String.repeat "─" p in
    let after : String := String.repeat "─" (13 - p) in
    [
        banner_seg frame "│ ",
        banner_seg warp before,
        banner_seg shuttle "▸",
        banner_seg warp after,
        banner_seg frame " │",
    ]

def banner_widget (m : TuiModel) : Widget :=
    let colors : Bool := m.state.colors in
    let frame := theme_banner_style_with colors BannerPart.frame in
    let provider : String := m.state.provider in
    let model : String := m.state.run.session.config.model in
    let tagline : String := String.concat "coding agent · "
        (String.concat provider (String.concat "/" (String.concat model " · /help"))) in
    let tag_w : I64 := Text.width tagline in
    let right_w : I64 := if tag_w < 11 then 11 else tag_w in
    let pad : I64 := banner_pad m (18 + 3 + right_w) in
    let top : String := String.concat "╭" (String.concat (String.repeat "─" 16) "╮") in
    let bot : String := String.concat "╰" (String.concat (String.repeat "─" 16) "╯") in
    let lead : SizedWidget := sized (LayoutSize.fixed pad) (label "") in
    let gap : SizedWidget := sized (LayoutSize.fixed 3) (label "") in
    let row0 : SizedWidget := sized (LayoutSize.fixed 1) (Widget.row [lead, banner_seg frame top]) in
    let mid : List SizedWidget := List.append [lead] (List.append (banner_art_mid m) [gap, banner_word colors]) in
    let row1 : SizedWidget := sized (LayoutSize.fixed 1) (Widget.row mid) in
    let row2 : SizedWidget := sized (LayoutSize.fixed 1)
        (Widget.row [lead, banner_seg frame bot, gap, banner_seg (theme_banner_style_with colors BannerPart.tagline) tagline]) in
    let row3 : SizedWidget := sized (LayoutSize.fixed 1) (label "") in
    Widget.column [row0, row1, row2, row3]

// ── view ─────────────────────────────────────────────────────────────────

/// Three rows: a bordered transcript panel (fills whatever is left), a
/// one-line status bar, and the input box. Named `Model.view`, not bare
/// `view` -- `init::optics` already owns that name for applying a
/// `Lens`, and a whole-program check loads both (a real collision,
/// caught by checking the whole corpus, not just this mote).
pub def Model.picker_height (m : TuiModel) : I64 :=
    // The header and footer lines come out of the same budget; a panel
    // too short for them gets a zero-row list, never an overflowing one.
    let h : I64 := panel_height m - 2i64 in
    if h < 0i64 then 0i64 else h

def picker_header_text (m : TuiModel) (p : PickerState) : String :=
    String.concat "Select a model — "
        (String.concat m.state.provider (String.concat "   current: " p.current))

def picker_footer_text : String := "↑/↓ move · Enter select · Esc cancel"

def picker_row_widgets (p : PickerState) (row : I64) (names : List String) : List SizedWidget :=
    match names {
        List.empty => List.empty,
        List.cons name rest =>
            let cursor : String := if I64.beq row p.selected then "> " else "  " in
            let mark : String := if String.beq name p.current then "*" else " " in
            let text : String := String.concat cursor (String.concat mark (String.concat " " name)) in
            let style : TextStyle :=
                if I64.beq row p.selected
                then { style_default with reverse := true }
                else style_default in
            List.cons (sized (LayoutSize.fixed 1) (with_style style (label text)))
                (picker_row_widgets p (row + 1i64) rest),
    }

def picker_column (m : TuiModel) (p : PickerState) : Widget :=
    let avail : I64 := panel_height m in
    let dim : TextStyle := { style_default with dim := true } in
    let head : SizedWidget := sized (LayoutSize.fixed 1) (with_style dim (label (picker_header_text m p))) in
    let foot : SizedWidget := sized (LayoutSize.fixed 1) (with_style dim (label picker_footer_text)) in
    // The layout does not clip children, so a row emitted past the
    // panel paints over its border and the status line: a 1-row panel
    // gets the header alone, a 2-row one header + footer, and only a
    // 3-row one has room for a listed model.
    if avail < 1i64
    then Widget.column List.empty
    else if I64.beq avail 1i64
    then Widget.column [head]
    else if I64.beq avail 2i64
    then Widget.column [head, foot]
    else
        let h : I64 := Model.picker_height m in
        let start : I64 := Picker.window_offset h p in
        let names : List String := Picker.visible h p in
        let rows : List SizedWidget := picker_row_widgets p start names in
        Widget.column (List.append (List.cons head rows) [foot])

pub def Model.view (m : TuiModel) : Widget :=
    let colors : Bool := m.state.colors in
    let mode : Mode := m.state.mode in
    let body : Widget := match m.picker {
        Option.none => transcript_column m,
        Option.some p => picker_column m p,
    } in
    // `border_with`, not `with_style (border ...)`: the frame is dim, the
    // rows inside it are not (with_style merges into the whole subtree).
    let inner : Widget :=
        if I64.lt m.cols 5
        then body
        else Widget.row [sized (LayoutSize.fill 1) body, sized (LayoutSize.fixed 1) (Model.scrollbar_column m)] in
    let transcript : SizedWidget := sized (LayoutSize.fill 1) (border_with (theme_border_style_with colors) BorderStyle.rounded (padding 1 0 0 0 inner)) in
    let status : SizedWidget := sized (LayoutSize.fixed 1) (with_style (theme_status_style_with colors mode) (label (status_line m))) in
    let input : SizedWidget := sized (LayoutSize.fixed 3) (padding 1 0 1 0 (text_input m.input)) in
    let head : List SizedWidget := if m.banner then [sized (LayoutSize.fixed Model.banner_height) (banner_widget m)] else List.empty in
    Widget.column (List.append head [transcript, status, input])

/// The transcript panel's content: the window of lines that fit, one
/// `label` row each. `rows - 4` is the fill share's height (`rows`
/// minus the status and input's one row each) minus the border's own
/// top/bottom lines; clamped so a tiny or not-yet-known terminal never
/// asks for a negative slice. Scrolled up (scroll > 0), the panel's
/// first row shows the count indicator.
/// One display row: wrapped text plus the style of its ORIGINAL logical
/// line (a continuation row must not be reclassified by a prefix it
/// happens to start with).
pub struct DisplayRow {
    text : String,
    style : TextStyle,
    /// Empty for an ordinary row (painted as one label); a Markdown row
    /// carries its inline segments so bold/code/link styling survives
    /// wrapping and selection.
    spans : List TextSegment,
}

def mk_row (style : TextStyle) (text : String) : DisplayRow :=
    let r : DisplayRow := { text := text, style := style, spans := List.empty } in
    r

pub def mk_span_row (style : TextStyle) (ss : List TextSegment) : DisplayRow :=
    let text : String := String.concat_all (List.map (fn (s : TextSegment) => s.text) ss) in
    let r : DisplayRow := { text := text, style := style, spans := ss } in
    r

// ── mouse selection ─────────────────────────────────────────────────────
// Coordinates are DISPLAY rows (the painted list, indicator included) and
// CELL columns inside the transcript content. Screen -> display mapping is
// the panel's border (1) plus its left padding (1).

/// The transcript content's first screen row/column. The row depends on
/// the launch banner: while it shows, the panel starts four rows lower.
pub def Model.panel_top : I64 := 1
pub def Model.panel_top_of (m : TuiModel) : I64 :=
    let banner : I64 := if m.banner then Model.banner_height else 0 in
    banner + Model.panel_top
pub def Model.panel_left : I64 := 2

// ── input-box geometry and mouse selection ──────────────────────────────
// The input is `sized (fixed 3) (padding 1 0 1 0 …)`: content starts at
// column 1 and row rows-3, three rows tall (single-line text on the first,
// multiline down to the third). Banner-independent.

pub def Model.input_top (m : TuiModel) : I64 :=
    let y : I64 := m.rows - 3 in
    if y < 0 then 0 else y
pub def Model.input_left : I64 := 1
pub def Model.input_width (m : TuiModel) : I64 :=
    let w : I64 := m.cols - 2 in
    if w < 1 then 1 else w
pub def Model.input_height : I64 := 3

pub def Model.in_input (m : TuiModel) (row : I64) (col : I64) : Bool :=
    let top : I64 := Model.input_top m in
    let right : I64 := Model.input_left + Model.input_width m in
    Bool.and (Bool.not (row < top))
        (Bool.and (row < top + Model.input_height)
            (Bool.and (Bool.not (col < Model.input_left)) (col < right)))

pub def Model.input_press (m : TuiModel) (row : I64) (col : I64) : TuiModel :=
    let rel_row : I64 := row - Model.input_top m in
    let rel_col : I64 := col - Model.input_left in
    let st : InputState := InputState.press m.input (Model.input_width m) Model.input_height rel_row rel_col in
    { m with input := st, sel := Option.none }

pub def Model.input_drag (m : TuiModel) (row : I64) (col : I64) : TuiModel :=
    let rel_row : I64 := row - Model.input_top m in
    let rel_col : I64 := col - Model.input_left in
    { m with input := InputState.drag m.input (Model.input_width m) Model.input_height rel_row rel_col }

pub def Model.clear_input_selection (m : TuiModel) : TuiModel :=
    { m with input := InputState.clear_selection m.input }

/// Whether a drag in the input box is in progress.
pub def Model.input_sel_active (m : TuiModel) : Bool :=
    match m.input.sel {
        Option.none => false,
        Option.some _ => true,
    }

/// Finish a drag in the input: drop the highlight and return its text.
pub def Model.input_release (m : TuiModel) (row : I64) (col : I64) : Pair TuiModel (Option String) :=
    let dragged : TuiModel := Model.input_drag m row col in
    match InputState.finish_selection dragged.input {
        Pair.pair input2 text => Pair.pair { dragged with input := input2 } text,
    }

pub struct TextSelection {
    anchor_row : I64,
    anchor_col : I64,
    focus_row : I64,
    focus_col : I64,
    moved : Bool
}

#[partial]
def row_at (rows : List DisplayRow) (i : I64) : Option DisplayRow :=
    match rows {
        List.empty => Option.none,
        List.cons r rest => if i < 1 then Option.some r else row_at rest (i - 1),
    }

/// The display cell under a mouse report, when it lies inside the panel.
/// `clamp_it` is the drag rule (clamp to the nearest edge); a press must
/// land inside.
#[partial]
def selection_point_in (m : TuiModel) (row : I64) (col : I64) (clamp_it : Bool) : Option (Pair I64 I64) :=
    let n : I64 := rows_len m.rows_cache in
    let w : I64 := Model.content_width m in
    let r0 : I64 := row - Model.panel_top_of m in
    let c0 : I64 := col - Model.panel_left in
    if Bool.or (n < 1) (w < 1)
    then Option.none
    else if clamp_it
    then Option.some (Pair.pair (clamp r0 0 (n - 1)) (clamp c0 0 (w - 1)))
    else if Bool.and (Bool.not (r0 < 0)) (Bool.and (r0 < n) (Bool.and (Bool.not (c0 < 0)) (c0 < w)))
    then Option.some (Pair.pair r0 c0)
    else Option.none

pub def Model.begin_selection (m : TuiModel) (row : I64) (col : I64) : TuiModel :=
    match selection_point_in m row col false {
        Option.none => { m with sel := Option.none },
        Option.some pr => match pr {
            Pair.pair r c =>
                let s : TextSelection := { anchor_row := r, anchor_col := c, focus_row := r, focus_col := c, moved := false } in
                { m with sel := Option.some s },
        },
    }

pub def Model.drag_selection (m : TuiModel) (row : I64) (col : I64) : TuiModel :=
    match m.sel {
        Option.none => m,
        Option.some s => match selection_point_in m row col true {
            Option.none => m,
            Option.some pr => match pr {
                Pair.pair r c =>
                    let moved : Bool := Bool.or s.moved
                        (Bool.or (Bool.not (r == s.anchor_row)) (Bool.not (c == s.anchor_col))) in
                    let s2 : TextSelection := { s with focus_row := r, focus_col := c, moved := moved } in
                    { m with sel := Option.some s2 },
            },
        },
    }

#[terminating]
def trim_end_spaces (s : String) : String :=
    if String.is_empty s
    then s
    else
        let n : I64 := String.length s in
        if String.slice s (n - 1) 1 == " " then trim_end_spaces (String.slice s 0 (n - 1)) else s

/// (forward, top, bottom, left, right): the selection normalized to
/// reading order, right INCLUSIVE.
struct SelSpan {
    forward : Bool,
    top : I64,
    bottom : I64,
    left : I64,
    right : I64
}

def sel_span (s : TextSelection) : SelSpan :=
    let forward : Bool := Bool.or (s.anchor_row < s.focus_row)
        (Bool.and (s.anchor_row == s.focus_row) (Bool.not (s.focus_col < s.anchor_col))) in
    let top : I64 := if forward then s.anchor_row else s.focus_row in
    let bottom : I64 := if forward then s.focus_row else s.anchor_row in
    let left : I64 := if forward then s.anchor_col else s.focus_col in
    let right : I64 := if forward then s.focus_col else s.anchor_col in
    { forward := forward, top := top, bottom := bottom, left := left, right := right }

#[partial]
def selection_text_go (rows : List DisplayRow) (idx : I64) (sp : SelSpan) (width : I64) (acc : List String) : List String :=
    if sp.bottom < idx then List.reverse acc
    else match rows {
        List.empty => List.reverse acc,
        List.cons r rest =>
            if idx < sp.top
            then selection_text_go rest (idx + 1) sp width acc
            else
                let a : I64 := if idx == sp.top then sp.left else 0 in
                let b : I64 := if idx == sp.bottom then sp.right + 1 else width in
                let piece : String := trim_end_spaces (Text.slice_cols r.text a b) in
                selection_text_go rest (idx + 1) sp width (List.cons piece acc),
    }

/// The selected text, or `none` for a plain click (no drag) or an empty
/// selection. Rows join with newlines; per-row trailing padding is
/// trimmed, so dragging past the end of a line does not copy blanks.
pub def Model.selection_text (m : TuiModel) : Option String :=
    match m.sel {
        Option.none => Option.none,
        Option.some s =>
            if Bool.not s.moved
            then Option.none
            else
                let sp : SelSpan := sel_span s in
                let pieces : List String := selection_text_go m.rows_cache 0 sp (Model.content_width m) List.empty in
                let joined : String := List.intercalate "\n" pieces in
                if String.is_empty joined then Option.none else Option.some joined,
    }

/// The half-open cell span to highlight on display row `idx`.
pub def Model.selection_cols (m : TuiModel) (idx : I64) : Option (Pair I64 I64) :=
    match m.sel {
        Option.none => Option.none,
        Option.some s =>
            let sp : SelSpan := sel_span s in
            if Bool.or (idx < sp.top) (sp.bottom < idx)
            then Option.none
            else match row_at m.rows_cache idx {
                Option.none => Option.none,
                Option.some r =>
                    let a : I64 := if idx == sp.top then sp.left else 0 in
                    let b : I64 := if idx == sp.bottom then sp.right + 1 else Model.content_width m in
                    match Text.snap_span r.text a b {
                        Pair.pair sa sb => Option.some (Pair.pair sa sb),
                    },
            },
    }

/// Drop the selection and return its text (the copy is the caller's job:
/// a pure update cannot write the clipboard).
pub def Model.finish_selection (m : TuiModel) : Pair TuiModel (Option String) :=
    let text : Option String := Model.selection_text m in
    Pair.pair { m with sel := Option.none } text

/// The panel's content width: the terminal minus the rounded border (2)
/// and the horizontal padding (2).
pub def Model.content_width (m : TuiModel) : I64 :=
    let w : I64 := m.cols - 4 in
    if w < 1 then 1 else w

#[partial]
def rows_len (rs : List DisplayRow) : I64 :=
    match rs {
        List.empty => 0,
        List.cons _ rest => 1 + rows_len rest,
    }

#[partial]
def drop_rows (n : I64) (rs : List DisplayRow) : List DisplayRow :=
    if n < 1 then rs
    else match rs {
        List.empty => rs,
        List.cons _ rest => drop_rows (n - 1) rest,
    }

/// The last `n` rows (never more than the panel holds).
#[partial]
pub def Model.take_last_rows (n : I64) (rs : List DisplayRow) : List DisplayRow :=
    if n < 1 then List.empty
    else
        let cut : I64 := rows_len rs - n in
        drop_rows (if cut < 0 then 0 else cut) rs

/// The first `n` rows.
#[partial]
def take_rows (n : I64) (rs : List DisplayRow) : List DisplayRow :=
    if n < 1 then List.empty
    else match rs {
        List.empty => List.empty,
        List.cons r rest => List.cons r (take_rows (n - 1) rest),
    }

/// The display bound for one logical line. The stored transcript keeps the
/// full text; only rendering truncates, so one enormous assistant message
/// cannot make every repaint (and every row-count walk) arbitrarily large.
/// The dialog preview has its own, stricter cap.
pub def Model.display_cap_bytes : I64 := 262144

/// A UTF-8-safe prefix: `String.slice` answers "" when its end offset is a
/// continuation byte, so back off up to three bytes rather than render a
/// blank line.
#[partial]
def cap_utf8 (s : String) (max : I64) (back : I64) : String :=
    if I64.gt back 3 then ""
    else if I64.lt (max - back) 1 then ""
    else
        let x : String := String.slice s 0 (max - back) in
        if String.is_empty x then cap_utf8 s max (back + 1) else x

#[partial]
def plain_rows (style : TextStyle) (width : I64) (text : String) : List DisplayRow :=
    if String.is_empty text
    then List.singleton (mk_row style "")
    else
        List.flatten (List.map (fn (part : String) =>
            List.map (fn (t : String) => mk_row style t) (wrap_text width part)) (theme_split_lines text))

#[partial]
def plain_line_list (width : I64) (lines : List String) : List DisplayRow :=
    match lines {
        List.empty => List.empty,
        List.cons l rest => List.append (plain_rows style_default width l) (plain_line_list width rest),
    }

def md_span (colors : Bool) (s : Markdown.StyledSpan) : TextSegment :=
    mk_text_segment s.text (theme_markdown_span_style_with colors s.style)

#[partial]
def md_rows_go (colors : Bool) (width : I64) (lines : List Markdown.StyledLine) : List DisplayRow :=
    match lines {
        List.empty => List.empty,
        List.cons l rest =>
            let ss : List TextSegment := List.map (md_span colors) l.spans in
            let wrapped : List (List TextSegment) := Text.wrap_spans width ss in
            let rows : List DisplayRow := List.map (fn (row : List TextSegment) => mk_span_row style_default row) wrapped in
            List.append rows (md_rows_go colors width rest),
    }

/// An assistant Markdown block: parsed once, wrapped with span-aware
/// wrapping. With colors off the same AST flattens to plain lines, so a
/// `--no-color` run shows the same text without the styling.
def markdown_rows (colors : Bool) (width : I64) (text : String) : List DisplayRow :=
    let doc := Markdown.parse text in
    if colors
    then md_rows_go colors width (Markdown.to_lines doc)
    else plain_line_list width (Markdown.to_plain_lines doc)

/// One logical line, split on its own newlines and wrapped. The kind wins
/// over the text: a Markdown block is rendered as Markdown, a thinking
/// row keeps the thinking style, and a plain row falls back to the prefix
/// classification (user wins first).
pub def Model.display_line (colors : Bool) (width : I64) (line : TLine) : List DisplayRow :=
    let style : TextStyle :=
        match line.kind {
            TLineKind.line_thinking => theme_thinking_style_with colors,
            TLineKind.line_markdown => style_default,
            _ => theme_tline_style_with colors line.user line.text,
        } in
    let n : I64 := String.length line.text in
    let truncated : Bool := I64.lt Model.display_cap_bytes n in
    let text : String := if truncated then cap_utf8 line.text Model.display_cap_bytes 0 else line.text in
    let rows : List DisplayRow :=
        match line.kind {
            TLineKind.line_markdown => markdown_rows colors width text,
            _ => plain_rows style width text,
        } in
    if truncated
    then List.append rows [mk_row style "[truncated for display -- full text is in the session history]"]
    else rows

/// Wrap `s` with the DEFAULT style, one row per wrapped part: a dialog
/// body that is prose (a plan, a permission prompt) must not inherit the
/// transcript's line classification -- a plan bullet starting "+ " turned
/// the whole line green, diff colors and all.
pub def Model.display_plain (width : I64) (s : String) : List DisplayRow :=
    let w : I64 := if width < 1 then 1 else width in
    if String.is_empty s
    then List.singleton (mk_row style_default "")
    else List.flatten (List.map (fn (part : String) => List.map (fn (t : String) => mk_row style_default t) (wrap_text w part)) (theme_split_lines s))

#[partial]
pub def Model.rows_of_line (colors : Bool) (width : I64) (line : TLine) : I64 :=
    rows_len (Model.display_line colors width line)

#[partial]
def rows_of_lines (colors : Bool) (width : I64) (lines : List TLine) : I64 :=
    match lines {
        List.empty => 0,
        List.cons l rest => Model.rows_of_line colors width l + rows_of_lines colors width rest,
    }

/// The loaded window: the loaded page (if any) through the tail. Lines
/// before `start` are not on disk yet and render as one blank row each.
pub struct LoadedWindow {
    start : I64,
    lines : List TLine
}

pub def Model.loaded_window (t : Transcript) : LoadedWindow :=
    let start : I64 := match t.page {
        Option.some p => p.start,
        Option.none => t.tail_start,
    } in
    let n : I64 := t.total - start in
    let lw : LoadedWindow := { start := start, lines := Transcript.slice t start (if n < 0 then 0 else n) } in
    lw

/// The loaded window with detail lines hidden unless Ctrl+O asks for
/// them. Detail lines still count in the transcript's total; hiding
/// them only changes the rows and the scroll range.
#[partial]
def shown_lines (show : Bool) (ls : List TLine) : List TLine :=
    if show then ls
    else match ls {
        List.empty => List.empty,
        List.cons l rest =>
            if l.detail then shown_lines show rest
            else List.cons l (shown_lines show rest),
    }

pub def Model.loaded_shown (m : TuiModel) : LoadedWindow :=
    let lw : LoadedWindow := Model.loaded_window m.transcript in
    let lines : List TLine := shown_lines m.show_details lw.lines in
    let lw2 : LoadedWindow := { start := lw.start, lines := lines } in
    lw2

/// The whole loaded window's row count, plus one row per placeholder line
/// before it. This is the scroll clamp's `len`.
pub def Model.row_total_of (m : TuiModel) : I64 :=
    let lw : LoadedWindow := Model.loaded_shown m in
    lw.start + rows_of_lines m.state.colors (Model.content_width m) lw.lines

/// The logical line containing absolute display row `row`.
#[partial]
def first_line_at_row_go (colors : Bool) (width : I64) (lines : List TLine) (idx : I64) (off : I64) (target : I64) : I64 :=
    match lines {
        List.empty => idx,
        List.cons l rest =>
            let n : I64 := Model.rows_of_line colors width l in
            if target < off + n
            then idx
            else first_line_at_row_go colors width rest (idx + 1) (off + n) target,
    }

pub def Model.first_line_at_row (m : TuiModel) (row : I64) : I64 :=
    let lw : LoadedWindow := Model.loaded_shown m in
    if row < lw.start
    then row
    else first_line_at_row_go m.state.colors (Model.content_width m) lw.lines lw.start 0 (row - lw.start)

/// Collect `count` display rows starting at relative row `start` of the
/// loaded lines. Rows of a line taller than the window can start inside a
/// line: the drop is per ROW, which is the whole point of this unit.
#[partial]
def collect_rows_go (colors : Bool) (width : I64) (lines : List TLine) (off : I64) (start : I64) (count : I64) (acc : List DisplayRow) : List DisplayRow :=
    if count < 1 then acc
    else match lines {
        List.empty => acc,
        List.cons l rest =>
            let rows : List DisplayRow := Model.display_line colors width l in
            let n : I64 := rows_len rows in
            let line_end : I64 := off + n in
            if Bool.not (start < line_end)
            then collect_rows_go colors width rest line_end start count acc
            else
                let skip : I64 := if start < off then 0 else start - off in
                let avail : I64 := n - skip in
                let take : I64 := if count < avail then count else avail in
                let picked : List DisplayRow := take_rows take (drop_rows skip rows) in
                collect_rows_go colors width rest line_end start (count - take) (List.append acc picked),
    }

#[partial]
def blank_rows (n : I64) (style : TextStyle) : List DisplayRow :=
    if n < 1 then List.empty
    else List.cons (mk_row style "") (blank_rows (n - 1) style)

/// The display rows the panel shows, top to bottom; when scrolled, the
/// indicator row is prepended and spends one content row.
pub def Model.visible_rows (m : TuiModel) : List DisplayRow :=
    let w : Window := Model.window m in
    let lw : LoadedWindow := Model.loaded_shown m in
    let colors : Bool := m.state.colors in
    let width : I64 := Model.content_width m in
    let gap_total : I64 := if w.start < lw.start then lw.start - w.start else 0 in
    let gap : I64 := if w.count < gap_total then w.count else gap_total in
    let placeholders : List DisplayRow := blank_rows gap (theme_line_style_with colors "") in
    let rel_start : I64 := if w.start < lw.start then 0 else w.start - lw.start in
    let content : List DisplayRow := collect_rows_go colors width lw.lines 0 rel_start (w.count - gap) List.empty in
    let rows : List DisplayRow := List.append placeholders content in
    if w.eff > 0
    then List.cons (mk_row (theme_line_style_with colors (scrolled_indicator m w)) (scrolled_indicator m w)) rows
    else rows

pub def Model.rows_key_of (m : TuiModel) : RowsKey :=
    let pstart : I64 := match m.transcript.page { Option.some p => p.start, Option.none => 0 - 1 } in
    let k : RowsKey := { total := m.transcript.total, tail_start := m.transcript.tail_start,
                         cols := m.cols, rows := m.rows, scroll := m.scroll, page_start := pstart,
                         banner := m.banner, pending := m.turn_pending, details := m.show_details,
                         think_stream := Model.live_thinking_height m, text_stream := Model.live_text_height m } in
    k

def rows_key_eq (a : RowsKey) (b : RowsKey) : Bool :=
    a.total == b.total && a.tail_start == b.tail_start && a.cols == b.cols
        && a.rows == b.rows && a.scroll == b.scroll && a.page_start == b.page_start
        && a.banner == b.banner && a.pending == b.pending && a.details == b.details
        && a.think_stream == b.think_stream && a.text_stream == b.text_stream

/// Recompute the wrapped rows only when the transcript, the viewport or
/// the scroll position actually moved.
pub def Model.refresh_rows (m : TuiModel) : TuiModel :=
    let k : RowsKey := Model.rows_key_of m in
    match m.rows_key {
        Option.some k0 => if rows_key_eq k k0 then m else rebuild_rows m k,
        Option.none => rebuild_rows m k,
    }

def rebuild_rows (m : TuiModel) (k : RowsKey) : TuiModel :=
    let rt : I64 := Model.row_total_of m in
    let scroll2 : I64 := scroll_clamp m.scroll rt (Model.body_height m) in
    let m2 : TuiModel := { m with row_total := rt, scroll := scroll2, sel := Option.none, rows_cache := List.empty, rows_key := Option.some k } in
    let rows : List DisplayRow := Model.visible_rows m2 in
    { m2 with rows_cache := rows }

/// The rows to paint (the cache `refresh_rows` keeps current).
pub def Model.display_rows (m : TuiModel) : List DisplayRow :=
    m.rows_cache

pub def Model.display_row_widget (r : DisplayRow) : SizedWidget :=
    let base : Widget :=
        match r.spans {
            List.empty => label r.text,
            List.cons _ _ => spans r.spans,
        } in
    sized (LayoutSize.fixed 1) (with_style r.style base)

/// A span-row selection: head/mid/tail spans, the middle reversed in place.
/// The plain-row path stays text-based so it keeps its exact cell padding.
def selected_span_row (r : DisplayRow) (a : I64) (b : I64) : SizedWidget :=
    let total : I64 := Text.width r.text in
    let mw : I64 := if b < a then 0 else b - a in
    let head : List TextSegment := Text.slice_spans r.spans 0 a in
    let mid0 : List TextSegment := Text.slice_spans r.spans a b in
    let tail : List TextSegment := Text.slice_spans r.spans b total in
    let midw : I64 := Text.width_spans mid0 in
    let pad : I64 := if mw < midw then 0 else mw - midw in
    let mid : List TextSegment :=
        List.append (List.map (fn (s : TextSegment) => mk_text_segment s.text { s.style with reverse := true }) mid0)
            (if pad < 1 then List.empty else [mk_text_segment (String.repeat " " pad) { r.style with reverse := true }]) in
    let hw : I64 := Text.width_spans head in
    let tw : I64 := Text.width_spans tail in
    let p1 : List SizedWidget :=
        if hw < 1 then List.empty
        else List.cons (sized (LayoutSize.fixed hw) (with_style r.style (spans head))) List.empty in
    let p2 : List SizedWidget :=
        if mw < 1 then List.empty
        else List.cons (sized (LayoutSize.fixed mw) (with_style r.style (spans mid))) List.empty in
    let p3 : List SizedWidget :=
        if tw < 1 then List.empty
        else List.cons (sized (LayoutSize.fixed tw) (with_style r.style (spans tail))) List.empty in
    let parts : List SizedWidget := List.append p1 (List.append p2 p3) in
    match parts {
        List.empty => Model.display_row_widget r,
        List.cons _ _ => sized (LayoutSize.fixed 1) (Widget.row parts),
    }

/// One row split into head / selected middle / tail, so the selection is
/// reverse video on exactly the chosen cells. Fixed widths come from
/// `Text.width`, never from byte length.
pub def Model.display_row_widget_selected (m : TuiModel) (idx : I64) (r : DisplayRow) : SizedWidget :=
    match Model.selection_cols m idx {
        Option.none => Model.display_row_widget r,
        Option.some pr => match pr {
            Pair.pair a b =>
                match r.spans {
                    List.cons _ _ => selected_span_row r a b,
                    List.empty =>
                        let total : I64 := Text.width r.text in
                        let head : String := Text.slice_cols r.text 0 a in
                        let mid : String := Text.padded_slice_cols r.text a b in
                        let tail : String := Text.slice_cols r.text b total in
                        let hw : I64 := Text.width head in
                        let mw : I64 := if b < a then 0 else b - a in
                        let tw : I64 := Text.width tail in
                        let base : TextStyle := r.style in
                        let sel : TextStyle := { base with reverse := true } in
                        let p1 : List SizedWidget :=
                            if hw < 1 then List.empty
                            else List.cons (sized (LayoutSize.fixed hw) (with_style r.style (label head))) List.empty in
                        let p2 : List SizedWidget :=
                            if mw < 1 then List.empty
                            else List.cons (sized (LayoutSize.fixed mw) (with_style sel (label mid))) List.empty in
                        let p3 : List SizedWidget :=
                            if tw < 1 then List.empty
                            else List.cons (sized (LayoutSize.fixed tw) (with_style r.style (label tail))) List.empty in
                        let parts : List SizedWidget := List.append p1 (List.append p2 p3) in
                        match parts {
                            List.empty => Model.display_row_widget r,
                            List.cons _ _ => sized (LayoutSize.fixed 1) (Widget.row parts),
                        },
                },
        },
    }

#[partial]
def transcript_row_widgets (m : TuiModel) (rows : List DisplayRow) (i : I64) : List SizedWidget :=
    match rows {
        List.empty => List.empty,
        List.cons r rest => List.cons (Model.display_row_widget_selected m i r) (transcript_row_widgets m rest (i + 1)),
    }

def transcript_column (m : TuiModel) : Widget :=
    let body : List SizedWidget := transcript_row_widgets m (Model.display_rows m) 0 in
    // The live row is painted AFTER the cached rows (it is not part of
    // them), so ticks update it without re-wrapping the transcript.
    if m.turn_pending
    then
        let thinking : List SizedWidget :=
            List.map (fn (r : DisplayRow) => Model.display_row_widget r) (Model.live_thinking_rows m) in
        let answer : List SizedWidget :=
            List.map (fn (r : DisplayRow) => Model.display_row_widget r) (Model.live_text_rows m) in
        Widget.column (List.append body
            (List.append thinking (List.append answer [Model.display_row_widget (Model.live_row m)])))
    else Widget.column body

/// The TURN's spend the live row shows: the cumulative report from
/// `on_usage` minus the submit-time baseline. Zero until the first model
/// call reports.
pub def Model.thinking_spent (m : TuiModel) : Usage :=
    match m.live_spent {
        Option.some u => match m.live_base {
            Option.some base => Usage.delta u base,
            Option.none => u,
        },
        Option.none => usage_zero,
    }

/// `| thinking 3.4s · ↑1.2k ↓345`, or `| stopping…` once Esc asked the
/// turn to stop (the fiber ends at its next step boundary).
pub def Model.thinking_text (m : TuiModel) : String :=
    if m.stop_requested
    then String.concat (spinner_glyph m.spinner_frame) " stopping…"
    else
        let u : Usage := Model.thinking_spent m in
        let tail : String := String.concat (format_elapsed m.spinner_frame)
            (String.concat " · ↑"
                (String.concat (format_tokens u.input_tokens)
                    (String.concat " ↓" (format_tokens u.output_tokens)))) in
        let mid : String := String.concat (Model.live_phase m) (String.concat " " tail) in
        String.concat (spinner_glyph m.spinner_frame) (String.concat " " mid)

/// What the live line says the turn is doing: the dispatching tool,
/// else "responding" once assistant text has streamed, else
/// "thinking".
pub def Model.live_phase (m : TuiModel) : String :=
    match m.live_activity {
        Option.some name => String.concat "running " name,
        Option.none =>
            if String.is_empty m.live_text then "thinking" else "responding",
    }

/// The thinking line under the last prompt, clipped to the content width.
pub def Model.live_row (m : TuiModel) : DisplayRow :=
    let style : TextStyle := theme_running_style_with m.state.colors in
    let text : String := Text.take_width (Model.thinking_text m) (Model.content_width m) in
    mk_row style text

/// The absolute ROW window the panel shows. `eff` is the clamped scroll
/// in rows; the scrolled panel spends ONE row on the indicator, so the
/// content window is `panel_height - 1` rows ending `eff` rows above the
/// bottom. `first_line` is the logical transcript line at the window top
/// (placeholders count one row per line, so it is also the count of lines
/// still above when the window starts in the not-yet-loaded prefix).
pub struct Window {
    start : I64,
    count : I64,
    eff : I64,
    first_line : I64,
}

pub def Model.window (m : TuiModel) : Window :=
    let total : I64 := m.row_total in
    let eff : I64 := scroll_clamp m.scroll total (Model.body_height m) in
    let h : I64 := if eff > 0 then Model.body_height m - 1 else Model.body_height m in
    let endp : I64 := total - eff in
    let start : I64 := if endp - h < 0 then 0 else endp - h in
    let count : I64 := if endp - start < 0 then 0 else endp - start in
    let w : Window := { start := start, count := count, eff := eff, first_line := Model.first_line_at_row m start } in
    w

/// The window's top still needs a page when it is above the loaded tail
/// and above the loaded page (if any). A page always reaches the tail, so
/// covering `first_line` is enough.
pub def Model.needs_page (m : TuiModel) (w : Window) : Bool :=
    let ts : I64 := m.transcript.tail_start in
    if Bool.not (w.first_line < ts) then false
    else match m.transcript.page {
        Option.none => true,
        Option.some p => if w.first_line < p.start then true else false,
    }

/// The range to load: one page ending at the top of the tail, or above
/// the loaded page when the window has scrolled past that.
pub def Model.page_request (m : TuiModel) (w : Window) : Option (Pair I64 I64) :=
    let upto : I64 := match m.transcript.page {
        Option.none => m.transcript.tail_start,
        Option.some p => p.start,
    } in
    let req_start : I64 := if upto - Store.page_lines < 0 then 0 else upto - Store.page_lines in
    if Bool.not (req_start < upto)
    then Option.none
    else Option.some (Pair.pair req_start (upto - req_start))

/// The indicator row: a page-read failure replaces the line count while
/// the window still cannot be covered (otherwise the count is the truth).
def scrolled_indicator (m : TuiModel) (w : Window) : String :=
    if Model.needs_page m w then indicator_or_error m w.first_line else scroll_indicator w.first_line

def indicator_or_error (m : TuiModel) (n : I64) : String :=
    match m.transcript.page_error {
        Option.some e => String.concat "page load failed: " e,
        Option.none => scroll_indicator n,
    }

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
    let banner : I64 := if m.banner then Model.banner_height else 0 in
    let h := m.rows - 6 - banner in
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
    else 1 + Model.live_thinking_height m + Model.live_text_height m

/// The most reasoning / answer bytes painted: bounds on the per-tick wrap.
pub def Model.live_thinking_cap_bytes : I64 := 4096
pub def Model.live_stream_cap_bytes : I64 := 8192

/// The rows the two blocks share, leaving one transcript row. The spinner
/// spends one row of its own, so the panel never overflows.
def live_content_cap (m : TuiModel) : I64 :=
    let p : I64 := panel_height m in
    if I64.lt p 2 then 0 else p - 1

pub def Model.live_thinking_cap (m : TuiModel) : I64 :=
    let c : I64 := live_content_cap m in
    c / 2

pub def Model.live_text_cap (m : TuiModel) : I64 :=
    let c : I64 := live_content_cap m in
    c - (c / 2)

/// A tail slice that never starts mid-UTF-8: `String.slice` can answer
/// "" at a continuation boundary, so back off up to three bytes.
#[partial]
def tail_safe (text : String) (start : I64) (back : I64) : String :=
    let n : I64 := String.length text in
    if I64.gt back 3i64 then ""
    else if I64.lt (n - start - back) 1i64 then ""
    else
        let s : String := String.slice text (start + back) (n - start - back) in
        if String.is_empty s then tail_safe text start (back + 1i64) else s

def tail_bytes (text : String) (cap : I64) : String :=
    let n : I64 := String.length text in
    if I64.gt n cap then tail_safe text (n - cap) 0i64 else text

pub def Model.live_thinking_source (m : TuiModel) : String :=
    tail_bytes m.live_thinking Model.live_thinking_cap_bytes

pub def Model.live_text_source (m : TuiModel) : String :=
    let t : String := tail_bytes m.live_text Model.live_stream_cap_bytes in
    if String.is_empty t then "" else String.concat t "▌"

#[partial]
def rows_drop (n : I64) (rs : List DisplayRow) : List DisplayRow :=
    if n < 1i64 then rs
    else match rs {
        List.empty => rs,
        List.cons _ rest => rows_drop (n - 1i64) rest,
    }

#[partial]
def wrap_plain_rows (style : TextStyle) (width : I64) (src : String) : List DisplayRow :=
    List.flatten (List.map (fn (part : String) =>
        List.map (fn (t : String) => mk_row style t) (wrap_text width part)) (theme_split_lines src))

/// Reasoning: dim magenta, its own byte and row budget.
pub def Model.live_thinking_rows (m : TuiModel) : List DisplayRow :=
    let src : String := Model.live_thinking_source m in
    if String.is_empty src then List.empty
    else
        let all : List DisplayRow := wrap_plain_rows (theme_thinking_style_with m.state.colors) (Model.content_width m) src in
        let n : I64 := rows_len all in
        let cap : I64 := Model.live_thinking_cap m in
        if I64.gt n cap then rows_drop (n - cap) all else all

/// The answer: rendered as Markdown while it streams (the parser is total,
/// so an unfinished fence or list is literal text until it closes).
pub def Model.live_text_rows (m : TuiModel) : List DisplayRow :=
    let src : String := Model.live_text_source m in
    if String.is_empty src then List.empty
    else
        let all : List DisplayRow := markdown_rows m.state.colors (Model.content_width m) src in
        let n : I64 := rows_len all in
        let cap : I64 := Model.live_text_cap m in
        if I64.gt n cap then rows_drop (n - cap) all else all

pub def Model.live_thinking_height (m : TuiModel) : I64 :=
    rows_len (Model.live_thinking_rows m)

pub def Model.live_text_height (m : TuiModel) : I64 :=
    rows_len (Model.live_text_rows m)

/// Both live blocks together (the historical name tests use).
pub def Model.live_stream_height (m : TuiModel) : I64 :=
    Model.live_thinking_height m + Model.live_text_height m

// ── the scrollbar ──────────────────────────────────────────────────────
// The bar lives in the transcript panel's rightmost cell: the old right
// padding column, so `content_width` (cols - 4) is unchanged. It covers
// only the transcript viewport (`body_height`), never the live rows.

pub def Model.scrollbar_visible (m : TuiModel) : Bool :=
    let h : I64 := Model.body_height m in
    let no_picker : Bool := match m.picker { Option.none => true, Option.some _ => false } in
    Bool.and no_picker (Bool.and (I64.lt 1 h) (I64.lt h m.row_total))

def scrollbar_room (m : TuiModel) : I64 :=
    let h : I64 := Model.body_height m in
    if I64.lt m.row_total (h - 1) then 0 else m.row_total - (h - 1)

/// `(top, length)` in panel-relative rows; none when not scrollable.
pub def Model.scrollbar_thumb (m : TuiModel) : Option (Pair I64 I64) :=
    if Bool.not (Model.scrollbar_visible m)
    then Option.none
    else
        let h : I64 := Model.body_height m in
        let total : I64 := if I64.lt m.row_total 1 then 1 else m.row_total in
        let w : Window := Model.window m in
        let eff : I64 := w.eff in
        let vh : I64 := if I64.gt eff 0 then h - 1 else h in
        let len0 : I64 := (vh * h) / total in
        let len : I64 := if I64.lt len0 1 then 1 else if I64.gt len0 h then h else len0 in
        let room : I64 := scrollbar_room m in
        if I64.lt room 1
        then Option.some (Pair.pair (h - len) len)
        else
            let span : I64 := h - len in
            let off : I64 := if I64.lt span 1 then 0 else (eff * span) / room in
            Option.some (Pair.pair (span - off) len)

pub def Model.scrollbar_hit (m : TuiModel) (row : I64) (col : I64) : Bool :=
    let h : I64 := Model.body_height m in
    Bool.and (I64.lt 4 m.cols)
        (Bool.and (I64.beq col (m.cols - 2))
        (Bool.and (Model.scrollbar_visible m)
            (Bool.and (Bool.not (I64.lt row (Model.panel_top_of m)))
                (I64.lt row (Model.panel_top_of m + h)))))

/// Where a pointer row puts the scroll for a grab offset.
def scrollbar_scroll_for (m : TuiModel) (row : I64) (grab : I64) : I64 :=
    let h : I64 := Model.body_height m in
    match Model.scrollbar_thumb m {
        Option.none => m.scroll,
        Option.some pr => match pr {
            Pair.pair top len =>
                let span : I64 := h - len in
                let rel : I64 := row - Model.panel_top_of m in
                let target_top : I64 := clamp (rel - grab) 0 span in
                if I64.lt span 1
                then 0
                else (span - target_top) * scrollbar_room m / span,
        },
    }

pub def Model.scroll_to (m : TuiModel) (target : I64) : TuiModel :=
    let m2 : TuiModel := { m with scroll := scroll_clamp target m.row_total (Model.body_height m) } in
    Model.refresh_rows m2

pub def Model.scrollbar_press (m : TuiModel) (row : I64) : TuiModel :=
    match Model.scrollbar_thumb m {
        Option.none => m,
        Option.some pr => match pr {
            Pair.pair top len =>
                let rel : I64 := row - Model.panel_top_of m in
                let in_thumb : Bool := Bool.and (Bool.not (I64.lt rel top)) (I64.lt rel (top + len)) in
                let grab : I64 := if in_thumb then rel - top else len / 2 in
                let target : I64 := scrollbar_scroll_for m row grab in
                Model.scroll_to { m with scroll_drag := Option.some grab } target,
        },
    }

pub def Model.scrollbar_drag_to (m : TuiModel) (row : I64) : TuiModel :=
    match m.scroll_drag {
        Option.none => m,
        Option.some grab => Model.scroll_to m (scrollbar_scroll_for m row grab),
    }

pub def Model.scrollbar_release (m : TuiModel) : TuiModel :=
    { m with scroll_drag := Option.none }

#[partial]
def scrollbar_rows (m : TuiModel) (i : I64) (h : I64) (top : I64) (len : I64) : List SizedWidget :=
    if I64.lt (h - 1) i
    then List.empty
    else
        let thumb : Bool := Bool.and (Bool.not (I64.lt i top)) (I64.lt i (top + len)) in
        let glyph : String := if thumb then "█" else "│" in
        let style : TextStyle :=
            if thumb then theme_scrollbar_thumb_style_with m.state.colors
            else theme_border_style_with m.state.colors in
        List.cons (sized (LayoutSize.fixed 1) (with_style style (label glyph)))
            (scrollbar_rows m (i + 1) h top len)

pub def Model.scrollbar_column (m : TuiModel) : Widget :=
    match Model.scrollbar_thumb m {
        Option.none => Widget.column List.empty,
        Option.some pr => match pr {
            Pair.pair top len => Widget.column (scrollbar_rows m 0 (Model.body_height m) top len),
        },
    }

/// The scroll state machine: `scroll` counts WRAPPED ROWS above the
/// pinned bottom. The delta moves the window (PageUp/Ctrl+U positive,
/// i.e. older; PageDown negative), clamped at both ends. Ctrl+D is the
/// double-press exit gesture, not a scroll key.
#[partial]
pub def Model.scroll_step (m : TuiModel) (delta : I64) : TuiModel :=
    let m2 : TuiModel := { m with scroll := scroll_clamp (m.scroll + delta) m.row_total (Model.body_height m) } in
    Model.refresh_rows m2

/// A new block of transcript lines: the blank separator row in front
/// (skipped on an empty transcript), and a scrolled view HELD in place
/// -- the scroll grows by the block's WRAPPED ROW count, so the visible
/// rows do not slide (auto-pin only happens when the user was already at
/// the bottom, i.e. scroll = 0: it stays 0 and the tail keeps riding).
#[partial]
pub def Model.append_block (m : TuiModel) (lines : List TLine) : TuiModel :=
    let block : List TLine := Transcript.next_block m.transcript lines in
    let tr2 : Transcript := Transcript.append m.transcript block in
    // The row count is only needed to hold a SCROLLED view in place. A
    // pinned view stays at 0, so the extra wrap of the whole block would
    // be pure waste -- and for one huge message it was a visible freeze.
    let m2 : TuiModel :=
        if m.scroll > 0
        then
            let shown : List TLine := shown_lines m.show_details block in
            let added : I64 := rows_of_lines m.state.colors (Model.content_width m) shown in
            { m with transcript := tr2, scroll := m.scroll + added }
        else { m with transcript := tr2, scroll := 0 } in
    Model.refresh_rows m2

/// A gapless append (the Ctrl+C hint): no separator row, and no scroll
/// adjustment -- the line joins the tail like any other output.
#[partial]
pub def Model.append_lines (m : TuiModel) (lines : List TLine) : TuiModel :=
    let tr2 : Transcript := Transcript.append m.transcript lines in
    let m2 : TuiModel := { m with transcript := tr2 } in
    Model.refresh_rows m2

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
/// prompt (the input box itself is the prompt here). It is STATIC
/// mid-turn: the spinner now lives on the thinking row under the prompt.
pub def status_line (m : TuiModel) : String :=
    Dumb.status_fields m.state

/// The spinner's four frames, cycling on the tick count.
pub def spinner_glyph (frame : I64) : String :=
    let idx : I64 := frame - (frame / 4) * 4 in
    if I64.beq idx 0 then "|"
    else if I64.beq idx 1 then "/"
    else if I64.beq idx 2 then "-"
    else "\\"
