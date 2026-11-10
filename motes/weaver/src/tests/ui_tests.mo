/// The scroll state machine, pure: the clamps (now in WRAPPED ROWS), the
/// stay-put append, the indicator row, and row-accurate reachability for
/// a message taller than the panel. `TuiModel`s are built 24 rows tall,
/// so `panel_height` is 18 (the 3-row input box). Theme tests live in
/// `ui_theme_tests.mo`. Two parser corners worth knowing: an `--` comment
/// line directly after `:=` breaks the parse, and an expression projection
/// `(f x).field` binds looser than `==` -- bind to a `let` first.
use weaver::todo {TodoItem, TodoStatus}
use shuttle::agent {RunState, silent_sleep, silent_usage, silent_stop, silent_inbox, silent_side_spend}
use shuttle::context {usage_zero}
use shuttle::message {Usage}
use shuttle::gate {Gate}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use weaver::commands {WeaverState}
use weaver::policy {Mode}
use std::map {BTreeMap}
use std::list {List.intercalate}
use tui::text {Text.width}
use weaver::ui::live {LiveModel, LiveView, Live.start, Live.request_stop, Live.status_text, Live.thinking_height, Live.text_height,
    Live.separator_height, Live.rows}
use weaver::ui::rows {DisplayRow, Rows.of_line, Rows.wrap, Rows.cap_bytes, Rows.length}
use weaver::ui::banner {Banner.shown, Banner.hidden}
use weaver::model {
    TuiModel, init_tui_model, Model.todo_rows,
    Model.scroll_step, Model.append_block, Model.pane_view, panel_height,
    Model.display_rows, Model.content_width,
    Model.body_height, Model.live_view, status_line, Model.refresh_rows,
    Model.view, Model.panel_top_of, Model.panel_left,
}
use tui::render {render}
use tui::core {empty_screen, mk_rect, screen_get_cell, style_default}
use tui::types {Screen}
use weaver::ui::pane {
    PaneModel, PaneCache, Window, Pane.window, Pane.needs_page, Pane.page_request, Pane.visible_rows,
    Pane.indicator_text, Pane.row_total_of, Pane.first_line_at_row, Pane.refresh, Pane.reset,
}
use weaver::store {TLine, TLine.plain, TLine.detail_line, Transcript, TranscriptPage, Transcript.with_page}

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 8, wire := Wire.mock, thinking := false }

def session_of : Session :=
    { config := mock_config, system_prompt := "test", tools := List.empty, history := List.empty, turns := 0, spent := usage_zero }

def run_of : RunState :=
    { session := session_of, reg := ToolRegistry.empty, turns_left := 10, emit := fn (_ : String) => IO.pure unit, gate := Gate.auto, always := List.empty, retries := 1, sleep_ms := silent_sleep, on_usage := silent_usage, should_stop := silent_stop, inbox := silent_inbox, side_spend := silent_side_spend, stopped := false }

def state_of : WeaverState :=
    { run := run_of, mode := Mode.manual, provider := "mock", budget := 10, context_window := 128000, compact_at := 80, plan := Option.none, last_context := 0, grants := Option.none, place := Option.none, mcps := List.empty, keys := BTreeMap.empty, catalog := BTreeMap.empty, quit := false, colors := false, fatal := Option.none, name := Option.none, store := Option.none }

def model_of : TuiModel :=
    let m : TuiModel := init_tui_model Option.none state_of 24 80 in
    { m with banner := Banner.hidden }

def visible_of (m : TuiModel) : List DisplayRow := Pane.visible_rows (Model.pane_view m) m.pane

def row_total_of (m : TuiModel) : I64 := Pane.row_total_of (Model.pane_view m) m.pane

def with_transcript (m : TuiModel) (tr : Transcript) : TuiModel :=
    let p : PaneModel := m.pane in
    { m with pane := { p with transcript := tr } }

def nth_line (i : I64) : String := String.concat "l" (I64.to_string i)

/// `l1..lk`.
#[partial]
def lines_up_to (k : I64) (i : I64) : List TLine :=
    if i > k then List.empty else List.cons (TLine.plain (nth_line i)) (lines_up_to k (i + 1))

/// `k` hidden detail lines, as a thinking body writes them.
#[partial]
def detail_up_to (k : I64) (i : I64) : List TLine :=
    if i > k then List.empty
    else List.cons (TLine.detail_line (String.concat "d" (I64.to_string i))) (detail_up_to k (i + 1))

def detail_block (k : I64) : List TLine := detail_up_to k 1

/// One block of `l1..lk` on an empty transcript (no gap line).
#[partial]
def filled (k : I64) : TuiModel := Model.append_block model_of (lines_up_to k 1)

def first_text_of (rows : List DisplayRow) : String :=
    match rows { List.cons h _ => h.text, _ => "" }

/// The LAST row's text, by recursion.
#[partial]
def last_text_of (rows : List DisplayRow) : String :=
    match rows {
        List.empty => "",
        List.cons h t =>
            match t {
                List.empty => h.text,
                _ => last_text_of t,
            },
    }

#[test]
def test_panel_height_is_rows_minus_six : Bool :=
    panel_height model_of == 18

/// The launch banner spends four panel rows while it shows.
#[test]
def test_banner_spends_four_rows : Bool :=
    let m : TuiModel := init_tui_model Option.none state_of 24 80 in
    m.banner.shown && panel_height m == 14

#[test]
def test_pinned_shows_the_tail : Bool :=
    let vis := visible_of (filled 25) in
    let count : I64 := List.length vis in
    first_text_of vis == "l8" && count == 18 && last_text_of vis == "l25"

#[test]
def test_page_up_clamps_to_headroom : Bool :=
    let m := Model.scroll_step (filled 25) 20 in
    m.pane.scroll == 8

#[test]
def test_scroll_clamps_at_top : Bool :=
    let m := Model.scroll_step (Model.scroll_step (filled 25) 5) 999999 in
    m.pane.scroll == 8

#[test]
def test_scroll_clamps_at_zero : Bool :=
    let m := Model.scroll_step (filled 25) (0 - 99) in
    m.pane.scroll == 0

#[test]
def test_tiny_terminal_clamps_to_zero : Bool :=
    let tiny : TuiModel := init_tui_model Option.none state_of 5 80 in
    let stepped := Model.scroll_step tiny 1 in
    panel_height tiny == 0 && stepped.pane.scroll == 0

#[test]
def test_indicator_count_is_the_first_line : Bool :=
    Pane.indicator_text 7 == "7 lines above -- PgDn for latest"

#[test]
def test_scroll_window_shows_indicator_and_stops_a_row_short : Bool :=
    let vis := visible_of (Model.scroll_step (filled 25) 5) in
    first_text_of vis == "3 lines above -- PgDn for latest" && last_text_of vis == "l20"

#[test]
def test_stay_put_scroll_append_holds_the_visible_top : Bool :=
    let m2 := Model.append_block (Model.scroll_step (filled 25) 5) [TLine.plain (nth_line 26), TLine.plain (nth_line 27)] in
    m2.pane.scroll == 8

#[test]
def test_pinned_append_stays_pinned : Bool :=
    let m2 := Model.append_block (filled 25) [TLine.plain (nth_line 26)] in
    m2.pane.scroll == 0

#[test]
def test_pinned_append_rides_the_tail : Bool :=
    let vis := visible_of (Model.append_block (filled 25) [TLine.plain (nth_line 26)]) in
    last_text_of vis == "l26"

#[test]
def test_full_scroll_reaches_the_first_line : Bool :=
    let vis := visible_of (Model.scroll_step (filled 25) 8) in
    match vis {
        List.cons _ rest => first_text_of rest == "l1",
        List.empty => false,
    }

#[test]
def test_end_repins : Bool :=
    let m := Model.scroll_step (Model.scroll_step (filled 25) 5) (0 - 5) in
    m.pane.scroll == 0

// ── the bounded window: overflow and pages ────────────────────────────

#[test]
def test_pinned_tail_after_overflow : Bool :=
    let vis := visible_of (filled 600) in
    let count : I64 := List.length vis in
    first_text_of vis == "l583" && count == 18 && last_text_of vis == "l600"

#[test]
def test_home_window_precedes_the_tail : Bool :=
    let m := Model.scroll_step (filled 600) 999999 in
    let w : Window := Pane.window (Model.pane_view m) m.pane in
    // The window is pinned to the LOADED top (`tail_start`), not to a
    // phantom row 0: unloaded lines have no rows to scroll through.
    let at_loaded_top : Bool := w.first_line == 88 in
    at_loaded_top && Pane.needs_page m.pane w

#[test]
def test_page_request_covers_the_pre_tail : Bool :=
    let m := Model.scroll_step (filled 600) 999999 in
    let w : Window := Pane.window (Model.pane_view m) m.pane in
    match Pane.page_request m.pane {
        Option.none => false,
        Option.some req => match req { Pair.pair s c => s == 0 && c == 88 },
    }

#[test]
def test_loaded_page_covers_the_top : Bool :=
    let base := filled 600 in
    let tr0 := base.pane.transcript in
    let p : TranscriptPage := { start := 0, lines := lines_up_to 88 1 } in
    let tr := Transcript.with_page tr0 p in
    let m0 : TuiModel := with_transcript base tr in
    let m := Model.scroll_step m0 999999 in
    let w : Window := Pane.window (Model.pane_view m) m.pane in
    let vis := visible_of m in
    Bool.not (Pane.needs_page m.pane w)
        && (match vis { List.cons _ rest => first_text_of rest == "l1", List.empty => false })

#[test]
def test_stay_put_append_holds_the_absolute_top : Bool :=
    let m := Model.scroll_step (filled 600) 5 in
    let before : String := first_content_of (visible_of m) in
    let m2 := Model.append_block m [TLine.plain (nth_line 601)] in
    // The tail cap drops the two oldest lines on this append, so the
    // RELATIVE start moves while the content must not: compare the line.
    m2.pane.scroll == 7 && first_content_of (visible_of m2) == before

// ── the scroll space holds only LOADED rows ───────────────────────────
// The unloaded prefix used to count one row per line, so a long session
// scrolled through phantom rows: each step moved almost nothing, and at
// the top the whole pane was blank placeholders. Home/max scroll on an
// overflowing session must paint real loaded lines instead.

/// The first CONTENT row's text (the scrolled indicator is not content).
#[partial]
def first_content_of (rs : List DisplayRow) : String :=
    match rs {
        List.empty => "",
        List.cons r rest =>
            if String.contains r.text "lines above" then first_content_of rest else r.text,
    }

#[partial]
def all_nonempty (rs : List DisplayRow) : Bool :=
    match rs {
        List.empty => true,
        List.cons r rest => Bool.and (Bool.not (String.is_empty r.text)) (all_nonempty rest),
    }

#[test]
def test_home_shows_loaded_lines_not_blank_placeholders : Bool :=
    let vis := visible_of (Model.scroll_step (filled 600) 999999) in
    match vis {
        List.cons _ rest => first_text_of rest == "l89" && all_nonempty vis,
        List.empty => false,
    }

/// Hidden detail lines still COUNT as transcript lines: the indicator is
/// the absolute position, not an index into the visible lines.
#[test]
def test_first_line_counts_hidden_detail_lines : Bool :=
    let details : List TLine := detail_block 40 in
    let m : TuiModel := Model.append_block model_of (List.append details (lines_up_to 20 1)) in
    Pane.first_line_at_row (Model.pane_view m) m.pane 0 == 40

/// Scrolled into a loaded page when the NEXT page lands: the view must
/// still be real lines. The second page used to replace the first, and
/// the first page's range came back as blank placeholder rows.
#[test]
def test_second_page_leaves_no_blank_rows : Bool :=
    let base : TuiModel := Model.scroll_step (filled 1200) 30 in
    let p1 : TranscriptPage := { start := 176, lines := lines_up_to 688 177 } in
    let tr1 : Transcript := Transcript.with_page base.pane.transcript p1 in
    let m1 : TuiModel := with_transcript base tr1 in
    let m2 : TuiModel := Model.scroll_step m1 520 in
    let p2 : TranscriptPage := { start := 0, lines := lines_up_to 176 1 } in
    let tr2 : Transcript := Transcript.with_page m2.pane.transcript p2 in
    let m3 : TuiModel := with_transcript m2 tr2 in
    let m4 : TuiModel := Model.scroll_step m3 17 in
    all_nonempty (visible_of m4)

/// A page arriving above a bottom-anchored view does not move it.
#[test]
def test_loaded_page_above_holds_the_view : Bool :=
    let m := Model.scroll_step (filled 600) 5 in
    let bottom : String := last_text_of (visible_of m) in
    let p : TranscriptPage := { start := 0, lines := lines_up_to 88 1 } in
    let tr : Transcript := Transcript.with_page m.pane.transcript p in
    let m1 : TuiModel := with_transcript m tr in
    let m2 : TuiModel := Model.refresh_rows m1 in
    last_text_of (visible_of m2) == bottom

// ── line wrap ─────────────────────────────────────────────────────────

def rows_fit (rs : List DisplayRow) (w : I64) : Bool :=
    match rs {
        List.empty => true,
        List.cons r rest =>
            let n : I64 := Text.width r.text in
            Bool.and (Bool.not (w < n)) (rows_fit rest w),
    }

#[test]
def test_content_width_is_cols_minus_four : Bool :=
    Model.content_width model_of == 76

#[test]
def test_long_lines_wrap_to_the_panel_width : Bool :=
    let m := Model.append_block model_of [TLine.plain (String.repeat "x" 200)] in
    let rows := Model.display_rows m in
    List.length rows == 3 && rows_fit rows 76

#[test]
def test_wrapped_rows_are_capped_at_the_panel : Bool :=
    let m := Model.append_block model_of (lines_up_to 100 1) in
    let m2 := Model.append_block m [TLine.plain (String.repeat "y" 500)] in
    Bool.not (panel_height m2 < List.length (Model.display_rows m2))

#[test]
def test_scrolled_window_keeps_the_indicator : Bool :=
    let m := Model.scroll_step (filled 30) 5 in
    let rows := Model.display_rows m in
    match rows {
        List.cons first _ => String.contains first.text "lines above" && Bool.not (panel_height m < List.length rows),
        List.empty => false,
    }

/// One 2000-character line wraps to 27 rows (76 + 26*76 + 24). Pinned,
/// the panel shows the LAST 18; at max scroll it shows the FIRST 17.
/// Every row of the message is reachable -- the bug this unit fixes.
// ── the live thinking row ───────────────────────────────────────────────

def live_usage : Usage :=
    { input_tokens := 1234, output_tokens := 345, cached_tokens := 0 }

def live_model : TuiModel :=
    let l0 : LiveModel := Live.start Option.none in
    let live : LiveModel := { l0 with frame := 12, spent := Option.some live_usage } in
    let m : TuiModel := { model_of with turn_pending := true, live := live } in
    m

def with_live (m : TuiModel) (f : LiveModel -> LiveModel) : TuiModel :=
    { m with live := f m.live }

#[test]
def test_live_row_reserves_one_panel_row : Bool :=
    Model.body_height live_model == panel_height live_model - 1
        && Model.body_height model_of == panel_height model_of

#[test]
def test_thinking_text_carries_time_and_tokens : Bool :=
    let lm : TuiModel := live_model in
    let t : String := Live.status_text lm.live in
    String.contains t "thinking" && String.contains t "1.2s"
        && String.contains t "↑1.2k" && String.contains t "↓345"

/// Esc asked the turn to stop: the live row says so instead of the
/// token/time line.
#[test]
def test_thinking_text_says_stopping : Bool :=
    let lm : TuiModel := live_model in
    String.contains (Live.status_text (Live.request_stop lm.live)) "stopping"

#[test]
def test_thinking_text_says_responding_after_streaming : Bool :=
    let lm : TuiModel := live_model in
    let l : LiveModel := { lm.live with text := "hello" } in
    String.contains (Live.status_text l) "responding"

#[test]
def test_thinking_text_names_the_running_tool : Bool :=
    let lm : TuiModel := live_model in
    let l : LiveModel := { lm.live with activity := Option.some "read" } in
    String.contains (Live.status_text l) "running read"

#[test]
def test_live_stream_reserves_rows : Bool :=
    let m : TuiModel := with_live live_model (fn (l : LiveModel) => { l with text := "streamed reply" }) in
    let v : LiveView := Model.live_view m in
    Model.body_height m == panel_height m - 1i64 - Live.thinking_height v m.live - Live.text_height v m.live
        && I64.lt 0 (Live.text_height v m.live)

/// Reasoning and answer both streaming: one rule row parts them, and the
/// body gives it up.
#[test]
def test_live_separator_between_thinking_and_text : Bool :=
    let m : TuiModel := with_live live_model (fn (l : LiveModel) => { l with thinking := "weighing it", text := "the reply" }) in
    let v : LiveView := Model.live_view m in
    let rows : List DisplayRow := Live.rows v m.live in
    Live.separator_height m.live == 1
        && Model.body_height m == panel_height m - 2i64 - Live.thinking_height v m.live - Live.text_height v m.live
        && Rows.length rows == 2i64 + Live.thinking_height v m.live + Live.text_height v m.live

/// Only one of them: no separator.
#[test]
def test_live_no_separator_without_thinking : Bool :=
    let m : TuiModel := with_live live_model (fn (l : LiveModel) => { l with text := "the reply" }) in
    Live.separator_height m.live == 0

#[test]
def test_detail_lines_are_hidden_until_ctrl_o : Bool :=
    let base : TuiModel := Model.append_block model_of [TLine.plain "summary", TLine.detail_line "full output"] in
    let p : PaneModel := base.pane in
    let hidden : TuiModel := { base with pane := { p with details := false } } in
    let opened : TuiModel := { base with pane := { p with details := true } } in
    row_total_of opened == row_total_of hidden + 1i64

/// The status bar is static mid-turn; the spinner lives on the live row.
#[test]
def test_status_line_is_static_mid_turn : Bool :=
    status_line live_model == status_line model_of

/// The live row is painted after the cache, never inside it: ticks must
/// not invalidate (and re-wrap) the transcript.
#[test]
def test_live_row_is_not_in_the_rows_cache : Bool :=
    let idle : TuiModel := Model.append_block model_of [TLine.plain "hello"] in
    let pending : TuiModel := { idle with turn_pending := true } in
    List.length (Model.display_rows pending) == List.length (Model.display_rows idle)

/// The display cap keeps one enormous logical line from making every
/// repaint and row-count walk unbounded; the marker says where the rest is.
#[test]
def test_display_line_caps_an_enormous_line : Bool :=
    let long : String := String.repeat "x" (Rows.cap_bytes + 1) in
    let rows : List DisplayRow := Rows.of_line false 80 (TLine.plain long) in
    match List.reverse rows {
        List.cons last _ => String.contains last.text "truncated for display",
        List.empty => false,
    }

#[test]
def test_a_message_taller_than_the_panel_is_fully_reachable : Bool :=
    let m := Model.append_block model_of [TLine.plain (String.repeat "z" 2000)] in
    let pinned := Model.display_rows m in
    let top := Model.display_rows (Model.scroll_step m 999999) in
    let pinned_first : String := first_text_of pinned in
    let pinned_last : String := last_text_of pinned in
    let top_first : String := first_text_of top in
    let top_last : String := last_text_of top in
    List.length pinned == 18
        && List.length top == 18
        && Text.width pinned_first == 76
        && Text.width pinned_last == 24
        && String.contains top_first "lines above"
        && Text.width top_last == 76

// ── plain dialog bodies ────────────────────────────────────────────────

/// A plan line that looks like a diff row keeps the default style in a
/// plain dialog body: plans are prose, not diffs.
#[test]
def test_display_plain_does_not_classify : Bool :=
    let rows := Rows.wrap style_default 40 "+ not a diff" in
    match rows {
        List.cons r _ => r.style.fg == Option.none && Bool.not r.style.dim,
        List.empty => false,
    }

#[test]
def test_display_plain_wraps_like_a_transcript_line : Bool :=
    Bool.not (I64.lt (List.length (Rows.wrap style_default 4 "abcdefghij")) 3)

/// A colored 24x80 model with one block appended. The render pins need the
/// real palette; `model_of` is colorless (the dumb-mode default).
def colored_model_of (lines : List TLine) : TuiModel :=
    let st : WeaverState := { state_of with colors := true } in
    let m : TuiModel := { (init_tui_model Option.none st 24 80) with banner := Banner.hidden } in
    Model.append_block m lines

/// V1: the panel's frame is dim, the rows inside it are NOT. The panel used
/// to be wrapped in `with_style dim`, and `style_merge` propagates into the
/// whole subtree -- the entire transcript rendered faint, while `--no-color`
/// (which passes the plain style) did not.
#[test]
def test_render_keeps_transcript_rows_undimmed : Bool :=
    let m : TuiModel := colored_model_of [TLine.plain "hello"] in
    let screen : Screen := render (Model.view m) (mk_rect 0 0 80 24) (empty_screen 24 80) in
    let body_dim : Bool := match screen_get_cell screen (Model.panel_top_of m) Model.panel_left {
        Option.some c => c.style.dim,
        Option.none => true,
    } in
    let border_dim : Bool := match screen_get_cell screen 0 0 {
        Option.some c => c.style.dim,
        Option.none => false,
    } in
    Bool.not body_dim && border_dim

// ── the rendered-rows cache ─────────────────────────────────────────────

#[partial]
def joined_texts (rs : List DisplayRow) : String :=
    match rs {
        List.empty => "",
        List.cons r rest => String.concat r.text (String.concat "\n" (joined_texts rest)),
    }

def cache_rows (p : PaneModel) : I64 :=
    match p.cache { Option.some c => c.row_total, Option.none => 0 - 1 }

/// Scrolling slices the cached rows: the window equals a cold rebuild's.
#[test]
def test_scrolled_window_matches_a_cold_rebuild : Bool :=
    let m : TuiModel := Model.scroll_step (Model.scroll_step (filled 600) 40) 7 in
    let p : PaneModel := m.pane in
    let cold : PaneModel := Pane.refresh (Model.pane_view m) { p with cache := Option.none, key := Option.none } in
    joined_texts p.rows == joined_texts cold.rows && Bool.not (String.is_empty (joined_texts p.rows))

/// A scroll-only step keeps the cache: same row total, every loaded line
/// still cached.
#[test]
def test_scroll_keeps_the_cache : Bool :=
    let m0 : TuiModel := filled 300 in
    let m1 : TuiModel := Model.scroll_step m0 25 in
    cache_rows m0.pane == cache_rows m1.pane && cache_rows m1.pane == row_total_of m1

/// An append renders only the new lines; the old rows still read the same.
#[test]
def test_append_reuses_cached_lines : Bool :=
    let m0 : TuiModel := Model.scroll_step (filled 300) 30 in
    let before : String := joined_texts m0.pane.rows in
    let m1 : TuiModel := Model.append_block m0 [TLine.plain "fresh"] in
    joined_texts m1.pane.rows == before && cache_rows m1.pane > cache_rows m0.pane

/// A session switch drops the cache: line indices name another transcript.
#[test]
def test_reset_drops_the_cache : Bool :=
    let m : TuiModel := filled 50 in
    let p2 : PaneModel := Pane.reset m.pane m.pane.transcript in
    match p2.cache { Option.none => true, Option.some _ => false }

// ── the todo panel ──────────────────────────────────────────────────────

def with_todos (unfolded : Bool) : TuiModel :=
    let a : TodoItem := { content := "Read the module", status := TodoStatus.todo_completed, active := "" } in
    let b : TodoItem := { content := "Run the tests", status := TodoStatus.todo_in_progress, active := "Running the tests" } in
    let c : TodoItem := { content := "Commit", status := TodoStatus.todo_pending, active := "" } in
    let m : TuiModel := model_of in
    Model.refresh_rows { m with todos := [a, b, c], todos_open := unfolded }

/// Open, the panel is the summary and one row per item, and the transcript
/// gives up exactly those rows.
#[test]
def test_todo_panel_open : Bool :=
    let m : TuiModel := with_todos true in
    let rows : List String := Model.todo_rows m in
    List.length rows == 4
        && panel_height m == panel_height model_of - 4
        && String.contains (List.intercalate "|" rows) "◐ Running the tests"

/// Folded (Ctrl+T), one summary row; without todos, no panel at all.
#[test]
def test_todo_panel_folded_and_empty : Bool :=
    let m : TuiModel := with_todos false in
    List.length (Model.todo_rows m) == 1
        && String.contains (List.intercalate "|" (Model.todo_rows m)) "todos 1/3"
        && List.is_empty (Model.todo_rows model_of)

// ── the session name ────────────────────────────────────────────────────

#[partial]
def top_row_go (screen : Screen) (col : I64) (acc : String) : String :=
    if Bool.not (col < 80) then acc
    else match screen_get_cell screen 0 col {
        Option.some c => top_row_go screen (col + 1) (String.concat acc c.char),
        Option.none => acc,
    }

/// A named session shows its name in the frame's top edge; an unnamed one
/// keeps the plain edge. The frame costs no extra row either way.
#[test]
def test_session_name_sits_in_the_top_edge : Bool :=
    let plain : TuiModel := colored_model_of [TLine.plain "hello"] in
    let named : TuiModel := { plain with state := { (plain.state) with name := Option.some "fix the flake" } } in
    let s1 : Screen := render (Model.view named) (mk_rect 0 0 80 24) (empty_screen 24 80) in
    let s0 : Screen := render (Model.view plain) (mk_rect 0 0 80 24) (empty_screen 24 80) in
    String.starts_with "\u{256d}\u{2500} fix the flake \u{2500}" (top_row_go s1 0 "")
        && Bool.not (String.contains (top_row_go s0 0 "") "fix")
        && Model.panel_top_of named == Model.panel_top_of plain
