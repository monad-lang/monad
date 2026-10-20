/// The scroll state machine, pure: the clamps (now in WRAPPED ROWS), the
/// stay-put append, the indicator row, and row-accurate reachability for
/// a message taller than the panel. `TuiModel`s are built 24 rows tall,
/// so `panel_height` is 18 (the 3-row input box). Theme tests live in
/// `ui_theme_tests.mo`. Two parser corners worth knowing: an `--` comment
/// line directly after `:=` breaks the parse, and an expression projection
/// `(f x).field` binds looser than `==` -- bind to a `let` first.
use shuttle::agent {RunState, silent_sleep}
use shuttle::context {usage_zero}
use shuttle::gate {Gate}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use weaver::commands {WeaverState}
use weaver::policy {Mode}
use std::map {BTreeMap}
use std::list {List.length}
use tui::text {Text.width}
use weaver::model {
    TuiModel, Window, init_tui_model,
    Model.scroll_step, Model.append_block, Model.window, Model.needs_page,
    Model.page_request, Model.visible_rows, scroll_indicator, panel_height,
    Model.display_rows, Model.content_width, DisplayRow,
}
use weaver::store {TLine, TLine.plain, TranscriptPage, Transcript.with_page}

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 8, wire := Wire.mock }

def session_of : Session :=
    { config := mock_config, system_prompt := "test", tools := List.empty, history := List.empty, turns := 0, spent := usage_zero }

def run_of : RunState :=
    { session := session_of, reg := ToolRegistry.empty, turns_left := 10, emit := fn (_ : String) => IO.pure unit, gate := Gate.auto, always := List.empty, retries := 1, sleep_ms := silent_sleep }

def state_of : WeaverState :=
    { run := run_of, mode := Mode.manual, provider := "mock", budget := 10, mcps := List.empty, keys := BTreeMap.empty, quit := false, colors := false, fatal := Option.none, store := Option.none }

def model_of : TuiModel :=
    let m : TuiModel := init_tui_model state_of 24 80 in
    { m with banner := false }

def nth_line (i : I64) : String := String.concat "l" (I64.to_string i)

/// `l1..lk`.
#[partial]
def lines_up_to (k : I64) (i : I64) : List TLine :=
    if i > k then List.empty else List.cons (TLine.plain (nth_line i)) (lines_up_to k (i + 1))

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
    let m : TuiModel := init_tui_model state_of 24 80 in
    m.banner && panel_height m == 14

#[test]
def test_pinned_shows_the_tail : Bool :=
    let vis := Model.visible_rows (filled 25) in
    let count : I64 := List.length vis in
    first_text_of vis == "l8" && count == 18 && last_text_of vis == "l25"

#[test]
def test_page_up_clamps_to_headroom : Bool :=
    let m := Model.scroll_step (filled 25) 20 in
    m.scroll == 8

#[test]
def test_scroll_clamps_at_top : Bool :=
    let m := Model.scroll_step (Model.scroll_step (filled 25) 5) 999999 in
    m.scroll == 8

#[test]
def test_scroll_clamps_at_zero : Bool :=
    let m := Model.scroll_step (filled 25) (0 - 99) in
    m.scroll == 0

#[test]
def test_tiny_terminal_clamps_to_zero : Bool :=
    let tiny : TuiModel := init_tui_model state_of 5 80 in
    let stepped := Model.scroll_step tiny 1 in
    panel_height tiny == 0 && stepped.scroll == 0

#[test]
def test_indicator_count_is_the_first_line : Bool :=
    scroll_indicator 7 == "7 lines above -- PgDn for latest"

#[test]
def test_scroll_window_shows_indicator_and_stops_a_row_short : Bool :=
    let vis := Model.visible_rows (Model.scroll_step (filled 25) 5) in
    first_text_of vis == "3 lines above -- PgDn for latest" && last_text_of vis == "l20"

#[test]
def test_stay_put_scroll_append_holds_the_visible_top : Bool :=
    let m2 := Model.append_block (Model.scroll_step (filled 25) 5) [TLine.plain (nth_line 26), TLine.plain (nth_line 27)] in
    m2.scroll == 8

#[test]
def test_pinned_append_stays_pinned : Bool :=
    let m2 := Model.append_block (filled 25) [TLine.plain (nth_line 26)] in
    m2.scroll == 0

#[test]
def test_pinned_append_rides_the_tail : Bool :=
    let vis := Model.visible_rows (Model.append_block (filled 25) [TLine.plain (nth_line 26)]) in
    last_text_of vis == "l26"

#[test]
def test_full_scroll_reaches_the_first_line : Bool :=
    let vis := Model.visible_rows (Model.scroll_step (filled 25) 8) in
    match vis {
        List.cons _ rest => first_text_of rest == "l1",
        List.empty => false,
    }

#[test]
def test_end_repins : Bool :=
    let m := Model.scroll_step (Model.scroll_step (filled 25) 5) (0 - 5) in
    m.scroll == 0

// ── the bounded window: overflow and pages ────────────────────────────

#[test]
def test_pinned_tail_after_overflow : Bool :=
    let vis := Model.visible_rows (filled 600) in
    let count : I64 := List.length vis in
    first_text_of vis == "l583" && count == 18 && last_text_of vis == "l600"

#[test]
def test_home_window_precedes_the_tail : Bool :=
    let m := Model.scroll_step (filled 600) 999999 in
    let w : Window := Model.window m in
    let at_top : Bool := w.first_line == 0 in
    at_top && Model.needs_page m w

#[test]
def test_page_request_covers_the_pre_tail : Bool :=
    let m := Model.scroll_step (filled 600) 999999 in
    let w : Window := Model.window m in
    match Model.page_request m w {
        Option.none => false,
        Option.some req => match req { Pair.pair s c => s == 0 && c == 88 },
    }

#[test]
def test_loaded_page_covers_the_top : Bool :=
    let base := filled 600 in
    let tr0 := base.transcript in
    let p : TranscriptPage := { start := 0, lines := lines_up_to 88 1 } in
    let tr := Transcript.with_page tr0 p in
    let m0 : TuiModel := { base with transcript := tr } in
    let m := Model.scroll_step m0 999999 in
    let w : Window := Model.window m in
    let vis := Model.visible_rows m in
    Bool.not (Model.needs_page m w)
        && (match vis { List.cons _ rest => first_text_of rest == "l1", List.empty => false })

#[test]
def test_stay_put_append_holds_the_absolute_top : Bool :=
    let m := Model.scroll_step (filled 600) 5 in
    let before : I64 := m.scroll in
    let w0 : Window := Model.window m in
    let m2 := Model.append_block m [TLine.plain (nth_line 601)] in
    let w2 : Window := Model.window m2 in
    m2.scroll == before + 2 && w2.start == w0.start

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
