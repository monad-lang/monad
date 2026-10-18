/// Phase 11b's scroll state machine, pure: the clamps, the stay-put
/// append, the indicator row. `TuiModel`s are built 24 rows tall, so
/// `panel_height` is 18 (the 3-row input box). (The theme
/// `ui_theme_tests.mo`. Two parser corners worth knowing: an
/// `--` comment line directly after `:=` breaks the parse, and an
/// expression projection `(f x).field` binds looser than `==` -- bind
/// to a `let` first.)
use shuttle::agent {RunState, silent_sleep}
use shuttle::context {usage_zero}
use shuttle::gate {Gate}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use weaver::commands {WeaverState}
use weaver::policy {Mode}
use std::list {List.length}
use weaver::model {TuiModel, init_tui_model, Model.scroll_step, Model.append_block, visible_transcript, panel_height, scroll_indicator}

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 8, wire := Wire.mock }

def session_of : Session :=
    { config := mock_config, system_prompt := "test", tools := List.empty, history := List.empty, turns := 0, spent := usage_zero }

def run_of : RunState :=
    { session := session_of, reg := ToolRegistry.empty, turns_left := 10, emit := fn (_ : String) => IO.pure unit, gate := Gate.auto, always := List.empty, retries := 1, sleep_ms := silent_sleep }

def state_of : WeaverState :=
    { run := run_of, mode := Mode.manual, provider := "mock", budget := 10, mcps := List.empty, quit := false, colors := false }

def model_of : TuiModel := init_tui_model state_of 24 80

def nth_line (i : I64) : String := String.concat "l" (I64.to_string i)

/// `l1..lk`.
#[partial]
def lines_up_to (k : I64) (i : I64) : List String :=
    if i > k then List.empty else List.cons (nth_line i) (lines_up_to k (i + 1))

/// One block of `l1..lk` on an empty transcript (no gap line).
#[partial]
def filled (k : I64) : TuiModel := Model.append_block model_of (lines_up_to k 1)

def first_line_of (lines : List String) : String :=
    match lines { List.cons h _ => h, _ => "" }

/// The LAST line, by recursion.
#[partial]
def last_of (lines : List String) : String :=
    match lines {
        List.empty => "",
        List.cons h t =>
            match t {
                List.empty => h,
                _ => last_of t,
            },
    }

#[test]
def test_panel_height_is_rows_minus_four : Bool :=
    panel_height model_of == 18

#[test]
def test_pinned_shows_the_tail : Bool :=
    let vis := visible_transcript (filled 25) in
    let count : I64 := List.length vis in
    first_line_of vis == "l8" && count == 18 && last_of vis == "l25"

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
def test_indicator_count_is_the_scroll : Bool :=
    scroll_indicator 7 == "7 lines above -- PgDn for latest"

#[test]
def test_scroll_window_shows_indicator_and_stops_a_row_short : Bool :=
    let vis := visible_transcript (Model.scroll_step (filled 25) 5) in
    first_line_of vis == "3 lines above -- PgDn for latest" && last_of vis == "l20"

#[test]
def test_stay_put_scroll_append_holds_the_visible_top : Bool :=
    let m2 := Model.append_block (Model.scroll_step (filled 25) 5) [nth_line 26, nth_line 27] in
    m2.scroll == 8

#[test]
def test_pinned_append_stays_pinned : Bool :=
    let m2 := Model.append_block (filled 25) [nth_line 26] in
    m2.scroll == 0

#[test]
def test_pinned_append_rides_the_tail : Bool :=
    let vis := visible_transcript (Model.append_block (filled 25) [nth_line 26]) in
    last_of vis == "l26"

#[test]
def test_full_scroll_reaches_the_first_line : Bool :=
    let vis := visible_transcript (Model.scroll_step (filled 25) 8) in
    match vis {
        List.cons _ rest => first_line_of rest == "l1",
        List.empty => false,
    }

#[test]
def test_end_repins : Bool :=
    let m := Model.scroll_step (Model.scroll_step (filled 25) 5) (0 - 5) in
    m.scroll == 0