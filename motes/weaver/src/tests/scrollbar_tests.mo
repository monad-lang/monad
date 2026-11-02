/// The scrollbar's pure geometry and pointer mapping: visibility, thumb
/// position at both ends, hit-testing the rightmost column, and a press
/// that never starts a text selection.
use shuttle::agent {RunState, silent_sleep, silent_usage, silent_stop}
use shuttle::context {usage_zero}
use shuttle::gate {Gate}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use weaver::commands {WeaverState}
use weaver::policy {Mode}
use std::map {BTreeMap}
use std::list {List.length}
use weaver::ui::banner {Banner.shown, Banner.hidden}
use weaver::model {
    TuiModel, init_tui_model, Model.append_block, Model.body_height,
    Model.content_width, Model.panel_top_of, Model.scroll_to,
    Model.scrollbar_visible, Model.scrollbar_thumb, Model.scrollbar_hit,
    Model.scrollbar_press, Model.scrollbar_drag_to, Model.scrollbar_release,
    Model.row_total_of,
}
use weaver::store {TLine, TLine.plain}

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 8, wire := Wire.mock, thinking := false }

def session_of : Session :=
    { config := mock_config, system_prompt := "test", tools := List.empty, history := List.empty, turns := 0, spent := usage_zero }

def run_of : RunState :=
    { session := session_of, reg := ToolRegistry.empty, turns_left := 10, emit := fn (_ : String) => IO.pure unit, gate := Gate.auto, always := List.empty, retries := 1, sleep_ms := silent_sleep, on_usage := silent_usage, should_stop := silent_stop, stopped := false }

def state_of : WeaverState :=
    { run := run_of, mode := Mode.manual, provider := "mock", budget := 10, context_window := 128000, compact_at := 80, plan := Option.none, last_context := 0, grants := Option.none, workspace_root := Option.none, mcps := List.empty, keys := BTreeMap.empty, catalog := BTreeMap.empty, quit := false, colors := false, fatal := Option.none, store := Option.none }

def model_of : TuiModel :=
    let m : TuiModel := init_tui_model Option.none state_of 24 80 in
    { m with banner := Banner.hidden }

#[partial]
def lines_up_to (k : I64) (i : I64) : List TLine :=
    if i > k then List.empty else List.cons (TLine.plain (String.concat "line " (I64.to_string i))) (lines_up_to k (i + 1))

def filled : TuiModel := Model.append_block model_of (lines_up_to 100 1)

#[test]
def test_scrollbar_hidden_without_overflow : Bool :=
    let m : TuiModel := Model.append_block model_of [TLine.plain "one"] in
    Bool.not (Model.scrollbar_visible m)
    && match Model.scrollbar_thumb m { Option.none => true, Option.some _ => false }

#[test]
def test_content_width_is_unchanged : Bool :=
    Model.content_width filled == 76

#[test]
def test_thumb_is_at_the_bottom_when_pinned : Bool :=
    match Model.scrollbar_thumb filled {
        Option.none => false,
        Option.some pr => match pr {
            Pair.pair top len => I64.gt len 0 && I64.beq (top + len) (Model.body_height filled),
        },
    }

#[test]
def test_thumb_reaches_the_top_at_max_scroll : Bool :=
    let m : TuiModel := Model.scroll_to filled 999999 in
    match Model.scrollbar_thumb m {
        Option.none => false,
        Option.some pr => match pr {
            Pair.pair top _ => I64.beq top 0,
        },
    }

#[test]
def test_hit_test_is_the_last_column_inside_the_panel : Bool :=
    let row : I64 := Model.panel_top_of filled in
    Model.scrollbar_hit filled row 78
    && Bool.not (Model.scrollbar_hit filled row 77)
    && Bool.not (Model.scrollbar_hit filled (row + Model.body_height filled) 78)

#[test]
def test_track_press_jumps_and_starts_a_drag_not_a_selection : Bool :=
    let m : TuiModel := Model.scrollbar_press filled (Model.panel_top_of filled) in
    match m.scroll_drag {
        Option.none => false,
        Option.some _ => m.scroll > 0 && match m.sel { Option.none => true, Option.some _ => false },
    }

#[test]
def test_drag_to_the_bottom_returns_to_the_latest : Bool :=
    let pressed : TuiModel := Model.scrollbar_press filled (Model.panel_top_of filled) in
    let dragged : TuiModel := Model.scrollbar_drag_to pressed (Model.panel_top_of filled + Model.body_height filled - 1) in
    dragged.scroll == 0 && match dragged.scroll_drag { Option.some _ => true, Option.none => false }

#[test]
def test_release_clears_the_drag : Bool :=
    let pressed : TuiModel := Model.scrollbar_press filled (Model.panel_top_of filled) in
    let released : TuiModel := Model.scrollbar_release pressed in
    match released.scroll_drag { Option.none => true, Option.some _ => false }

#[test]
def test_row_total_exceeds_the_viewport : Bool :=
    I64.gt (Model.row_total_of filled) (Model.body_height filled)
