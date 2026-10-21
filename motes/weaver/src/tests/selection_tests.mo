/// Mouse selection, pure: display-row coordinates, wide glyphs, multi-row
/// spans, no-drag clicks, and invalidation when the rows cache rebuilds.
use shuttle::agent {RunState, silent_sleep}
use shuttle::context {usage_zero}
use shuttle::gate {Gate}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use weaver::commands {WeaverState}
use weaver::policy {Mode}
use std::map {BTreeMap}
use weaver::model {
    TuiModel, init_tui_model, Model.append_block, Model.begin_selection,
    Model.drag_selection, Model.finish_selection, Model.selection_text,
    Model.selection_cols, Model.scroll_step, Model.display_rows, DisplayRow,
    Model.input_press, Model.input_drag, Model.input_release, Model.in_input,
}
use weaver::store {TLine, TLine.plain}
use tui::widgets::input {input_state}

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

def plain_lines (ss : List String) : List TLine :=
    match ss {
        List.empty => List.empty,
        List.cons s rest => List.cons (TLine.plain s) (plain_lines rest),
    }

#[partial]
def lines_up_to (k : I64) (i : I64) : List String :=
    if i > k then List.empty else List.cons (String.concat "l" (I64.to_string i)) (lines_up_to k (i + 1))

/// Drag from screen (r0,c0) to (r1,c1) and return the copied text.
def drag_text (m : TuiModel) (r0 : I64) (c0 : I64) (r1 : I64) (c1 : I64) : Option String :=
    let m1 : TuiModel := Model.begin_selection m r0 c0 in
    let m2 : TuiModel := Model.drag_selection m1 r1 c1 in
    match Model.finish_selection m2 {
        Pair.pair _ text => text,
    }

#[test]
def test_drag_selects_a_word : Bool :=
    let m : TuiModel := Model.append_block model_of (plain_lines ["hello world"]) in
    match drag_text m 1 2 1 7 {
        Option.none => false,
        Option.some t => t == "hello",
    }

#[test]
def test_a_click_without_drag_copies_nothing : Bool :=
    let m : TuiModel := Model.append_block model_of (plain_lines ["hello"]) in
    match drag_text m 1 2 1 2 {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_drag_selects_wide_glyphs_whole : Bool :=
    let m : TuiModel := Model.append_block model_of (plain_lines ["日本"]) in
    // 日 occupies cells 0-1, 本 2-3; drag across both.
    match drag_text m 1 2 1 5 {
        Option.none => false,
        Option.some t => t == "日本",
    }

#[test]
def test_drag_across_rows_joins_with_newlines : Bool :=
    let m : TuiModel := Model.append_block model_of (plain_lines ["abc", "def"]) in
    match drag_text m 1 2 2 5 {
        Option.none => false,
        Option.some t => t == "abc\ndef",
    }

#[test]
def test_backwards_drag_normalizes : Bool :=
    let m : TuiModel := Model.append_block model_of (plain_lines ["hello world"]) in
    match drag_text m 1 7 1 2 {
        Option.none => false,
        Option.some t => t == "hello",
    }

#[test]
def test_selection_cols_covers_the_dragged_cells : Bool :=
    let m0 : TuiModel := Model.append_block model_of (plain_lines ["hello"]) in
    let m1 : TuiModel := Model.begin_selection m0 1 2 in
    let m2 : TuiModel := Model.drag_selection m1 1 6 in
    match Model.selection_cols m2 0 {
        Option.none => false,
        Option.some pr => match pr { Pair.pair a b => a == 0 && b == 5 },
    }

/// A click outside the panel clears any prior selection.
#[test]
def test_press_outside_the_panel_clears : Bool :=
    let m0 : TuiModel := Model.append_block model_of (plain_lines ["hello"]) in
    let m1 : TuiModel := Model.begin_selection m0 1 2 in
    let m2 : TuiModel := Model.begin_selection m1 0 0 in
    match Model.selection_text m2 {
        Option.none => true,
        Option.some _ => false,
    }

/// Scrolling rebuilds the rows cache and must drop the selection (its row
/// indices no longer name the same text).
// ── input-box selection ─────────────────────────────────────────────────

def with_input (m : TuiModel) (value : String) : TuiModel :=
    { m with input := input_state value "" }

def input_drag_text (m : TuiModel) (r0 : I64) (c0 : I64) (r1 : I64) (c1 : I64) : Option String :=
    let m1 : TuiModel := Model.input_press m r0 c0 in
    let m2 : TuiModel := Model.input_drag m1 r1 c1 in
    match Model.input_release m2 r1 c1 {
        Pair.pair _ text => text,
    }

#[test]
def test_input_geometry_is_the_bottom_three_rows : Bool :=
    let m : TuiModel := model_of in
    Model.in_input m 21 1 && Model.in_input m 23 78
        && Bool.not (Model.in_input m 20 1)
        && Bool.not (Model.in_input m 21 0)
        && Bool.not (Model.in_input m 21 79)

#[test]
def test_input_drag_copies_the_selection : Bool :=
    match input_drag_text (with_input model_of "hello") 21 1 21 4 {
        Option.some t => t == "hell",
        Option.none => false,
    }

#[test]
def test_input_click_moves_the_caret_without_copying : Bool :=
    let m1 : TuiModel := Model.input_press (with_input model_of "hello") 21 2 in
    match Model.input_release m1 21 2 {
        Pair.pair m2 text => m2.input.cursor == 1
            && (match text { Option.some _ => false, Option.none => true }),
    }

#[test]
def test_input_multiline_drag_joins_with_a_newline : Bool :=
    match input_drag_text (with_input model_of "ab\ncd") 21 2 22 2 {
        Option.some t => t == "b\ncd",
        Option.none => false,
    }

#[test]
def test_input_drag_keeps_a_wide_glyph_whole : Bool :=
    match input_drag_text (with_input model_of "日本") 21 1 21 2 {
        Option.some t => t == "日",
        Option.none => false,
    }

#[test]
def test_scrolling_invalidates_the_selection : Bool :=
    let m0 : TuiModel := Model.append_block model_of (plain_lines (lines_up_to 25 1)) in
    let m1 : TuiModel := Model.begin_selection m0 1 2 in
    let m2 : TuiModel := Model.drag_selection m1 1 4 in
    let m3 : TuiModel := Model.scroll_step m2 1 in
    match Model.selection_text m3 {
        Option.none => true,
        Option.some _ => false,
    }
