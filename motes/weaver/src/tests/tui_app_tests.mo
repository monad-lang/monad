/// `TuiApp.update`'s pure transitions -- weaver.md Phase 4: typing,
/// Tab-cycling the mode, and what Enter does, all without a terminal.
/// `Cmd.perform`'s action (`run_submitted_line`, the real turn/command
/// IO) is asserted by SHAPE here (it IS a `perform`), never executed --
/// the turn/command machinery itself is shuttle's and `commands.mo`'s
/// own, already pinned by their own test files.
use shuttle::agent {RunState, silent_sleep}
use shuttle::context {usage_zero}
use shuttle::gate {Gate}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use weaver::commands {WeaverState, set_fatal}
use weaver::error {WeaverError}
use weaver::policy {Mode}
use weaver::model {TuiModel, WeaverMsg, init_tui_model}
use weaver::tui_app {TuiApp.update}
use tui::types {Event, Key}
use tui::tui {Cmd}
use std::list {List.length}

// ── The offline state (commands_tests.mo's shape) ───────────────────────

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 8, wire := Wire.mock }

def session_of : Session :=
    { config := mock_config, system_prompt := "test", tools := List.empty, history := List.empty, turns := 0, spent := usage_zero }

def run_of : RunState :=
    { session := session_of, reg := ToolRegistry.empty, turns_left := 10, emit := fn (_ : String) => IO.pure unit, gate := Gate.auto, always := List.empty, retries := 1, sleep_ms := silent_sleep }

def state_of (mode : Mode) : WeaverState :=
    { run := run_of, mode := mode, provider := "mock", budget := 10, mcps := List.empty, quit := false, colors := false }

def model_of (mode : Mode) : TuiModel :=
    init_tui_model (state_of mode) 24 80

def mode_eq (a : Mode) (b : Mode) : Bool :=
    match a {
        Mode.manual => match b { Mode.manual => true, _ => false },
        Mode.plan => match b { Mode.plan => true, _ => false },
        Mode.allow_edit => match b { Mode.allow_edit => true, _ => false },
        Mode.auto => match b { Mode.auto => true, _ => false },
    }

def cmd_is_perform (c : Cmd WeaverMsg) : Bool :=
    match c { Cmd.perform _ => true, _ => false }

def cmd_is_none (c : Cmd WeaverMsg) : Bool :=
    match c { Cmd.none => true, _ => false }

def key_msg (k : Key) : WeaverMsg :=
    WeaverMsg.key_event (Event.key k)

def transcript_contains (needle : String) (lines : List String) : Bool :=
    match lines {
        List.empty => false,
        List.cons l rest => (l == needle) || transcript_contains needle rest,
    }

// ── typing ───────────────────────────────────────────────────────────────

#[test]
def test_char_inserts_into_input : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "h")) {
        Pair.pair m2 cmd => m2.input.value == "h" && cmd_is_none cmd
    }

#[test]
def test_backspace_removes_last_char : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "h")) {
        Pair.pair m2 _ =>
            match TuiApp.update m2 (key_msg Key.backspace) {
                Pair.pair m3 _ => String.is_empty m3.input.value
            }
    }

// ── Tab cycles the mode ──────────────────────────────────────────────────

#[test]
def test_tab_cycles_mode : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg Key.tab) {
        Pair.pair m2 cmd => mode_eq m2.state.mode Mode.plan && cmd_is_none cmd
    }

#[test]
def test_tab_does_not_touch_input : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "x")) {
        Pair.pair m2 _ =>
            match TuiApp.update m2 (key_msg Key.tab) {
                Pair.pair m3 _ => m3.input.value == "x"
            }
    }

// ── Enter ────────────────────────────────────────────────────────────────

#[test]
def test_enter_on_empty_input_is_noop : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg Key.enter) {
        Pair.pair m2 cmd =>
            cmd_is_none cmd && String.is_empty m2.input.value && List.length m2.transcript == 0
    }

#[test]
def test_enter_with_text_echoes_clears_and_performs : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "h")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg Key.enter) {
                Pair.pair m2 cmd =>
                    cmd_is_perform cmd
                        && String.is_empty m2.input.value
                        && transcript_contains "you: h" m2.transcript
            }
    }

// ── resize ───────────────────────────────────────────────────────────────

#[test]
def test_resize_updates_rows_and_cols : Bool :=
    match TuiApp.update (model_of Mode.manual) (WeaverMsg.key_event (Event.resize 40 120)) {
        Pair.pair m2 cmd => m2.rows == 40 && m2.cols == 120 && cmd_is_none cmd
    }

// ── double Ctrl+C exit ───────────────────────────────────────────────────

def cmd_is_quit (c : Cmd WeaverMsg) : Bool :=
    match c { Cmd.quit => true, _ => false }

#[test]
def test_single_ctrl_c_appends_hint_keeps_running : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.ctrl "c")) {
        Pair.pair m2 cmd =>
            cmd_is_none cmd
                && m2.ctrl_c_streak == 1
                && transcript_contains "press Ctrl+C again to exit (or /quit)" m2.transcript
    }

#[test]
def test_double_ctrl_c_quits : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.ctrl "c")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg (Key.ctrl "c")) {
                Pair.pair _ cmd => cmd_is_quit cmd
            }
    }

#[test]
def test_other_key_resets_ctrl_c_streak : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.ctrl "c")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg (Key.char "x")) {
                Pair.pair m2 _ =>
                    match TuiApp.update m2 (key_msg (Key.ctrl "c")) {
                        Pair.pair m3 cmd => cmd_is_none cmd && m3.ctrl_c_streak == 1
                    }
            }
    }

#[test]
def test_resize_resets_ctrl_c_streak : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.ctrl "c")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (WeaverMsg.key_event (Event.resize 40 120)) {
                Pair.pair m2 _ =>
                    match TuiApp.update m2 (key_msg (Key.ctrl "c")) {
                        Pair.pair _ cmd => cmd_is_none cmd
                    }
            }
    }

// ── failures carry their class: the dumb failed_step contract mirrored ──

// A provider-class error is recoverable: the error line lands, the
// session's fatal slot stays empty, no quit.
#[test]
def test_recoverable_turn_fails_keeps_running : Bool :=
    match TuiApp.update (model_of Mode.manual) (WeaverMsg.turn_failed run_of (WeaverError.provider "wire down")) {
        Pair.pair m2 cmd =>
            cmd_is_none cmd
                && Bool.not (fatal_is_some2 m2)
                && transcript_contains "error: provider: wire down" m2.transcript
    }

// A config-class error is fatal: the fatal slot is set (main exits
// 1) and the run ends.
#[test]
def test_fatal_turn_ends_the_tui : Bool :=
    match TuiApp.update (model_of Mode.manual) (WeaverMsg.turn_failed run_of (WeaverError.config "startup misspelled")) {
        Pair.pair m2 cmd => cmd_is_quit cmd && fatal_is_some2 m2
    }

def fatal_is_some2 (m : TuiModel) : Bool :=
    match m.state.fatal { Option.some _ => true, Option.none => false }
