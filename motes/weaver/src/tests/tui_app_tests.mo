/// `TuiApp.update`'s pure transitions -- weaver.md Phase 4: typing,
/// Tab-cycling the mode, and what Enter does, all without a terminal.
/// `Cmd.perform`'s action (`run_submitted_line`, the real turn/command
/// IO) is asserted by SHAPE here (it IS a `perform`), never executed --
/// the turn/command machinery itself is shuttle's and `commands.mo`'s
/// own, already pinned by their own test files.
use shuttle::agent {RunState, silent_sleep, silent_usage, silent_stop}
use shuttle::context {usage_zero}
use shuttle::message {Usage}
use shuttle::gate {Gate}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use weaver::commands {WeaverState, Effect, TranscriptChange, set_fatal}
use weaver::error {WeaverError}
use weaver::policy {Mode}
use weaver::model {
    TuiModel, WeaverMsg, LiveDelta, DisplayRow, init_tui_model, Model.append_block,
    Model.scroll_step, Model.display_rows, Model.thinking_text,
    PickerState, Picker.count, Picker.selected_model, Picker.init, Picker.move,
    Picker.window_offset, Picker.visible,
}
use weaver::overlay {OverlayState}
use weaver::store {StoreState, TLine, TLine.plain, TranscriptPage}
use std::path {Path, Path.of}
use std::map {Map, BTreeMap}
use weaver::tui_app {TuiApp.update}
use tui::types {Event, Key}
use tui::tui {Cmd}
use std::list {List.length}

// ── The offline state (commands_tests.mo's shape) ───────────────────────

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 8, wire := Wire.mock, thinking := false }

def session_of : Session :=
    { config := mock_config, system_prompt := "test", tools := List.empty, history := List.empty, turns := 0, spent := usage_zero }

def run_of : RunState :=
    { session := session_of, reg := ToolRegistry.empty, turns_left := 10, emit := fn (_ : String) => IO.pure unit, gate := Gate.auto, always := List.empty, retries := 1, sleep_ms := silent_sleep, on_usage := silent_usage, should_stop := silent_stop, stopped := false }

def state_of (mode : Mode) : WeaverState :=
    { run := run_of, mode := mode, provider := "mock", budget := 10, context_window := 128000, compact_at := 80, mcps := List.empty, keys := BTreeMap.empty, catalog := BTreeMap.empty, quit := false, colors := false, fatal := Option.none, store := Option.none }

def model_of (mode : Mode) : TuiModel :=
    let m : TuiModel := init_tui_model Option.none (state_of mode) 24 80 in
    { m with banner := false }

def mode_eq (a : Mode) (b : Mode) : Bool :=
    match a {
        Mode.manual => match b { Mode.manual => true, _ => false },
        Mode.plan => match b { Mode.plan => true, _ => false },
        Mode.allow_edit => match b { Mode.allow_edit => true, _ => false },
        Mode.auto => match b { Mode.auto => true, _ => false },
    }

def cmd_is_perform (c : Cmd WeaverMsg) : Bool :=
    match c { Cmd.perform_async _ => true, _ => false }

def cmd_is_none (c : Cmd WeaverMsg) : Bool :=
    match c { Cmd.none => true, _ => false }

def key_msg (k : Key) : WeaverMsg :=
    WeaverMsg.key_event (Event.key k)

def transcript_contains (needle : String) (lines : List TLine) : Bool :=
    match lines {
        List.empty => false,
        List.cons l rest => (l.text == needle) || transcript_contains needle rest,
    }

def transcript_user_contains (needle : String) (lines : List TLine) : Bool :=
    match lines {
        List.empty => false,
        List.cons l rest =>
            (Bool.and (l.text == needle) l.user) || transcript_user_contains needle rest,
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
            cmd_is_none cmd && String.is_empty m2.input.value && List.length m2.transcript.tail == 0
    }

#[test]
def test_enter_with_text_echoes_clears_and_performs : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "h")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg Key.enter) {
                Pair.pair m2 cmd =>
                    cmd_is_perform cmd
                        && String.is_empty m2.input.value
                        && transcript_user_contains "h" m2.transcript.tail
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
                && transcript_contains "press Ctrl+C again to exit (or /quit)" m2.transcript.tail
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

// Ctrl+D is the second exit gesture: same streak rules as Ctrl+C, and
// each gesture arms only itself.
#[test]
def test_single_ctrl_d_appends_hint_keeps_running : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.ctrl "d")) {
        Pair.pair m2 cmd =>
            cmd_is_none cmd
                && m2.ctrl_d_streak == 1
                && m2.ctrl_c_streak == 0
                && transcript_contains "press Ctrl+D again to exit (or /quit)" m2.transcript.tail
    }

#[test]
def test_double_ctrl_d_quits : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.ctrl "d")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg (Key.ctrl "d")) {
                Pair.pair _ cmd => cmd_is_quit cmd
            }
    }

#[test]
def test_ctrl_c_then_ctrl_d_does_not_quit : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.ctrl "c")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg (Key.ctrl "d")) {
                Pair.pair m2 cmd => cmd_is_none cmd && m2.ctrl_d_streak == 1 && m2.ctrl_c_streak == 0
            }
    }

#[test]
def test_ctrl_d_then_ctrl_c_does_not_quit : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.ctrl "d")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg (Key.ctrl "c")) {
                Pair.pair m2 cmd => cmd_is_none cmd && m2.ctrl_c_streak == 1 && m2.ctrl_d_streak == 0
            }
    }

#[test]
def test_other_key_resets_ctrl_d_streak : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.ctrl "d")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg (Key.char "x")) {
                Pair.pair m2 _ =>
                    match TuiApp.update m2 (key_msg (Key.ctrl "d")) {
                        Pair.pair m3 cmd => cmd_is_none cmd && m3.ctrl_d_streak == 1
                    }
            }
    }

#[test]
def test_tick_does_not_reset_ctrl_d_streak : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.ctrl "d")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (WeaverMsg.key_event Event.tick) {
                Pair.pair m2 _ =>
                    match TuiApp.update m2 (key_msg (Key.ctrl "d")) {
                        Pair.pair _ cmd => cmd_is_quit cmd
                    }
            }
    }

// ── the live stream ──────────────────────────────────────────────────────

#[test]
def test_polled_live_delta_appends_streamed_text : Bool :=
    let base0 : TuiModel := model_of Mode.manual in
    let base : TuiModel := { base0 with turn_pending := true, live_seen := 4 } in
    let d : LiveDelta := { text := "he", thinking := "hm", text_seen := 6, thinking_seen := 2, activity := Option.some "read" } in
    match TuiApp.update base (WeaverMsg.polled Option.none Option.none (Option.some d)) {
        Pair.pair m2 _ =>
            m2.live_text == "he" && m2.live_thinking == "hm" && m2.live_seen == 6
                && m2.live_thinking_seen == 2
                && (match m2.live_activity {
                    Option.some n => n == "read",
                    Option.none => false,
                })
    }

#[test]
def test_polled_live_delta_ignored_when_idle : Bool :=
    let d : LiveDelta := { text := "late", thinking := "", text_seen := 4, thinking_seen := 0, activity := Option.none } in
    match TuiApp.update (model_of Mode.manual) (WeaverMsg.polled Option.none Option.none (Option.some d)) {
        Pair.pair m2 _ => String.is_empty m2.live_text
    }

#[test]
def test_turn_end_clears_the_live_stream : Bool :=
    let st : WeaverState := state_of Mode.manual in
    let base0 : TuiModel := model_of Mode.manual in
    let base : TuiModel := { base0 with turn_pending := true, live_text := "partial", live_thinking := "why" } in
    match TuiApp.update base (WeaverMsg.turn_result st.run [] []) {
        Pair.pair m2 _ => String.is_empty m2.live_text && String.is_empty m2.live_thinking
    }

// ── failures carry their class: the dumb failed_step contract mirrored ──

// A provider-class error is recoverable: the error line lands, the
// session's fatal slot stays empty, no quit.
#[test]
def test_recoverable_turn_fails_keeps_running : Bool :=
    match TuiApp.update (model_of Mode.manual) (WeaverMsg.turn_failed run_of (WeaverError.provider "wire down")) {
        Pair.pair m2 cmd =>
            cmd_is_perform_repaint cmd
                && Bool.not (fatal_is_some2 m2)
                && transcript_contains "error: provider: wire down" m2.transcript.tail
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

// ── multiline input + prompt history ─────────────────────────────────────

#[test]
def test_alt_enter_inserts_a_newline : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "a")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg (Key.alt "\n")) {
                Pair.pair m2 _ =>
                    match TuiApp.update m2 (key_msg (Key.char "b")) {
                        Pair.pair m3 _ => m3.input.value == "a\nb"
                    }
            }
    }

// Alt+Enter at the start: the newline is IN the value, Enter still
// submits the whole thing (the box clears, the echo is plain text).
def model_of_step (m : TuiModel) (msg : WeaverMsg) : TuiModel :=
    match TuiApp.update m msg { Pair.pair m2 _ => m2 }

#[test]
def test_multiline_value_routs_single_line_handler : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "a")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg (Key.alt "\n")) {
                Pair.pair m2 _ =>
                    match TuiApp.update m2 (key_msg Key.enter) {
                        Pair.pair m3 cmd =>
                            cmd_is_perform cmd
                                && Bool.not (String.contains (String.trim m3.input.value) "a")
                                && transcript_user_contains "a" m3.transcript.tail
                    }
            }
    }

#[test]
def test_up_on_empty_input_recalls_history : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "h")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg (Key.char "i")) {
                Pair.pair m2 _ =>
                    match TuiApp.update m2 (key_msg Key.enter) {
                        Pair.pair m3 _ =>
                            match TuiApp.update m3 (key_msg Key.up) {
                                Pair.pair m4 cmd =>
                                    cmd_is_none cmd && m4.input.value == "hi" && m4.hist_idx == 0
                            }
                    }
            }
    }

// Recall then down: the live edit (empty box) is back.
#[test]
def test_down_from_history_returns_to_live : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "h")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg Key.enter) {
                Pair.pair m2 _ =>
                    match TuiApp.update m2 (key_msg Key.up) {
                        Pair.pair m3 _ =>
                            match TuiApp.update m3 (key_msg Key.down) {
                                Pair.pair m4 cmd =>
                                    cmd_is_none cmd && String.is_empty m4.input.value && m4.hist_idx == 0 - 1
                            }
                    }
            }
    }

// Only an EMPTY input recalls; a typed value's up-arrow is the
// multiline cursor's (the reconciliation).
#[test]
def test_up_with_text_is_not_history : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "a")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg Key.up) {
                Pair.pair m2 cmd => cmd_is_none cmd && m2.input.value == "a" && m2.hist_idx == 0 - 1
            }
    }

// ── async turns (Phase 12) ───────────────────────────────────────────────

// Enter sets `turn_pending` and fires a `perform_async`; a second Enter
// is refused while pending (turns are serial).
def cmd_be (a : Cmd WeaverMsg) (b : Cmd WeaverMsg) : Bool :=
    match a {
        Cmd.none => match b { Cmd.none => true, _ => false },
        Cmd.perform_async _ => match b { Cmd.perform_async _ => true, _ => false },
        _ => false,
    }

#[test]
def test_enter_forks_the_turn : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "h")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg Key.enter) {
                Pair.pair m2 cmd =>
                    cmd_be cmd (Cmd.perform_async (fn (_ : Unit) => IO.pure unused_placeholder))
                        && m2.turn_pending
            }
    }

// The action's shape placeholder: never executed, only a type anchor for
// the cmd equality above.
def unused_placeholder : WeaverMsg := WeaverMsg.command_failed (WeaverError.config "unused")

#[test]
def test_enter_while_pending_is_refused : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg (Key.char "h")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg Key.enter) {
                Pair.pair m2 _ =>
                    match TuiApp.update m2 (key_msg (Key.char "i")) {
                        Pair.pair m3 _ =>
                            match TuiApp.update m3 (key_msg Key.enter) {
                                // Refused: nothing appends, no echo, and
                                // the typed text STAYS in the box (the
                                // still-open edit survives the turn).
                                Pair.pair m4 cmd => cmd_be cmd Cmd.none && m4.input.value == "i"
                            }
                    }
            }
    }

// Ticks advance the spinner only while a turn is pending, and never
// touch the Ctrl-C streak (the 100 ms frame clock would otherwise make
// the double-press gesture impossible).
#[test]
def test_tick_spins_only_while_pending : Bool :=
    match TuiApp.update (model_of Mode.manual) (WeaverMsg.key_event Event.tick) {
        Pair.pair idle _ =>
            match TuiApp.update (enter_pending idle) (WeaverMsg.key_event Event.tick) {
                Pair.pair spun cmd => spun.spinner_frame == 1 && idle.spinner_frame == 0 && idle.ctrl_c_streak == spun.ctrl_c_streak && cmd_is_inspect cmd
            }
    }

// A pending-turn model: type + enter (the fork fires, pending rides).
def enter_pending (m : TuiModel) : TuiModel :=
    match TuiApp.update m (key_msg (Key.char "h")) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg Key.enter) { Pair.pair m2 _ => m2 }
    }

// The completion clears `turn_pending` (the spinner stops) and repaints
// (the progress fragment's cleanup); a run rides back into the state.
#[test]
def test_turn_result_ends_the_turn : Bool :=
    match TuiApp.update (enter_pending (model_of Mode.manual)) (WeaverMsg.turn_result run_of [TLine.plain "done"] List.empty) {
        Pair.pair m2 cmd =>
            cmd_is_perform_repaint cmd
                && Bool.not m2.turn_pending
                && (match m2.live_spent { Option.none => true, Option.some _ => false })
                && transcript_contains "done" m2.transcript.tail
    }

// A submit starts the live clock at zero and snapshots the spend.
#[test]
def test_enter_resets_the_live_clock : Bool :=
    let m : TuiModel := enter_pending (model_of Mode.manual) in
    m.spinner_frame == 0 && m.scroll == 0
        && (match m.live_spent { Option.some _ => true, Option.none => false })

// The tenth frame arms the 1 Hz usage poll (an inspect, not a repaint).
#[test]
def test_tick_at_ten_polls_usage : Bool :=
    let base : TuiModel := enter_pending (model_of Mode.manual) in
    let m9 : TuiModel := { base with spinner_frame := 9 } in
    match TuiApp.update m9 (WeaverMsg.key_event Event.tick) {
        Pair.pair m10 cmd => m10.spinner_frame == 10 && cmd_is_inspect cmd,
    }

// The usage half of a poll only lands while a turn is pending.
#[test]
def test_live_usage_updates_only_while_pending : Bool :=
    let u : Usage := { input_tokens := 3, output_tokens := 4, cached_tokens := 0 } in
    match TuiApp.update (enter_pending (model_of Mode.manual)) (WeaverMsg.polled (Option.some u) Option.none Option.none) {
        Pair.pair m1 _ =>
            match TuiApp.update (model_of Mode.manual) (WeaverMsg.polled (Option.some u) Option.none Option.none) {
                Pair.pair idle _ =>
                    (match m1.live_spent { Option.some x => x.input_tokens == 3 && x.output_tokens == 4, Option.none => false })
                    && (match idle.live_spent { Option.none => true, Option.some _ => false }),
            },
    }

def cmd_is_inspect (c : Cmd WeaverMsg) : Bool :=
    match c { Cmd.inspect _ => true, _ => false }

// A poll that sees a dialog's `want` marks the overlay open and stops
// tick draws (modal).
#[test]
def test_polled_open_marks_the_overlay : Bool :=
    let st : OverlayState := { want := true, ack := false, seq := 0 } in
    match TuiApp.update (enter_pending (model_of Mode.manual)) (WeaverMsg.polled Option.none (Option.some st) Option.none) {
        Pair.pair m2 cmd => m2.overlay_open && m2.modal && cmd_is_none cmd,
    }

// A close poll clears it and forces the clear+repaint that erases the
// dialog.
#[test]
def test_polled_close_repaints : Bool :=
    let opened : OverlayState := { want := true, ack := true, seq := 0 } in
    let finished : OverlayState := { want := false, ack := false, seq := 1 } in
    match TuiApp.update (enter_pending (model_of Mode.manual)) (WeaverMsg.polled Option.none (Option.some opened) Option.none) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (WeaverMsg.polled Option.none (Option.some finished) Option.none) {
                Pair.pair m2 cmd =>
                    Bool.not m2.overlay_open && Bool.not m2.modal && m2.dialog_seq == 1 && cmd_is_perform_repaint cmd,
            },
    }

// The plan dialog's revise path ends the turn (it used to strand
// modal/turn_pending) and repaints.
#[test]
def test_input_set_ends_the_turn : Bool :=
    match TuiApp.update (enter_pending (model_of Mode.manual)) (WeaverMsg.input_set "fix it") {
        Pair.pair m2 cmd =>
            Bool.not m2.turn_pending && Bool.not m2.modal && cmd_is_perform_repaint cmd
                && m2.input.value == "fix it",
    }

// Esc while a turn runs requests the stop (an inspect that writes the
// signal) and the live row switches to "stopping…".
#[test]
def test_escape_requests_stop_while_pending : Bool :=
    match TuiApp.update (enter_pending (model_of Mode.manual)) (key_msg Key.escape) {
        Pair.pair m2 cmd =>
            m2.stop_requested && cmd_is_inspect cmd
                && String.contains (Model.thinking_text m2) "stopping",
    }

// Esc with nothing to cancel is a no-op.
#[test]
def test_escape_idle_is_a_no_op : Bool :=
    match TuiApp.update (model_of Mode.manual) (key_msg Key.escape) {
        Pair.pair m2 cmd => cmd_is_none cmd && Bool.not m2.stop_requested,
    }

// A stopped turn keeps its partial block and appends `[stopped]`; the
// completion clears the request.
#[test]
def test_stopped_turn_appends_the_line : Bool :=
    let base : RunState := run_of in
    let stopped_run : RunState := { base with stopped := true } in
    match TuiApp.update (enter_pending (model_of Mode.manual))
            (WeaverMsg.turn_result stopped_run [TLine.plain "partial answer"] List.empty) {
        Pair.pair m2 _ =>
            transcript_contains "[stopped]" m2.transcript.tail
                && Bool.not m2.turn_pending
                && Bool.not m2.stop_requested,
    }

// The repaint cmd IS a plain perform (the forced blank repaint).
def cmd_is_perform_repaint (c : Cmd WeaverMsg) : Bool :=
    match c { Cmd.perform _ => true, _ => false }

// ── paging commands (Phase 3) ───────────────────────────────────────────

def test_dir : Path :=
    match Path.of "/tmp/weaver_paging_unit" {
        Result.err _ => Path.path "/tmp",
        Result.ok p => p,
    }

def store_st : Option StoreState :=
    let s : StoreState := { root := Path.path "/tmp", dir := test_dir, id := "s-1" } in
    Option.some s

def state_with_store (mode : Mode) : WeaverState :=
    { (state_of mode) with store := store_st }

#[partial]
def lines_go (i : I64) (n : I64) : List TLine :=
    if n < i then List.empty
    else List.cons (TLine.plain (String.concat "l" (I64.to_string i))) (lines_go (i + 1) n)

def big_model (stored : Bool) : TuiModel :=
    let st : WeaverState := if stored then state_with_store Mode.manual else state_of Mode.manual in
    let m : TuiModel := init_tui_model Option.none st 24 80 in
    Model.append_block { m with banner := false } (lines_go 1 600)

#[test]
def test_home_with_a_store_requests_a_page : Bool :=
    match TuiApp.update (big_model true) (key_msg Key.home) {
        Pair.pair m2 cmd => m2.page_pending && cmd_is_perform_repaint cmd
    }

#[test]
def test_home_without_a_store_is_pure : Bool :=
    match TuiApp.update (big_model false) (key_msg Key.home) {
        Pair.pair m2 cmd => Bool.not m2.page_pending
    }

#[test]
def test_home_without_a_store_has_no_command : Bool :=
    match TuiApp.update (big_model false) (key_msg Key.home) {
        Pair.pair _ cmd => cmd_is_none cmd
    }

#[test]
def test_page_loaded_clears_pending : Bool :=
    match TuiApp.update (big_model true) (key_msg Key.home) {
        Pair.pair m1 _ =>
            let p : TranscriptPage := { start := 0, lines := lines_go 1 17 } in
            match TuiApp.update m1 (WeaverMsg.page_loaded p) {
                Pair.pair m2 _ => Bool.not m2.page_pending,
            }
    }

#[partial]
def row_has (rs : List DisplayRow) (s : String) : Bool :=
    match rs {
        List.empty => false,
        List.cons r rest => Bool.or (r.text == s) (row_has rest s),
    }

/// A page load that EXTENDS the loaded range keeps the same start, so
/// the rows cache must be dropped rather than compared by start alone.
#[test]
def test_page_loaded_refreshes_the_rows : Bool :=
    match TuiApp.update (big_model true) (key_msg Key.home) {
        Pair.pair m1 _ =>
            let p : TranscriptPage := { start := 0, lines := lines_go 1 17 } in
            match TuiApp.update m1 (WeaverMsg.page_loaded p) {
                Pair.pair m2 _ => row_has (Model.display_rows m2) "l1",
            }
    }

/// The same short page twice cannot cover the window; the second load
/// stops (with a visible error) instead of re-requesting it forever.
#[test]
def test_page_load_that_makes_no_progress_stops : Bool :=
    match TuiApp.update (big_model true) (key_msg Key.home) {
        Pair.pair m1 _ =>
            let p : TranscriptPage := { start := 0, lines := lines_go 1 5 } in
            match TuiApp.update m1 (WeaverMsg.page_loaded p) {
                Pair.pair m2 _ =>
                    match TuiApp.update m2 (WeaverMsg.page_loaded p) {
                        Pair.pair m3 cmd =>
                            cmd_is_none cmd
                            && match m3.transcript.page_error { Option.some _ => true, Option.none => false },
                    }
            }
    }

#[test]
def test_state_of_has_no_store : Bool :=
    let st : WeaverState := state_of Mode.manual in
    match st.store { Option.none => true, Option.some _ => false }

#[test]
def test_scroll_keeps_the_store_field : Bool :=
    let m : TuiModel := big_model false in
    let m2 := Model.scroll_step m 5 in
    match m2.state.store { Option.none => true, Option.some _ => false }

#[test]
def test_big_model_state_store : Bool :=
    let m : TuiModel := big_model false in
    match m.state.store { Option.none => true, Option.some _ => false }

// ── bracketed paste ─────────────────────────────────────────────────────

#[test]
def test_paste_fills_the_box_without_submitting : Bool :=
    match TuiApp.update (model_of Mode.manual) (WeaverMsg.key_event (Event.paste "one\ntwo")) {
        Pair.pair m2 cmd => cmd_is_none cmd && m2.input.value == "one\ntwo" && Bool.not m2.turn_pending
    }

// ── the launch banner ───────────────────────────────────────────────────

#[test]
def test_enter_hides_the_banner : Bool :=
    let base : TuiModel := model_of Mode.manual in
    let shown : TuiModel := { base with banner := true } in
    match TuiApp.update shown (key_msg (Key.char "h")) {
        Pair.pair m1 _ => match TuiApp.update m1 (key_msg Key.enter) {
            Pair.pair m2 _ => Bool.not m2.banner,
        },
    }

#[test]
def test_tick_advances_the_banner_sweep : Bool :=
    let base : TuiModel := model_of Mode.manual in
    let shown : TuiModel := { base with banner := true } in
    match TuiApp.update shown (WeaverMsg.key_event Event.tick) {
        Pair.pair m2 _ => m2.banner && m2.banner_frame == 1,
    }

// ── the model picker ───────────────────────────────────────────────────

def picker_models : List String := ["alpha", "beta", "gamma"]

/// A command result carrying a model list: the shape `/model` builds
/// (`command_keep` is what opens the picker).
def picker_command (models : List String) : WeaverMsg :=
    let cat : BTreeMap String (List String) := Map.insert "mock" models BTreeMap.empty in
    let st : WeaverState := { (state_of Mode.manual) with catalog := cat } in
    let e : Effect := {
        state := st,
        output := "models (mock): 3",
        transcript := TranscriptChange.keep,
        picker := Option.some models,
    } in
    WeaverMsg.command_result e

#[test]
def test_command_result_opens_the_picker : Bool :=
    match TuiApp.update (model_of Mode.manual) (picker_command picker_models) {
        Pair.pair m2 _ =>
            match m2.picker {
                Option.some p => Picker.count p == 3 && Picker.selected_model p == "alpha",
                Option.none => false,
            },
    }

#[test]
def test_picker_enter_sets_the_selected_model : Bool :=
    match TuiApp.update (model_of Mode.manual) (picker_command picker_models) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg Key.down) {
                Pair.pair m2 _ =>
                    match TuiApp.update m2 (key_msg Key.enter) {
                        Pair.pair m3 _ =>
                            m3.state.run.session.config.model == "beta"
                                && (match m3.picker {
                                    Option.none => true,
                                    Option.some _ => false,
                                }),
                    },
            },
    }

#[test]
def test_picker_escape_closes_without_changing_the_model : Bool :=
    match TuiApp.update (model_of Mode.manual) (picker_command picker_models) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg Key.escape) {
                Pair.pair m2 _ =>
                    m2.state.run.session.config.model == "mock"
                        && (match m2.picker {
                            Option.none => true,
                            Option.some _ => false,
                        }),
            },
    }

#[test]
def test_picker_swallows_typing : Bool :=
    match TuiApp.update (model_of Mode.manual) (picker_command picker_models) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg (Key.char "x")) {
                Pair.pair m2 _ => m2.input.value == "",
            },
    }

#[test]
def test_picker_move_clamps_at_both_ends : Bool :=
    // A one-item list still reaches both clamped ends; nothing indexes
    // past them.
    let p : PickerState := Picker.init ["only"] "only" in
    let up : PickerState := Picker.move (0i64 - 1i64) 2i64 p in
    let down : PickerState := Picker.move 9i64 2i64 p in
    Picker.selected_model up == "only" && Picker.selected_model down == "only"

#[test]
def test_picker_window_follows_the_selection : Bool :=
    let p : PickerState := Picker.init ["a", "b", "c", "d", "e", "f"] "a" in
    let p2 : PickerState := Picker.move 4i64 2i64 p in
    let vis : List String := Picker.visible 2i64 p2 in
    Picker.selected_model p2 == "e"
        && Picker.window_offset 2i64 p2 == 3i64
        && List.length vis == 2

#[test]
def test_picker_init_misses_the_current_name_without_breaking : Bool :=
    let p : PickerState := Picker.init picker_models "not-listed" in
    Picker.count p == 3 && Picker.selected_model p == "alpha"

#[test]
def test_picker_swallows_ctrl_d : Bool :=
    match TuiApp.update (model_of Mode.manual) (picker_command picker_models) {
        Pair.pair m1 _ =>
            match TuiApp.update m1 (key_msg (Key.ctrl "d")) {
                Pair.pair m2 cmd1 =>
                    match TuiApp.update m2 (key_msg (Key.ctrl "d")) {
                        Pair.pair m3 cmd2 =>
                            cmd_is_none cmd1 && cmd_is_none cmd2 && m3.ctrl_d_streak == 0
                                && (match m3.picker {
                                    Option.some _ => true,
                                    Option.none => false,
                                }),
                    }
            }
    }

#[test]
def test_empty_model_list_opens_no_picker : Bool :=
    match TuiApp.update (model_of Mode.manual) (picker_command []) {
        Pair.pair m2 _ =>
            match m2.picker {
                Option.none => true,
                Option.some _ => false,
            },
    }


