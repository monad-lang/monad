// weaver / pty -- the terminal suite's one test file. The drivers live in
// `weaver::pty::*`; collecting them here builds ONE test binary, where a file
// per driver paid a ~60 s compile each for a few seconds of terminal time.
//
// Gated on `WEAVER_PTY=1` (see `weaver::pty_support`); scripts/ci-weaver-pty.sh
// runs it against a release weaver.
use weaver::pty::async {
    run_async_live_turn_and_completion,
    run_async_one_ctrl_c_mid_turn,
    run_async_double_ctrl_c_mid_turn,
    run_async_esc_stops_turn,
    run_async_overlay_owns_stdin
}
use weaver::pty::base {run_base_initial_frame_overlay_exit}
use weaver::pty::bigplan {run_bigplan_paint_home_dialog_paste}
use weaver::pty::crash {run_crash_detect_and_clean_exit}
use weaver::pty::ctrl_d {run_ctrl_d_single_and_cross_gesture, run_ctrl_d_double_exits}
use weaver::pty::dialogs {
    run_dialog_deny_with_note,
    run_dialog_arrow_approves,
    run_dialog_plan_revise,
    run_dialog_settings_edit,
    run_dialog_open_long_keeps_the_stack_flat
}
use weaver::pty::input {run_input_caret_click_drag}
use weaver::pty::models {run_model_picker_select_and_cancel}
use weaver::pty::processes {run_background_shell_list_and_kill, run_exit_note_mid_turn, run_monitor_refreshes_itself}
use weaver::pty::approvals {run_auto_mode_holds_destructive_commands}
use weaver::pty::todos {run_todo_panel_shows_and_folds}
use weaver::pty::trust {run_trust_asks_records_and_reasks}
use weaver::pty::instructions {run_instructions_note_a_mid_session_edit}
use weaver::pty::shell_wait {run_shell_wait_esc, run_shell_wait_ctrl_b}
use weaver::pty::resize {run_resize_clears_and_rewraps}
use weaver::pty::resume {
    run_resume_picker_lists_current_and_esc,
    run_resume_choose_loads_transcript,
    run_resume_pager
    , run_name_shows_in_the_frame}
use weaver::pty::round2 {run_round2_scroll_multiline_history}
use weaver::pty::selection {run_selection_drag_and_osc52}
use weaver::pty::side {run_side_commands_beside_a_turn}
use weaver::pty::sessions {
    run_sessions_persist_then_resume,
    run_sessions_home_pages_from_disk,
    run_sessions_bracketed_paste_is_one_block,
    run_sessions_no_color,
    run_sessions_big_session_rss
}
use weaver::pty::soak {
    run_soak_long_run_keeps_the_stack_flat,
    run_soak_pending_turn_keeps_rss_flat
}
use weaver::pty::weaver_spike {run_weaver_frame_resize_exit}

#[test]
def test_async_live_turn_and_completion : IO Bool := run_async_live_turn_and_completion

#[test]
def test_async_one_ctrl_c_mid_turn : IO Bool := run_async_one_ctrl_c_mid_turn

#[test]
def test_async_double_ctrl_c_mid_turn : IO Bool := run_async_double_ctrl_c_mid_turn

#[test]
def test_async_esc_stops_turn : IO Bool := run_async_esc_stops_turn

#[test]
def test_async_overlay_owns_stdin : IO Bool := run_async_overlay_owns_stdin

#[test]
def test_base_initial_frame_overlay_exit : IO Bool := run_base_initial_frame_overlay_exit

#[test]
def test_bigplan_paint_home_dialog_paste : IO Bool := run_bigplan_paint_home_dialog_paste

#[test]
def test_crash_detect_and_clean_exit : IO Bool := run_crash_detect_and_clean_exit

#[test]
def test_ctrl_d_single_and_cross_gesture : IO Bool := run_ctrl_d_single_and_cross_gesture

#[test]
def test_ctrl_d_double_exits : IO Bool := run_ctrl_d_double_exits

#[test]
def test_dialog_deny_with_note : IO Bool := run_dialog_deny_with_note

#[test]
def test_dialog_arrow_approves : IO Bool := run_dialog_arrow_approves

#[test]
def test_dialog_plan_revise : IO Bool := run_dialog_plan_revise

#[test]
def test_dialog_settings_edit : IO Bool := run_dialog_settings_edit

#[test]
def test_dialog_open_long_keeps_the_stack_flat : IO Bool := run_dialog_open_long_keeps_the_stack_flat

#[test]
def test_input_caret_click_drag : IO Bool := run_input_caret_click_drag

#[test]
def test_model_picker_select_and_cancel : IO Bool := run_model_picker_select_and_cancel

#[test]
def test_background_shell_list_and_kill : IO Bool := run_background_shell_list_and_kill

#[test]
def test_exit_note_mid_turn : IO Bool := run_exit_note_mid_turn

#[test]
def test_monitor_refreshes_itself : IO Bool := run_monitor_refreshes_itself

#[test]
def test_auto_mode_holds_destructive_commands : IO Bool := run_auto_mode_holds_destructive_commands

#[test]
def test_todo_panel_shows_and_folds : IO Bool := run_todo_panel_shows_and_folds

#[test]
def test_resize_clears_and_rewraps : IO Bool := run_resize_clears_and_rewraps

#[test]
def test_resume_picker_lists_current_and_esc : IO Bool := run_resume_picker_lists_current_and_esc

#[test]
def test_resume_choose_loads_transcript : IO Bool := run_resume_choose_loads_transcript

#[test]
def test_resume_pager : IO Bool := run_resume_pager

#[test]
def test_round2_scroll_multiline_history : IO Bool := run_round2_scroll_multiline_history

#[test]
def test_selection_drag_and_osc52 : IO Bool := run_selection_drag_and_osc52

#[test]
def test_sessions_persist_then_resume : IO Bool := run_sessions_persist_then_resume

#[test]
def test_sessions_home_pages_from_disk : IO Bool := run_sessions_home_pages_from_disk

#[test]
def test_sessions_bracketed_paste_is_one_block : IO Bool :=
    run_sessions_bracketed_paste_is_one_block

#[test]
def test_sessions_no_color : IO Bool := run_sessions_no_color

#[test]
def test_sessions_big_session_rss : IO Bool := run_sessions_big_session_rss

#[test]
def test_soak_long_run_keeps_the_stack_flat : IO Bool := run_soak_long_run_keeps_the_stack_flat

#[test]
def test_soak_pending_turn_keeps_rss_flat : IO Bool := run_soak_pending_turn_keeps_rss_flat

#[test]
def test_weaver_frame_resize_exit : IO Bool := run_weaver_frame_resize_exit

#[test]
def test_name_shows_in_the_frame : IO Bool := run_name_shows_in_the_frame

#[test]
def test_trust_asks_records_and_reasks : IO Bool := run_trust_asks_records_and_reasks

#[test]
def test_instructions_note_a_mid_session_edit : IO Bool := run_instructions_note_a_mid_session_edit

#[test]
def test_shell_wait_esc_kills_the_command : IO Bool := run_shell_wait_esc

#[test]
def test_shell_wait_ctrl_b_moves_it_to_the_background : IO Bool := run_shell_wait_ctrl_b

#[test]
def test_side_commands_beside_a_turn : IO Bool := run_side_commands_beside_a_turn
