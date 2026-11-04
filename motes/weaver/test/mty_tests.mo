// weaver / mty -- the terminal suite's one test file. The drivers live in
// `weaver::mty::*`; collecting them here builds ONE test binary, where a file
// per driver paid a ~60 s compile each for a few seconds of terminal time.
//
// Gated on `WEAVER_MTY=1` (see `weaver::mty_support`); scripts/ci-weaver-pty.sh
// runs it against a release weaver.
use weaver::mty::async {
    run_async_live_turn_and_completion,
    run_async_one_ctrl_c_mid_turn,
    run_async_double_ctrl_c_mid_turn,
    run_async_esc_stops_turn,
    run_async_overlay_owns_stdin
}
use weaver::mty::base {run_base_initial_frame_overlay_exit}
use weaver::mty::bigplan {run_bigplan_paint_home_dialog_paste}
use weaver::mty::crash {run_crash_detect_and_clean_exit}
use weaver::mty::ctrl_d {run_ctrl_d_single_and_cross_gesture, run_ctrl_d_double_exits}
use weaver::mty::dialogs {
    run_dialog_deny_with_note,
    run_dialog_arrow_approves,
    run_dialog_plan_revise,
    run_dialog_settings_edit,
    run_dialog_open_long_keeps_the_stack_flat
}
use weaver::mty::input {run_input_caret_click_drag}
use weaver::mty::models {run_model_picker_select_and_cancel}
use weaver::mty::processes {run_start_process_list_and_kill}
use weaver::mty::resize {run_resize_clears_and_rewraps}
use weaver::mty::resume {
    run_resume_picker_lists_current_and_esc,
    run_resume_choose_loads_transcript,
    run_resume_pager
}
use weaver::mty::round2 {run_round2_scroll_multiline_history}
use weaver::mty::selection {run_selection_drag_and_osc52}
use weaver::mty::sessions {
    run_sessions_persist_then_resume,
    run_sessions_home_pages_from_disk,
    run_sessions_bracketed_paste_is_one_block,
    run_sessions_no_color,
    run_sessions_big_session_rss
}
use weaver::mty::soak {
    run_soak_long_run_keeps_the_stack_flat,
    run_soak_pending_turn_keeps_rss_flat
}
use weaver::mty::weaver_spike {run_weaver_frame_resize_exit}

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
def test_start_process_list_and_kill : IO Bool := run_start_process_list_and_kill

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
