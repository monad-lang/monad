/// Tests for the dialog component (`motes/tui/src/widgets/dialog.mo`):
/// key transitions, the note field, editable values, and the layout's
/// fixed rows.

use lib::widgets::dialog {
    DialogModel, DialogOption, DialogStep, Dialog.make, Dialog.step, Dialog.paste,
    Dialog.note_text, Dialog.with_default, Dialog.apply, Dialog.rows, Dialog.body_rows,
    Dialog.total_rows, Dialog.frame_width, Dialog.frame_height, Dialog.content_width,
    Dialog.frame_width_for, Dialog.frame_height_for,
    Dialog.with_notes, Dialog.clamp_scroll, Dialog.footer_line, ModalState, ModalNext, Modal.fold, Modal.idle, modal_quiet, Dialog.refresh_due,
}
use lib::input {InputReader, input_reader}
use lib::types {Key, Event, MouseEvent, MouseButton}
use lib::widget {SizedWidget}
use lib::core {empty_screen}
use std::list {List.length}

def opt_y : DialogOption := { label := "Approve once", hint := "y", key := "y" }
def opt_a : DialogOption := { label := "Always", hint := "a", key := "a" }
def opt_n : DialogOption := { label := "Deny", hint := "n", key := "n" }

def opts : List DialogOption := [opt_y, opt_a, opt_n]

def dialog : DialogModel := Dialog.make "Permission" "write edit" ["body"] opts

def noted : DialogModel := Dialog.with_notes dialog

def dlg_of (pr : Pair DialogModel DialogStep) : DialogModel :=
    match pr { Pair.pair d _ => d }

#[test]
def test_down_moves_the_selection : Bool :=
    match Dialog.step dialog Key.down {
        Pair.pair d step => d.selected == 1 && (match step { DialogStep.continue => true, _ => false }),
    }

#[test]
def test_down_clamps_at_the_last_option : Bool :=
    match Dialog.step (dlg_of (Dialog.step (dlg_of (Dialog.step dialog Key.down)) Key.down)) Key.down {
        Pair.pair d _ => d.selected == 2,
    }

#[test]
def test_enter_chooses_the_selection : Bool :=
    match Dialog.step (dlg_of (Dialog.step dialog Key.down)) Key.enter {
        Pair.pair _ step => match step { DialogStep.choose i => i == 1, _ => false },
    }

#[test]
def test_a_direct_key_chooses : Bool :=
    match Dialog.step dialog (Key.char "a") {
        Pair.pair _ step => match step { DialogStep.choose i => i == 1, _ => false },
    }

#[test]
def test_escape_cancels : Bool :=
    match Dialog.step dialog Key.escape {
        Pair.pair _ step => match step { DialogStep.cancel => true, _ => false },
    }

#[test]
def test_with_default_clamps : Bool :=
    let hi : DialogModel := Dialog.with_default dialog 9 in
    let lo : DialogModel := Dialog.with_default dialog (0 - 1) in
    hi.selected == 2 && lo.selected == 0

#[test]
def test_e_opens_the_note_and_typing_edits_it : Bool :=
    match Dialog.step noted (Key.char "e") {
        Pair.pair d1 _ => match Dialog.step d1 (Key.char "h") {
            Pair.pair d2 step => d2.editing && Dialog.note_text d2 == "h"
                && (match step { DialogStep.continue => true, _ => false }),
        },
    }

#[test]
def test_enter_leaves_the_note_without_choosing : Bool :=
    match Dialog.step (dlg_of (Dialog.step noted (Key.char "e"))) Key.enter {
        Pair.pair d step => Bool.not d.editing && (match step { DialogStep.continue => true, _ => false }),
    }

#[test]
def test_selection_keys_do_not_edit_the_note : Bool :=
    match Dialog.step noted (Key.char "h") {
        Pair.pair d _ => Bool.not d.editing && String.is_empty (Dialog.note_text d),
    }

#[test]
def test_paste_only_edits_an_open_note : Bool :=
    let closed : DialogModel := Dialog.paste noted "pasted" in
    match Dialog.step noted (Key.char "e") {
        Pair.pair opened _ =>
            String.is_empty (Dialog.note_text closed)
                && Dialog.note_text (Dialog.paste opened "pasted") == "pasted",
    }

#[test]
def test_apply_ends_only_on_a_choice : Bool :=
    let moved : Bool := match Dialog.apply dialog (Event.key Key.down) {
        Pair.pair d step => d.selected == 1 && (match step { Option.none => true, Option.some _ => false }),
    } in
    let chose : Bool := match Dialog.apply dialog (Event.key Key.enter) {
        Pair.pair _ step => match step {
            Option.some s => match s { DialogStep.choose i => i == 0, _ => false },
            Option.none => false,
        },
    } in
    moved && chose

// ── layout ──────────────────────────────────────────────────────────────

#[test]
def test_frame_width_clamps : Bool :=
    Dialog.frame_width 200 == 88 && Dialog.frame_width 40 == 36 && Dialog.frame_width 2 == 1
        && Dialog.content_width 36 == 32

#[test]
def test_frame_height_fits_or_caps : Bool :=
    Dialog.frame_height 40 10 == 14 && Dialog.frame_height 20 30 == 18 && Dialog.frame_height 4 30 == 6

/// A fullscreen dialog takes the whole terminal; a normal one keeps the
/// centred, capped frame.
#[test]
def test_fullscreen_frame_fills_the_terminal : Bool :=
    let d : DialogModel := Dialog.make "t" "" List.empty List.empty in
    let full : DialogModel := { d with fullscreen := true } in
    Dialog.frame_width_for full 200 == 200 && Dialog.frame_height_for full 40 3 == 40
        && Dialog.frame_width_for d 200 == 88 && Dialog.frame_height_for d 40 10 == 14

/// A body that fits is shown whole: title, subtitle, blank, body, blank,
/// three options, blank, footer -- plus a blank and the note row when the
/// dialog offers a note.
#[test]
def test_rows_show_everything_when_it_fits : Bool :=
    let body : List SizedWidget := Dialog.body_rows 40 dialog in
    let total : I64 := Dialog.total_rows dialog (List.length body) in
    let noted_total : I64 := Dialog.total_rows noted (List.length body) in
    List.length (Dialog.rows 40 (total + 4) dialog body) == total && total == 9
        && List.length (Dialog.rows 40 (noted_total + 4) noted body) == noted_total && noted_total == 11

/// On a short frame the body yields first: the options, note and footer
/// keep their rows.
#[test]
def test_rows_keep_the_fixed_rows_on_a_short_frame : Bool :=
    let d : DialogModel := Dialog.make "T" "s" ["1", "2", "3", "4", "5", "6", "7", "8"] opts in
    let body : List SizedWidget := Dialog.body_rows 40 d in
    List.length (Dialog.rows 40 14 d body) == 10

#[test]
def test_body_rows_wrap : Bool :=
    let d : DialogModel := Dialog.make "T" "s" ["aaaa bbbb cccc"] opts in
    List.length (Dialog.body_rows 5 d) == 3

#[test]
def test_e_is_no_note_key_without_notes : Bool :=
    match Dialog.step dialog (Key.char "e") {
        Pair.pair d step => Bool.not d.editing && (match step { DialogStep.continue => true, _ => false }),
    }

// ── editable values ─────────────────────────────────────────────────────

def opt_budget : DialogOption := { label := "Budget", hint := "", key := "", value := Option.some "40" }

def editable : DialogModel := Dialog.make "Settings" "s" [] [opt_y, opt_budget]

/// The editable dialog with its second option's field open.
def opened : DialogModel :=
    dlg_of (Dialog.step (dlg_of (Dialog.step editable Key.down)) Key.enter)

#[test]
def test_enter_opens_a_prefilled_field : Bool :=
    match Dialog.step (dlg_of (Dialog.step editable Key.down)) Key.enter {
        Pair.pair d step => d.field_input.value == "40"
            && (match d.field { Option.some i => i == 1, Option.none => false })
            && (match step { DialogStep.continue => true, _ => false }),
    }

#[test]
def test_typing_then_enter_submits_the_field : Bool :=
    match Dialog.step (dlg_of (Dialog.step opened (Key.char "9"))) Key.enter {
        Pair.pair d step =>
            (match d.field { Option.none => true, Option.some _ => false })
                && (match step { DialogStep.submit i text => i == 1 && text == "409", _ => false }),
    }

#[test]
def test_escape_leaves_the_field_not_the_dialog : Bool :=
    match Dialog.step opened Key.escape {
        Pair.pair d step =>
            (match d.field { Option.none => true, Option.some _ => false })
                && (match step { DialogStep.continue => true, _ => false }),
    }

#[test]
def test_ctrl_u_clears_the_field : Bool :=
    match Dialog.step opened (Key.ctrl "u") {
        Pair.pair d _ => String.is_empty d.field_input.value,
    }

#[test]
def test_paste_lands_in_the_open_field : Bool :=
    let d : DialogModel := Dialog.paste opened "0" in
    d.field_input.value == "400"

#[test]
def test_enter_on_a_plain_option_still_chooses : Bool :=
    match Dialog.step editable Key.enter {
        Pair.pair _ step => match step { DialogStep.choose i => i == 0, _ => false },
    }

#[test]
def test_rows_count_is_the_same_with_a_field_open : Bool :=
    let total : I64 := Dialog.total_rows opened 0 in
    List.length (Dialog.rows 40 (total + 4) opened List.empty) == total

// ── wheel and scroll clamping ───────────────────────────────────────────

#[test]
def test_wheel_scrolls_the_body : Bool :=
    let down : DialogModel := dlg_of_apply (Dialog.apply dialog (Event.mouse (MouseEvent.scroll_down 1 1))) in
    let up : DialogModel := dlg_of_apply (Dialog.apply down (Event.mouse (MouseEvent.scroll_up 1 1))) in
    down.scroll == 3 && up.scroll == 0

#[test]
def test_a_click_changes_nothing : Bool :=
    let d : DialogModel := dlg_of_apply (Dialog.apply dialog (Event.mouse (MouseEvent.press MouseButton.left 1 1))) in
    d.scroll == 0 && d.selected == 0

def dlg_of_apply (pr : Pair DialogModel (Option DialogStep)) : DialogModel :=
    match pr { Pair.pair d _ => d }

/// A 14-row frame holds two of the eight body rows, so the scroll stops at 6.
#[test]
def test_clamp_scroll_stops_at_the_last_body_row : Bool :=
    let d : DialogModel := Dialog.make "T" "s" ["1", "2", "3", "4", "5", "6", "7", "8"] opts in
    let far : DialogModel := { d with scroll := 50 } in
    let clamped : DialogModel := Dialog.clamp_scroll 14 8 far in
    let kept : DialogModel := Dialog.clamp_scroll 14 8 d in
    clamped.scroll == 6 && kept.scroll == 0

// ── the modal step ──────────────────────────────────────────────────────

def modal_of (d : DialogModel) (r : InputReader) : ModalState :=
    { d := d, r := r, queued := List.empty, prev := Option.none, dirty := false,
        refresh := Option.none, every := 0, idle := 0 }

#[test]
def test_quiet_poll_with_a_lone_escape_queues_the_key : Bool :=
    let r0 : InputReader := input_reader 24 80 in
    let r : InputReader := { r0 with pending := "\u{1b}" } in
    match Modal.idle (modal_of opened r) {
        ModalNext.more s => String.is_empty s.r.pending && List.length s.queued == 1,
        ModalNext.done _ => false,
    }

#[test]
def test_escape_in_an_open_field_keeps_the_modal_running : Bool :=
    match Modal.fold (modal_of opened (input_reader 24 80)) (Event.key Key.escape) List.empty {
        ModalNext.more s => s.dirty && (match s.d.field { Option.none => true, Option.some _ => false }),
        ModalNext.done _ => false,
    }

#[test]
def test_escape_on_the_options_ends_the_modal : Bool :=
    match Modal.fold (modal_of dialog (input_reader 24 80)) (Event.key Key.escape) List.empty {
        ModalNext.done pr => match pr { Pair.pair _ step => match step { DialogStep.cancel => true, _ => false } },
        ModalNext.more _ => false,
    }

#[test]
def test_a_closed_reader_cancels_on_a_quiet_poll : Bool :=
    let r0 : InputReader := input_reader 24 80 in
    let r : InputReader := { r0 with closed := true } in
    match Modal.idle (modal_of dialog r) {
        ModalNext.done _ => true,
        ModalNext.more _ => false,
    }

#[test]
def test_a_no_op_event_needs_no_repaint : Bool :=
    match Modal.fold (modal_of dialog (input_reader 24 80)) (Event.mouse (MouseEvent.press MouseButton.left 1 1)) List.empty {
        ModalNext.more s => Bool.not s.dirty,
        ModalNext.done _ => false,
    }

/// A regained focus forgets the last paint: the next step clears and
/// repaints the whole dialog.
#[test]
def test_focus_in_repaints_the_whole_dialog : Bool :=
    let s0 : ModalState := modal_of dialog (input_reader 24 80) in
    let s : ModalState := { s0 with prev := Option.some (empty_screen 24 80) } in
    match Modal.fold s Event.focus_in List.empty {
        ModalNext.more s2 => s2.dirty && (match s2.prev { Option.none => true, Option.some _ => false }),
        ModalNext.done _ => false,
    }

#[test]
def test_focus_out_needs_no_repaint : Bool :=
    let s0 : ModalState := modal_of dialog (input_reader 24 80) in
    let s : ModalState := { s0 with prev := Option.some (empty_screen 24 80) } in
    match Modal.fold s Event.focus_out List.empty {
        ModalNext.more s2 => Bool.not s2.dirty && (match s2.prev { Option.none => false, Option.some _ => true }),
        ModalNext.done _ => false,
    }

/// A scheduled heal counts quiet polls down, then forgets the last paint
/// once.
#[test]
def test_heal_repaints_once_after_its_quiet_polls : Bool :=
    let s0 : ModalState := modal_of dialog (input_reader 24 80) in
    let s : ModalState := { s0 with prev := Option.some (empty_screen 24 80), heal := 2 } in
    let a : ModalState := quiet_state (Modal.idle s) in
    let b : ModalState := quiet_state (Modal.idle a) in
    let c : ModalState := quiet_state (Modal.idle { b with prev := Option.some (empty_screen 24 80), dirty := false }) in
    a.heal == 1 && Bool.not a.dirty
        && b.heal == 0 && b.dirty && (match b.prev { Option.none => true, Option.some _ => false })
        && Bool.not c.dirty

// ── the refresh ─────────────────────────────────────────────────────────

def retitle (d : DialogModel) : IO (Option DialogModel) :=
    let d2 : DialogModel := { d with title := "refreshed" } in
    IO.pure (Option.some d2)

def ticking (every : I64) : ModalState :=
    let s : ModalState := modal_of opened (input_reader 24 80) in
    { s with refresh := Option.some retitle, every := every }

def quiet_state (n : ModalNext) : ModalState :=
    match n { ModalNext.more s => s, ModalNext.done _ => ticking 0 }

#[test]
def test_refresh_due_on_every_nth_quiet_poll : Bool :=
    Bool.not (Dialog.refresh_due 0 3) && Bool.not (Dialog.refresh_due 1 3) && Dialog.refresh_due 2 3
        && Dialog.refresh_due 0 1

/// Two quiet polls only count; the third runs the refresh, swaps the
/// dialog in, asks for a paint and starts the count over.
#[test]
def test_quiet_polls_run_the_refresh : IO Bool := do {
    let a <- modal_quiet (ModalNext.more (ticking 3));
    let b <- modal_quiet (ModalNext.more (quiet_state a));
    let c <- modal_quiet (ModalNext.more (quiet_state b));
    let sa : ModalState := quiet_state a;
    let sb : ModalState := quiet_state b;
    let sc : ModalState := quiet_state c;
    IO.pure (sa.idle == 1 && Bool.not sa.dirty && sb.idle == 2 && Bool.not (String.beq sb.d.title "refreshed")
        && sc.idle == 0 && sc.dirty && String.beq sc.d.title "refreshed")
}

/// A body taller than its frame names the scroll keys in the footer.
#[test]
def test_footer_names_scroll_keys_on_overflow : Bool :=
    String.contains (Dialog.footer_line dialog true) "PgUp/PgDn"
        && Bool.not (String.contains (Dialog.footer_line dialog false) "PgUp/PgDn")
