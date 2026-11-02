/// Tests for the dialog component (`motes/tui/src/widgets/dialog.mo`):
/// key transitions, the note field, and the layout's fixed rows.

use lib::widgets::dialog {
    DialogModel, DialogOption, DialogStep, Dialog.make, Dialog.step, Dialog.paste,
    Dialog.note_text, Dialog.with_default, Dialog.apply, Dialog.rows, Dialog.body_rows,
    Dialog.total_rows, Dialog.frame_width, Dialog.frame_height, Dialog.content_width,
}
use lib::types {Key, Event}
use lib::widget {SizedWidget}
use std::list {List.length}

def opt_y : DialogOption := { label := "Approve once", hint := "y", key := "y" }
def opt_a : DialogOption := { label := "Always", hint := "a", key := "a" }
def opt_n : DialogOption := { label := "Deny", hint := "n", key := "n" }

def opts : List DialogOption := [opt_y, opt_a, opt_n]

def dialog : DialogModel := Dialog.make "Permission" "write edit" ["body"] opts

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
    match Dialog.step dialog (Key.char "e") {
        Pair.pair d1 _ => match Dialog.step d1 (Key.char "h") {
            Pair.pair d2 step => d2.editing && Dialog.note_text d2 == "h"
                && (match step { DialogStep.continue => true, _ => false }),
        },
    }

#[test]
def test_enter_leaves_the_note_without_choosing : Bool :=
    match Dialog.step (dlg_of (Dialog.step dialog (Key.char "e"))) Key.enter {
        Pair.pair d step => Bool.not d.editing && (match step { DialogStep.continue => true, _ => false }),
    }

#[test]
def test_selection_keys_do_not_edit_the_note : Bool :=
    match Dialog.step dialog (Key.char "h") {
        Pair.pair d _ => Bool.not d.editing && String.is_empty (Dialog.note_text d),
    }

#[test]
def test_paste_only_edits_an_open_note : Bool :=
    let closed : DialogModel := Dialog.paste dialog "pasted" in
    match Dialog.step dialog (Key.char "e") {
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

/// A body that fits is shown whole: title, subtitle, blank, body, blank,
/// three options, blank, note, footer.
#[test]
def test_rows_show_everything_when_it_fits : Bool :=
    let body : List SizedWidget := Dialog.body_rows 40 dialog in
    let total : I64 := Dialog.total_rows dialog (List.length body) in
    List.length (Dialog.rows 40 (total + 4) dialog body) == total && total == 11

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
