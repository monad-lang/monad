/// Tests for the picker component (`motes/tui/src/widgets/picker.mo`).

use lib::widgets::picker {PickerModel, PickerStep, Picker.make, Picker.update, Picker.selected, Picker.count, Picker.window_offset, Picker.visible}
use lib::types {Key}
use std::list {}

def names : List String := ["alpha", "beta", "gamma"]

/// The picker after `k`, or the input unchanged when `k` ends it.
def after (height : I64) (p : PickerModel) (k : Key) : PickerModel :=
    match Picker.update height p k {
        PickerStep.stay p2 => p2,
        _ => p,
    }

#[test]
def test_open_selects_the_current_name : Bool :=
    Picker.selected (Picker.make "t" names "beta") == "beta"

#[test]
def test_open_misses_the_current_name_without_breaking : Bool :=
    let p : PickerModel := Picker.make "t" names "not-listed" in
    Picker.count p == 3 && Picker.selected p == "alpha"

#[test]
def test_move_clamps_at_both_ends : Bool :=
    let p : PickerModel := Picker.make "t" ["only"] "only" in
    Picker.selected (after 2 p Key.up) == "only" && Picker.selected (after 2 p Key.down) == "only"

#[test]
def test_window_follows_the_selection : Bool :=
    let p : PickerModel := Picker.make "t" ["a", "b", "c", "d", "e", "f"] "a" in
    let p2 : PickerModel := after 2 (after 2 (after 2 (after 2 p Key.down) Key.down) Key.down) Key.down in
    Picker.selected p2 == "e" && Picker.window_offset 2 p2 == 3 && List.length (Picker.visible 2 p2) == 2

#[test]
def test_enter_chooses_and_escape_cancels : Bool :=
    let p : PickerModel := after 2 (Picker.make "t" names "alpha") Key.down in
    let chose : Bool := match Picker.update 2 p Key.enter {
        PickerStep.choose x => x == "beta",
        _ => false,
    } in
    let cancelled : Bool := match Picker.update 2 p Key.escape {
        PickerStep.cancel => true,
        _ => false,
    } in
    chose && cancelled

#[test]
def test_typing_stays_open_unchanged : Bool :=
    match Picker.update 2 (Picker.make "t" names "gamma") (Key.char "x") {
        PickerStep.stay p => Picker.selected p == "gamma",
        _ => false,
    }
