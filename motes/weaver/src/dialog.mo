/// The confirmation dialog's pure state machine, shared by the permission
/// and plan dialogs: a title, a subtitle, scrollable body lines, a list of
/// options with a highlighted selection, and an optional note field.
///
/// The TUI driver (tui_app.mo) owns rendering and input; this module owns
/// what a key means, so the transitions are unit-testable without a tty.
use tui::types {Key}
use tui::widgets::input {InputState, input_state, handle_input_key, insert_text}

pub struct DialogOption {
    label : String,
    hint : String,
    /// The direct key that chooses this option ("" = no shortcut).
    key : String,
}

pub struct Dialog {
    title : String,
    subtitle : String,
    body : List String,
    options : List DialogOption,
    selected : I64,
    /// Body lines scrolled off the top.
    scroll : I64,
    note : InputState,
    editing : Bool,
    footer : String,
}

pub type DialogStep {
    continue,
    choose (index : I64),
    cancel,
}

pub def Dialog.make (title : String) (subtitle : String) (body : List String) (options : List DialogOption) : Dialog :=
    let d : Dialog := {
        title := title,
        subtitle := subtitle,
        body := body,
        options := options,
        selected := 0,
        scroll := 0,
        note := input_state "" "add a note (optional)",
        editing := false,
        footer := "↑/↓ select · Enter confirm · e note · Esc cancel",
    } in
    d

#[terminating]
def count_go {A : Type} (n : I64) (xs : List A) : I64 :=
    match xs {
        List.empty => n,
        List.cons _ rest => count_go (n + 1) rest,
    }

pub def Dialog.option_count (d : Dialog) : I64 := count_go 0 d.options

#[terminating]
def nth_go {A : Type} (i : I64) (xs : List A) : Option A :=
    match xs {
        List.empty => Option.none,
        List.cons x rest => if i < 1 then Option.some x else nth_go (i - 1) rest,
    }

pub def Dialog.option_at (d : Dialog) (i : I64) : Option DialogOption := nth_go i d.options

pub def Dialog.note_text (d : Dialog) : String := d.note.value

pub def Dialog.with_default (d : Dialog) (i : I64) : Dialog :=
    let n : I64 := Dialog.option_count d in
    let s : I64 := if i < 0 then 0 else if n - 1 < i then (if n < 1 then 0 else n - 1) else i in
    { d with selected := s }

#[terminating]
def option_key_at (i : I64) (k : String) (xs : List DialogOption) : Option I64 :=
    match xs {
        List.empty => Option.none,
        List.cons o rest =>
            if Bool.and (Bool.not (String.is_empty o.key)) (o.key == k)
            then Option.some i
            else option_key_at (i + 1) k rest,
    }

/// One key's transition. While the note is being edited every key edits
/// it (Enter/Esc leave the field); otherwise arrows/Enter/letters drive
/// the selection.
pub def Dialog.step (d : Dialog) (k : Key) : Pair Dialog DialogStep :=
    if d.editing
    then match k {
        Key.escape => Pair.pair { d with editing := false } DialogStep.continue,
        Key.enter => Pair.pair { d with editing := false } DialogStep.continue,
        _ => Pair.pair { d with note := handle_input_key k d.note } DialogStep.continue,
    }
    else
        let n : I64 := Dialog.option_count d in
        match k {
            Key.escape => Pair.pair d DialogStep.cancel,
            Key.ctrl c => if c == "c" then Pair.pair d DialogStep.cancel else Pair.pair d DialogStep.continue,
            Key.enter => Pair.pair d (DialogStep.choose d.selected),
            Key.up => Pair.pair { d with selected := (if d.selected < 1 then 0 else d.selected - 1) } DialogStep.continue,
            Key.down => Pair.pair { d with selected := (if d.selected + 1 < n then d.selected + 1 else (if n < 1 then 0 else n - 1)) } DialogStep.continue,
            Key.home => Pair.pair { d with selected := 0, scroll := 0 } DialogStep.continue,
            Key.end => Pair.pair { d with selected := (if n < 1 then 0 else n - 1) } DialogStep.continue,
            Key.page_up => Pair.pair { d with scroll := (if d.scroll < 5 then 0 else d.scroll - 5) } DialogStep.continue,
            Key.page_down => Pair.pair { d with scroll := d.scroll + 5 } DialogStep.continue,
            Key.char c =>
                if c == "e" then Pair.pair { d with editing := true } DialogStep.continue
                else if c == "k" then Pair.pair { d with selected := (if d.selected < 1 then 0 else d.selected - 1) } DialogStep.continue
                else if c == "j" then Pair.pair { d with selected := (if d.selected + 1 < n then d.selected + 1 else (if n < 1 then 0 else n - 1)) } DialogStep.continue
                else match option_key_at 0 c d.options {
                    Option.some i => Pair.pair d (DialogStep.choose i),
                    Option.none => Pair.pair d DialogStep.continue,
                },
            _ => Pair.pair d DialogStep.continue,
        }

/// A bracketed paste edits the note only while it is open; it never
/// chooses an option.
pub def Dialog.paste (d : Dialog) (text : String) : Dialog :=
    if d.editing then { d with note := insert_text text d.note } else d

// ==================== tests ====================

def opt_y : DialogOption := { label := "Approve once", hint := "y", key := "y" }
def opt_a : DialogOption := { label := "Always", hint := "a", key := "a" }
def opt_n : DialogOption := { label := "Deny", hint := "n", key := "n" }

def opts : List DialogOption := [opt_y, opt_a, opt_n]

def dialog : Dialog := Dialog.make "Permission" "write edit" ["body"] opts

def dlg_of (pr : Pair Dialog DialogStep) : Dialog :=
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
    let closed : Dialog := Dialog.paste dialog "pasted" in
    match Dialog.step dialog (Key.char "e") {
        Pair.pair opened _ =>
            String.is_empty (Dialog.note_text closed)
                && Dialog.note_text (Dialog.paste opened "pasted") == "pasted",
    }
