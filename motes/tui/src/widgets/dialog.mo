// Terminal UI Library - confirmation dialog (a component)
//
// A titled modal: a subtitle, scrollable body rows, a list of options with
// a highlighted selection, and an optional note field. `Dialog.step` owns
// what a key means and answers a `DialogStep`, so the parent decides what
// a choice does. `Dialog.view` lays the dialog out in a fixed frame; the
// body arrives as rows the HOST rendered (Markdown, styled transcript
// lines), or `Dialog.body_rows` wraps it as plain text. `Dialog.modal`
// runs the dialog over stdin until it is chosen or cancelled.

use lib::types {Key, Event, LayoutSize, TextStyle, Rect}
use lib::core {style_default, empty_screen, mk_rect}
use lib::widget {Widget, SizedWidget, BorderStyle, border_with, padding, sized, label, with_style}
use lib::widgets::input {InputState, input_state, handle_input_key, insert_text}
use lib::layout {center_rect_in}
use lib::render {render, diff, apply_deltas}
use lib::terminal {Terminal.clear_screen, Terminal.cursor_move, Terminal.poll, Terminal.size}
use lib::input {Input.step, InputReader, input_reader}
use lib::text {Text.wrap}
use std::io {IO.read_stdin_exact, IO.write_stdout, IO.flush_stdout}
use std::list {List.length}

pub struct DialogOption {
    label : String,
    hint : String,
    /// The direct key that chooses this option ("" = no shortcut).
    key : String,
}

pub struct DialogModel {
    title : String,
    subtitle : String,
    body : List String,
    options : List DialogOption,
    selected : I64,
    /// Body rows scrolled off the top.
    scroll : I64,
    note : InputState,
    editing : Bool,
    footer : String,
    /// The body is ONE Markdown document, not literal lines: a hint to the
    /// host's body renderer (`Dialog.body_rows` ignores it).
    markdown : Bool := false,
}

pub type DialogStep {
    continue,
    choose (index : I64),
    cancel,
}

pub def Dialog.make (title : String) (subtitle : String) (body : List String) (options : List DialogOption) : DialogModel :=
    let d : DialogModel := {
        title := title,
        subtitle := subtitle,
        body := body,
        options := options,
        selected := 0,
        scroll := 0,
        note := input_state "" "add a note (optional)",
        editing := false,
        footer := "↑/↓ select · Enter confirm · e note · Esc cancel",
        markdown := false,
    } in
    d

pub def Dialog.option_count (d : DialogModel) : I64 := List.length d.options

#[terminating]
def nth_go {A : Type} (i : I64) (xs : List A) : Option A :=
    match xs {
        List.empty => Option.none,
        List.cons x rest => if i < 1 then Option.some x else nth_go (i - 1) rest,
    }

pub def Dialog.option_at (d : DialogModel) (i : I64) : Option DialogOption := nth_go i d.options

pub def Dialog.note_text (d : DialogModel) : String := d.note.value

pub def Dialog.with_default (d : DialogModel) (i : I64) : DialogModel :=
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
pub def Dialog.step (d : DialogModel) (k : Key) : Pair DialogModel DialogStep :=
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
pub def Dialog.paste (d : DialogModel) (text : String) : DialogModel :=
    if d.editing then { d with note := insert_text text d.note } else d

/// Fold one decoded event into the dialog; `some` ends the modal.
pub def Dialog.apply (d : DialogModel) (e : Event) : Pair DialogModel (Option DialogStep) :=
    match e {
        Event.key k => match Dialog.step d k {
            Pair.pair d2 step => match step {
                DialogStep.continue => Pair.pair d2 Option.none,
                _ => Pair.pair d2 (Option.some step),
            },
        },
        Event.paste text => Pair.pair (Dialog.paste d text) Option.none,
        _ => Pair.pair d Option.none,
    }

// ==================== layout and view ====================

/// The frame's width on a `cols`-wide terminal: two columns of margin a
/// side, at most 88.
pub def Dialog.frame_width (cols : I64) : I64 :=
    let raw : I64 := cols - 4 in
    if raw < 1 then 1 else if raw < 88 then raw else 88

/// The text width inside a `frame_width` frame (border and padding).
pub def Dialog.content_width (frame_w : I64) : I64 :=
    if frame_w - 4 < 1 then 1 else frame_w - 4

/// Every row the dialog would show with `body_count` body rows.
pub def Dialog.total_rows (d : DialogModel) (body_count : I64) : I64 :=
    body_count + Dialog.option_count d + 7

/// The frame's height on a `rows`-high terminal: the whole dialog when it
/// fits, else the screen less a row of margin a side (at least 6).
pub def Dialog.frame_height (rows : I64) (total : I64) : I64 :=
    let max_h : I64 := if rows - 2 < 6 then 6 else rows - 2 in
    if total + 4 < max_h then total + 4 else max_h

#[partial]
def take {A : Type} (n : I64) (xs : List A) : List A :=
    if n < 1 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (take (n - 1) rest),
    }

#[partial]
def drop {A : Type} (n : I64) (xs : List A) : List A :=
    if n < 1 then xs
    else match xs {
        List.empty => xs,
        List.cons _ rest => drop (n - 1) rest,
    }

/// `text` wrapped to `width`, one row per line, in `style`.
pub def Dialog.text_rows (style : TextStyle) (width : I64) (text : String) : List SizedWidget :=
    List.map (fn (l : String) => sized (LayoutSize.fixed 1) (with_style style (label l))) (Text.wrap width text)

/// The body as plain wrapped text: the default for a host with no richer
/// renderer.
pub def Dialog.body_rows (width : I64) (d : DialogModel) : List SizedWidget :=
    List.flatten (List.map (Dialog.text_rows style_default width) d.body)

#[partial]
def option_rows (d : DialogModel) (i : I64) (width : I64) : List SizedWidget :=
    match Dialog.option_at d i {
        Option.none => List.empty,
        Option.some o =>
            let here : Bool := i == d.selected in
            let marker : String := if here then "> " else "  " in
            let suffix : String := if String.is_empty o.hint then "" else String.concat "  (" (String.concat o.hint ")") in
            let style : TextStyle := if here then { style_default with reverse := true } else style_default in
            List.append (Dialog.text_rows style width (String.concat marker (String.concat o.label suffix)))
                (option_rows d (i + 1) width),
    }

def note_text (d : DialogModel) : String :=
    if d.editing
    then String.concat "note: " (String.concat d.note.value "_")
    else if String.is_empty d.note.value
    then "note: (press e to add one)"
    else String.concat "note: " d.note.value

/// The rows inside a `height`-high frame. The body yields to the fixed
/// rows on a short terminal, so the options, note and footer stay
/// visible; `body` is every body row, scrolled here by `d.scroll`.
pub def Dialog.rows (width : I64) (height : I64) (d : DialogModel) (body : List SizedWidget) : List SizedWidget :=
    let budget : I64 := if height - 4 < 1 then 1 else height - 4 in
    let fixed : I64 := Dialog.total_rows d 0 in
    let body_budget : I64 := if budget - fixed < 1 then 0 else budget - fixed in
    let dim : TextStyle := { style_default with dim := true } in
    let bold : TextStyle := { style_default with bold := true } in
    let blank : List SizedWidget := [sized (LayoutSize.fixed 1) (label "")] in
    let parts : List (List SizedWidget) := [
        Dialog.text_rows bold width d.title,
        Dialog.text_rows dim width d.subtitle,
        blank,
        take body_budget (drop d.scroll body),
        blank,
        option_rows d 0 width,
        blank,
        Dialog.text_rows dim width (note_text d),
        Dialog.text_rows dim width d.footer,
    ] in
    take budget (List.flatten parts)

/// The dialog in its rounded `border`-styled frame.
pub def Dialog.view (border : TextStyle) (width : I64) (height : I64) (d : DialogModel) (body : List SizedWidget) : Widget :=
    Widget.column [
        sized (LayoutSize.fill 1) (border_with border BorderStyle.rounded
            (padding 1 1 1 2 (Widget.column (Dialog.rows width height d body)))),
    ]

// ==================== the modal loop ====================

/// Paint the dialog centered on a cleared screen. `body` renders the body
/// at a content width; it runs once per paint.
pub def Dialog.paint (border : TextStyle) (body : I64 -> DialogModel -> List SizedWidget) (d : DialogModel) : IO Unit := do {
    let size <- Terminal.size;
    match size {
        Pair.pair rows cols => do {
            let frame_w : I64 := Dialog.frame_width cols;
            let width : I64 := Dialog.content_width frame_w;
            let body_all : List SizedWidget := body width d;
            let height : I64 := Dialog.frame_height rows (Dialog.total_rows d (List.length body_all));
            let rect : Rect := center_rect_in (mk_rect 0 0 cols rows) frame_w height;
            Terminal.clear_screen;
            Terminal.cursor_move 0 0;
            let screen := render (Dialog.view border width height d body_all) rect (empty_screen rows cols);
            IO.write_stdout (apply_deltas (diff (empty_screen rows cols) screen));
            IO.flush_stdout
        }
    }
}

def same_size (a : Pair I64 I64) (b : Pair I64 I64) : Bool :=
    match a {
        Pair.pair ar ac => match b {
            Pair.pair br bc => Bool.and (ar == br) (ac == bc),
        },
    }

/// One byte through `Input.step` -- the same decoder the main loop uses,
/// including its linear bracketed-paste accumulator. EOF closes the reader.
def read_events (r : InputReader) : IO (Pair (List Event) InputReader) := do {
    let chunk <- IO.read_stdin_exact 1;
    if String.length chunk == 0
    then
        let closed_reader : InputReader := { r with closed := true } in
        IO.pure (Pair.pair List.empty closed_reader)
    else IO.pure (Input.step r List.empty chunk)
}

/// Repaint when the dialog or the terminal size changed, then poll for
/// input. Decoded events are queued and folded in order. A lone ESC
/// cancels; any other incomplete prefix stays pending in the reader, so
/// the loop never blocks on it.
#[partial]
def modal_loop (paint : DialogModel -> IO Unit) (d : DialogModel) (r : InputReader) (queued : List Event) (last : Option (Pair I64 I64)) : IO (Pair DialogModel DialogStep) := do {
    let size <- Terminal.size;
    let need : Bool := match last {
        Option.none => true,
        Option.some p => Bool.not (same_size p size),
    };
    let _ <- if need then paint d else IO.pure unit;
    match queued {
        List.cons e rest =>
            match Dialog.apply d e {
                Pair.pair d2 step => match step {
                    Option.some s => IO.pure (Pair.pair d2 s),
                    Option.none => modal_loop paint d2 r rest Option.none,
                },
            },
        List.empty => do {
            let ready <- Terminal.poll 100;
            if Bool.not ready
            then
                if r.closed
                then IO.pure (Pair.pair d DialogStep.cancel)
                else if r.pending == "\u{1b}"
                then IO.pure (Pair.pair d DialogStep.cancel)
                else modal_loop paint d r List.empty (Option.some size)
            else do {
                let got <- read_events r;
                match got {
                    Pair.pair evs r2 =>
                        if Bool.and r2.closed (List.is_empty evs)
                        then IO.pure (Pair.pair d DialogStep.cancel)
                        else modal_loop paint d r2 evs (Option.some size),
                }
            }
        },
    }
}

/// Run the dialog over stdin until it is chosen, cancelled or stdin
/// closes. The final dialog rides along so the caller can read the note.
pub def Dialog.modal (paint : DialogModel -> IO Unit) (d : DialogModel) : IO (Pair DialogModel DialogStep) := do {
    let size <- Terminal.size;
    match size {
        Pair.pair rows cols => modal_loop paint d (input_reader rows cols) List.empty Option.none,
    }
}
