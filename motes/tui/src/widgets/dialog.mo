// Terminal UI Library - confirmation dialog (a component)
//
// A titled modal: a subtitle, scrollable body rows, a list of options with
// a highlighted selection, an optional note field (`notes`), and editable
// option values (an option with a `value` opens a field on Enter). `Dialog.step` owns
// what a key means and answers a `DialogStep`, so the parent decides what
// a choice does. `Dialog.view` lays the dialog out in a fixed frame; the
// body arrives as rows the HOST rendered (Markdown, styled transcript
// lines), or `Dialog.body_rows` wraps it as plain text. `Dialog.modal`
// runs the dialog over stdin until it is chosen or cancelled.

use lib::types {Key, Event, MouseEvent, LayoutSize, TextStyle, TextSegment, Rect, Screen}
use lib::core {style_default, empty_screen, mk_rect}
use lib::widget {Widget, SizedWidget, BorderStyle, border_with, padding, sized, label, with_style}
use lib::widgets::input {InputState, input_state, handle_input_key, insert_text}
use lib::layout {center_rect_in}
use lib::render {render, diff, apply_deltas}
use lib::terminal {Terminal.clear_screen, Terminal.cursor_move, Terminal.poll, Terminal.size}
use lib::input {Input.step, InputReader, input_reader}
use lib::text {Text.wrap}
use std::io {IO.read_stdin_exact, IO.write_stdout, IO.flush_stdout}
use std::list {}

pub struct DialogOption {
    label : String,
    hint : String,
    /// The direct key that chooses this option ("" = no shortcut).
    key : String,
    /// An editable value: Enter opens a field holding it and answers
    /// `submit` with the edited text, instead of `choose`.
    value : Option String := Option.none,
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
    /// Whether the dialog offers a note (`e`); only dialogs that read
    /// `Dialog.note_text` turn it on.
    notes : Bool := false,
    /// The option whose value is being edited, and the edit itself.
    field : Option I64 := Option.none,
    field_input : InputState,
    /// Fill the whole terminal instead of a centred box of at most 88
    /// columns: for long documents such as a plan.
    fullscreen : Bool := false,
    /// Pre-rendered styled rows appended after `body`: a host that owns a
    /// richer renderer (weaver's hunk diff) sets these instead of flattening
    /// its styles into text.
    body_spans : Option (List (List TextSegment)) := Option.none,
}

pub type DialogStep {
    continue,
    choose (index : I64),
    cancel,
    /// An editable option's field was confirmed with this text.
    submit (index : I64) (text : String),
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
        footer := "↑/↓ select · Enter confirm · Esc cancel",
        markdown := false,
        notes := false,
        field := Option.none,
        field_input := input_state "" "",
        fullscreen := false,
        body_spans := Option.none,
    } in
    d

/// Offer a note: `e` edits it and the dialog shows its row.
pub def Dialog.with_notes (d : DialogModel) : DialogModel :=
    { d with notes := true, footer := "↑/↓ select · Enter confirm · e note · Esc cancel" }

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

/// A key while an option's field is open: Enter submits it, Esc leaves it
/// (the dialog stays open), ctrl-u clears it.
def field_step (d : DialogModel) (i : I64) (k : Key) : Pair DialogModel DialogStep :=
    match k {
        Key.enter => Pair.pair { d with field := Option.none } (DialogStep.submit i d.field_input.value),
        Key.escape => Pair.pair { d with field := Option.none } DialogStep.continue,
        Key.ctrl c =>
            if c == "u"
            then Pair.pair { d with field_input := input_state "" "" } DialogStep.continue
            else Pair.pair d DialogStep.continue,
        _ => Pair.pair { d with field_input := handle_input_key k d.field_input } DialogStep.continue,
    }

/// Enter on the selection: open its field when it has a value, else
/// choose it.
def enter_step (d : DialogModel) : Pair DialogModel DialogStep :=
    match Dialog.option_at d d.selected {
        Option.some o => match o.value {
            Option.some v => Pair.pair { d with field := Option.some d.selected, field_input := input_state v "" } DialogStep.continue,
            Option.none => Pair.pair d (DialogStep.choose d.selected),
        },
        Option.none => Pair.pair d (DialogStep.choose d.selected),
    }

/// One key's transition. An open field or note takes every key (Enter/Esc
/// leave it); otherwise arrows/Enter/letters drive the selection.
pub def Dialog.step (d : DialogModel) (k : Key) : Pair DialogModel DialogStep :=
    match d.field {
        Option.some i => field_step d i k,
        Option.none => select_step d k,
    }

def select_step (d : DialogModel) (k : Key) : Pair DialogModel DialogStep :=
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
            Key.enter => enter_step d,
            Key.up => Pair.pair { d with selected := (if d.selected < 1 then 0 else d.selected - 1) } DialogStep.continue,
            Key.down => Pair.pair { d with selected := (if d.selected + 1 < n then d.selected + 1 else (if n < 1 then 0 else n - 1)) } DialogStep.continue,
            Key.home => Pair.pair { d with selected := 0, scroll := 0 } DialogStep.continue,
            Key.end => Pair.pair { d with selected := (if n < 1 then 0 else n - 1) } DialogStep.continue,
            Key.page_up => Pair.pair { d with scroll := (if d.scroll < 5 then 0 else d.scroll - 5) } DialogStep.continue,
            Key.page_down => Pair.pair { d with scroll := d.scroll + 5 } DialogStep.continue,
            Key.char c =>
                if Bool.and d.notes (c == "e") then Pair.pair { d with editing := true } DialogStep.continue
                else if c == "k" then Pair.pair { d with selected := (if d.selected < 1 then 0 else d.selected - 1) } DialogStep.continue
                else if c == "j" then Pair.pair { d with selected := (if d.selected + 1 < n then d.selected + 1 else (if n < 1 then 0 else n - 1)) } DialogStep.continue
                else match option_key_at 0 c d.options {
                    Option.some i => Pair.pair d (DialogStep.choose i),
                    Option.none => Pair.pair d DialogStep.continue,
                },
            _ => Pair.pair d DialogStep.continue,
        }

/// A bracketed paste edits the open field or note; it never chooses an
/// option.
pub def Dialog.paste (d : DialogModel) (text : String) : DialogModel :=
    match d.field {
        Option.some _ => { d with field_input := insert_text text d.field_input },
        Option.none => if d.editing then { d with note := insert_text text d.note } else d,
    }

/// Wheel notches scroll the body; other mouse events do nothing.
def mouse_step (d : DialogModel) (m : MouseEvent) : DialogModel :=
    match m {
        MouseEvent.scroll_up _ _ => { d with scroll := (if d.scroll < 3 then 0 else d.scroll - 3) },
        MouseEvent.scroll_down _ _ => { d with scroll := d.scroll + 3 },
        _ => d,
    }

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
        Event.mouse m => Pair.pair (mouse_step d m) Option.none,
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
    body_count + Dialog.option_count d + (if d.notes then 7 else 5)

/// The frame's height on a `rows`-high terminal: the whole dialog when it
/// fits, else the screen less a row of margin a side (at least 6).
pub def Dialog.frame_height (rows : I64) (total : I64) : I64 :=
    let max_h : I64 := if rows - 2 < 6 then 6 else rows - 2 in
    if total + 4 < max_h then total + 4 else max_h

/// `frame_width`, or every column for a fullscreen dialog.
pub def Dialog.frame_width_for (d : DialogModel) (cols : I64) : I64 :=
    if d.fullscreen then (if cols < 1 then 1 else cols) else Dialog.frame_width cols

/// `frame_height`, or every row for a fullscreen dialog (at least 6).
pub def Dialog.frame_height_for (d : DialogModel) (rows : I64) (total : I64) : I64 :=
    if d.fullscreen then (if rows < 6 then 6 else rows) else Dialog.frame_height rows total

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
            let text : String := String.concat o.label (option_value d i o.value) in
            List.append (Dialog.text_rows style width (String.concat marker (String.concat text suffix)))
                (option_rows d (i + 1) width),
    }

/// An editable option's `: value`, with the caret while its field is open.
def option_value (d : DialogModel) (i : I64) (value : Option String) : String :=
    match value {
        Option.none => "",
        Option.some v => match d.field {
            Option.some j => if i == j then String.concat ": " (String.concat d.field_input.value "_") else String.concat ": " v,
            Option.none => String.concat ": " v,
        },
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
    let body_budget : I64 := body_budget_of height d in
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
        if d.notes then Dialog.text_rows dim width (note_text d) else List.empty,
        Dialog.text_rows dim width (Dialog.footer_line d (I64.lt body_budget (List.length body))),
    ] in
    take budget (List.flatten parts)

/// The footer, naming the scroll keys when the body does not fit.
pub def Dialog.footer_line (d : DialogModel) (overflow : Bool) : String :=
    if overflow then String.concat (footer_text d) " · PgUp/PgDn scroll" else footer_text d

def footer_text (d : DialogModel) : String :=
    match d.field {
        Option.some _ => "Enter apply · Esc cancel edit · ctrl-u clear",
        Option.none => d.footer,
    }

/// The body rows a `height`-high frame has room for.
def body_budget_of (height : I64) (d : DialogModel) : I64 :=
    let budget : I64 := if height - 4 < 1 then 1 else height - 4 in
    let fixed : I64 := Dialog.total_rows d 0 in
    if budget - fixed < 1 then 0 else budget - fixed

/// `d` scrolled no further than its last body row.
pub def Dialog.clamp_scroll (height : I64) (body_count : I64) (d : DialogModel) : DialogModel :=
    let room : I64 := body_budget_of height d in
    let max_scroll : I64 := if body_count - room < 0 then 0 else body_count - room in
    if max_scroll < d.scroll then { d with scroll := max_scroll } else d

/// The dialog in its rounded `border`-styled frame.
pub def Dialog.view (border : TextStyle) (width : I64) (height : I64) (d : DialogModel) (body : List SizedWidget) : Widget :=
    Widget.column [
        sized (LayoutSize.fill 1) (border_with border BorderStyle.rounded
            (padding 1 1 1 2 (Widget.column (Dialog.rows width height d body)))),
    ]

// ==================== the modal loop ====================

/// Paint the dialog centered on the screen, writing only the cells that
/// differ from `prev` (the last paint); with no `prev`, or after a resize,
/// the screen is cleared first. `body` renders the body at a content
/// width. Answers the painted screen and `d` with its scroll clamped.
pub def Dialog.paint (border : TextStyle) (body : I64 -> DialogModel -> List SizedWidget) (prev : Option Screen) (d : DialogModel) : IO (Pair Screen DialogModel) := do {
    let size <- Terminal.size;
    match size {
        Pair.pair rows cols => do {
            let frame_w : I64 := Dialog.frame_width_for d cols;
            let width : I64 := Dialog.content_width frame_w;
            let body_all : List SizedWidget := body width d;
            let height : I64 := Dialog.frame_height_for d rows (Dialog.total_rows d (List.length body_all));
            let d2 : DialogModel := Dialog.clamp_scroll height (List.length body_all) d;
            let rect : Rect := center_rect_in (mk_rect 0 0 cols rows) frame_w height;
            let base : Option Screen := same_screen prev rows cols;
            let _ <- match base {
                Option.some _ => IO.pure unit,
                Option.none => do { Terminal.clear_screen; Terminal.cursor_move 0 0 },
            };
            let old : Screen := match base { Option.some s => s, Option.none => empty_screen rows cols };
            let screen := render (Dialog.view border width height d2 body_all) rect (empty_screen rows cols);
            IO.write_stdout (apply_deltas (diff old screen));
            IO.flush_stdout;
            IO.pure (Pair.pair screen d2)
        }
    }
}

def same_screen (prev : Option Screen) (rows : I64) (cols : I64) : Option Screen :=
    match prev {
        Option.some s => if Bool.and (s.rows == rows) (s.cols == cols) then Option.some s else Option.none,
        Option.none => Option.none,
    }

def same_opt (a : Option I64) (b : Option I64) : Bool :=
    match a {
        Option.none => match b { Option.none => true, Option.some _ => false },
        Option.some x => match b { Option.none => false, Option.some y => x == y },
    }

/// Whether an event changed anything a paint shows.
def changed (a : DialogModel) (b : DialogModel) : Bool :=
    Bool.not (a.selected == b.selected && a.scroll == b.scroll && a.editing == b.editing
        && same_opt a.field b.field
        && a.note.value == b.note.value && a.note.cursor == b.note.cursor
        && a.field_input.value == b.field_input.value && a.field_input.cursor == b.field_input.cursor)

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

/// The modal's loop state: the dialog, the input decoder, decoded events
/// not yet folded, the last painted screen, and whether a repaint is due;
/// with a refresh, how many quiet polls run between calls and how many
/// have passed; `heal`, the quiet polls left before one full repaint
/// (0 = none scheduled).
struct ModalState {
    d : DialogModel,
    r : InputReader,
    queued : List Event,
    prev : Option Screen,
    dirty : Bool,
    refresh : Option (DialogModel -> IO (Option DialogModel)),
    every : I64,
    idle : I64,
    heal : I64 := 0,
}

/// What one modal step decided: keep going, or end with this answer.
type ModalNext {
    more (s : ModalState),
    done (result : Pair DialogModel DialogStep),
}

/// The modal loop, one step per call, as plain recursion with a single
/// self-call: the IO do-bind fusion leaves it in tail position and
/// `tco.mo` makes it a back-edge, so a dialog left open for hours polls in
/// constant stack (`plans/bootstrapping/heapless-loops.md`). The old
/// multi-function loop nested a native frame per 100 ms poll and
/// overflowed its fiber's stack.
#[partial]
def modal_loop (paint : Option Screen -> DialogModel -> IO (Pair Screen DialogModel)) (s : ModalState) : IO (Pair DialogModel DialogStep) := do {
    let next <- modal_step paint s;
    // Annotated local: the do-binder's own type is not inferred.
    let decided : ModalNext := next;
    match decided {
        ModalNext.done result => IO.pure result,
        ModalNext.more s2 => modal_loop paint s2,
    }
}

/// One modal step: repaint when the dialog or the terminal size changed,
/// then fold one queued event or poll stdin once.
def modal_step (paint : Option Screen -> DialogModel -> IO (Pair Screen DialogModel)) (s : ModalState) : IO ModalNext := do {
    let size <- Terminal.size;
    let resized : Bool := match s.prev {
        Option.none => true,
        Option.some p => match size { Pair.pair rows cols => Bool.not (Bool.and (p.rows == rows) (p.cols == cols)) },
    };
    let painted <- if Bool.or s.dirty resized
        then paint s.prev s.d
        else IO.pure (Pair.pair (match s.prev { Option.some p => p, Option.none => empty_screen 0 0 }) s.d);
    match painted {
        Pair.pair screen d1 => modal_advance { s with d := d1, prev := Option.some screen, dirty := false },
    }
}

/// Fold the next queued event, or poll stdin once when none is queued.
def modal_advance (s : ModalState) : IO ModalNext :=
    match s.queued {
        List.cons e rest => IO.pure (Modal.fold s e rest),
        List.empty => modal_poll s,
    }

/// Fold one decoded event: an answer ends the modal; otherwise a repaint
/// is due only if the event changed what a paint shows. A regained focus
/// forgets the last paint, so the next step clears and repaints all of
/// it: the dialog's diff only knows its own writes, and whatever touched
/// the screen while the window was away is repaired here.
def Modal.fold (s : ModalState) (e : Event) (rest : List Event) : ModalNext :=
    match e {
        Event.focus_in => ModalNext.more (Modal.forget { s with queued := rest }),
        _ => Modal.fold_dialog s e rest,
    }

/// Drop the last paint: the next step clears the screen and paints the
/// whole dialog.
pub def Modal.forget (s : ModalState) : ModalState :=
    { s with prev := Option.none, dirty := true }

def Modal.fold_dialog (s : ModalState) (e : Event) (rest : List Event) : ModalNext :=
    match Dialog.apply s.d e {
        Pair.pair d2 step => match step {
            Option.some a => ModalNext.done (Pair.pair d2 a),
            Option.none => ModalNext.more { s with d := d2, queued := rest, dirty := changed s.d d2 },
        },
    }

/// Wait up to 100 ms for input. A quiet poll with a lone ESC pending is
/// the Escape key; EOF cancels.
def modal_poll (s : ModalState) : IO ModalNext := do {
    let ready <- Terminal.poll 100;
    if ready
    then modal_read s
    else modal_quiet (Modal.idle s)
}

/// A quiet poll that did not end the modal counts toward the refresh.
def modal_quiet (next : ModalNext) : IO ModalNext :=
    match next {
        ModalNext.done _ => IO.pure next,
        ModalNext.more s => match s.refresh {
            Option.none => IO.pure next,
            Option.some f =>
                if Dialog.refresh_due s.idle s.every then modal_refresh f s
                else IO.pure (ModalNext.more { s with idle := s.idle + 1 }),
        },
    }

def modal_refresh (f : DialogModel -> IO (Option DialogModel)) (s : ModalState) : IO ModalNext := do {
    let got <- f s.d;
    IO.pure (ModalNext.more (match got {
        Option.none => { s with idle := 0 },
        Option.some d2 => { s with d := d2, idle := 0, dirty := true },
    }))
}

/// Whether this quiet poll, after `idle` earlier ones, is the refresh's.
pub def Dialog.refresh_due (idle : I64) (every : I64) : Bool :=
    Bool.not (idle + 1 < every)

/// A quiet poll: EOF cancels, a pending lone ESC becomes the Escape key
/// (it leaves an open field or note, else cancels), a scheduled heal
/// counts down to its full repaint, anything else waits.
def Modal.idle (s : ModalState) : ModalNext :=
    if s.r.closed
    then ModalNext.done (Pair.pair s.d DialogStep.cancel)
    else if s.r.pending == "\u{1b}"
    then ModalNext.more { s with r := { s.r with pending := "" }, queued := [Event.key Key.escape] }
    else if s.heal == 1 then ModalNext.more (Modal.forget { s with heal := 0 })
    else if 1 < s.heal then ModalNext.more { s with heal := s.heal - 1 }
    else ModalNext.more s

def modal_read (s : ModalState) : IO ModalNext := do {
    let got <- read_events s.r;
    match got {
        Pair.pair evs r2 =>
            if Bool.and r2.closed (List.is_empty evs)
            then IO.pure (ModalNext.done (Pair.pair s.d DialogStep.cancel))
            else IO.pure (ModalNext.more { s with r := r2, queued := evs }),
    }
}

/// Run the dialog over stdin until it is chosen, cancelled, submitted or
/// stdin closes. The final dialog rides along so the caller can read the
/// note.
pub def Dialog.modal (paint : Option Screen -> DialogModel -> IO (Pair Screen DialogModel)) (d : DialogModel) : IO (Pair DialogModel DialogStep) :=
    modal_start Option.none 0 0 paint d

/// `Dialog.modal`, repainting the whole dialog once after `heal` quiet
/// polls (100 ms each). For a dialog that may have opened while another
/// painter was still drawing (weaver: the main loop's ack timed out).
pub def Dialog.modal_healing (heal : I64) (paint : Option Screen -> DialogModel -> IO (Pair Screen DialogModel)) (d : DialogModel) : IO (Pair DialogModel DialogStep) :=
    modal_start Option.none 0 heal paint d

/// `Dialog.modal`, calling `refresh` every `every` quiet polls (100 ms
/// each): `some` replaces the dialog and repaints it, `none` keeps it.
pub def Dialog.modal_refresh (every : I64) (refresh : DialogModel -> IO (Option DialogModel)) (paint : Option Screen -> DialogModel -> IO (Pair Screen DialogModel)) (d : DialogModel) : IO (Pair DialogModel DialogStep) :=
    modal_start (Option.some refresh) every 0 paint d

def modal_start (refresh : Option (DialogModel -> IO (Option DialogModel))) (every : I64) (heal : I64) (paint : Option Screen -> DialogModel -> IO (Pair Screen DialogModel)) (d : DialogModel) : IO (Pair DialogModel DialogStep) := do {
    let size <- Terminal.size;
    let start : ModalState := match size {
        Pair.pair rows cols => { d := d, r := input_reader rows cols, queued := List.empty, prev := Option.none, dirty := true,
            refresh := refresh, every := every, idle := 0, heal := heal },
    };
    modal_loop paint start
}
