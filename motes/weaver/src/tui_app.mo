/// Weaver's TUI driver -- weaver.md Phase 4, now that `tui::run_app`
/// supports `Cmd.perform` (see `motes/tui/src/tui.mo`'s header). `update`
/// lives HERE rather than in `model.mo`: it closes over `run_submitted_line`
/// (a model turn or a slash command) and `Gate.weaver_tui` (the approval
/// overlay), and putting those in `model.mo` would need `model.mo` to
/// import this file for the gate/turn machinery while THIS file already
/// needs `model.mo` for `TuiModel`/`WeaverMsg` -- a cycle. `model.mo` stays
/// the pure half (`TuiModel`/`WeaverMsg`/`view`); everything that touches
/// `IO` sits here.
///
/// `Gate.weaver_tui` does not thread the main loop's `InputReader` through
/// shuttle's sealed `Pick -> IO Approval` seam -- there is no `IORef` to
/// carry that state across, and an approval prompt is modal (nothing else
/// reads stdin meanwhile) -- so it owns a private one-shot key read
/// instead, and a full-screen (not diffed) render of the pick. `tui.mo`'s
/// `Cmd.perform`-fires-a-forced-repaint rule is what cleans the real
/// screen up again on the next ordinary frame.
use shuttle::agent {RunState}
use shuttle::gate {Pick, Approval, Gate, Capability}
use shuttle::message {Message}
use shuttle::message_types {Role, Content}
use weaver::commands {WeaverState, Effect, Effect.ok, set_fatal, Commands.dispatch}
use weaver::policy {Mode, Mode.cycle, Policy.decide, Decision}
use weaver::gate {pick_header, cap_name, capped_diff}
use weaver::diff {Diff.for_input, Diff.lines}
use weaver::dumb {append_user, drive_loop}
use weaver::model {
    TuiModel, WeaverMsg, Window, on_event, init_tui_model, init_tui_model_with,
    Model.view, Model.scroll_step, Model.append_block, Model.append_lines,
    Model.window, Model.needs_page, Model.page_request, Model.hist_keep,
    DisplayRow, Model.display_line, Model.take_last_rows, Model.display_row_widget,
    Model.refresh_rows, Model.begin_selection, Model.drag_selection, Model.finish_selection,
    list_length, panel_height, input_placeholder,
}
use weaver::store {
    Transcript, TranscriptPage, StoreState,
    Transcript.empty, Transcript.with_page, Transcript.next_block, Transcript.append,
    Store.read_page, Store.append_transcript, Store.record_turn, Store.record_output,
    Store.startup_transcript, Store.append_chunk, Store.discard_live,
    Store.append_history_note,
}
use weaver::commands {TranscriptChange}
use shuttle::session {Session}
use weaver::theme {theme_split_lines, theme_line_style_with, theme_border_style_with}
use weaver::store {TLine, TLine.plain, TLine.user_line}
use weaver::error {WeaverError, WeaverError.show, WeaverError.recoverable}
use tui::types {Event, Key, MouseEvent, MouseButton, LayoutSize, TextStyle, Rect}
use tui::widget {Widget, SizedWidget, BorderStyle, border, padding, sized, label, with_style}
use tui::widgets::input {InputState, input_state, handle_input_multiline_key, insert_text}
use tui::widgets::input {handle_input_key}
use tui::core {empty_screen, mk_rect}
use tui::render {render, diff, apply_deltas}
use tui::text {Text.take_width}
use tui::clipboard {Clipboard.copy}
use tui::layout {center_rect_in}
use weaver::dialog {
    Dialog, DialogOption, DialogStep, Dialog.make, Dialog.step, Dialog.paste,
    Dialog.with_default, Dialog.note_text, Dialog.option_count,
}
use tui::terminal {
    Terminal.clear_screen, Terminal.cursor_move, Terminal.enter_raw_mode, Terminal.poll, Terminal.size,
}
use tui::input {Input.decode}
use tui::tui {App, Cmd, run_app}
use init::transformers {ResultT}
use std::io {IO.read_stdin_exact, IO.write_stdout, IO.flush_stdout}
use std::list {List.intercalate}

// ── Tui.run: the tty probe and the App wiring ───────────────────────────

/// Probes `Terminal.enter_raw_mode` -- `false` when stdin is not a tty
/// (the native degrades instead of failing, `terminal.mo`'s own
/// contract), which doubles as the auto-detect `main.mo` needs: no
/// other terminal write happens before this check, so the caller can
/// fall back to `Dumb.run` cleanly. `true` runs the whole TUI to
/// completion (quit or EOF) before returning.
pub def Tui.run (st : WeaverState) : IO Bool :=
    Tui.run_resumed st Transcript.empty

/// The startup tail is loaded before `run_app` builds the model, so the
/// first frame already shows the previous session.
pub def Tui.run_resumed (st : WeaverState) (tr : Transcript) : IO Bool := do {
    let is_tty <- Terminal.enter_raw_mode;
    if Bool.not is_tty
    then return false
    else do {
        let size <- Terminal.size;
        run_tui_with_size st tr size
    }
}

def run_tui_with_size (st : WeaverState) (tr : Transcript) (size : Pair I64 I64) : IO Bool :=
    match size {
        Pair.pair rows cols => do {
            // 100 ms: the tick is the spinner's frame clock AND the
            // async-turn poll cadence (a completed turn's result joins
            // the next batch within one tick); idle ticks with an
            // unchanged model are zero-diff draws. The tui default (-1)
            // stays untouched.
            let app : App TuiModel WeaverMsg :=
                App.app_ticked (init_tui_model_with st rows cols tr) on_event TuiApp.update Model.view 100
                    (fn (m : TuiModel) => Bool.or m.turn_pending (Bool.and m.banner (m.banner_frame < 12)));
            let _ <- run_app app;
            return true
        }
    }

// ── update ───────────────────────────────────────────────────────────────

/// Named `TuiApp.update`, not bare `update` -- a one-word generic name
/// is exactly the shape that collides across a whole-program check
/// (`Model.view` already did), so this one is qualified pre-emptively.
pub def TuiApp.update (m : TuiModel) (msg : WeaverMsg) : Pair TuiModel (Cmd WeaverMsg) :=
    let step := update_msg m msg in
    match step {
        Pair.pair m2 cmd => Pair.pair (Model.refresh_rows m2) cmd,
    }

def update_msg (m : TuiModel) (msg : WeaverMsg) : Pair TuiModel (Cmd WeaverMsg) :=
    match msg {
        WeaverMsg.key_event e => update_event m e,
        WeaverMsg.turn_result run lines delta => turn_result_step m run lines delta,
        WeaverMsg.turn_failed run e => failure_step m run e,
        WeaverMsg.command_result effect => command_result_step m effect,
        WeaverMsg.command_failed e => failure_step m m.state.run e,
        WeaverMsg.page_loaded page => page_loaded_step m page,
        WeaverMsg.page_failed e => page_failed_step m e,
        WeaverMsg.transcript_reset tr => transcript_reset_step m tr,
        WeaverMsg.store_result e => store_result_step m e,
        WeaverMsg.input_set text =>
            Pair.pair { m with input := input_state text input_placeholder, banner := false } Cmd.none,
    }

// ── persistence commands ─────────────────────────────────────────────────

#[partial]
def plain_lines (ss : List String) : List TLine :=
    List.map TLine.plain ss

def append_block_at (m : TuiModel) (lines : List TLine) : Pair TuiModel (Pair I64 (List TLine)) :=
    let block : List TLine := Transcript.next_block m.transcript lines in
    let start : I64 := m.transcript.total in
    let m2 : TuiModel := Model.append_block m lines in
    Pair.pair m2 (Pair.pair start block)

def warning_of (r : Result String Unit) : Option String :=
    match r {
        Result.err e => Option.some e,
        Result.ok _ => Option.none,
    }

def persist_block_cmd (store : Option StoreState) (start : I64) (block : List TLine) : Cmd WeaverMsg :=
    match store {
        Option.none => Cmd.none,
        Option.some s => Cmd.perform (fn (_ : Unit) => do {
            let r <- Store.append_transcript s.dir start block;
            IO.pure (WeaverMsg.store_result (warning_of r))
        }),
    }

/// `live.txt` is the only copy of the streamed text until the turn's
/// block is written, so it is discarded ONLY after a successful write.
def discard_live_msg (s : StoreState) : IO WeaverMsg := do {
    let _ <- Store.discard_live s;
    IO.pure (WeaverMsg.store_result Option.none)
}

/// Clear the real screen after an action that wrote outside the frame
/// pipeline (the live progress row). The following forced repaint then
/// starts from a blank terminal instead of inheriting the fragment.
def clear_terminal : IO Unit := do {
    Terminal.clear_screen;
    Terminal.cursor_move 0 0
}

def after_clear (action : IO WeaverMsg) : IO WeaverMsg := do {
    let msg <- action;
    clear_terminal;
    IO.pure msg
}

def persist_turn_action (s : StoreState) (run : RunState) (delta : List Message) (start : I64) (block : List TLine) : IO WeaverMsg :=
    after_clear (record_turn_action s run delta start block)

def record_turn_action (s : StoreState) (run : RunState) (delta : List Message) (start : I64) (block : List TLine) : IO WeaverMsg := do {
    let r <- Store.record_turn s run.session delta start block;
    match r {
        Result.err e => IO.pure (WeaverMsg.store_result (Option.some e)),
        Result.ok _ => discard_live_msg s,
    }
}

def persist_turn_cmd (store : Option StoreState) (run : RunState) (delta : List Message) (start : I64) (block : List TLine) : Cmd WeaverMsg :=
    match store {
        Option.none => repaint_cmd,
        Option.some s => Cmd.perform (fn (_ : Unit) => persist_turn_action s run delta start block),
    }

def persist_output_action (s : StoreState) (sess : Session) (start : I64) (block : List TLine) : IO WeaverMsg :=
    after_clear (record_output_action s sess start block)

def record_output_action (s : StoreState) (sess : Session) (start : I64) (block : List TLine) : IO WeaverMsg := do {
    let r <- Store.record_output s sess block start;
    match r {
        Result.err e => IO.pure (WeaverMsg.store_result (Option.some e)),
        Result.ok _ => discard_live_msg s,
    }
}

def persist_output_cmd (fallback : Cmd WeaverMsg) (store : Option StoreState) (start : I64) (block : List TLine) (sess : Session) : Cmd WeaverMsg :=
    match store {
        Option.none => fallback,
        Option.some s => Cmd.perform (fn (_ : Unit) => persist_output_action s sess start block),
    }

def turn_result_step (m : TuiModel) (run : RunState) (lines : List TLine) (delta : List Message) : Pair TuiModel (Cmd WeaverMsg) :=
    let with_run : TuiModel := set_run m run in
    let pair := append_block_at with_run lines in
    match pair {
        Pair.pair m2 at => match at {
            Pair.pair start block =>
                let m3 : TuiModel := with_turn_end (fn (mm : TuiModel) => mm) m2 in
                let store : Option StoreState := m3.state.store in
                Pair.pair m3 (persist_turn_cmd store run delta start block),
        },
    }

/// A failed turn or command: the error line lands, then the failure's one
/// classification decides. A fatal error quits without persisting the
/// final line (`Cmd.quit` cannot ride with a `Cmd.perform`).
def failure_step (m : TuiModel) (run : RunState) (e : WeaverError) : Pair TuiModel (Cmd WeaverMsg) :=
    let with_run : TuiModel := set_run m run in
    let pair := append_block_at with_run [error_line e] in
    match pair {
        Pair.pair m2 at => match at {
            Pair.pair start block =>
                if WeaverError.recoverable e
                then
                    let m3 : TuiModel := with_turn_end (fn (mm : TuiModel) => mm) m2 in
                    let store : Option StoreState := m3.state.store in
                    Pair.pair m3 (persist_output_cmd Cmd.none store start block m3.state.run.session)
                else
                    let m3 : TuiModel := with_turn_end (fn (mm : TuiModel) => mm) m2 in
                    let st2 : WeaverState := set_fatal m3.state e in
                    let m4 : TuiModel := set_state m3 st2 in
                    Pair.pair m4 Cmd.quit,
        },
    }

// ── transcript paging ────────────────────────────────────────────────────

/// The window after a scroll delta, plus a page load when the requested
/// range is above the loaded tail and no page covers it.
def scroll_with_pages (m : TuiModel) (delta : I64) : Pair TuiModel (Cmd WeaverMsg) :=
    let m2 : TuiModel := with_streak_reset (fn (mm : TuiModel) => Model.scroll_step mm delta) m in
    maybe_page_cmd m2

def maybe_page_cmd (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    match m.state.store {
        Option.none => Pair.pair m Cmd.none,
        Option.some st => page_cmd_for m st,
    }

def page_cmd_for (m : TuiModel) (st : StoreState) : Pair TuiModel (Cmd WeaverMsg) :=
    let w : Window := Model.window m in
    if Bool.not (Model.needs_page m w) then Pair.pair m Cmd.none
    else if m.page_pending then Pair.pair m Cmd.none
    else match Model.page_request m w {
        Option.none => Pair.pair m Cmd.none,
        Option.some req => match req {
            Pair.pair start count =>
                let m2 : TuiModel := { m with page_pending := true } in
                Pair.pair m2 (Cmd.perform (fn (_ : Unit) => load_page st start count)),
        },
    }

def load_page (st : StoreState) (start : I64) (count : I64) : IO WeaverMsg := do {
    let r <- Store.read_page st.dir start count;
    match r {
        Result.err e => IO.pure (WeaverMsg.page_failed e),
        Result.ok p => IO.pure (WeaverMsg.page_loaded p),
    }
}

/// The rows cache keys on `page.start` only, so a page that EXTENDS the
/// loaded range (same start) would otherwise reuse stale blank rows;
/// every transcript/page replacement drops the key instead.
def page_loaded_step (m : TuiModel) (p : TranscriptPage) : Pair TuiModel (Cmd WeaverMsg) :=
    let prev : Option TranscriptPage := m.transcript.page in
    let tr : Transcript := Transcript.with_page m.transcript p in
    let m2 : TuiModel := { m with transcript := tr, page_pending := false, rows_key := Option.none } in
    if same_page prev p
    then Pair.pair (with_page_error m2 "page read made no progress") Cmd.none
    else maybe_page_cmd m2

/// The same page served twice means the store cannot cover the window
/// (a short block file, or a window taller than one page): stop rather
/// than re-requesting it inline forever.
#[partial]
def tline_count (ls : List TLine) : I64 :=
    match ls {
        List.empty => 0,
        List.cons _ rest => 1 + tline_count rest,
    }

def same_page (old : Option TranscriptPage) (p : TranscriptPage) : Bool :=
    match old {
        Option.none => false,
        Option.some q => Bool.and (q.start == p.start) (tline_count q.lines == tline_count p.lines),
    }

def with_page_error (m : TuiModel) (e : String) : TuiModel :=
    let tr0 : Transcript := m.transcript in
    let tr : Transcript := { tr0 with page_error := Option.some e } in
    let m2 : TuiModel := { m with transcript := tr } in
    m2

def page_failed_step (m : TuiModel) (e : String) : Pair TuiModel (Cmd WeaverMsg) :=
    let m2 : TuiModel := { m with page_pending := false, rows_key := Option.none } in
    let m3 : TuiModel := with_page_error m2 e in
    Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m3) Cmd.none

def transcript_reset_step (m : TuiModel) (tr : Transcript) : Pair TuiModel (Cmd WeaverMsg) :=
    let m2 : TuiModel := { m with transcript := tr, scroll := 0, page_pending := false, rows_key := Option.none, banner := true, banner_frame := 0 } in
    maybe_page_cmd m2

/// A store write failure disables persistence for the rest of the run;
/// the session keeps working in memory.
def store_result_step (m : TuiModel) (e : Option String) : Pair TuiModel (Cmd WeaverMsg) :=
    match e {
        Option.none => Pair.pair m Cmd.none,
        Option.some msg =>
            let st0 : WeaverState := m.state in
            let st : WeaverState := { st0 with store := Option.none } in
            let line : String := String.concat "warning: transcript persistence disabled: " msg in
            Pair.pair (Model.append_lines { m with state := st } [TLine.plain line]) Cmd.none,
    }

/// A turn's or command's completion: the fold `f` runs, the streak
/// resets, and `turn_pending` clears -- the spinner stops.
def with_turn_end (f : TuiModel -> TuiModel) (m : TuiModel) : TuiModel :=
    { (with_streak_reset f m) with turn_pending := false }

/// The completion frame's repaint: a trivial `perform` forces the next
/// draw to repaint from blank (`step_cmd`'s force_repaint rule), which
/// cleans whatever the raw `TuiApp.progress` fragment wrote on the
/// transcript's last row mid-turn -- the sync loop's own
/// perform-enforced repaint, re-created at completion. The tick it
/// folds is a harmless no-op (`update_event` leaves an idle tick's
/// model untouched).
def repaint_cmd : Cmd WeaverMsg :=
    Cmd.perform (fn (_ : Unit) => do {
        clear_terminal;
        IO.pure (WeaverMsg.key_event Event.tick)
    })

def command_result_step (m : TuiModel) (effect : Effect) : Pair TuiModel (Cmd WeaverMsg) :=
    match effect.transcript {
        TranscriptChange.keep => command_keep m effect,
        TranscriptChange.reset => command_reset m effect,
    }

def command_keep (m : TuiModel) (effect : Effect) : Pair TuiModel (Cmd WeaverMsg) :=
    let with_state : TuiModel := set_state m effect.state in
    let pair := append_block_at with_state (plain_lines (Diff.lines effect.output)) in
    match pair {
        Pair.pair m2 at => match at {
            Pair.pair start block =>
                let m3 : TuiModel := with_turn_end (fn (mm : TuiModel) => mm) m2 in
                if effect.state.quit then Pair.pair m3 Cmd.quit
                else
                    let store : Option StoreState := m3.state.store in
                    Pair.pair m3 (persist_output_cmd repaint_cmd store start block m3.state.run.session),
        },
    }

/// `/clear` and `/resume`: replace the window with the new session's
/// tail (plus the command's own line).
def command_reset (m : TuiModel) (effect : Effect) : Pair TuiModel (Cmd WeaverMsg) :=
    let with_state : TuiModel := set_state m effect.state in
    let m2 : TuiModel := with_turn_end (fn (mm : TuiModel) => mm) with_state in
    match m2.state.store {
        Option.none => reset_in_memory m2 effect.output,
        Option.some st => Pair.pair m2 (Cmd.perform (fn (_ : Unit) => reset_action st effect.output)),
    }

def reset_in_memory (m : TuiModel) (output : String) : Pair TuiModel (Cmd WeaverMsg) :=
    let tr : Transcript := Transcript.append Transcript.empty (plain_lines (theme_split_lines output)) in
    let m2 : TuiModel := { m with transcript := tr, scroll := 0, page_pending := false } in
    Pair.pair m2 Cmd.none

def reset_action (st : StoreState) (output : String) : IO WeaverMsg := do {
    let tr0 <- Store.startup_transcript st.dir;
    let total : I64 := tr0.total;
    let block : List TLine := Transcript.next_block tr0 (plain_lines (theme_split_lines output));
    let _ <- Store.append_transcript st.dir total block;
    IO.pure (WeaverMsg.transcript_reset (Transcript.append tr0 block))
}

def update_event (m : TuiModel) (e : Event) : Pair TuiModel (Cmd WeaverMsg) :=
    match e {
        Event.key k => update_key m k,
        Event.resize rows cols =>
            Pair.pair (with_streak_reset (fn (mm : TuiModel) => set_size mm rows cols) m) Cmd.none,
        Event.paste text =>
            Pair.pair (with_streak_reset (fn (mm : TuiModel) => { mm with input := insert_text text mm.input }) m) Cmd.none,
        Event.mouse me => update_mouse m me,
        // The frame clock: the spinner advances ONLY while a turn is
        // pending, so an idle tick folds to an unchanged model (a
        // zero-diff draw). Deliberately NO streak reset -- ticks arrive
        // every 100 ms and would make the double-Ctrl-C gesture
        // impossible.
        Event.tick =>
            let m1 : TuiModel := if m.turn_pending
                then { m with spinner_frame := m.spinner_frame + 1 }
                else m in
            if Bool.and m1.banner (m1.banner_frame < 12)
            then Pair.pair { m1 with banner_frame := m1.banner_frame + 1 } Cmd.none
            else Pair.pair m1 Cmd.none,
        _ => Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m) Cmd.none,
    }

/// The mouse's gestures: the wheel scrolls (three rows a notch), and a
/// left drag selects transcript text (the selection is highlighted while
/// dragging and copied through OSC 52 on release). Other buttons are
/// ignored.
def is_left (b : MouseButton) : Bool :=
    match b {
        MouseButton.left => true,
        _ => false,
    }

def update_mouse (m : TuiModel) (me : MouseEvent) : Pair TuiModel (Cmd WeaverMsg) :=
    match me {
        MouseEvent.scroll_up _ _ => scroll_with_pages m wheel_step,
        MouseEvent.scroll_down _ _ => scroll_with_pages m (0 - wheel_step),
        MouseEvent.press btn r c =>
            if is_left btn
            then Pair.pair (with_streak_reset (fn (mm : TuiModel) => Model.begin_selection mm r c) m) Cmd.none
            else Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m) Cmd.none,
        MouseEvent.drag btn r c =>
            if is_left btn
            then Pair.pair (with_streak_reset (fn (mm : TuiModel) => Model.drag_selection mm r c) m) Cmd.none
            else Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m) Cmd.none,
        MouseEvent.release btn r c =>
            if is_left btn
            then finish_selection_step m r c
            else Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m) Cmd.none,
    }

/// End a drag: the release point is folded in one last time, the model
/// drops the highlight, and a non-empty selection is copied (a perform,
/// so the forced repaint also repaints the de-highlighted row).
def finish_selection_step (m : TuiModel) (r : I64) (c : I64) : Pair TuiModel (Cmd WeaverMsg) :=
    let dragged : TuiModel := Model.drag_selection m r c in
    match Model.finish_selection dragged {
        Pair.pair m2 text => match text {
            Option.none => Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m2) Cmd.none,
            Option.some t => Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m2)
                (Cmd.perform (fn (_ : Unit) => do {
                    Clipboard.copy t;
                    IO.pure (WeaverMsg.key_event Event.tick)
                })),
        },
    }

def wheel_step : I64 := 3

def update_key (m : TuiModel) (k : Key) : Pair TuiModel (Cmd WeaverMsg) :=
    match k {
        Key.tab => Pair.pair (with_streak_reset cycle_mode m) Cmd.none,
        Key.enter => enter_key m,
        Key.up => hist_key m,
        Key.down => hist_down_key m,
        Key.page_up => scroll_with_pages m (page_step m),
        Key.page_down => scroll_with_pages m (0 - page_step m),
        Key.ctrl c =>
            if c == "c" then ctrl_c_step m
            else if c == "u" then scroll_with_pages m (half_page m)
            else if c == "d" then scroll_with_pages m (0 - half_page m)
            else Pair.pair (streak_reset_input m k) Cmd.none,
        Key.end => Pair.pair (with_streak_reset (fn (mm : TuiModel) => { mm with scroll := 0 }) m) Cmd.none,
        Key.home => scroll_with_pages m 999999,
        _ => Pair.pair (streak_reset_input m k) Cmd.none,
    }

/// A screenful of CONTENT rows: the panel minus the indicator row it
/// spends while scrolled.
def page_step (m : TuiModel) : I64 :=
    let h : I64 := panel_height m in
    if h < 2 then 1 else h - 1

/// The half-page scroll: half a screen, at least one row (Claude
/// Code's Ctrl+U/Ctrl+D binding).
def half_page (m : TuiModel) : I64 :=
    let h : I64 := page_step m in
    if h < 2 then 1 else h / 2

def streak_reset_input (m : TuiModel) (k : Key) : TuiModel :=
    { (multiline_input m k) with ctrl_c_streak := 0 }

def multiline_input (m : TuiModel) (k : Key) : TuiModel :=
    { m with input := handle_input_multiline_key k m.input }

// ── prompt history (the up/down gesture) ────────────────────────────────

/// ArrowUp: history from an EMPTY input (otherwise the gesture is the
/// multiline cursor's, handled in the input field), and CONTINUED
/// history while a walk is already open (a recalled value is not
/// empty). Recall shows the entry and walks OLDER ones on repeats.
#[partial]
def hist_key (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    let browsing : Bool := Bool.not (m.hist_idx < 0) in
    if Bool.or browsing (String.is_empty m.input.value)
    then Pair.pair (with_streak_reset hist_up m) Cmd.none
    else Pair.pair (streak_reset_input m Key.up) Cmd.none

/// ArrowDown while browsing steps younger; at the first entry it
/// returns to the live edit (empty box, placeholder back). Not
/// browsing = the multiline cursor's move.
#[partial]
def hist_down_key (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    let browsing : Bool := Bool.not (m.hist_idx < 0) in
    if browsing
    then Pair.pair (with_streak_reset hist_down m) Cmd.none
    else Pair.pair (streak_reset_input m Key.down) Cmd.none

#[partial]
def hist_up (m : TuiModel) : TuiModel :=
    let next : I64 := m.hist_idx + 1 in
    if Bool.not (next < list_length m.hist)
    then m
    else hist_show m next

#[partial]
def hist_down (m : TuiModel) : TuiModel :=
    if m.hist_idx < 0
    then m
    else
        let next : I64 := m.hist_idx - 1 in
        if next < 0
        then { m with hist_idx := 0 - 1, input := input_state "" input_placeholder }
        else hist_show m next

#[partial]
def hist_show (m : TuiModel) (idx : I64) : TuiModel :=
    let value : String := hist_at m.hist idx in
    { m with hist_idx := idx, input := input_state value input_placeholder }

#[partial]
def hist_at (xs : List String) (i : I64) : String :=
    match xs {
        List.empty => "",
        List.cons h rest => if i < 1 then h else hist_at rest (i - 1),
    }

/// `with_streak_reset f m` = apply `f`, then zero the streak.
def with_streak_reset (f : TuiModel -> TuiModel) (m : TuiModel) : TuiModel :=
    { (f m) with ctrl_c_streak := 0 }

/// One Ctrl+C press: the first since the last other event appends a
/// hint line; the second CONSECUTIVE one quits through `run_app`'s own
/// exit -- `restore_terminal`, alt screen and raw mode both unwound.
/// Consecutive-event streak, not a timed window: a pure update has no
/// clock. Any other key or message zeroes the streak.
def ctrl_c_step (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    if m.ctrl_c_streak > 0
    then Pair.pair m Cmd.quit
    else
        let m1 : TuiModel := { m with ctrl_c_streak := 1 } in
        let start : I64 := m1.transcript.total in
        let m2 : TuiModel := Model.append_lines m1 [TLine.plain ctrl_c_hint_line] in
        // While a turn runs its fiber owns the store: an inline append
        // would race the echoed prompt (and the shared index temp file),
        // so the hint stays in memory -- it is a UI line, not content.
        let cmd : Cmd WeaverMsg :=
            if m.turn_pending then Cmd.none else persist_block_cmd m2.state.store start [TLine.plain ctrl_c_hint_line] in
        Pair.pair m2 cmd

def ctrl_c_hint_line : String := "press Ctrl+C again to exit (or /quit)"

def edit_input (m : TuiModel) (k : Key) : TuiModel :=
    { m with input := handle_input_multiline_key k m.input }

def cycle_mode (m : TuiModel) : TuiModel :=
    let st2 : WeaverState := { (m.state) with mode := Mode.cycle m.state.mode } in
    set_state m st2

/// Enter with a non-empty line: echo it into the transcript right away
/// and clear the box, then `perform_async` the real work -- a model
/// turn or a slash command -- off the state as it was BEFORE this key,
/// which `run_submitted_line` closes over. The submit FORKS: the UI
/// keeps folding ticks (the spinner) while the turn runs on its fiber,
/// and `turn_pending` rides along so a second submit is refused until
/// the result folds back (turns are serial: one pending handle, one
/// consumer).
def enter_key (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    let text : String := String.trim m.input.value in
    if Bool.or (String.is_empty text) m.turn_pending
    then Pair.pair m Cmd.none
    else
        let st : WeaverState := m.state in
        let echo : List TLine := echo_lines text in
        let block : List TLine := Transcript.next_block m.transcript echo in
        let start : I64 := m.transcript.total in
        let store : Option StoreState := m.state.store in
        let m2 : TuiModel :=
            { (with_streak_reset
                (fn (mm : TuiModel) => Model.append_block (hist_push (clear_input mm) text) echo) m)
                with turn_pending := true, banner := false } in
        Pair.pair m2 (Cmd.perform_async (fn (_ : Unit) => do {
            let _ <- write_echo store start block;
            run_submitted_line st text
        }))

/// The submitted line's echo block is durable before the turn starts (it
/// rides the async action -- a pure update cannot write).
def write_echo (store : Option StoreState) (start : I64) (block : List TLine) : IO (Result String Unit) :=
    match store {
        Option.none => IO.pure (Result.ok unit),
        Option.some s => do {
            let _ <- Store.discard_live s;
            Store.append_transcript s.dir start block
        },
    }

/// A submitted line enters the history (most recent first, deduped
/// against the current head) and the walk index returns to live.
#[partial]
def hist_push (m : TuiModel) (text : String) : TuiModel :=
    let pushed : List String :=
        match m.hist {
            List.empty => hist_cons_empty text,
            List.cons h rest => if h == text then m.hist else List.cons text m.hist,
        } in
    { m with hist := Model.hist_keep pushed, hist_idx := 0 - 1 }

#[partial]
def hist_cons_empty (text : String) : List String :=
    List.cons text List.empty

/// A submitted line is echoed as its OWN lines, all tagged as the user's
/// role -- a multiline submit is one undivided block, styled cyan with no
/// prefix. The blank separator before the block (and the next one) is the
/// spacing that distinguishes turns.
#[partial]
def echo_lines (text : String) : List TLine :=
    List.map TLine.user_line (theme_split_lines text)

def clear_input (m : TuiModel) : TuiModel :=
    { m with input := weaver_input_state }

def weaver_input_state : InputState :=
    input_state "" "type a message, or /help"

def set_state (m : TuiModel) (st : WeaverState) : TuiModel :=
    { m with state := st }

def set_run (m : TuiModel) (run : RunState) : TuiModel :=
    set_state m { (m.state) with run := run }

def set_size (m : TuiModel) (rows : I64) (cols : I64) : TuiModel :=
    { m with rows := rows, cols := cols }

// ── run_submitted_line: the dumb-mode twin over WeaverMsg ───────────────

/// A submitted line, run to completion: a slash command through
/// `Commands.dispatch`, or one model turn through shuttle's indexed
/// loop -- mirroring `dumb.mo`'s `route`/`command_turn`/`model_turn`,
/// but folding a `WeaverMsg` back instead of writing through line
/// seams.
pub def run_submitted_line (st : WeaverState) (text : String) : IO WeaverMsg :=
    if plan_dialog_wanted st text
    then plan_dialog_step st text
    else if String.starts_with "/" text
    then command_step_tui st text
    else model_step_tui st text

def mode_is_plan (m : Mode) : Bool :=
    match m { Mode.plan => true, _ => false }

/// In plan mode `/plan` (and `/plan approve …`) opens the review dialog
/// instead of printing the status line.
def plan_dialog_wanted (st : WeaverState) (text : String) : Bool :=
    Bool.and (mode_is_plan st.mode)
        (Bool.or (text == "/plan") (String.starts_with "/plan approve" text))

def command_step_tui (st : WeaverState) (line : String) : IO WeaverMsg := do {
    let r <- Commands.dispatch line st;
    return (command_msg st r)
}

/// A failed command folds the same styled-later error entry a failed
/// turn does (one render point, `WeaverError.show`); the state stands
/// untouched -- the session is intact. A successful command is the
/// effect the update folds as before.
def command_msg (st : WeaverState) (r : Result WeaverError Effect) : WeaverMsg :=
    match r {
        Result.err e => WeaverMsg.command_failed e,
        Result.ok e => WeaverMsg.command_result e,
    }

def model_step_tui (st : WeaverState) (text : String) : IO WeaverMsg :=
    if st.run.turns_left < 1
    then IO.pure (WeaverMsg.turn_result st.run [TLine.plain "turn budget spent -- /clear or restart with --max-turns"] List.empty)
    else drive_turn_tui st text

def drive_turn_tui (st : WeaverState) (text : String) : IO WeaverMsg :=
    let before : I64 := list_msg_length st.run.session.history in
    do {
        let r <- ResultT.run (drive_tui st text);
        return (turn_result_of st before r)
    }

def turn_result_of (st : WeaverState) (before : I64) (r : Result WeaverError RunState) : WeaverMsg :=
    match r {
        Result.err e => WeaverMsg.turn_failed st.run e,
        Result.ok run2 =>
            let delta : List Message := drop_n_messages before run2.session.history in
            let render : List Message := drop_n_messages 1 delta in
            WeaverMsg.turn_result run2 (transcript_lines_of_messages render) delta,
    }

/// The transcript's error entry: the one render point does the prose,
/// the entry is a transcript line Phase 11's palette will color.
def error_line (e : WeaverError) : TLine :=
    TLine.plain (String.concat "error: " (WeaverError.show e))

/// Rebuild the turn's `Gate` from `Gate.weaver_tui` (instead of
/// `Gate.weaver`) and swap the emit seam to `TuiApp.progress` (NOT
/// dumb's `stdout_write`: a perform-time raw write lands on the alt
/// screen mid-frame -- the recorded UI-repair finding). Drive the loop
/// -- `append_user`/`drive_loop` are `dumb.mo`'s own halves, reused
/// as-is (Phase 9: `drive_loop` is already `ResultT WeaverError IO`).
def drive_tui (st : WeaverState) (text : String) : ResultT WeaverError IO RunState := do {
    let gated : RunState := { (st.run) with gate := Gate.weaver_tui st.mode st.colors, emit := progress_live st.store };
    let ready : RunState := append_user gated text;
    drive_loop ready
}

/// The terminal row plus the session's per-chunk log: every streamed
/// fragment is durable before the turn completes.
def progress_live (store : Option StoreState) (frag : String) : IO Unit := do {
    TuiApp.progress frag;
    persist_chunk store frag
}

def persist_chunk (store : Option StoreState) (frag : String) : IO Unit :=
    match store {
        Option.none => IO.pure unit,
        Option.some s => Store.append_chunk s frag,
    }

/// The TUI turn's live progress sink: the model's streamed text, shown
/// as ONE transparent-overwrite line on the transcript panel's LAST
/// content row (`rows - 6`: fill is `rows - 4` after the status and
/// input's rows, minus the border's two lines; content rows start at
/// row 1, 0-based). A dedicated row, not the status bar:
/// the loop now redraws every tick while a turn runs, and the only
/// mid-turn cell the diff pipeline rewrites is the spinner glyph at
/// the status row's end -- this row's cells stay untouched by ticks,
/// so the fragment survives between emits. The `repaint_cmd` every
/// completion folds repaints from blank, erasing the last fragment
/// with the turn's real result.
pub def TuiApp.progress (frag : String) : IO Unit := do {
    let size <- Terminal.size;
    match size {
        Pair.pair rows cols => do {
            let row : I64 := rows - progress_row_offset;
            if row < 1 then IO.pure Unit.unit
            else do {
                let _ <- Terminal.cursor_move row 0;
                IO.write_stdout (blank_of cols);
                let _ <- Terminal.cursor_move row 0;
                IO.write_stdout (progress_text frag cols);
                IO.flush_stdout
            }
        }
    }
}

/// The progress row's distance from the bottom edge (see
/// `TuiApp.progress`'s comment for the arithmetic).
def progress_row_offset : I64 := 6

/// `n` spaces: the row wipe (tui has no erase-line builder; spaces are
/// blank cells and the forced repaint's blank-diff drops them anyway).
/// Bounded to `cols` -- the caller clips to the same width.
#[terminating]
def blank_of (n : I64) : String :=
    if n < 1 then "" else blank_of_go n

#[terminating]
def blank_of_go (n : I64) : String :=
    if n < 1 then "" else String.concat " " (blank_of_go (n - 1))

/// The preview is ONE row, so only the fragment's last line is shown
/// (a streamed newline would otherwise move the cursor onto the border).
def progress_text (frag : String) (cols : I64) : String :=
    let budget : I64 := if cols - 1 < 1 then 1 else cols - 1 in
    Text.take_width (String.concat "[thinking] " (last_fragment_line frag)) budget

def last_fragment_line (frag : String) : String :=
    match List.reverse (theme_split_lines frag) {
        List.cons l _ => l,
        List.empty => "",
    }

// ── transcript rendering ─────────────────────────────────────────────────

def transcript_lines_of_messages (ms : List Message) : List TLine :=
    List.map render_message ms

/// Assistant text is raw (no `assistant:` label); a user message is the
/// echoed prompt's role; tool/system output keeps its one-word label so
/// the theme can still classify it.
def render_message (m : Message) : TLine :=
    let text : String := List.intercalate " " (List.map render_content m.content) in
    match m.role {
        Role.user => TLine.user_line text,
        Role.assistant => TLine.plain text,
        Role.system_ => TLine.plain (String.concat "system: " text),
        Role.tool => TLine.plain (String.concat "tool: " text),
    }

def render_content (c : Content) : String :=
    match c {
        Content.text s => s,
        Content.tool_use id name input => String.concat "[running " (String.concat name "]"),
        Content.tool_result call_id output is_error => output,
        Content.thinking s signature => "",
    }

#[partial]
def drop_n_messages (n : I64) (xs : List Message) : List Message :=
    if n < 1 then xs
    else match xs {
        List.empty => xs,
        List.cons _ rest => drop_n_messages (n - 1) rest,
    }

#[partial]
def list_msg_length (xs : List Message) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _ rest => 1 + list_msg_length rest,
    }

// ── Gate.weaver_tui: the approval overlay ───────────────────────────────

/// A full-screen (not diffed) render of one pick, then a one-shot key
/// read for `y`/`n`/`a`. `mode` is the only parameter -- same shape as
/// `Gate.weaver`, minus the read/write seams dumb mode needs and this
/// does not (it owns its own screen and its own stdin read).
pub def Gate.weaver_tui (mode : Mode) (colors : Bool) : Gate :=
    { ask := weaver_tui_ask mode colors, precheck := weaver_tui_precheck mode }

def weaver_tui_precheck (mode : Mode) (p : Pick) : IO (Option Approval) :=
    match Policy.decide p.cap mode {
        Decision.refuse reason => IO.pure (Option.some (Approval.deny reason)),
        _ => IO.pure Option.none,
    }

def weaver_tui_ask (mode : Mode) (colors : Bool) (p : Pick) : IO Approval :=
    match Policy.decide p.cap mode {
        Decision.allow => IO.pure Approval.once,
        Decision.ask => prompt_overlay colors p,
        Decision.refuse reason => IO.pure (Approval.deny reason),
    }

def diff_lines_of (diff_pair : Option (Pair String String)) : List String :=
    match diff_pair {
        Option.none => List.empty,
        Option.some pr => match pr {
            Pair.pair old new => Diff.lines (capped_diff old new),
        }
    }

#[partial]
def list_length_rows (rs : List DisplayRow) : I64 :=
    match rs {
        List.empty => 0,
        List.cons _ rest => 1 + list_length_rows rest,
    }

def prompt_overlay (colors : Bool) (p : Pick) : IO Approval := do {
    let diff_pair <- Diff.for_input p.name p.input;
    let body : List String := List.append [pick_header p] (diff_lines_of diff_pair);
    let o0 : DialogOption := { label := "Approve once", hint := "y", key := "y" };
    let o1 : DialogOption := { label := String.concat "Always allow all " (String.concat (cap_name p.cap) "s this session"), hint := "a", key := "a" };
    let o2 : DialogOption := { label := "Deny", hint := "n", key := "n" };
    let subtitle : String := String.concat (cap_name p.cap) (String.concat " " p.name);
    let d : Dialog := Dialog.make "Permission required" subtitle body [o0, o1, o2];
    let default_idx : I64 := if cap_is_read p.cap then 0 else 2;
    let pr <- dialog_loop colors (Dialog.with_default d default_idx);
    match pr {
        Pair.pair final step => match step {
            DialogStep.choose i => IO.pure (approval_with_note i (Dialog.note_text final)),
            _ => IO.pure (Approval.deny "declined by user"),
        },
    }
}

def cap_is_read (c : Capability) : Bool :=
    match c { Capability.read => true, _ => false }

/// The first option approves once, the second approves for the whole
/// session, the third denies; a non-empty note rides the answer (on an
/// approval the model sees it on the tool result, on a denial it is the
/// reason).
def approval_with_note (i : I64) (note : String) : Approval :=
    let has : Bool := Bool.not (String.is_empty note) in
    if i == 1
    then (if has then Approval.always_note note else Approval.always)
    else if i == 2
    then Approval.deny (if has then note else "declined by user")
    else (if has then Approval.once_note note else Approval.once)

// ── the plan dialog ────────────────────────────────────────────────────

#[partial]
def content_text (c : Content) : String :=
    match c {
        Content.text s => s,
        _ => "",
    }

def message_text (m : Message) : String :=
    List.intercalate "\n" (List.map content_text m.content)

#[partial]
def last_assistant_go (ms : List Message) : Option String :=
    match ms {
        List.empty => Option.none,
        List.cons m rest =>
            match m.role {
                Role.assistant => Option.some (message_text m),
                _ => last_assistant_go rest,
            },
    }

def plan_body (st : WeaverState) : List String :=
    match last_assistant_go (List.reverse st.run.session.history) {
        Option.none => ["(no plan message found -- keep planning, then /plan again)"],
        Option.some content => theme_split_lines content,
    }

def plan_effect (st : WeaverState) (output : String) : Effect := Effect.ok st output

def note_into_state (st : WeaverState) (note : String) : WeaverState :=
    let msg : Message := { role := Role.user, content := [Content.text note] } in
    let base : Session := st.run.session in
    let hist : List Message := base.history in
    let sess : Session := { base with history := List.append hist [msg] } in
    let run0 : RunState := st.run in
    let run2 : RunState := { run0 with session := sess } in
    { st with run := run2 }

def persist_note (st : WeaverState) (note : String) : IO Unit :=
    match st.store {
        Option.none => IO.pure unit,
        Option.some s => do {
            let _ <- Store.append_history_note s st.run.session note;
            IO.pure unit
        },
    }

def plan_dialog_step (st : WeaverState) (text : String) : IO WeaverMsg := do {
    let o0 : DialogOption := { label := "Approve and execute (allow_edit)", hint := "a", key := "a" };
    let o1 : DialogOption := { label := "Approve to manual", hint := "m", key := "m" };
    let o2 : DialogOption := { label := "Revise with a note", hint := "r", key := "r" };
    let o3 : DialogOption := { label := "Cancel", hint := "Esc", key := "" };
    let d : Dialog := Dialog.make "Plan ready" "approve it to leave plan mode" (plan_body st) [o0, o1, o2, o3];
    let pr <- dialog_loop st.colors d;
    match pr {
        Pair.pair final step => match step {
            DialogStep.choose i =>
                if i == 2
                then do {
                    let note : String := Dialog.note_text final;
                    if String.is_empty note
                    then IO.pure (WeaverMsg.command_result (plan_effect st "plan not approved -- type your revision in the input box"))
                    else IO.pure (WeaverMsg.input_set note)
                } else if i == 3
                then IO.pure (WeaverMsg.command_result (plan_effect st "plan not approved"))
                else do {
                    let target : String := if i == 1 then "manual" else "allow_edit";
                    let line : String := String.concat "/plan approve " target;
                    let r <- Commands.dispatch line st;
                    match r {
                        Result.err e => IO.pure (WeaverMsg.command_failed e),
                        Result.ok e => do {
                            let note : String := Dialog.note_text final;
                            if String.is_empty note
                            then IO.pure (WeaverMsg.command_result e)
                            else do {
                                persist_note e.state note;
                                let st2 : WeaverState := note_into_state e.state note;
                                let out : String := String.concat e.output (String.concat "\nnote: " note);
                                let e2 : Effect := { e with state := st2, output := out };
                                IO.pure (WeaverMsg.command_result e2)
                            }
                        },
                    }
                },
            _ => IO.pure (WeaverMsg.command_result (plan_effect st "plan not approved")),
        },
    }
}

// ── dialog rendering and input ─────────────────────────────────────────

#[partial]
def take_rows (n : I64) (rs : List DisplayRow) : List DisplayRow :=
    if n < 1 then List.empty
    else match rs {
        List.empty => List.empty,
        List.cons r rest => List.cons r (take_rows (n - 1) rest),
    }

#[partial]
def drop_rows (n : I64) (rs : List DisplayRow) : List DisplayRow :=
    if n < 1 then rs
    else match rs {
        List.empty => rs,
        List.cons _ rest => drop_rows (n - 1) rest,
    }

#[partial]
def dialog_body_rows (colors : Bool) (width : I64) (lines : List String) : List DisplayRow :=
    match lines {
        List.empty => List.empty,
        List.cons l rest => List.append (Model.display_line colors width (TLine.plain l)) (dialog_body_rows colors width rest),
    }

def dim_row (r : DisplayRow) : DisplayRow :=
    let base : TextStyle := r.style in
    let st : TextStyle := { base with dim := true } in
    { r with style := st }

def bold_row (r : DisplayRow) : DisplayRow :=
    let base : TextStyle := r.style in
    let st : TextStyle := { base with bold := true } in
    { r with style := st }

def reverse_row (r : DisplayRow) : DisplayRow :=
    let base : TextStyle := r.style in
    let st : TextStyle := { base with reverse := true } in
    { r with style := st }

#[partial]
def dialog_option_rows (colors : Bool) (d : Dialog) (i : I64) (width : I64) : List DisplayRow :=
    match Dialog.option_at d i {
        Option.none => List.empty,
        Option.some o =>
            let marker : String := if i == d.selected then "> " else "  " in
            let suffix : String := if String.is_empty o.hint then "" else String.concat "  (" (String.concat o.hint ")") in
            let line : String := String.concat marker (String.concat o.label suffix) in
            let rows : List DisplayRow := Model.display_line colors width (TLine.plain line) in
            let styled : List DisplayRow := if i == d.selected then List.map reverse_row rows else rows in
            List.append styled (dialog_option_rows colors d (i + 1) width),
    }

def dialog_note_row (colors : Bool) (d : Dialog) (width : I64) : List DisplayRow :=
    let text : String :=
        if d.editing
        then String.concat "note: " (String.concat d.note.value "_")
        else if String.is_empty d.note.value
        then "note: (press e to add one)"
        else String.concat "note: " d.note.value in
    List.map dim_row (Model.display_line colors width (TLine.plain text))

/// The dialog's visible rows. The body yields to the fixed rows on a
/// short terminal, so the options, note and footer stay visible.
def dialog_rows (colors : Bool) (d : Dialog) (width : I64) (height : I64) : List DisplayRow :=
    let budget : I64 := if height - 4 < 1 then 1 else height - 4 in
    let nopts : I64 := Dialog.option_count d in
    let fixed : I64 := 2 + 1 + 1 + nopts + 1 + 1 + 1 in
    let body_budget : I64 := if budget - fixed < 1 then 0 else budget - fixed in
    let body_all : List DisplayRow := dialog_body_rows colors width d.body in
    let body : List DisplayRow := take_rows body_budget (drop_rows d.scroll body_all) in
    let title_rows : List DisplayRow := List.map bold_row (Model.display_line colors width (TLine.plain d.title)) in
    let subtitle_rows : List DisplayRow := List.map dim_row (Model.display_line colors width (TLine.plain d.subtitle)) in
    let blank : List DisplayRow := Model.display_line colors width (TLine.plain "") in
    let foot : List DisplayRow := List.map dim_row (Model.display_line colors width (TLine.plain d.footer)) in
    let a : List DisplayRow := List.append title_rows subtitle_rows in
    let b : List DisplayRow := List.append a blank in
    let c : List DisplayRow := List.append b body in
    let e : List DisplayRow := List.append c blank in
    let f : List DisplayRow := List.append e (dialog_option_rows colors d 0 width) in
    let g : List DisplayRow := List.append f blank in
    let h : List DisplayRow := List.append g (dialog_note_row colors d width) in
    let all : List DisplayRow := List.append h foot in
    take_rows budget all

def dialog_total_rows (colors : Bool) (d : Dialog) (width : I64) : I64 :=
    let nopts : I64 := Dialog.option_count d in
    let body : I64 := list_length_rows (dialog_body_rows colors width d.body) in
    body + nopts + 7

def dialog_widget (colors : Bool) (rows : List DisplayRow) : Widget :=
    Widget.column [
        sized (LayoutSize.fill 1) (with_style (theme_border_style_with colors) (border BorderStyle.rounded
            (padding 1 1 1 2 (Widget.column (List.map Model.display_row_widget rows))))),
    ]

def render_dialog (colors : Bool) (d : Dialog) : IO Unit := do {
    let size <- Terminal.size;
    match size {
        Pair.pair rows cols => do {
            let raw_w : I64 := cols - 4;
            let width : I64 := if raw_w < 20 then (if raw_w < 1 then 1 else raw_w) else (if raw_w < 88 then raw_w else 88);
            let content_w : I64 := if width - 4 < 1 then 1 else width - 4;
            let total : I64 := dialog_total_rows colors d content_w;
            let max_h : I64 := if rows - 2 < 6 then 6 else rows - 2;
            let wanted : I64 := total + 4;
            let height : I64 := if wanted < max_h then wanted else max_h;
            let body : List DisplayRow := dialog_rows colors d content_w height;
            let rect : Rect := center_rect_in (mk_rect 0 0 cols rows) width height;
            Terminal.clear_screen;
            Terminal.cursor_move 0 0;
            let screen := render (dialog_widget colors body) rect (empty_screen rows cols);
            let deltas := diff (empty_screen rows cols) screen;
            IO.write_stdout (apply_deltas deltas);
            IO.flush_stdout
        }
    }
}

/// The modal loop: repaint, then poll for a key with a timeout (a resize
/// while the dialog blocks is noticed on the next timeout). The final
/// dialog rides along so the caller can read the note.
#[partial]
def dialog_loop (colors : Bool) (d : Dialog) : IO (Pair Dialog DialogStep) := do {
    let _ <- render_dialog colors d;
    let ready <- Terminal.poll 100;
    if Bool.not ready
    then dialog_loop colors d
    else do {
        let eopt <- dialog_event_loop "";
        match eopt {
            Option.none => IO.pure (Pair.pair d DialogStep.cancel),
            Option.some e => match e {
                Event.key k => match Dialog.step d k {
                    Pair.pair d2 step => match step {
                        DialogStep.continue => dialog_loop colors d2,
                        _ => IO.pure (Pair.pair d2 step),
                    },
                },
                Event.paste text => dialog_loop colors (Dialog.paste d text),
                _ => dialog_loop colors d,
            },
        }
    }
}

#[terminating]
def dialog_event_loop (pending : String) : IO (Option Event) := do {
    let chunk <- IO.read_stdin_exact 1;
    if String.length chunk == 0
    then IO.pure Option.none
    else match Input.decode (pending ++ chunk) {
        Pair.pair evs leftover => match evs {
            List.empty =>
                if leftover == "\u{1b}"
                then do {
                    // A lone ESC: give a split sequence 50 ms to finish,
                    // otherwise it is the Escape key.
                    let more <- Terminal.poll 50;
                    if more then dialog_event_loop leftover else IO.pure (Option.some (Event.key Key.escape))
                } else dialog_event_loop leftover,
            List.cons e _ => IO.pure (Option.some e),
        },
    }
}
