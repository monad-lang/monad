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
use weaver::place {Place.cwd_of}
use shuttle::agent {RunState}
use shuttle::registry {ToolRegistry}
use shuttle::gate {Pick, Approval, Gate, Capability}
use shuttle::message {Message, Usage}
use shuttle::message_types {Role, Content}
use weaver::usage {UsageTracker.start, UsageTracker.silent, UsageTracker.last}
use std::ref {Ref}
use weaver::commands {
    WeaverState, Effect, Effect.ok, set_fatal, Commands.dispatch, Commands.set_model,
    Commands.autocompact, Commands.last_assistant_text, Commands.current_plan,
    Commands.plan_after_turn, Commands.setting_rows, Commands.cycle_setting, Commands.apply_setting, SettingRow, SettingKind,
    SessionPage, Commands.session_page, Commands.sessions_for, Commands.turns_label, Commands.turn_context,
}
use log::logger {Logger}
use weaver::policy {Mode, Mode.show, Mode.cycle, Policy.decide, Decision}
use weaver::gate {pick_header, pick_target, cap_name, capped_diff, PickAnswer, record_answer, answer_approval, Gate.assessment_lines}
use weaver::permissions {PermGrant, Permissions.get, Permissions.matches, Permissions.render}
use weaver::assess {Assessment, Reach.is_inside, Assess.pick}
use weaver::diff {Diff.for_input, Diff.lines}
use weaver::dumb {append_user, drive_loop}
use weaver::model {
    TuiModel, WeaverMsg, on_event, init_tui_model, init_tui_model_with,
    Model.view, Model.scroll_step, Model.append_block, Model.append_lines,
    Model.pane_view, Model.pane_step, Model.refresh_rows,
    Model.prompt_box, Model.picker_height,
    panel_height,
}
use weaver::ui::pane {
    PaneModel, PaneMsg, Pane.reset, Pane.end_drag, Pane.selecting,
    Pane.page_wanted, Pane.page_requested, Pane.page_loaded, Pane.page_failed,
}
use weaver::ui::rows {DisplayRow, Rows.of_line, Rows.widget}
use weaver::logs {Logs.info, Logs.debug, Logs.warn, Logs.error, Logs.log_rss}
use weaver::title {Title.generate, Title.needed}
use weaver::subagent {Subagent.task_tool}
use weaver::store {
    Transcript, TranscriptPage, StoreState,
    Transcript.empty, Transcript.with_page, Transcript.next_block, Transcript.append, Transcript.drop_page,
    Store.read_page, Store.append_transcript, Store.record_turn, Store.record_output,
    Store.startup_transcript, Store.append_chunk, Store.discard_live,
    Store.append_history_note, Store.append_named, Store.write_named, Store.write_plan,
    Store.discard_named,
    SessionInfo, Store.list_sessions, Store.read_meta, Store.write_title, Store.derive_name,
    Store.derive_description, TitleField, StoreMeta,
}
use weaver::stop {Stop.predicate, Stop.request, Stop.reset}
use weaver::overlay {
    OverlayState, Overlay.read, Overlay.reset, Overlay.ack, Overlay.begin, Overlay.finish,
}
use weaver::commands {TranscriptChange}
use shuttle::session {Session}
use weaver::theme {theme_split_lines, theme_line_style_with, theme_border_style_with}
use weaver::store {TLine, TLine.plain, TLine.user_line}
use weaver::error {WeaverError, WeaverError.show, WeaverError.recoverable}
use std::concurrent::fiber {FiberError, FiberError.message}
use tui::types {Event, Key, MouseEvent, MouseButton, Screen}
use tui::widget {SizedWidget}
use tui::text {Text.take_width, Text.width}
use tui::clipboard {Clipboard.copy}
use tui::widgets::dialog {
    DialogModel, DialogOption, DialogStep, Dialog.make, Dialog.with_default, Dialog.with_notes, Dialog.note_text,
    Dialog.paint, Dialog.modal,
}
use tui::terminal {
    Terminal.clear_screen, Terminal.cursor_move, Terminal.enter_raw_mode, Terminal.size,
}
use tui::tui {App, Cmd, run_app}
use tui::widgets::picker {PickerModel, PickerStep, Picker.make, Picker.update}
use weaver::ui::prompt {PromptMsg, Prompt.update, Prompt.text, Prompt.set_text, Prompt.clear, Prompt.submitted, Prompt.selecting, Prompt.clear_selection, Prompt.box_contains}
use weaver::ui::banner {BannerMsg, Banner.shown, Banner.hidden, Banner.update, Banner.animating, Banner.subscriptions}
use tui::component {Subs, Subs.map, Subs.on_tick}
use weaver::ui::live {LiveMsg, Live.idle, Live.start, Live.update, Live.request_stop, Live.subscriptions, Live.write_usage, Live.store_usage}
use init::transformers {ResultT}
use std::path {Path}
use json::json {Json, Json.to_string}
use std::list {List.intercalate, List.length}

// ── Tui.run: the tty probe and the App wiring ───────────────────────────

/// Probes `Terminal.enter_raw_mode` -- `false` when stdin is not a tty
/// (the native degrades instead of failing, `terminal.mo`'s own
/// contract), which doubles as the auto-detect `main.mo` needs: no
/// other terminal write happens before this check, so the caller can
/// fall back to `Dumb.run` cleanly. `true` runs the whole TUI to
/// completion (quit or EOF) before returning.
pub def Tui.run (log : Option Logger) (st : WeaverState) : IO Bool :=
    Tui.run_resumed log st Transcript.empty

/// The startup tail is loaded before `run_app` builds the model, so the
/// first frame already shows the previous session.
pub def Tui.run_resumed (log : Option Logger) (st : WeaverState) (tr : Transcript) : IO Bool := do {
    let is_tty <- Terminal.enter_raw_mode;
    if Bool.not is_tty
    then return false
    else do {
        let size <- Terminal.size;
        run_tui_with_size log st tr size
    }
}

def run_tui_with_size (log : Option Logger) (st : WeaverState) (tr : Transcript) (size : Pair I64 I64) : IO Bool :=
    match size {
        Pair.pair rows cols => do {
            let _ <- Stop.reset st.store;
            let _ <- Overlay.reset st.store;
            // 100 ms: the tick is the spinner's frame clock AND the
            // async-turn poll cadence (a completed turn's result joins
            // the next batch within one tick); idle ticks with an
            // unchanged model are zero-diff draws. The tui default (-1)
            // stays untouched.
            let app : App TuiModel WeaverMsg :=
                App.app_ticked (init_tui_model_with log st rows cols tr) on_event TuiApp.update Model.view 100
                    tick_redraw reads_input;
            let _ <- run_app app;
            return true
        }
    }

/// Draw a tick-only batch only when the spinner/banner moved, and never
/// while a dialog owns the terminal (`modal`).
pub def tick_redraw (m : TuiModel) : Bool :=
    Bool.or (Bool.and m.turn_pending (Bool.not m.modal))
        (Banner.animating m.banner)

/// The loop's read gate: while a dialog is open, ack its ownership (only
/// now -- the poll has already marked the overlay open and this model's
/// last frame has drawn) and decline the read. Otherwise read normally.
def reads_input (m : TuiModel) : IO Bool := do {
    // Read the handshake FILE, not just the polled `overlay_open`: the
    // poll is a tick message, and a dialog must own stdin even on a loop
    // whose tick state is stale (the frame clock is not the authority on
    // who reads). Acking here is what `Overlay.begin` waits for.
    let ov <- Overlay.read m.state.store;
    let want : Bool := match ov {
        Option.some s => s.want,
        Option.none => m.overlay_open,
    };
    if want
    then do { Overlay.ack m.state.store; IO.pure false }
    else IO.pure true
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

#[partial]
def update_msg (m : TuiModel) (msg : WeaverMsg) : Pair TuiModel (Cmd WeaverMsg) :=
    match msg {
        WeaverMsg.key_event e => update_event m e,
        WeaverMsg.turn_result run lines delta last_context plan => turn_result_step m run lines delta last_context plan,
        WeaverMsg.turn_failed run e => failure_step m run e,
        WeaverMsg.command_result effect => command_result_step m effect,
        WeaverMsg.command_failed e => failure_step m m.state.run e,
        WeaverMsg.page_loaded page => page_loaded_step m page,
        WeaverMsg.page_failed e => page_failed_step m e,
        WeaverMsg.transcript_reset tr => transcript_reset_step m tr,
        WeaverMsg.store_result e => store_result_step m e,
        // The plan dialog's "revise with a note" is a terminal outcome
        // too: the dialog closed, so the turn ends and the overlay must
        // be repainted away (leaving modal/turn_pending set used to
        // strand the app).
        WeaverMsg.submit st text => submit_line (set_state { m with plan_ready := false } st) text,
        WeaverMsg.input_set text =>
            let m2 : TuiModel := with_turn_end (fn (mm : TuiModel) =>
                { mm with prompt := Prompt.set_text mm.prompt text, banner := Banner.hidden }) m in
            Pair.pair m2 repaint_cmd,
        // The Esc request reached the signal file.
        WeaverMsg.stop_sent => Pair.pair m Cmd.none,
        // The background title call wrote (or skipped) the session's
        // name/description: already persisted, nothing to fold.
        WeaverMsg.title_result _ => Pair.pair m Cmd.none,
        WeaverMsg.live lm => live_step m lm,
        WeaverMsg.banner bm => Pair.pair { m with banner := Banner.update m.banner bm } Cmd.none,
        WeaverMsg.overlay_polled ov => overlay_step m ov,
        WeaverMsg.batch msgs => batch_step m msgs,
    }

// ── persistence commands ─────────────────────────────────────────────────

#[partial]
def plain_lines (ss : List String) : List TLine :=
    List.map TLine.plain ss

def append_block_at (m : TuiModel) (lines : List TLine) : Pair TuiModel (Pair I64 (List TLine)) :=
    let block : List TLine := Transcript.next_block m.pane.transcript lines in
    let start : I64 := m.pane.transcript.total in
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

def persist_turn_action (log : Option Logger) (s : StoreState) (run : RunState) (delta : List Message) (start : I64) (block : List TLine) : IO WeaverMsg :=
    after_clear (record_turn_action log s run delta start block)

def record_turn_action (log : Option Logger) (s : StoreState) (run : RunState) (delta : List Message) (start : I64) (block : List TLine) : IO WeaverMsg := do {
    let r <- Store.record_turn s run.session delta start block;
    match r {
        Result.err e => do {
            Logs.warn log (String.concat "ev=persist_error kind=transcript msg=" e);
            IO.pure (WeaverMsg.store_result (Option.some e))
        },
        Result.ok _ => discard_live_msg s,
    }
}

def plan_prompt_cmd (st : WeaverState) : Cmd WeaverMsg :=
    Cmd.perform (fn (_ : Unit) => plan_approval_step st)

def persist_turn_cmd (log : Option Logger) (store : Option StoreState) (run : RunState) (delta : List Message) (start : I64) (block : List TLine) (ready : Bool) (st : WeaverState) : Cmd WeaverMsg :=
    match store {
        Option.none => if ready then plan_prompt_cmd st else repaint_cmd,
        Option.some s => Cmd.perform (fn (_ : Unit) => persist_turn_action log s run delta start block),
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

def turn_result_step (m : TuiModel) (run : RunState) (lines : List TLine) (delta : List Message) (last_context : I64) (plan : Option String) : Pair TuiModel (Cmd WeaverMsg) :=
    let plan_mode : Bool := mode_is_plan m.state.mode in
    let ready : Bool := Bool.and plan_mode (match plan { Option.some _ => true, Option.none => false }) in
    // A stopped turn keeps its partial block and carries one marker line.
    // It is display output, not history: the session's messages are the
    // ones the loop kept.
    let shown : List TLine :=
        if run.stopped then List.append lines [TLine.plain "[stopped]"] else lines in
    let notice : List TLine :=
        if Bool.and plan_mode (Bool.not ready)
        then [TLine.plain "[plan not ready -- ask for the plan, or /plan]"]
        else if ready then [TLine.plain "plan ready -- review it"] else List.empty in
    let st1 : WeaverState := { (m.state) with run := run, last_context := last_context } in
    let st2 : WeaverState := match plan {
        Option.none => st1,
        Option.some p => { st1 with plan := Option.some p },
    } in
    let with_run : TuiModel := set_state m st2 in
    let pair := append_block_at with_run (List.append shown notice) in
    match pair {
        Pair.pair m2 at => match at {
            Pair.pair start block =>
                let m3 : TuiModel := with_turn_end (fn (mm : TuiModel) => mm) m2 in
                let m4 : TuiModel := { m3 with plan_ready := ready, title_due := title_wanted st2 plan } in
                let store : Option StoreState := m4.state.store in
                if Bool.not (queued_waiting m4)
                then Pair.pair m4 (persist_turn_cmd m4.log store run delta start block ready m4.state)
                else match store {
                    Option.none => start_queued m4,
                    Option.some _ => Pair.pair { m4 with queued_ready := true } (persist_turn_cmd m4.log store run delta start block ready m4.state),
                },
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
                    if Bool.not (queued_waiting m3)
                    then Pair.pair m3 (persist_output_cmd repaint_cmd store start block m3.state.run.session)
                    else match store {
                        Option.none => start_queued m3,
                        Option.some _ => Pair.pair { m3 with queued_ready := true } (persist_output_cmd repaint_cmd store start block m3.state.run.session),
                    }
                else
                    let m3 : TuiModel := with_turn_end (fn (mm : TuiModel) => mm) m2 in
                    let st2 : WeaverState := set_fatal m3.state e in
                    let m4 : TuiModel := set_state m3 st2 in
                    Pair.pair m4 Cmd.quit,
        },
    }

// ── transcript paging ────────────────────────────────────────────────────

/// The window after a scroll delta, plus a page load when the loaded top
/// is (nearly) on screen and older lines exist.
def scroll_with_pages (m : TuiModel) (delta : I64) : Pair TuiModel (Cmd WeaverMsg) :=
    maybe_page_cmd (with_streak_reset (fn (mm : TuiModel) => Model.scroll_step mm delta) m)

/// A pane message that may move the window, then any page it now wants.
def pane_paged_step (m : TuiModel) (msg : PaneMsg) : Pair TuiModel (Cmd WeaverMsg) :=
    match Model.pane_step m msg {
        Pair.pair m2 _ => maybe_page_cmd (with_streak_reset (fn (mm : TuiModel) => mm) m2),
    }

def maybe_page_cmd (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    match m.state.store {
        Option.none => Pair.pair m Cmd.none,
        Option.some st => page_cmd_for m st,
    }

def page_cmd_for (m : TuiModel) (st : StoreState) : Pair TuiModel (Cmd WeaverMsg) :=
    match Pane.page_wanted (Model.pane_view m) m.pane {
        Option.none => Pair.pair m Cmd.none,
        Option.some req => match req {
            Pair.pair start count =>
                let m2 : TuiModel := { m with pane := Pane.page_requested m.pane } in
                // `perform` forces a full repaint, which is written as a
                // diff against a BLANK screen: without clearing the real
                // terminal first, every cell that becomes blank keeps its
                // old content (a paged scroll left stale fragments and
                // blank rows). Every other transcript-changing perform
                // goes through `after_clear` for the same reason.
                Pair.pair m2 (Cmd.perform (fn (_ : Unit) => after_clear (load_page st start count))),
        },
    }

def load_page (st : StoreState) (start : I64) (count : I64) : IO WeaverMsg := do {
    let r <- Store.read_page st.dir start count;
    match r {
        Result.err e => IO.pure (WeaverMsg.page_failed e),
        Result.ok p => IO.pure (WeaverMsg.page_loaded p),
    }
}

/// An older page landed; the next one is asked for unless the same page
/// came back (the store cannot cover the window: stop rather than
/// re-requesting it forever).
def page_loaded_step (m : TuiModel) (p : TranscriptPage) : Pair TuiModel (Cmd WeaverMsg) :=
    match Pane.page_loaded (Model.pane_view m) m.pane p {
        Pair.pair p2 progressed =>
            let m2 : TuiModel := { m with pane := p2 } in
            if progressed then maybe_page_cmd m2 else Pair.pair m2 Cmd.none,
    }

def page_failed_step (m : TuiModel) (e : String) : Pair TuiModel (Cmd WeaverMsg) :=
    Pair.pair (with_streak_reset (fn (mm : TuiModel) => { mm with pane := Pane.page_failed mm.pane e }) m) Cmd.none

def transcript_reset_step (m : TuiModel) (tr : Transcript) : Pair TuiModel (Cmd WeaverMsg) :=
    let m2 : TuiModel := { m with pane := Pane.reset m.pane tr, banner := Banner.shown,
        queued := List.empty, queued_ready := false, title_due := false } in
    maybe_page_cmd m2

/// A store write failure disables persistence for the rest of the run;
/// the session keeps working in memory.
def store_result_step (m : TuiModel) (e : Option String) : Pair TuiModel (Cmd WeaverMsg) :=
    match e {
        Option.none =>
            if m.plan_ready
            then Pair.pair { m with plan_ready := false } (plan_prompt_cmd m.state)
            else if m.queued_ready then start_queued m else Pair.pair m Cmd.none,
        Option.some msg =>
            let st0 : WeaverState := m.state in
            let st : WeaverState := { st0 with store := Option.none } in
            let line : String := String.concat "warning: transcript persistence disabled: " msg in
            let m2 : TuiModel := Model.append_lines { m with state := st } [TLine.plain line] in
            if m2.plan_ready
            then Pair.pair { m2 with plan_ready := false } (plan_prompt_cmd m2.state)
            else if m2.queued_ready then start_queued m2 else Pair.pair m2 (Cmd.none),
    }

/// A turn's or command's completion: the fold `f` runs, the streak
/// resets, and `turn_pending` clears -- the spinner stops.
def with_turn_end (f : TuiModel -> TuiModel) (m : TuiModel) : TuiModel :=
    let m2 : TuiModel := with_streak_reset f m in
    { m2 with turn_pending := false, live := Live.idle,
        pane := Pane.end_drag m2.pane, modal := false, overlay_open := false }

// ── subscriptions ────────────────────────────────────────────────────────

/// The dialog handshake is polled on EVERY tick, not only while a turn is
/// pending: a dialog opened by a fiber must be seen and acked even if the
/// model's own pending flag is stale. A running turn adds its live
/// display's spinner and polls.
pub def TuiApp.subscriptions (m : TuiModel) : Subs WeaverMsg :=
    let store : Option StoreState := m.state.store in
    let overlay : Subs WeaverMsg := Subs.poll 1 (fn (_ : Unit) => do {
        let ov <- Overlay.read store;
        IO.pure (WeaverMsg.overlay_polled ov)
    }) in
    let banner : Subs WeaverMsg := Subs.map WeaverMsg.banner (Banner.subscriptions m.banner) in
    if m.turn_pending
    then Subs.batch [overlay, banner, Subs.map WeaverMsg.live (Live.subscriptions store m.live)]
    else Subs.batch [overlay, banner]

/// Live messages count only while a turn runs: a poll that lands after
/// the turn folded must not resurrect its text.
def live_step (m : TuiModel) (msg : LiveMsg) : Pair TuiModel (Cmd WeaverMsg) :=
    if m.turn_pending
    then Pair.pair { m with live := Live.update m.live msg } Cmd.none
    else Pair.pair m Cmd.none

/// The dialog handshake. Opening suppresses tick draws (modal); a new
/// close sequence clears it and returns the clear+repaint that erases the
/// dialog. A missing/garbled state file is a no-op (the startup reset
/// guarantees a valid one; a torn read must not drop ownership).
def overlay_step (m : TuiModel) (ov : Option OverlayState) : Pair TuiModel (Cmd WeaverMsg) :=
    match ov {
        Option.none => Pair.pair m Cmd.none,
        Option.some s =>
            if s.want
            then
                if m.overlay_open
                then Pair.pair m Cmd.none
                else Pair.pair { m with overlay_open := true, modal := true } Cmd.none
            else if Bool.or m.overlay_open (Bool.not (s.seq == m.dialog_seq))
            then
                let closed : TuiModel := { m with overlay_open := false, modal := false, dialog_seq := s.seq } in
                Pair.pair closed repaint_cmd
            else Pair.pair m Cmd.none,
    }

/// Fold a batch in order. A fold returns one command, so the first
/// non-trivial one wins; subscription messages only ever produce one (the
/// overlay close's repaint).
#[partial]
def batch_step (m : TuiModel) (msgs : List WeaverMsg) : Pair TuiModel (Cmd WeaverMsg) :=
    batch_go m msgs Cmd.none

#[partial]
def batch_go (m : TuiModel) (msgs : List WeaverMsg) (cmd : Cmd WeaverMsg) : Pair TuiModel (Cmd WeaverMsg) :=
    match msgs {
        List.empty => Pair.pair m cmd,
        List.cons x rest => batch_next (update_msg m x) rest cmd,
    }

#[partial]
def batch_next (step : Pair TuiModel (Cmd WeaverMsg)) (rest : List WeaverMsg) (cmd : Cmd WeaverMsg) : Pair TuiModel (Cmd WeaverMsg) :=
    match step {
        Pair.pair m2 c => batch_go m2 rest (first_cmd cmd c),
    }

def first_cmd (a : Cmd WeaverMsg) (b : Cmd WeaverMsg) : Cmd WeaverMsg :=
    match a {
        Cmd.none => b,
        _ => a,
    }

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

/// A command that fetched a model list opens the picker. The picker
/// replaces the transcript for the command's output: the listing is not
/// appended, so dismissing the dialog leaves no wall of model names.
def open_picker_from (m : TuiModel) (models_opt : Option (List String)) : TuiModel :=
    match models_opt {
        Option.none => m,
        Option.some models => match models {
            List.empty => m,
            List.cons _ _ =>
                let current : String := m.state.run.session.config.model in
                let title : String := String.concat "Select a model — " m.state.provider in
                { m with picker := Option.some (Picker.make title models current) },
        },
    }

def command_keep (m : TuiModel) (effect : Effect) : Pair TuiModel (Cmd WeaverMsg) :=
    let with_state : TuiModel := set_state m effect.state in
    let opened : TuiModel := open_picker_from with_state effect.picker in
    match effect.picker {
        Option.some _ =>
            // The picker IS the output: appending the whole listing would
            // leave a wall of model names behind after the dialog is
            // dismissed. Esc then returns to the untouched transcript.
            let m2 : TuiModel := with_turn_end (fn (mm : TuiModel) => mm) opened in
            if effect.state.quit then Pair.pair m2 Cmd.quit else Pair.pair m2 repaint_cmd,
        Option.none => command_keep_append opened effect,
    }

def command_keep_append (m : TuiModel) (effect : Effect) : Pair TuiModel (Cmd WeaverMsg) :=
    let pair := append_block_at m (plain_lines (Diff.lines effect.output)) in
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
    // A session switch drops instructions queued for the old session.
    let m1 : TuiModel := { with_state with queued := List.empty, queued_ready := false } in
    let m2 : TuiModel := with_turn_end (fn (mm : TuiModel) => mm) m1 in
    match m2.state.store {
        Option.none => reset_in_memory m2 effect.output,
        Option.some st => Pair.pair m2 (Cmd.perform (fn (_ : Unit) => reset_action st effect.output)),
    }

def reset_in_memory (m : TuiModel) (output : String) : Pair TuiModel (Cmd WeaverMsg) :=
    let tr : Transcript := Transcript.append Transcript.empty (plain_lines (theme_split_lines output)) in
    let m2 : TuiModel := { m with pane := Pane.reset m.pane tr } in
    Pair.pair m2 Cmd.none

def reset_action (st : StoreState) (output : String) : IO WeaverMsg := do {
    let tr0 <- Store.startup_transcript st.dir;
    let total : I64 := tr0.total;
    let block : List TLine := Transcript.next_block tr0 (plain_lines (theme_split_lines output));
    let _ <- Store.append_transcript st.dir total block;
    IO.pure (WeaverMsg.transcript_reset (Transcript.append tr0 block))
}

#[partial]
def update_event (m : TuiModel) (e : Event) : Pair TuiModel (Cmd WeaverMsg) :=
    match e {
        Event.key k => update_key m k,
        Event.resize rows cols =>
            Pair.pair (with_streak_reset (fn (mm : TuiModel) => set_size mm rows cols) m) Cmd.none,
        Event.paste text =>
            if picker_open m
            then Pair.pair m Cmd.none
            else Pair.pair (with_streak_reset (fn (mm : TuiModel) => prompt_step mm (PromptMsg.paste text)) m) Cmd.none,
        Event.mouse me => update_mouse m me,
        // The frame clock: each tick delivers what the subscriptions want
        // (the dialog handshake always; the banner sweep and a running
        // turn's live display while they animate). An idle tick folds to
        // an unchanged model (a zero-diff draw). Deliberately NO streak
        // reset -- ticks arrive every 100 ms and would make the
        // double-Ctrl-C/Ctrl-D gestures impossible.
        Event.tick =>
            let m2 : TuiModel := { m with frame := m.frame + 1 } in
            tick_step m2 (Subs.on_tick m2.frame (TuiApp.subscriptions m2) WeaverMsg.batch),
        _ => Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m) Cmd.none,
    }

/// A tick: fold the subscriptions' pure messages (the spinner frame) now,
/// then run their polls -- unless a session title is due, which forks
/// here instead (once), AFTER persistence and the plan dialog.
def tick_step (m : TuiModel) (due : Pair (List WeaverMsg) (Cmd WeaverMsg)) : Pair TuiModel (Cmd WeaverMsg) :=
    match due {
        Pair.pair msgs poll => match batch_step m msgs {
            Pair.pair m2 _ =>
                if m2.title_due
                then Pair.pair { m2 with title_due := false } (title_cmd m2)
                else Pair.pair m2 poll,
        },
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
    if picker_open m
    then Pair.pair m Cmd.none
    else match me {
        MouseEvent.scroll_up _ _ => scroll_with_pages m wheel_step,
        MouseEvent.scroll_down _ _ => scroll_with_pages m (0 - wheel_step),
        MouseEvent.press btn r c =>
            if is_left btn
            then
                // An input-box press places the caret and starts an input
                // selection; anything else goes to the pane (the bar, or a
                // transcript selection) and drops the input highlight.
                if Prompt.box_contains (Model.prompt_box m) r c
                then
                    let m2 : TuiModel := prompt_step m (PromptMsg.press r c) in
                    Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) (pane_only m2 PaneMsg.clear_selection)) Cmd.none
                else pane_paged_step { m with prompt := Prompt.clear_selection m.prompt } (PaneMsg.press r c)
            else Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m) Cmd.none,
        MouseEvent.drag btn r c =>
            if Bool.and (is_left btn) (Prompt.selecting m.prompt)
            then Pair.pair (with_streak_reset (fn (mm : TuiModel) => prompt_step mm (PromptMsg.drag r c)) m) Cmd.none
            else if is_left btn
            then pane_paged_step m (PaneMsg.drag r c)
            else Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m) Cmd.none,
        MouseEvent.release btn r c =>
            if Bool.and (is_left btn) (Prompt.selecting m.prompt)
            then finish_input_selection_step m r c
            else if is_left btn
            then finish_selection_step m r c
            else Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m) Cmd.none,
    }

/// A pane message whose copied text (none for these) is not wanted.
def pane_only (m : TuiModel) (msg : PaneMsg) : TuiModel :=
    match Model.pane_step m msg {
        Pair.pair m2 _ => m2,
    }

/// The OSC 52 copy command; the forced repaint also clears the highlight.
def clipboard_cmd (t : String) : Cmd WeaverMsg :=
    Cmd.perform (fn (_ : Unit) => do {
        Clipboard.copy t;
        IO.pure (WeaverMsg.key_event Event.tick)
    })

/// End a drag: the release point is folded in one last time, the pane
/// drops the highlight, and a non-empty selection is copied (a perform,
/// so the forced repaint also repaints the de-highlighted row). A bar
/// drag just ends.
def finish_selection_step (m : TuiModel) (r : I64) (c : I64) : Pair TuiModel (Cmd WeaverMsg) :=
    match Model.pane_step m (PaneMsg.release r c) {
        Pair.pair m2 text => match text {
            Option.none => Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m2) Cmd.none,
            Option.some t => Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m2) (clipboard_cmd t),
        },
    }

/// The input-box twin: the release folds into the input selection, then a
/// non-empty drag copies through OSC 52.
def finish_input_selection_step (m : TuiModel) (r : I64) (c : I64) : Pair TuiModel (Cmd WeaverMsg) :=
    match Prompt.update (Model.prompt_box m) m.prompt (PromptMsg.release r c) {
        Pair.pair p2 text => let m2 : TuiModel := { m with prompt := p2 } in match text {
            Option.none => Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m2) Cmd.none,
            Option.some t => Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m2) (clipboard_cmd t),
        },
    }

def wheel_step : I64 := 3

def picker_open (m : TuiModel) : Bool :=
    match m.picker {
        Option.none => false,
        Option.some _ => true,
    }

/// While the model picker is open it owns the keys: the app loop still
/// reads stdin, so every key is routed here instead of the editor.
def update_key (m : TuiModel) (k : Key) : Pair TuiModel (Cmd WeaverMsg) :=
    match m.picker {
        Option.some p => picker_key m p k,
        Option.none => editor_key m k,
    }

def picker_close (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    let m2 : TuiModel := { m with picker := Option.none } in
    Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m2) repaint_cmd

/// Enter: set the chosen model and echo it through the command path,
/// which appends and persists the line and repaints (keeping the store
/// index in sync).
def picker_choose (m : TuiModel) (chosen : String) : Pair TuiModel (Cmd WeaverMsg) :=
    let st2 : WeaverState := Commands.set_model m.state chosen in
    let effect : Effect := Effect.ok st2 (String.concat "model: " chosen) in
    let m2 : TuiModel := { m with picker := Option.none } in
    command_result_step (with_streak_reset (fn (mm : TuiModel) => mm) m2) effect

def picker_key (m : TuiModel) (p : PickerModel) (k : Key) : Pair TuiModel (Cmd WeaverMsg) :=
    match Picker.update (Model.picker_height m) p k {
        PickerStep.stay p2 => Pair.pair (with_streak_reset (fn (mm : TuiModel) => { mm with picker := Option.some p2 }) m) Cmd.none,
        PickerStep.choose chosen => picker_choose m chosen,
        PickerStep.cancel => picker_close m,
    }

/// The editor's key map (the picker is closed).
def editor_key (m : TuiModel) (k : Key) : Pair TuiModel (Cmd WeaverMsg) :=
    match k {
        Key.tab => Pair.pair (with_streak_reset cycle_mode m) Cmd.none,
        Key.enter => enter_key m,
        Key.up => Pair.pair (streak_reset_input m Key.up) Cmd.none,
        Key.down => Pair.pair (streak_reset_input m Key.down) Cmd.none,
        Key.page_up => scroll_with_pages m (page_step m),
        Key.page_down => scroll_with_pages m (0 - page_step m),
        Key.ctrl c =>
            if c == "c" then ctrl_c_step m
            else if c == "d" then ctrl_d_step m
            else if c == "o" then toggle_details m
            else if c == "u" then scroll_with_pages m (half_page m)
            else Pair.pair (streak_reset_input m k) Cmd.none,
        Key.end => Pair.pair (with_streak_reset (fn (mm : TuiModel) => pane_only mm PaneMsg.repin) m) Cmd.none,
        // Home pins to the loaded top and keeps loading pages until the
        // transcript's first line is in memory (the pages land above a
        // bottom-anchored view, so each one is pinned in turn).
        Key.home => pane_paged_step m PaneMsg.top,
        Key.escape => escape_key m,
        _ => Pair.pair (streak_reset_input m k) Cmd.none,
    }

/// The Esc stop request's IO: write the generation into the signal file
/// the running turn's `should_stop` seam reads.
def stop_cmd (store : Option StoreState) (gen : I64) : Unit -> IO WeaverMsg :=
    fn (_ : Unit) => do {
        Stop.request store gen;
        IO.pure WeaverMsg.stop_sent
    }

/// Esc: clear an active selection first; otherwise, while a turn runs,
/// ask it to stop -- the fiber ends at its next model/tool boundary and
/// the live row says `stopping…` meanwhile.
def escape_key (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    if Prompt.selecting m.prompt
    then Pair.pair (with_streak_reset (fn (mm : TuiModel) => { mm with prompt := Prompt.clear_selection mm.prompt }) m) Cmd.none
    else if Pane.selecting m.pane
    then Pair.pair (with_streak_reset (fn (mm : TuiModel) => pane_only mm PaneMsg.clear_selection) m) Cmd.none
    else if Bool.and m.turn_pending (Bool.not m.live.stopping)
    then
        let m2 : TuiModel := { m with live := Live.request_stop m.live } in
        Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m2)
            (Cmd.inspect (stop_cmd m.state.store m.turn_gen))
    else Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m) Cmd.none

/// A screenful of CONTENT rows: the panel minus the indicator row it
/// spends while scrolled.
def page_step (m : TuiModel) : I64 :=
    let h : I64 := panel_height m in
    if h < 2 then 1 else h - 1

/// The half-page scroll: half a screen, at least one row (Ctrl+U;
/// Ctrl+D is the exit gesture, PageDown still scrolls a screen).
def half_page (m : TuiModel) : I64 :=
    let h : I64 := page_step m in
    if h < 2 then 1 else h / 2

/// A key for the prompt (editing, or the up/down history walk).
def streak_reset_input (m : TuiModel) (k : Key) : TuiModel :=
    { (prompt_step m (PromptMsg.key k)) with ctrl_c_streak := 0, ctrl_d_streak := 0 }

/// Route one message to the prompt; a selection's copied text is dropped
/// here (only a mouse release produces one, and that path copies it).
def prompt_step (m : TuiModel) (msg : PromptMsg) : TuiModel :=
    match Prompt.update (Model.prompt_box m) m.prompt msg {
        Pair.pair p2 _ => { m with prompt := p2 },
    }

/// `with_streak_reset f m` = apply `f`, then zero both exit streaks.
def with_streak_reset (f : TuiModel -> TuiModel) (m : TuiModel) : TuiModel :=
    { (f m) with ctrl_c_streak := 0, ctrl_d_streak := 0 }

/// One Ctrl+C press: the first since the last other event appends a
/// hint line; the second CONSECUTIVE one quits through `run_app`'s own
/// exit -- `restore_terminal`, alt screen and raw mode both unwound.
/// Consecutive-event streak, not a timed window: a pure update has no
/// clock. Any other key or message zeroes the streak.
def ctrl_c_step (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    if m.ctrl_c_streak > 0
    then Pair.pair m Cmd.quit
    else
        let m1 : TuiModel := { m with ctrl_c_streak := 1, ctrl_d_streak := 0 } in
        exit_hint_step m1 ctrl_c_hint_line

/// The Ctrl+D twin of `ctrl_c_step`: same streak rules, same hint, same
/// `Cmd.quit`. Ctrl+D replaces the old half-page scroll binding.
def ctrl_d_step (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    if m.ctrl_d_streak > 0
    then Pair.pair m Cmd.quit
    else
        let m1 : TuiModel := { m with ctrl_d_streak := 1, ctrl_c_streak := 0 } in
        exit_hint_step m1 ctrl_d_hint_line

/// Append one exit hint and persist it unless a turn owns the store.
/// `m` already carries the armed streak.
def exit_hint_step (m : TuiModel) (hint : String) : Pair TuiModel (Cmd WeaverMsg) :=
    let start : I64 := m.pane.transcript.total in
    let m2 : TuiModel := Model.append_lines m [TLine.plain hint] in
    // While a turn runs its fiber owns the store: an inline append
    // would race the echoed prompt (and the shared index temp file),
    // so the hint stays in memory -- it is a UI line, not content.
    let cmd : Cmd WeaverMsg :=
        if m.turn_pending then Cmd.none else persist_block_cmd m2.state.store start [TLine.plain hint] in
    Pair.pair m2 cmd

/// Ctrl+O: show or hide the detail lines (tool output, completed
/// thinking). The rows key carries the flag, so `TuiApp.update`'s
/// `refresh_rows` rebuilds the window.
def toggle_details (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    Pair.pair (with_streak_reset (fn (mm : TuiModel) => pane_only mm PaneMsg.toggle_details) m) Cmd.none

def ctrl_c_hint_line : String := "press Ctrl+C again to exit (or /quit)"
def ctrl_d_hint_line : String := "press Ctrl+D again to exit (or /quit)"

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
/// consumer). A turn whose fiber never ran folds back as `turn_failed`,
/// so `turn_pending` clears the same way a failed turn's does.
def enter_key (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    let text : String := String.trim (Prompt.text m.prompt) in
    if String.is_empty text then Pair.pair m Cmd.none
    else if m.turn_pending then queue_line m text
    else submit_line m text

/// Enter while a turn runs QUEUES the line instead of dropping it: the
/// head starts when the running turn's result folds in. The
/// acknowledgement is a transcript line, in memory only -- the queue is
/// per-run UI state, not session content.
def queue_line (m : TuiModel) (text : String) : Pair TuiModel (Cmd WeaverMsg) :=
    let queued : List String := List.append m.queued (List.cons text List.empty) in
    let line : TLine := TLine.plain (String.concat "queued: " text) in
    let m2 : TuiModel :=
        { (with_streak_reset (fn (mm : TuiModel) => Model.append_block { mm with prompt := Prompt.clear mm.prompt } (List.cons line List.empty)) m)
            with queued := queued } in
    Pair.pair m2 Cmd.none

/// Are instructions waiting behind the running turn?
def queued_waiting (m : TuiModel) : Bool :=
    match m.queued {
        List.empty => false,
        List.cons _ _ => true,
    }

/// Start the queue's head as the next turn, if one is waiting.
#[partial]
def start_queued (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    match m.queued {
        List.empty => Pair.pair { m with queued_ready := false } Cmd.none,
        List.cons text rest => submit_line { m with queued := rest, queued_ready := false } text,
    }

/// Submit `text` as this turn's line: echo, history, and the async turn.
def submit_line (m : TuiModel) (text : String) : Pair TuiModel (Cmd WeaverMsg) :=
    let st : WeaverState := m.state in
    let echo : List TLine := echo_lines text in
    let block : List TLine := Transcript.next_block m.pane.transcript echo in
    let start : I64 := m.pane.transcript.total in
    let store : Option StoreState := m.state.store in
    let gen : I64 := m.turn_gen + 1 in
    let m1 : TuiModel := with_streak_reset
        (fn (mm : TuiModel) => Model.append_block { mm with prompt := Prompt.submitted mm.prompt text } echo) m in
    let p1 : PaneModel := m1.pane in
    let m2 : TuiModel :=
        { m1 with turn_pending := true, banner := Banner.hidden,
            live := Live.start (Option.some m.state.run.session.spent), pane := { p1 with scroll := 0 },
            turn_gen := gen,
            modal := modal_command st text } in
    Pair.pair m2 (Cmd.perform_async
        (fn (_ : Unit) => do {
            let _ <- write_echo store start block;
            run_submitted_line m.log gen st text
        })
        (turn_never_ran st.run))

/// `enter_key`'s fiber-error message: the turn never ran, so it fails
/// against the run state it started from. Classed `io`, which is
/// recoverable: a thread that could not be created is resource
/// exhaustion, and the next submit may well succeed.
def turn_never_ran (run : RunState) (e : FiberError) : WeaverMsg :=
    WeaverMsg.turn_failed run (WeaverError.io (FiberError.message e))

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

/// A submitted line is echoed as its OWN lines, all tagged as the user's
/// role -- a multiline submit is one undivided block, styled cyan with no
/// prefix. The blank separator before the block (and the next one) is the
/// spacing that distinguishes turns.
#[partial]
def echo_lines (text : String) : List TLine :=
    List.map TLine.user_line (theme_split_lines text)

def set_state (m : TuiModel) (st : WeaverState) : TuiModel :=
    { m with state := st }

def set_run (m : TuiModel) (run : RunState) : TuiModel :=
    set_state m { (m.state) with run := run }

def set_size (m : TuiModel) (rows : I64) (cols : I64) : TuiModel :=
    { m with rows := rows, cols := cols, pane := Pane.end_drag m.pane }

// ── run_submitted_line: the dumb-mode twin over WeaverMsg ───────────────

/// A submitted line, run to completion: a slash command through
/// `Commands.dispatch`, or one model turn through shuttle's indexed
/// loop -- mirroring `dumb.mo`'s `route`/`command_turn`/`model_turn`,
/// but folding a `WeaverMsg` back instead of writing through line
/// seams.
pub def run_submitted_line (log : Option Logger) (gen : I64) (st : WeaverState) (text : String) : IO WeaverMsg := do {
    let t0 <- IO.current_time;
    let kind : String := if String.starts_with "/" text then "command" else "turn";
    Logs.info log (String.concat "ev=submit kind=" (String.concat kind
        (String.concat " bytes=" (I64.to_string (String.length text)))));
    Logs.log_rss log "submit";
    let msg <- dispatch_submitted log gen st text;
    let t1 <- IO.current_time;
    Logs.info log (String.concat "ev=submit_end elapsed_ms=" (I64.to_string (t1 - t0)));
    Logs.log_rss log "submit_end";
    Logs.info log (outcome_of msg);
    IO.pure msg
}

def outcome_of (msg : WeaverMsg) : String :=
    match msg {
        WeaverMsg.turn_result run _ _ _ _ =>
            let reason : String := if run.stopped then "stopped" else "ok" in
            String.concat "ev=turn_end reason=" (String.concat reason (String.concat " turns=" (String.concat (I64.to_string run.session.turns)
                (String.concat " in=" (String.concat (I64.to_string run.session.spent.input_tokens)
                    (String.concat " out=" (I64.to_string run.session.spent.output_tokens))))))),
        WeaverMsg.turn_failed _ e => String.concat "ev=turn_error " (WeaverError.show e),
        WeaverMsg.command_result _ => "ev=command_end",
        WeaverMsg.command_failed e => String.concat "ev=command_error " (WeaverError.show e),
        _ => "ev=submit_other",
    }

/// `/permissions` in the TUI: the current grants and one row per revoke
/// action. Revoking is a normal command dispatch, so dumb mode and the
/// dialog share every semantic.
def permissions_dialog_step (st : WeaverState) : IO WeaverMsg := do {
    let gs <- Permissions.get st.grants;
    let o0 : DialogOption := { label := "Revoke all grants", hint := "", key := "" };
    let o1 : DialogOption := { label := "Revoke read grants", hint := "", key := "" };
    let o2 : DialogOption := { label := "Revoke write grants", hint := "", key := "" };
    let o3 : DialogOption := { label := "Revoke exec grants", hint := "", key := "" };
    let o4 : DialogOption := { label := "Revoke net grants", hint := "", key := "" };
    let o5 : DialogOption := { label := "Close", hint := "Esc", key := "" };
    let text : String := Permissions.render (Place.cwd_of st.place) (Mode.show st.mode) gs;
    let body : List String := theme_split_lines text;
    let opts : List DialogOption := List.cons o0 (List.cons o1 (List.cons o2 (List.cons o3 (List.cons o4 (List.cons o5 List.empty)))));
    let d : DialogModel := Dialog.make "Permissions" "session grants (cleared on /clear and /resume)" body opts;
    let pr <- dialog_run st.colors st.store d;
    let step : DialogStep := match pr { Pair.pair _ s => s };
    permissions_step_msg st step
}

def permissions_step_msg (st : WeaverState) (step : DialogStep) : IO WeaverMsg :=
    match step {
        DialogStep.choose i => permissions_choose i st,
        _ => IO.pure (WeaverMsg.command_result (Effect.ok st "permissions closed")),
    }

def permissions_choose (i : I64) (st : WeaverState) : IO WeaverMsg := do {
    let line : String :=
        if i == 0 then "/permissions revoke all"
        else if i == 1 then "/permissions revoke read"
        else if i == 2 then "/permissions revoke write"
        else if i == 3 then "/permissions revoke exec"
        else if i == 4 then "/permissions revoke net"
        else "";
    if String.is_empty line
    then return (WeaverMsg.command_result (Effect.ok st "permissions closed"))
    else do {
        let r <- Commands.dispatch line st;
        return (command_msg st r)
    }
}

/// `/settings` in the TUI: one row per setting -- Enter types a number
/// row's value in place, or cycles the mode and thinking rows -- then
/// Model/Provider and the two save targets. The dialog stays open across
/// edits, with the last result (or a rejected value's error) as its
/// subtitle, until Esc or an action closes it.
def settings_dialog_step (st : WeaverState) : IO WeaverMsg := do {
    Overlay.begin st.store;
    let pr <- settings_loop st 0 "Enter edits or cycles -- Esc closes";
    Overlay.finish st.store;
    match pr { Pair.pair st2 action => settings_choose_action action st2 }
}

/// The setting rows as dialog options: a number row carries its value,
/// so Enter edits it; the other rows show theirs and Enter cycles them.
pub def TuiApp.settings_options (rows : List SettingRow) : List DialogOption :=
    List.map (fn (r : SettingRow) =>
        match r.kind {
            SettingKind.setting_number =>
                let o : DialogOption := { label := r.label, hint := "", key := "", value := Option.some r.value } in
                o,
            _ =>
                let o : DialogOption := { label := String.concat r.label (String.concat ": " r.value), hint := "Enter", key := "" } in
                o,
        }) rows

def settings_actions : List DialogOption :=
    let a_model : DialogOption := { label := "Model... (opens the picker)", hint := "", key := "" } in
    let a_provider : DialogOption := { label := "Provider (use /provider <name>)", hint := "", key := "" } in
    let a_save_p : DialogOption := { label := "Save to project (.weaver/config.toml)", hint := "", key := "" } in
    let a_save_g : DialogOption := { label := "Save to global (~/.weaver/config.toml)", hint := "", key := "" } in
    let a_close : DialogOption := { label := "Close", hint := "Esc", key := "" } in
    [a_model, a_provider, a_save_p, a_save_g, a_close]

/// One open of the dialog with `selected` highlighted and `status` as the
/// subtitle. Answers the edited state and the chosen action's index
/// (-1 = closed).
#[partial]
def settings_loop (st : WeaverState) (selected : I64) (status : String) : IO (Pair WeaverState I64) := do {
    let rows : List SettingRow := Commands.setting_rows st;
    let opts : List DialogOption := List.append (TuiApp.settings_options rows) settings_actions;
    let body : List String := [String.concat st.provider (String.concat "/" st.run.session.config.model)];
    let d : DialogModel := Dialog.with_default (Dialog.make "Settings" status body opts) selected;
    let pr <- Dialog.modal (paint_dialog st.colors) d;
    match pr { Pair.pair _ step => settings_step st (List.length rows) step }
}

#[partial]
def settings_step (st : WeaverState) (nrows : I64) (step : DialogStep) : IO (Pair WeaverState I64) :=
    match step {
        DialogStep.choose i =>
            if I64.lt i nrows
            then settings_applied st i (Commands.cycle_setting st (row_key_at i (Commands.setting_rows st)))
            else IO.pure (Pair.pair st (i - nrows)),
        DialogStep.submit i text =>
            settings_applied st i (Commands.apply_setting st (row_key_at i (Commands.setting_rows st)) (String.trim text)),
        _ => IO.pure (Pair.pair st (0 - 1)),
    }

/// Reopen on row `i` after an edit: the new state and its output line, or
/// the unchanged state and the error.
#[partial]
def settings_applied (st : WeaverState) (i : I64) (r : Result String (Pair WeaverState String)) : IO (Pair WeaverState I64) :=
    match r {
        Result.err e => settings_loop st i e,
        Result.ok pr => match pr { Pair.pair st2 out => settings_loop st2 i out },
    }

#[partial]
def row_key_at (i : I64) (rows : List SettingRow) : String :=
    match rows {
        List.empty => "",
        List.cons r rest => if I64.lt i 1 then r.key else row_key_at (i - 1) rest,
    }

def settings_choose_action (i : I64) (st : WeaverState) : IO WeaverMsg := do {
    let line : String :=
        if i == 0 then "/model"
        else if i == 1 then "/provider"
        else if i == 2 then "/settings save project"
        else if i == 3 then "/settings save global"
        else "";
    if String.is_empty line
    then return (WeaverMsg.command_result (Effect.ok st "settings closed"))
    else do {
        let r <- Commands.dispatch line st;
        return (command_msg st r)
    }
}

def dispatch_submitted (log : Option Logger) (gen : I64) (st : WeaverState) (text : String) : IO WeaverMsg :=
    if text == "/resume"
    then resume_dialog_step st
    else if text == "/settings"
    then settings_dialog_step st
    else if text == "/permissions"
    then permissions_dialog_step st
    else if plan_dialog_wanted st text
    then plan_dialog_step st text
    else if String.starts_with "/" text
    then command_step_tui st text
    else model_step_tui log gen st text

def mode_is_plan (m : Mode) : Bool :=
    match m { Mode.plan => true, _ => false }

/// `/plan` opens the review dialog in plan mode and a read-only view
/// outside it. `/plan approve …` stays a plain command (a deliberate
/// direct path); only the exact command is intercepted.
def plan_dialog_wanted (st : WeaverState) (text : String) : Bool :=
    text == "/plan"

/// Commands that open a modal dialog on this turn's fiber: the main
/// loop must not read stdin while one runs (`enter_key` suppresses tick
/// redraws through the same flag). Exact matches only; subcommands such
/// as `/resume <id>` and `/settings save` stay plain commands.
def modal_command (st : WeaverState) (text : String) : Bool :=
    Bool.or (plan_dialog_wanted st text)
        (Bool.or (text == "/processes")
            (Bool.or (text == "/procs")
                (Bool.or (text == "/settings")
                    (Bool.or (text == "/permissions") (text == "/resume")))))

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

def model_step_tui (log : Option Logger) (gen : I64) (st : WeaverState) (text : String) : IO WeaverMsg :=
    if st.run.turns_left < 1
    then IO.pure (WeaverMsg.turn_result st.run [TLine.plain "turn budget spent -- raise it with /budget <n>, or /clear"] List.empty st.last_context Option.none)
    else drive_turn_tui log gen st text

def drive_turn_tui (log : Option Logger) (gen : I64) (st : WeaverState) (text : String) : IO WeaverMsg := do {
    // Autocompact before the user message lands: the post-turn deltas
    // assume append-only history, so compaction cannot happen mid-turn.
    let ac <- Commands.autocompact st;
    match ac {
        Pair.pair st2 note => do {
            let before : I64 := list_msg_length st2.run.session.history;
            // The live row's baseline: the file carries cumulative spend,
            // and the live display's `base` is the submit-time total.
            Live.store_usage st2.store st2.run.session.spent;
            // The live row reads the cumulative file; the tracker answers
            // the one number autocompact needs -- the LAST call's prompt
            // (the turn's summed delta overstates it per tool call).
            let tracker <- UsageTracker.start st2.run.session.spent;
            let live_seam : Usage -> IO Unit := Live.write_usage log st2.store;
            let on_u : Usage -> IO Unit := fn (u : Usage) => do {
                let _ <- live_seam u;
                UsageTracker.silent tracker u
            };
            let r <- ResultT.run (drive_tui log gen st2 text on_u);
            let last <- UsageTracker.last tracker;
            let last_context : I64 := match r {
                Result.err _ => st2.last_context,
                Result.ok run2 => Commands.turn_context st2.run.session.spent last run2,
            };
            // A plan-mode turn's text is captured and persisted here, as
            // dumb mode does: `turn_result_of` must get it at the call,
            // or it returns a partial application (the checker does not
            // reject an under-applied constructor/def in value position).
            let plan : Option String := Commands.plan_after_turn st2 before r;
            let _ <- persist_plan st2.store plan;
            return (turn_result_of st2 before note r last_context plan)
        }
    }
}

def turn_result_of (st : WeaverState) (before : I64) (note : Option String) (r : Result WeaverError RunState) (last_context : I64) (plan : Option String) : WeaverMsg :=
    match r {
        Result.err e => WeaverMsg.turn_failed st.run e,
        Result.ok run2 =>
            let delta : List Message := drop_n_messages before run2.session.history in
            let render : List Message := drop_n_messages 1 delta in
            let lines : List TLine := transcript_lines_of_messages render in
            let with_note : List TLine := match note {
                Option.none => lines,
                Option.some text => List.append (plain_lines (theme_split_lines text)) lines,
            } in
            WeaverMsg.turn_result run2 with_note delta last_context plan,
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
def drive_tui (log : Option Logger) (gen : I64) (st : WeaverState) (text : String) (on_usage : Usage -> IO Unit) : ResultT WeaverError IO RunState := do {
    let stop : Unit -> IO Bool := Stop.predicate st.store gen;
    let with_task : RunState := { (st.run) with reg := ToolRegistry.register (Subagent.task_tool st.run.session.config log st.store stop) st.run.reg };
    let gated : RunState := { with_task with gate := Gate.weaver_tui st.mode st.colors st.store st.grants (Place.cwd_of st.place),
        emit := progress_live log st.store, on_usage := on_usage,
        should_stop := stop, stopped := false };
    let ready : RunState := append_user gated text;
    drive_loop ready
}

/// Persist every streamed fragment (live.txt). The terminal no longer
/// gets a raw preview: the live thinking row under the prompt is the
/// mid-turn display, and the turn's real block lands at completion.
def progress_live (log : Option Logger) (store : Option StoreState) (frag : String) : IO Unit :=
    if String.starts_with "retrying" frag
    then Logs.warn log (String.concat "ev=provider_retry " frag)
    else if String.starts_with "\u{1}toolerror\u{2}" frag
    then log_tool_error log frag
    else if String.starts_with "\u{1}activity\u{2}" frag
    then activity_step log store frag
    else if String.starts_with "\u{1}thinking\u{2}" frag
    then append_thinking store frag
    else persist_chunk store frag

/// Split at the first 0x02: the tool-error fragment's name/message pair.
#[partial]
def split_sep (bs : List U8) (acc : List U8) : Pair String String :=
    match bs {
        List.empty => Pair.pair (String.from_list (List.reverse acc)) "",
        List.cons b rest =>
            if U8.beq b 2u8
            then Pair.pair (String.from_list (List.reverse acc)) (String.from_list rest)
            else split_sep rest (List.cons b acc),
    }

pub def tool_error_payload (frag : String) : Option (Pair String String) :=
    let head : String := "\u{1}toolerror\u{2}" in
    if String.starts_with head frag
    then Option.some (split_sep (String.to_list (String.drop (String.length head) frag)) List.empty)
    else Option.none

/// A failed tool's name and error text at warn/error level (2 KB cap; no
/// file contents beyond what the tool itself returned as an error).
def log_tool_error (log : Option Logger) (frag : String) : IO Unit :=
    match tool_error_payload frag {
        Option.none => IO.pure unit,
        Option.some pr => match pr {
            Pair.pair name msg =>
                Logs.error log (String.concat "ev=tool_error name=" (String.concat name (String.concat " msg=" msg))),
        },
    }

/// The tool name in an activity fragment of `phase` (`start`/`end`), or
/// none for any other payload.
pub def activity_name (frag : String) (phase : String) : Option String :=
    let head : String := "\u{1}activity\u{2}" ++ phase ++ "\u{2}" in
    if String.starts_with head frag
    then Option.some (String.drop (String.length head) frag)
    else Option.none

/// Record a tool's phase at info. The crash detector can only report the
/// log's LAST line, so this is what makes it name the tool instead of just
/// the submit when a turn dies mid-dispatch.
def log_activity (log : Option Logger) (frag : String) : IO Unit :=
    match activity_name frag "start" {
        Option.some name => Logs.info log ("ev=tool_start name=" ++ name),
        Option.none => match activity_name frag "end" {
            Option.some name => Logs.info log ("ev=tool_end name=" ++ name),
            Option.none => IO.pure unit,
        },
    }

/// An activity fragment's two jobs: the crash record's event, and the live
/// row's latest phase.
def activity_step (log : Option Logger) (store : Option StoreState) (frag : String) : IO Unit := do {
    log_activity log frag;
    write_activity store frag
}

/// The activity feed: only the latest event matters, so it is
/// overwritten rather than appended.
def write_activity (store : Option StoreState) (frag : String) : IO Unit :=
    match store {
        Option.none => IO.pure unit,
        Option.some s => Store.write_named s "activity.txt" frag,
    }

/// A reasoning fragment, with the reserved tag stripped: the tagged
/// byte itself never belongs in a rendered file.
def append_thinking (store : Option StoreState) (frag : String) : IO Unit :=
    let tag : String := "\u{1}thinking\u{2}" in
    let n : I64 := String.length tag in
    let payload : String := String.slice frag n (String.length frag - n) in
    match store {
        Option.none => IO.pure unit,
        Option.some s => Store.append_named s "thinking.txt" payload,
    }

def persist_chunk (store : Option StoreState) (frag : String) : IO Unit :=
    match store {
        Option.none => IO.pure unit,
        Option.some s => Store.append_chunk s frag,
    }

// ── transcript rendering ─────────────────────────────────────────────────

def transcript_lines_of_messages (ms : List Message) : List TLine :=
    List.flatten (List.map TuiApp.render_message ms)

#[partial]
def take_strings (n : I64) (xs : List String) : List String :=
    if n < 1i64 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (take_strings (n - 1i64) rest),
    }

/// A one-line summary of a tool call's input JSON, clipped for display.
def tool_input_summary (input : Json) : String :=
    Text.take_width (Json.to_string input) 80

/// A tool result: the first three output lines plus a collapsed marker;
/// the full output rides as detail lines (Ctrl+O), never lost.
def tool_result_lines (output : String) (is_error : Bool) : List TLine :=
    let lines : List String := theme_split_lines output in
    let n : I64 := List.length lines in
    let mark : String := if is_error then "✘ " else "✔ " in
    if I64.gt n 3i64
    then
        // Collapsed: the summary line; expanded (Ctrl+O): the full text
        // as detail lines. The preview lines are NOT stored separately,
        // or Ctrl+O would show them twice.
        let summary : String := String.concat mark
            (String.concat (I64.to_string n) " lines · ctrl+o") in
        List.cons (TLine.plain summary) (List.map TLine.detail_line lines)
    else if Bool.and is_error (Bool.not (I64.gt n 0i64))
    then List.cons (TLine.plain (String.concat mark "error (no output)")) List.empty
    else List.map TLine.plain lines

/// Assistant text is raw (no `assistant:` label); a user message is the
/// echoed prompt's role; tool/system output keeps its one-word label so
/// the theme can still classify it. Only an assistant `text` block is
/// Markdown; a tool result that happens to carry text stays literal.
pub def TuiApp.render_message (m : Message) : List TLine :=
    let markdown : Bool := match m.role {
        Role.assistant => true,
        _ => false,
    } in
    let lines : List TLine :=
        List.flatten (List.map (fn (c : Content) => render_content_lines markdown c) m.content) in
    match m.role {
        Role.user => List.map (fn (l : TLine) => TLine.user_line l.text) lines,
        Role.assistant => lines,
        Role.system_ => List.map (fn (l : TLine) => prefixed "system: " l) lines,
        Role.tool => lines,
    }

def prefixed (p : String) (l : TLine) : TLine :=
    if l.detail
    then TLine.detail_line (String.concat p l.text)
    else TLine.plain (String.concat p l.text)

def render_content_lines (markdown : Bool) (c : Content) : List TLine :=
    match c {
        Content.text s => [if markdown then TLine.markdown_line s else TLine.plain s],
        Content.tool_use id name input =>
            let summary : String := String.concat "⏺ " (String.concat name
                (String.concat "(" (String.concat (tool_input_summary input) ")"))) in
            [TLine.plain summary],
        Content.tool_result call_id output is_error => tool_result_lines output is_error,
        Content.thinking s signature =>
            let n : I64 := String.length s in
            let marker : String := String.concat "[thinking · "
                (String.concat (I64.to_string n) " chars · ctrl+o]") in
            // A blank line after the block keeps the reasoning (collapsed or
            // not) apart from the answer and the tool log below it.
            List.cons (TLine.thinking_marker marker)
                (List.append (List.map TLine.thinking_detail (theme_split_lines s)) [TLine.plain ""]),
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
pub def Gate.weaver_tui (mode : Mode) (colors : Bool) (store : Option StoreState) (grants : Option (Ref (List PermGrant))) (root : Option Path) : Gate :=
    {
        ask := weaver_tui_ask mode colors store grants root,
        precheck := weaver_tui_precheck mode grants root,
    }

def weaver_tui_precheck (mode : Mode) (grants : Option (Ref (List PermGrant))) (root : Option Path) (p : Pick) : IO (Option Approval) :=
    let a : Assessment := Assess.pick root p in
    match Policy.decide p.cap mode a {
        Decision.refuse reason => IO.pure (Option.some (Approval.deny reason)),
        Decision.ask => do {
            let gs <- Permissions.get grants;
            if Permissions.matches gs p.cap (Reach.is_inside a.scope)
            then IO.pure (Option.some Approval.once)
            else IO.pure Option.none
        },
        Decision.allow => IO.pure Option.none,
    }

def weaver_tui_ask (mode : Mode) (colors : Bool) (store : Option StoreState) (grants : Option (Ref (List PermGrant))) (root : Option Path) (p : Pick) : IO Approval :=
    let a : Assessment := Assess.pick root p in
    match Policy.decide p.cap mode a {
        Decision.allow => IO.pure Approval.once,
        Decision.ask => prompt_overlay colors store grants root a p,
        Decision.refuse reason => IO.pure (Approval.deny reason),
    }

def diff_lines_of (diff_pair : Option (Pair String String)) : List String :=
    match diff_pair {
        Option.none => List.empty,
        Option.some pr => match pr {
            Pair.pair old new => Diff.lines (capped_diff old new),
        }
    }

def prompt_overlay (colors : Bool) (store : Option StoreState) (grants : Option (Ref (List PermGrant))) (root : Option Path) (a : Assessment) (p : Pick) : IO Approval := do {
    let diff_pair <- Diff.for_input p.name p.input;
    // The header names the target path; repeat it as its own line so a
    // long path stays visible above the diff.
    let target : List String := match pick_target p {
        Option.none => List.empty,
        Option.some path => List.cons (String.concat "file: " path) List.empty,
    };
    let place : List String := theme_split_lines (Gate.assessment_lines root a);
    let body : List String := List.append (List.append (List.append [pick_header p] place) target) (diff_lines_of diff_pair);
    let repo_ok : Bool := Reach.is_inside a.scope;
    let opts : List DialogOption := perm_options p.cap repo_ok;
    let subtitle : String := String.concat (cap_name p.cap) (String.concat " " p.name);
    let d : DialogModel := Dialog.with_notes (Dialog.make "Permission required" subtitle body opts);
    let default_idx : I64 := perm_default_index p.cap repo_ok;
    let pr <- dialog_run colors store (Dialog.with_default d default_idx);
    match pr {
        Pair.pair final step => match step {
            DialogStep.choose i => do {
                let ans : PickAnswer := perm_answer_at repo_ok i;
                let note : String := Dialog.note_text final;
                let _ <- record_answer grants p ans;
                IO.pure (answer_approval ans note)
            },
            _ => IO.pure (Approval.deny "declined by user"),
        },
    }
}

/// The approval rows. `r` (repo scope) is offered only when the pick stays
/// inside the workspace root -- a file there, or a command whose every
/// path is; an outside or unreadable pick has nothing to confine it to.
def perm_options (cap : Capability) (repo_ok : Bool) : List DialogOption :=
    let once : DialogOption := { label := "Approve once", hint := "y", key := "y" } in
    let here : DialogOption := { label := String.concat "Always allow all " (String.concat (cap_name cap) "s in this repo"), hint := "r", key := "r" } in
    let any : DialogOption := { label := String.concat "Always allow all " (String.concat (cap_name cap) "s this session (anywhere)"), hint := "a", key := "a" } in
    let deny : DialogOption := { label := "Deny", hint := "n", key := "n" } in
    if repo_ok then [once, here, any, deny] else [once, any, deny]

def perm_default_index (cap : Capability) (repo_ok : Bool) : I64 :=
    if cap_is_read cap then 0
    else if repo_ok then 3
    else 2

/// An option index to its answer; the list shape follows `repo_ok`.
def perm_answer_at (repo_ok : Bool) (i : I64) : PickAnswer :=
    if repo_ok
    then
        if i == 0 then PickAnswer.pick_once
        else if i == 1 then PickAnswer.pick_here
        else if i == 2 then PickAnswer.pick_any
        else PickAnswer.pick_deny "declined by user"
    else
        if i == 0 then PickAnswer.pick_once
        else if i == 1 then PickAnswer.pick_any
        else PickAnswer.pick_deny "declined by user"

def cap_is_read (c : Capability) : Bool :=
    match c { Capability.read => true, _ => false }

// ── the /resume picker ─────────────────────────────────────────────────

/// Sessions per dialog page. The dialog lays out `nopts + 7` fixed rows
/// inside `height - 4`, and only ~11 one-row options fit a 24-row
/// terminal; 8 sessions + Older + Cancel leaves room for the subtitle.
def resume_page_size (rows : I64) : I64 :=
    if rows < 22 then 4 else 8

/// `s` clipped to `max_cells` cells with an ellipsis when it was cut.
/// `Text.take_width` is cell-aware; a dialog label must stay one row
/// (a wrapped label breaks the dialog's row budget).
def ellipsize (max_cells : I64) (s : String) : String :=
    let w : I64 := Text.width s in
    if Bool.not (I64.lt max_cells w) then s
    else String.concat (Text.take_width s max_cells) "…"

/// What a picker row does: load a session, change page, or close.
pub type ResumeAction {
    resume_session (id : String),
    resume_shift (delta : I64),
    /// Widen the picker from this repo's sessions to every repo's.
    resume_all,
    resume_cancel,
}

/// One session's row: `name (current) — description`, hint `N turns`.
/// The caps keep label + hint inside one 80-column dialog row.
pub def TuiApp.resume_option (current : String) (i : SessionInfo) : DialogOption :=
    let id : String := i.id in
    let name : String := i.name in
    let desc : String := i.description in
    let turns : I64 := i.turns in
    let is_current : Bool := String.beq current id in
    let tagged : String := if is_current then String.concat name " (current)" else name in
    let name_text : String := ellipsize 26 tagged in
    let label : String :=
        if String.is_empty desc
        then name_text
        else String.concat name_text (String.concat " — " (ellipsize 22 desc)) in
    let hint : String := Commands.turns_label turns in
    let opt : DialogOption := { label := label, hint := hint, key := "" } in
    opt

#[partial]
def resume_option_rows (current : String) (infos : List SessionInfo) (opts : List DialogOption) (acts : List ResumeAction) : Pair (List DialogOption) (List ResumeAction) :=
    match infos {
        List.empty => Pair.pair (List.reverse opts) (List.reverse acts),
        List.cons i rest =>
            let id : String := i.id in
            let opt : DialogOption := TuiApp.resume_option current i in
            let act : ResumeAction := ResumeAction.resume_session id in
            resume_option_rows current rest (List.cons opt opts) (List.cons act acts),
    }

/// Append one option/action pair to the running lists.
def push_row (opt : DialogOption) (act : ResumeAction) (p : Pair (List DialogOption) (List ResumeAction)) : Pair (List DialogOption) (List ResumeAction) :=
    match p {
        Pair.pair opts acts =>
            Pair.pair (List.append opts (List.cons opt List.empty)) (List.append acts (List.cons act List.empty)),
    }

/// The page's rows: its sessions, then Newer/Older page shifts when
/// they exist, then (`offer_all`) the switch to every repo's sessions,
/// then Cancel. Pure, so the labels and the index-to-action mapping are
/// unit-testable without a terminal.
pub def TuiApp.resume_rows (current : String) (offer_all : Bool) (sp : SessionPage) : Pair (List DialogOption) (List ResumeAction) :=
    let close_opt : DialogOption := { label := "Cancel", hint := "Esc", key := "" } in
    let all_opt : DialogOption := { label := "All repos' sessions…", hint := "", key := "" } in
    let older_opt : DialogOption := { label := "Older sessions…", hint := "", key := "" } in
    let newer_opt : DialogOption := { label := "Newer sessions…", hint := "", key := "" } in
    let p0 : Pair (List DialogOption) (List ResumeAction) := resume_option_rows current sp.rows List.empty List.empty in
    let p1 : Pair (List DialogOption) (List ResumeAction) :=
        if sp.has_older then push_row older_opt (ResumeAction.resume_shift 1i64) p0 else p0 in
    let p2 : Pair (List DialogOption) (List ResumeAction) :=
        if sp.has_newer then push_row newer_opt (ResumeAction.resume_shift (0i64 - 1i64)) p1 else p1 in
    let p3 : Pair (List DialogOption) (List ResumeAction) :=
        if offer_all then push_row all_opt ResumeAction.resume_all p2 else p2 in
    push_row close_opt ResumeAction.resume_cancel p3

#[partial]
pub def TuiApp.resume_action_at (i : I64) (acts : List ResumeAction) : ResumeAction :=
    match acts {
        List.empty => ResumeAction.resume_cancel,
        List.cons a rest => if i < 1 then a else TuiApp.resume_action_at (i - 1) rest,
    }

/// The picker outcome: a session id to load, or the dialog was closed.
pub type ResumeChoice {
    resume_id (id : String),
    resume_closed,
}

/// Run the modal for one page and recurse when a page shift is chosen.
/// The caller holds the overlay open across the whole loop: releasing
/// it per page would leave a window where the main loop reads stdin and
/// steals the keystroke meant for the next page.
/// `every` is the whole store; `all` picks whether the page shows it or
/// only this repo's sessions.
#[partial]
def resume_pick (st : WeaverState) (s : StoreState) (page_size : I64) (every : List SessionInfo) (all : Bool) (page : I64) : IO ResumeChoice := do {
    let infos : List SessionInfo := Commands.sessions_for st.place all every;
    let sp : SessionPage := Commands.session_page page_size page infos;
    let rows : Pair (List DialogOption) (List ResumeAction) := TuiApp.resume_rows s.id (Bool.not all) sp;
    let subtitle : String := if all then "every repo's sessions · Enter loads · Esc cancels" else "this repo's sessions · Enter loads · Esc cancels";
    match rows {
        Pair.pair opts acts => do {
            let d0 : DialogModel := Dialog.make "Resume a session" subtitle List.empty opts;
            let d : DialogModel := { d0 with footer := "↑/↓ select · Enter load · Esc cancel" };
            let pr <- Dialog.modal (paint_dialog st.colors) d;
            match pr {
                Pair.pair _ step => match step {
                    DialogStep.choose i => match TuiApp.resume_action_at i acts {
                        ResumeAction.resume_session id => IO.pure (ResumeChoice.resume_id id),
                        ResumeAction.resume_shift delta => resume_pick st s page_size every all (page + delta),
                        ResumeAction.resume_all => resume_pick st s page_size every true 0,
                        ResumeAction.resume_cancel => IO.pure ResumeChoice.resume_closed,
                    },
                    _ => IO.pure ResumeChoice.resume_closed,
                },
            }
        },
    }
}

/// Bare `/resume` in the TUI: list the sessions in a dialog, then run
/// the chosen one through the ordinary command path (whose reset
/// restores its transcript). `/resume <id>` is untouched.
def resume_dialog_step (st : WeaverState) : IO WeaverMsg :=
    match st.store {
        Option.none => command_step_tui st "/resume",
        Option.some s => do {
            let every <- Store.list_sessions s.root;
            match every {
                List.empty => IO.pure (WeaverMsg.command_result (Effect.ok st "no saved sessions")),
                List.cons _ _ => do {
                    let size <- Terminal.size;
                    let rows : I64 := match size { Pair.pair r _ => r };
                    let page_size : I64 := resume_page_size rows;
                    // No session of this repo yet: open on every repo's.
                    let all : Bool := List.is_empty (Commands.sessions_for st.place false every);
                    let _ <- Overlay.begin (Option.some s);
                    let choice <- resume_pick st s page_size every all 0;
                    let _ <- Overlay.finish (Option.some s);
                    match choice {
                        ResumeChoice.resume_id id => command_step_tui st (String.concat "/resume " id),
                        ResumeChoice.resume_closed => IO.pure (WeaverMsg.command_result (Effect.ok st "resume closed")),
                    }
                },
            }
        },
    }

// ── the plan dialog ────────────────────────────────────────────────────

/// Display bounds for a plan preview. The full text stays in the session
/// transcript/history; the dialog scrolls, so the cap only bounds the
/// wrap cost for an absurdly large plan.
def plan_preview_bytes : I64 := 262144
def plan_preview_lines : I64 := 2000

#[partial]
def take_lines (n : I64) (ls : List String) : List String :=
    if n < 1 then List.empty
    else match ls {
        List.empty => List.empty,
        List.cons l rest => List.cons l (take_lines (n - 1) rest),
    }

def plan_body_of (content : String) : List String :=
    let n : I64 := String.length content in
    let capped : String := if plan_preview_bytes < n then String.slice content 0 plan_preview_bytes else content in
    let all : List String := theme_split_lines capped in
    let lines : List String := take_lines plan_preview_lines all in
    if Bool.or (plan_preview_bytes < n) (plan_preview_lines < List.length all)
    then List.append lines ["[plan preview truncated -- full plan is in the transcript/history]"]
    else lines

def plan_body (st : WeaverState) : List String :=
    match Commands.current_plan st {
        Option.none => ["(no plan yet -- switch to plan mode with /mode plan, then ask for a plan)"],
        Option.some content => plan_body_of content,
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

/// Persist a plan-mode turn's text for later `/plan` displays. A store
/// failure is silent here: the plan still lives in `WeaverState`, and
/// the transcript/history remains the fallback.
def persist_plan (store : Option StoreState) (p : Option String) : IO Unit :=
    match p {
        Option.none => IO.pure unit,
        Option.some text => match store {
            Option.none => IO.pure unit,
            Option.some s => do {
                let _ <- Store.write_plan s.dir text;
                IO.pure unit
            },
        },
    }

// ── agent-generated session titles ─────────────────────────────────────
// After the first turn (or a plan) one small model call names the
// session for `/resume`. It runs on its own fiber from the frame clock,
// after persistence (and after the plan dialog, which blocks frames),
// and it writes a field only while that field still holds the DERIVED
// value -- a `/name` typed meanwhile wins.

def store_present (o : Option StoreState) : Bool :=
    match o {
        Option.none => false,
        Option.some _ => true,
    }

def opt_text (o : Option String) : String :=
    match o {
        Option.none => "",
        Option.some s => s,
    }

/// Whether this completed turn warrants the title call.
def title_wanted (st : WeaverState) (plan : Option String) : Bool :=
    let has_plan : Bool := match plan {
        Option.none => false,
        Option.some _ => true,
    } in
    Title.needed (store_present st.store) (st.run.session.config.base_url == "mock")
        st.run.session.turns has_plan

def title_derived_name (m : StoreMeta) (s : Session) : Bool :=
    match m.name {
        Option.none => true,
        Option.some v => match Store.derive_name s {
            Option.none => false,
            Option.some d => v == d,
        },
    }

def title_derived_desc (m : StoreMeta) (s : Session) : Bool :=
    match m.description {
        Option.none => true,
        Option.some v => match Store.derive_description s {
            Option.none => false,
            Option.some d => v == d,
        },
    }

def title_write (yes : Bool) (dir : Path) (field : TitleField) (v : String) : IO Unit :=
    if Bool.not yes
    then IO.pure unit
    else do {
        let _ <- Store.write_title dir field (Option.some v);
        IO.pure unit
    }

/// The fiber's action. Every failure is cosmetic: the derived title
/// stays, and the turn has already landed.
def run_title_action (log : Option Logger) (st : WeaverState) (s : StoreState) : IO WeaverMsg := do {
    let sess : Session := st.run.session;
    let meta_r <- Store.read_meta s.dir;
    match meta_r {
        Result.err e => do {
            Logs.debug log (String.concat "ev=title_error " e);
            IO.pure (WeaverMsg.title_result Option.none)
        },
        Result.ok m => do {
            let keep_name : Bool := title_derived_name m sess;
            let keep_desc : Bool := title_derived_desc m sess;
            if Bool.and (Bool.not keep_name) (Bool.not keep_desc)
            then IO.pure (WeaverMsg.title_result Option.none)
            else do {
                let request : String := opt_text (Store.derive_name sess);
                let answer : String := match st.plan {
                    Option.some p => p,
                    Option.none => opt_text (Store.derive_description sess),
                };
                let got <- Title.generate sess.config request answer;
                match got {
                    Option.none => do {
                        Logs.debug log "ev=title_skip";
                        IO.pure (WeaverMsg.title_result Option.none)
                    },
                    Option.some p => match p {
                        Pair.pair n d => do {
                            let _ <- title_write (Bool.and keep_name (Bool.not (String.is_empty n)))
                                s.dir TitleField.title_name n;
                            let _ <- title_write (Bool.and keep_desc (Bool.not (String.is_empty d)))
                                s.dir TitleField.title_description d;
                            let _ <- Logs.info log (String.concat "ev=title name="
                                (String.concat n (String.concat " desc=" d)));
                            IO.pure (WeaverMsg.title_result (Option.some (Pair.pair n d)))
                        },
                    },
                }
            }
        },
    }
}

def title_cmd (m : TuiModel) : Cmd WeaverMsg :=
    match m.state.store {
        Option.none => Cmd.none,
        Option.some s => Cmd.perform_async
            (fn (_ : Unit) => run_title_action m.log m.state s)
            (fn (_ : FiberError) => WeaverMsg.title_result Option.none),
    }

def plan_dialog_step (st : WeaverState) (text : String) : IO WeaverMsg :=
    if mode_is_plan st.mode
    then plan_approval_step st
    else plan_view_step st

/// Outside plan mode `/plan` is a read-only view: the plan the mode
/// produced, still available after approval and later turns.
def plan_view_step (st : WeaverState) : IO WeaverMsg := do {
    let o0 : DialogOption := { label := "Close", hint := "Esc", key := "" };
    let d0 : DialogModel := Dialog.make "Current plan" "read-only -- switch to plan mode to revise or approve" (plan_body st) [o0];
    let d : DialogModel := { d0 with markdown := true, footer := "PageUp/PageDown or wheel scroll -- Enter/Esc close" };
    let pr <- dialog_run st.colors st.store d;
    match pr {
        Pair.pair _ _ => IO.pure (WeaverMsg.command_result (plan_effect st "plan closed")),
    }
}

def plan_approval_step (st : WeaverState) : IO WeaverMsg := do {
    let o0 : DialogOption := { label := "Approve and execute (allow_edit)", hint := "a", key := "a" };
    let o1 : DialogOption := { label := "Approve to manual", hint := "m", key := "m" };
    let o2 : DialogOption := { label := "Revise with a note", hint := "r", key := "r" };
    let o3 : DialogOption := { label := "Cancel", hint := "Esc", key := "" };
    let d0 : DialogModel := Dialog.make "Plan ready" "approve it to leave plan mode" (plan_body st) [o0, o1, o2, o3];
    let d : DialogModel := { (Dialog.with_notes d0) with markdown := true, footer := "PageUp/PageDown scroll -- e note, a approve/edit, m manual, r revise, Esc cancel" };
    let pr <- dialog_run st.colors st.store d;
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
                            if i == 0
                            then do {
                                // "Approve and execute": the mode change is
                                // in `e.state`; start a real turn with the
                                // instruction (the old code only switched
                                // modes and sat idle).
                                let text : String :=
                                    if String.is_empty note
                                    then "Implement the approved plan."
                                    else String.concat "Implement the approved plan.\n\nNote: " note;
                                IO.pure (WeaverMsg.submit e.state text)
                            } else do {
                                if String.is_empty note
                                then IO.pure (WeaverMsg.command_result e)
                                else do {
                                    persist_note e.state note;
                                    let st2 : WeaverState := note_into_state e.state note;
                                    let out : String := String.concat e.output (String.concat "\nnote: " note);
                                    let e2 : Effect := { e with state := st2, output := out };
                                    IO.pure (WeaverMsg.command_result e2)
                                }
                            }
                        },
                    }
                },
            _ => IO.pure (WeaverMsg.command_result (plan_effect st "plan not approved")),
        },
    }
}

// ── dialog rendering ───────────────────────────────────────────────────

/// A Markdown body: the lines join into ONE document, so headings,
/// lists and fences are parsed rather than shown as source.
pub def markdown_body_rows (colors : Bool) (width : I64) (lines : List String) : List DisplayRow :=
    if List.length lines < 1
    then List.empty
    else Rows.of_line colors width (TLine.markdown_line (List.intercalate "\n" lines))

/// The body as transcript rows: a Markdown dialog renders its body as one
/// document, any other keeps the transcript's line styling.
def dialog_body_rows (colors : Bool) (width : I64) (d : DialogModel) : List SizedWidget :=
    let rows : List DisplayRow :=
        if d.markdown
        then markdown_body_rows colors width d.body
        else List.flatten (List.map (fn (l : String) => Rows.of_line colors width (TLine.plain l)) d.body) in
    List.map Rows.widget rows

def paint_dialog (colors : Bool) (prev : Option Screen) (d : DialogModel) : IO (Pair Screen DialogModel) :=
    Dialog.paint (theme_border_style_with colors) (dialog_body_rows colors) prev d

/// Run a dialog. The overlay handshake brackets the whole modal --
/// confirm, cancel or EOF: `begin` takes stdin from the main loop;
/// `finish` releases it and bumps the close sequence the loop's poll
/// repaints on.
def dialog_run (colors : Bool) (store : Option StoreState) (d : DialogModel) : IO (Pair DialogModel DialogStep) := do {
    Overlay.begin store;
    let r <- Dialog.modal (paint_dialog colors) d;
    Overlay.finish store;
    IO.pure r
}
