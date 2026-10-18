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
use shuttle::gate {Pick, Approval, Gate}
use shuttle::message {Message}
use shuttle::message_types {Role, Content}
use weaver::commands {WeaverState, Effect, set_fatal, Commands.dispatch}
use weaver::policy {Mode, Mode.cycle, Policy.decide, Decision}
use weaver::gate {pick_header, capped_diff, gate_answer_prompt, gate_answer_feedback}
use weaver::diff {Diff.for_input, Diff.lines}
use weaver::dumb {append_user, drive_loop}
use weaver::model {TuiModel, WeaverMsg, on_event, init_tui_model, Model.view, Model.scroll_step, Model.append_block, list_length, panel_height}
use weaver::theme {theme_line_style}
use weaver::error {WeaverError, WeaverError.show, WeaverError.recoverable}
use tui::types {Event, Key, LayoutSize}
use tui::widget {Widget, SizedWidget, sized, label, with_style}
use tui::widgets::input {InputState, input_state, handle_input_key}
use tui::core {empty_screen, mk_rect}
use tui::render {render, diff, apply_deltas}
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
pub def Tui.run (st : WeaverState) : IO Bool := do {
    let is_tty <- Terminal.enter_raw_mode;
    if Bool.not is_tty
    then return false
    else do {
        let size <- Terminal.size;
        run_tui_with_size st size
    }
}

def run_tui_with_size (st : WeaverState) (size : Pair I64 I64) : IO Bool :=
    match size {
        Pair.pair rows cols => do {
            let app : App TuiModel WeaverMsg :=
                App.app (init_tui_model st rows cols) on_event TuiApp.update Model.view (0 - 1);
            let _ <- run_app app;
            return true
        }
    }

// ── update ───────────────────────────────────────────────────────────────

/// Named `TuiApp.update`, not bare `update` -- a one-word generic name
/// is exactly the shape that collides across a whole-program check
/// (`Model.view` already did), so this one is qualified pre-emptively.
pub def TuiApp.update (m : TuiModel) (msg : WeaverMsg) : Pair TuiModel (Cmd WeaverMsg) :=
    match msg {
        WeaverMsg.key_event e => update_event m e,
        WeaverMsg.turn_result run lines =>
            Pair.pair (with_streak_reset (fn (mm : TuiModel) => Model.append_block (set_run mm run) lines) m) Cmd.none,
        WeaverMsg.turn_failed run e =>
            Pair.pair (with_streak_reset (fn (mm : TuiModel) => model_for_failure mm run e) m) (failed_cmd e),
        WeaverMsg.command_result effect => command_result_step m effect,
        WeaverMsg.command_failed e =>
            Pair.pair (with_streak_reset (fn (mm : TuiModel) => model_for_command_failure mm e) m) (failed_cmd e),
    }

/// A failed turn's model: the failure's run lands (the pre-error
/// session), then the ONE classification point decides -- a recoverable
/// error leaves the fatal slot empty (dumb failed_step's contract); a
/// fatal one carries the error out. The error line block follows.
def model_for_failure (m : TuiModel) (run : RunState) (e : WeaverError) : TuiModel :=
    let m2 : TuiModel := set_run m run in
    if WeaverError.recoverable e
    then Model.append_block m2 [error_line e]
    else Model.append_block (set_state m2 (set_fatal m2.state e)) [error_line e]

/// A failed COMMAND keeps the run as it is; the fatal slot + line.
def model_for_command_failure (m : TuiModel) (e : WeaverError) : TuiModel :=
    let st : WeaverState := m.state in
    model_for_failure m st.run e

/// Dumb mode's `failed_step` contract, mirrored: a RECOVERABLE error
/// leaves the session running; a fatal one ends the run -- the state
/// carries the error out, `main` exits 1 through the fatal slot.
def failed_cmd (e : WeaverError) : Cmd WeaverMsg :=
    if WeaverError.recoverable e then Cmd.none else Cmd.quit

/// `append_block` over a state swap (command failures keep the run).
def append_block_state (m : TuiModel) (st : WeaverState) (lines : List String) : TuiModel :=
    Model.append_block (set_state m st) lines

def command_result_step (m : TuiModel) (effect : Effect) : Pair TuiModel (Cmd WeaverMsg) :=
    let m2 : TuiModel := with_streak_reset
        (fn (mm : TuiModel) => Model.append_block (set_state mm effect.state) (Diff.lines effect.output)) m in
    if effect.state.quit then Pair.pair m2 Cmd.quit else Pair.pair m2 Cmd.none

def update_event (m : TuiModel) (e : Event) : Pair TuiModel (Cmd WeaverMsg) :=
    match e {
        Event.key k => update_key m k,
        Event.resize rows cols =>
            Pair.pair (with_streak_reset (fn (mm : TuiModel) => set_size mm rows cols) m) Cmd.none,
        _ => Pair.pair (with_streak_reset (fn (mm : TuiModel) => mm) m) Cmd.none,
    }

def update_key (m : TuiModel) (k : Key) : Pair TuiModel (Cmd WeaverMsg) :=
    match k {
        Key.tab => Pair.pair (with_streak_reset cycle_mode m) Cmd.none,
        Key.enter => enter_key m,
        Key.page_up => Pair.pair (with_streak_reset (fn (mm : TuiModel) => Model.scroll_step mm (panel_height mm)) m) Cmd.none,
        Key.page_down => Pair.pair (with_streak_reset (fn (mm : TuiModel) => Model.scroll_step mm (0 - panel_height mm)) m) Cmd.none,
        Key.ctrl c =>
            if c == "c" then ctrl_c_step m
            else if c == "u" then Pair.pair (with_streak_reset (fn (mm : TuiModel) => Model.scroll_step mm (half_page mm)) m) Cmd.none
            else if c == "d" then Pair.pair (with_streak_reset (fn (mm : TuiModel) => Model.scroll_step mm (0 - half_page mm)) m) Cmd.none
            else Pair.pair (streak_reset_input m k) Cmd.none,
        Key.end => Pair.pair (with_streak_reset (fn (mm : TuiModel) => { mm with scroll := 0 }) m) Cmd.none,
        Key.home => Pair.pair (with_streak_reset (fn (mm : TuiModel) => Model.scroll_step mm 999999) m) Cmd.none,
        _ => Pair.pair (streak_reset_input m k) Cmd.none,
    }

/// The half-page scroll: half the panel, at least one row (Claude
/// Code's Ctrl+U/Ctrl+D binding).
def half_page (m : TuiModel) : I64 :=
    let h : I64 := panel_height m in
    if h < 2 then 1 else h / 2

def streak_reset_input (m : TuiModel) (k : Key) : TuiModel :=
    { (edit_input m k) with ctrl_c_streak := 0 }

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
    else Pair.pair (append_lines ({ m with ctrl_c_streak := 1 } : TuiModel) [ctrl_c_hint_line]) Cmd.none

def ctrl_c_hint_line : String := "press Ctrl+C again to exit (or /quit)"

def edit_input (m : TuiModel) (k : Key) : TuiModel :=
    { m with input := handle_input_key k m.input }

def cycle_mode (m : TuiModel) : TuiModel :=
    let st2 : WeaverState := { (m.state) with mode := Mode.cycle m.state.mode } in
    set_state m st2

/// Enter with a non-empty line: echo it into the transcript right away
/// (the turn itself is about to block the UI) and clear the box, then
/// `perform` the real work -- a model turn or a slash command -- off
/// the state as it was BEFORE this key, which `run_submitted_line`
/// closes over.
def enter_key (m : TuiModel) : Pair TuiModel (Cmd WeaverMsg) :=
    let text : String := String.trim m.input.value in
    if String.is_empty text
    then Pair.pair m Cmd.none
    else
        let st : WeaverState := m.state in
        let m2 : TuiModel := with_streak_reset
            (fn (mm : TuiModel) => Model.append_block (clear_input mm) [String.concat "you: " text]) m in
        Pair.pair m2 (Cmd.perform (fn (_ : Unit) => run_submitted_line st text))

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

def append_lines (m : TuiModel) (lines : List String) : TuiModel :=
    { m with transcript := List.append m.transcript lines }

// ── run_submitted_line: the dumb-mode twin over WeaverMsg ───────────────

/// A submitted line, run to completion: a slash command through
/// `Commands.dispatch`, or one model turn through shuttle's indexed
/// loop -- mirroring `dumb.mo`'s `route`/`command_turn`/`model_turn`,
/// but folding a `WeaverMsg` back instead of writing through line
/// seams.
pub def run_submitted_line (st : WeaverState) (text : String) : IO WeaverMsg :=
    if String.starts_with "/" text
    then command_step_tui st text
    else model_step_tui st text

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
    then IO.pure (WeaverMsg.turn_result st.run ["turn budget spent -- /clear or restart with --max-turns"])
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
            WeaverMsg.turn_result run2
                (transcript_lines_of_messages (drop_n_messages (before + 1) run2.session.history)),
    }

/// The transcript's error entry: the one render point does the prose,
/// the entry is a transcript line Phase 11's palette will color.
def error_line (e : WeaverError) : String :=
    String.concat "error: " (WeaverError.show e)

/// Rebuild the turn's `Gate` from `Gate.weaver_tui` (instead of
/// `Gate.weaver`) and swap the emit seam to `TuiApp.progress` (NOT
/// dumb's `stdout_write`: a perform-time raw write lands on the alt
/// screen mid-frame -- the recorded UI-repair finding). Drive the loop
/// -- `append_user`/`drive_loop` are `dumb.mo`'s own halves, reused
/// as-is (Phase 9: `drive_loop` is already `ResultT WeaverError IO`).
def drive_tui (st : WeaverState) (text : String) : ResultT WeaverError IO RunState := do {
    let gated : RunState := { (st.run) with gate := Gate.weaver_tui st.mode, emit := TuiApp.progress };
    let ready : RunState := append_user gated text;
    drive_loop ready
}

/// The TUI turn's live progress sink: the model's streamed text, shown
/// as ONE transparent-overwrite line at the status-bar row (row
/// `rows - 2` -- status at `rows - 2`, input at `rows - 1`). The line
/// lives only until the perform-enforced repaint, which repaints from
/// blank and rewrites the real status bar.
pub def TuiApp.progress (frag : String) : IO Unit := do {
    let size <- Terminal.size;
    match size {
        Pair.pair rows cols => do {
            let _ <- Terminal.cursor_move (rows - 2) 0;
            IO.write_stdout (blank_of cols);
            let _ <- Terminal.cursor_move (rows - 2) 0;
            IO.write_stdout (progress_text frag cols);
            IO.flush_stdout
        }
    }
}

/// `n` spaces: the row wipe (tui has no erase-line builder; spaces are
/// blank cells and the forced repaint's blank-diff drops them anyway).
/// Bounded to `cols` -- the caller clips to the same width.
#[terminating]
def blank_of (n : I64) : String :=
    if n < 1 then "" else blank_of_go n

#[terminating]
def blank_of_go (n : I64) : String :=
    if n < 1 then "" else String.concat " " (blank_of_go (n - 1))

def progress_text (frag : String) (cols : I64) : String :=
    String.slice (String.concat "[thinking] " frag) 0 (cols - 1)

// ── transcript rendering ─────────────────────────────────────────────────

def transcript_lines_of_messages (ms : List Message) : List String :=
    List.map render_message ms

def render_message (m : Message) : String :=
    String.concat (role_label m.role) (String.concat ": " (List.intercalate " " (List.map render_content m.content)))

def role_label (r : Role) : String :=
    match r {
        Role.system_ => "system",
        Role.user => "user",
        Role.assistant => "assistant",
        Role.tool => "tool",
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
pub def Gate.weaver_tui (mode : Mode) : Gate :=
    { ask := weaver_tui_ask mode }

def weaver_tui_ask (mode : Mode) (p : Pick) : IO Approval :=
    match Policy.decide p.cap mode {
        Decision.allow => IO.pure Approval.once,
        Decision.ask => prompt_overlay p,
        Decision.refuse reason => IO.pure (Approval.deny reason),
    }

def prompt_overlay (p : Pick) : IO Approval := do {
    let diff_pair <- Diff.for_input p.name p.input;
    let _ <- render_overlay p diff_pair;
    // Keys typed while the model call blocked sit in the tty buffer --
    // without this drain the overlay's one-shot read would consume the
    // STALE keystroke and phantom-answer the prompt.
    let _ <- drain_stale_keys 64;
    let key_opt <- read_one_key;
    let ap : Approval := approval_of_key key_opt;
    let _ <- echo_answer p diff_pair ap;
    return ap
}

/// Drop the buffered keystrokes the drain would otherwise feed the
/// answer read: `poll 0 -> read 1 -> drop` until the tap runs dry.
/// EOF stops the drain but leaves the reader to the read itself.
#[terminating]
def drain_stale_keys (budget : I64) : IO Unit :=
    if Bool.not (budget > 0)
    then IO.pure unit
    else do {
        let readable <- Terminal.poll 0;
        if Bool.not readable
        then IO.pure unit
        else do {
            let chunk <- IO.read_stdin_exact 1;
            if String.length chunk == 0
            then IO.pure unit
            else drain_stale_keys (budget - 1)
        }
    }

/// One immediate piece of feedback on the overlay's answer row (the
/// last line of the overlay): the answer's echo, written before the
/// gate returns -- an approval used to show nothing until the whole
/// turn's next render, so under a slow provider the prompt looked dead.
def echo_answer (p : Pick) (diff_pair : Option (Pair String String)) (ap : Approval) : IO Unit := do {
    let lines : List String := overlay_lines p diff_pair;
    // The answer row is the LAST overlay line, and its prompt's own
    // length is where the echo starts (columns are 0-based here).
    let row : I64 := list_length lines - 1;
    let col : I64 := String.length (gate_answer_prompt p.cap);
    let _ <- Terminal.cursor_move row col;
    IO.write_stdout (gate_answer_feedback p.cap ap);
    IO.flush_stdout
}

def approval_of_key (k : Option Key) : Approval :=
    match k {
        Option.none => Approval.deny "declined by user (eof)",
        Option.some key => match key {
            Key.char c =>
                if c == "y" then Approval.once
                else if c == "a" then Approval.always
                else Approval.deny "declined by user",
            _ => Approval.deny "declined by user",
        }
    }

def render_overlay (p : Pick) (diff_pair : Option (Pair String String)) : IO Unit := do {
    let size <- Terminal.size;
    render_overlay_at p diff_pair size
}

def render_overlay_at (p : Pick) (diff_pair : Option (Pair String String)) (size : Pair I64 I64) : IO Unit :=
    match size {
        Pair.pair rows cols => do {
            // A real clear, not a diff: an overlay fires mid-batch, so
            // `prev` (the main loop's back buffer) is irrelevant here --
            // only `Terminal.clear_screen` guarantees no transcript text
            // shows through around the prompt.
            Terminal.clear_screen;
            Terminal.cursor_move 0 0;
            let screen := render (overlay_widget p diff_pair) (mk_rect 0 0 cols rows) (empty_screen rows cols);
            let deltas := diff (empty_screen rows cols) screen;
            IO.write_stdout (apply_deltas deltas);
            IO.flush_stdout
        }
    }

def overlay_widget (p : Pick) (diff_pair : Option (Pair String String)) : Widget :=
    Widget.column (List.map overlay_row (overlay_lines p diff_pair))

def overlay_row (line : String) : SizedWidget :=
    sized (LayoutSize.fixed 1) (with_style (theme_line_style line) (label line))

def overlay_lines (p : Pick) (diff_pair : Option (Pair String String)) : List String :=
    List.append [pick_header p] (List.append (diff_lines_of diff_pair) ["", gate_answer_prompt p.cap])

def diff_lines_of (diff_pair : Option (Pair String String)) : List String :=
    match diff_pair {
        Option.none => List.empty,
        Option.some pr => match pr {
            Pair.pair old new => Diff.lines (capped_diff old new),
        }
    }

// ── a private, one-shot key read ────────────────────────────────────────
//
// Does not touch the main loop's `InputReader` -- see the header comment.
// Blocks (negative timeout) until one decoded `Key` arrives, or returns
// `none` at EOF (never silently approves).

def read_one_key : IO (Option Key) := do {
    let _ <- Terminal.poll (0 - 1);
    read_key_loop ""
}

#[terminating]
def read_key_loop (pending : String) : IO (Option Key) := do {
    let chunk <- IO.read_stdin_exact 1;
    if String.length chunk == 0
    then IO.pure Option.none
    else key_from_decoded (Input.decode (pending ++ chunk))
}

def key_from_decoded (decoded : Pair (List Event) String) : IO (Option Key) :=
    match decoded {
        Pair.pair evs leftover => key_from_list evs leftover
    }

#[terminating]
def key_from_list (evs : List Event) (leftover : String) : IO (Option Key) :=
    match evs {
        List.empty => read_key_loop leftover,
        List.cons e rest => match e {
            Event.key k => IO.pure (Option.some k),
            _ => key_from_list rest leftover,
        }
    }
