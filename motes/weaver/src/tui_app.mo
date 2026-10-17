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
use weaver::commands {WeaverState, Effect, Commands.dispatch}
use weaver::policy {Mode, Mode.cycle, Policy.decide, Decision}
use weaver::gate {pick_header, capped_diff}
use weaver::diff {Diff.for_input, Diff.lines}
use weaver::dumb {append_user, drive_loop}
use weaver::model {TuiModel, WeaverMsg, on_event, init_tui_model, Model.view}
use tui::types {Event, Key, LayoutSize}
use tui::widget {Widget, SizedWidget, sized, label}
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
        WeaverMsg.turn_result run lines => Pair.pair (append_lines (set_run m run) lines) Cmd.none,
        WeaverMsg.command_result effect => command_result_step m effect,
    }

def command_result_step (m : TuiModel) (effect : Effect) : Pair TuiModel (Cmd WeaverMsg) :=
    let m2 : TuiModel := append_lines (set_state m effect.state) (Diff.lines effect.output) in
    if effect.state.quit then Pair.pair m2 Cmd.quit else Pair.pair m2 Cmd.none

def update_event (m : TuiModel) (e : Event) : Pair TuiModel (Cmd WeaverMsg) :=
    match e {
        Event.key k => update_key m k,
        Event.resize rows cols => Pair.pair (set_size m rows cols) Cmd.none,
        _ => Pair.pair m Cmd.none,
    }

def update_key (m : TuiModel) (k : Key) : Pair TuiModel (Cmd WeaverMsg) :=
    match k {
        Key.tab => Pair.pair (cycle_mode m) Cmd.none,
        Key.enter => enter_key m,
        _ => Pair.pair (edit_input m k) Cmd.none,
    }

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
        let m2 : TuiModel := append_lines (clear_input m) [String.concat "you: " text] in
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
    let e <- Commands.dispatch line st;
    return (WeaverMsg.command_result e)
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

def turn_result_of (st : WeaverState) (before : I64) (r : Result String RunState) : WeaverMsg :=
    match r {
        Result.err e => WeaverMsg.turn_result st.run [String.concat "error: " e],
        Result.ok run2 =>
            WeaverMsg.turn_result run2
                (transcript_lines_of_messages (drop_n_messages (before + 1) run2.session.history)),
    }

/// Rebuild the turn's `Gate` from `Gate.weaver_tui` (instead of
/// `Gate.weaver`) and drive the loop -- `append_user`/`drive_loop` are
/// `dumb.mo`'s own read/write-independent halves, reused as-is.
def drive_tui (st : WeaverState) (text : String) : ResultT String IO RunState := do {
    let gated : RunState := { (st.run) with gate := Gate.weaver_tui st.mode };
    let ready : RunState := append_user gated text;
    drive_loop ready
}

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
    let key_opt <- read_one_key;
    return (approval_of_key key_opt)
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
    sized (LayoutSize.fixed 1) (label line)

def overlay_lines (p : Pick) (diff_pair : Option (Pair String String)) : List String :=
    List.append [pick_header p] (List.append (diff_lines_of diff_pair) ["", "[y/n/a]: "])

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
