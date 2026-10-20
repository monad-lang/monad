/// The dumb-mode interactive loop -- weaver.md Phase 3: line I/O over
/// `IO.read_line`-shaped seams (the TUI is Phase 4, gated on
/// terminal-ui; dumb mode stays in the product as the piped/non-tty
/// fallback, the niche `git --no-pager` serves). One prompt line before
/// every read, `/`-input routed to the command table
/// (`commands.mo`), everything else one model turn through shuttle's
/// indexed loop, the session persisting across inputs and the turn
/// budget spanning them.
///
/// Elm state threading throughout (no `IORef`, there is none): the
/// whole session lives in `commands.mo`'s `WeaverState` and every step
/// returns the advanced one. The read/write seams are PARAMETERS --
/// production passes stdin and a flushed stdout, the e2e passes a
/// scripted pair, and the gate answers through the same seams.
use shuttle::agent {Agent, Agent.exec, RunState}
use shuttle::loop {Loop.iterate}
use shuttle::message {Message}
use shuttle::message_types {Role, Content}
use shuttle::session {Session}
use weaver::commands {WeaverState, Effect, set_fatal, Commands.dispatch}
use weaver::gate {Gate.weaver}
use weaver::policy {Mode, Mode.show, Mode.warns_auto}
use weaver::error {WeaverError, WeaverError.show, WeaverError.recoverable, WeaverError.of_shuttle}
use weaver::store {StoreState, Store.record_history}
use weaver::theme {Theme.tint, theme_status_code, class_code, LineClass}
use init::transformers {ResultT}
use tui::terminal {Terminal.poll}

/// The interactive sleep: `Terminal.poll`'s timeout IS a timed wait --
/// there is no sleep native (no new natives -- the recorded owner
/// decision) -- and it wakes early on a keypress, which a queued
/// Ctrl+C or a typed line only makes livelier (the gate's stale-key
/// drain swallows what it buffered).
pub def Dumb.poll_sleep (ms : I64) : IO Unit := do {
    let _ <- Terminal.poll ms;
    IO.pure unit
}

/// One loop step's outcome: the advanced state, and whether the loop
/// continues. EOF and `/quit` are the only things that end a session.
struct Step {
    state : WeaverState,
    again : Bool,
}

/// Drive the session: prompt, read, route, repeat. EOF returns the
/// final state (the caller disposes what needs disposing); `/quit` does
/// the same through `state.quit`.
///
/// The read seam is `Unit -> IO (Option String)`, NOT a naked
/// `IO (Option String)`: in the compiled backend an `IO A` value is its
/// already-performed result (`RawIO.io` is a strict box, `io_bind` only
/// unwraps), so a naked action passed as a parameter would run ONCE at
/// the call site and serve the same line on every later bind. The
/// function form re-evaluates per call -- the same reason shuttle's
/// `emit` and `Gate.ask` seams are function-typed.
///
/// `#[terminating]`: the recursion is on the (external) input stream,
/// which no structural measure sees.
#[terminating]
pub def Dumb.run (read : Unit -> IO (Option String)) (write : String -> IO Unit) (st : WeaverState) : IO WeaverState := do {
    let w : String -> IO Unit := theme_write write st.colors;
    let _ <- write (dumb_banner st);
    let _ <- write (prompt_line st);
    let line <- read unit;
    let step <- step_of read w st line;
    if step.again then Dumb.run read write step.state else IO.pure step.state
}

/// The line-based UI's one-line launch banner (the TUI renders the full
/// colorful mark): `weaver · coding agent · provider/model`, dim.
def dumb_banner (st : WeaverState) : String :=
    let provider : String := st.provider in
    let model : String := st.run.session.config.model in
    let text : String := String.concat "weaver · coding agent · "
        (String.concat provider (String.concat "/" model)) in
    if st.colors
    then String.concat (class_code LineClass.hint) (String.concat text "\u{1b}[0m")
    else text

/// The dumb write, tinted through the theme by line class -- plain
/// when the session's colors are off (`NO_COLOR`).
def theme_write (write : String -> IO Unit) (colors : Bool) : String -> IO Unit :=
    fn (s : String) => write (Theme.tint colors s)

def step_of (read : Unit -> IO (Option String)) (write : String -> IO Unit) (st : WeaverState) (line : Option String) : IO Step :=
    match line {
        Option.none => IO.pure (mk_step st false),
        Option.some s => route read write st (String.trim s),
    }

/// Empty input re-prompts; `/` goes to the command table; anything
/// else is one model turn.
def route (read : Unit -> IO (Option String)) (write : String -> IO Unit) (st : WeaverState) (s : String) : IO Step :=
    if String.is_empty s then IO.pure (mk_step st true)
    else if String.starts_with "/" s then command_turn write st s
    else model_turn read write st s

// ── The command half ───────────────────────────────────────────────────

def command_turn (write : String -> IO Unit) (st : WeaverState) (line : String) : IO Step := do {
    let r <- Commands.dispatch line st;
    command_result write st r
}

/// A failed command is the typed error (the dispatch's `Result.err`,
/// no state attached -- the caller's stands, session intact); a
/// successful one prints its output and continues (or quits).
def command_result (write : String -> IO Unit) (st : WeaverState) (r : Result WeaverError Effect) : IO Step :=
    match r {
        Result.err e => failed_step write st e,
        Result.ok e => command_ok write e,
    }

def command_ok (write : String -> IO Unit) (e : Effect) : IO Step := do {
    let _ <- write (String.concat e.output "\n");
    command_step e
}

/// `/quit`'s flag ends the loop; every other command continues it.
def command_step (e : Effect) : IO Step :=
    let st2 : WeaverState := e.state in
    IO.pure (mk_step st2 (Bool.not st2.quit))

// ── The model half ─────────────────────────────────────────────────────

/// One user input, one turn of shuttle's indexed loop -- possibly
/// several model calls when tools dispatch (the mock wire's script
/// indexes by assistant message, so a scripted turn 1 tool call plus a
/// scripted turn 2 answer is ONE input's worth of loop).
def model_turn (read : Unit -> IO (Option String)) (write : String -> IO Unit) (st : WeaverState) (text : String) : IO Step :=
    if st.run.turns_left < 1 then budget_step write st else drive_turn read write st text

def budget_step (write : String -> IO Unit) (st : WeaverState) : IO Step := do {
    let _ <- write "turn budget spent -- /clear or restart with --max-turns\n";
    IO.pure (mk_step st true)
}

def drive_turn (read : Unit -> IO (Option String)) (write : String -> IO Unit) (st : WeaverState) (text : String) : IO Step := do {
    let r <- ResultT.run (drive read write st text);
    turn_result write st r
}

def turn_result (write : String -> IO Unit) (st : WeaverState) (r : Result WeaverError RunState) : IO Step :=
    match r {
        Result.err e => failed_step write st e,
        Result.ok run2 => turn_ok write st run2,
    }

/// One failure, classified through the one classification point: a
/// recoverable error prints `error: <show>` and the loop continues
/// with the session exactly as it was (the Phase 3 behavior, now
/// typed); a fatal one ALSO prints, then ends the run -- the state
/// carries the error out so `main` can exit 1.
def failed_step (write : String -> IO Unit) (st : WeaverState) (e : WeaverError) : IO Step := do {
    let _ <- write (String.concat "error: " (String.concat (WeaverError.show e) "\n"));
    if WeaverError.recoverable e
    then IO.pure (mk_step st true)
    else IO.pure (mk_step (set_fatal st e) false)
}

/// The turn's text reached stdout live through `emit`; all that is
/// left here is ending its line, adding the blank separator line
/// before the next prompt (Phase 11's spacing), and returning the
/// advanced state.
/// (The struct update lives in `advance_run`, not here: `{ x with
/// .. }` parses only in a plain body, not inside a do-block.)
def turn_ok (write : String -> IO Unit) (st : WeaverState) (run2 : RunState) : IO Step := do {
    let _ <- write "\n\n";
    let warn <- persist_turn st run2;
    finish_turn write st run2 warn
}

/// Same contract as the TUI: a store error disables persistence and
/// says so ONCE, instead of silently rewriting the same history block
/// on every later turn.
def finish_turn (write : String -> IO Unit) (st : WeaverState) (run2 : RunState) (warn : Option String) : IO Step :=
    match warn {
        Option.none => IO.pure (mk_step (advance_run st run2) true),
        Option.some e => warn_turn write st run2 e,
    }

def warn_turn (write : String -> IO Unit) (st : WeaverState) (run2 : RunState) (e : String) : IO Step := do {
    let line : String := String.concat "warning: session persistence disabled: " (String.concat e "\n");
    let _ <- write line;
    IO.pure (mk_step (disable_store (advance_run st run2)) true)
}

def disable_store (st : WeaverState) : WeaverState :=
    let st2 : WeaverState := { st with store := Option.none } in
    st2

/// The history delta of a successful dumb-mode turn (dumb mode has no
/// transcript block log -- the session file is the record). An error
/// rides back to `turn_ok`, which disables persistence.
def persist_turn (st : WeaverState) (run2 : RunState) : IO (Option String) :=
    match st.store {
        Option.none => IO.pure Option.none,
        Option.some s => do {
            let before : I64 := msg_len st.run.session.history;
            let delta : List Message := drop_msgs before run2.session.history;
            let r <- Store.record_history s run2.session delta;
            IO.pure (match r { Result.err e => Option.some e, Result.ok _ => Option.none })
        },
    }

#[partial]
def msg_len (ms : List Message) : I64 :=
    match ms {
        List.empty => 0,
        List.cons _ rest => 1 + msg_len rest,
    }

#[partial]
def drop_msgs (n : I64) (ms : List Message) : List Message :=
    if n < 1 then ms
    else match ms {
        List.empty => ms,
        List.cons _ rest => drop_msgs (n - 1) rest,
    }

def advance_run (st : WeaverState) (run2 : RunState) : WeaverState :=
    let st2 : WeaverState := { st with run := run2 } in
    st2

/// Append the user message, rebuild the gate for the CURRENT mode (the
/// gate closes over the mode it was built with), and drive the loop to
/// the end of the turn -- the returned `RunState` carries the advanced
/// session, the spent budget and the grown always-cache. Phase 9: the
/// drive seam is `ResultT WeaverError IO` -- shuttle's `String` errors
/// cross the boundary through `WeaverError.of_shuttle` (the one wrap,
/// provider-tagged: everything this seam produces is a wire failure).
def drive (read : Unit -> IO (Option String)) (write : String -> IO Unit) (st : WeaverState) (text : String) : ResultT WeaverError IO RunState := do {
    let gated : RunState := gate_for st.mode read (theme_write write st.colors) st.run;
    let ready : RunState := append_user gated text;
    drive_loop ready
}

/// `Loop.run_state`'s shape minus the projection: `Agent.exec` gives
/// back the WHOLE `RunState`, and Weaver needs it -- the always-cache
/// lives there and must survive across inputs. `Agent.exec`'s own seam
/// stays `ResultT String IO` (shuttle keeps `String`, Design 7); the
/// conversion runs it to a `Result` and re-wraps. (NOT `ResultT.lift`:
/// the lift-in-a-do-block shape crashes the compiled backend -- a
/// scratch repro confirmed it in isolation, while this
/// `ResultT.mk (do { let r <- ResultT.run ... })` shape is the one
/// `main.mo`'s `mcp_proxy_run` already uses.)
def drive_loop (run : RunState) : ResultT WeaverError IO RunState :=
    ResultT.mk (do {
        let r <- ResultT.run (Agent.exec Loop.iterate run);
        return (shuttle_result r)
    })

def shuttle_result (r : Result String (Pair RunState Unit)) : Result WeaverError RunState :=
    match r {
        Result.err e => Result.err (WeaverError.of_shuttle e),
        Result.ok p => Result.ok (run_of_pair p),
    }

def run_of_pair (p : Pair RunState Unit) : RunState :=
    match p { Pair.pair r _ => r }

def gate_for (mode : Mode) (read : Unit -> IO (Option String)) (write : String -> IO Unit) (run : RunState) : RunState :=
    let r2 : RunState := { run with gate := Gate.weaver mode read write } in
    r2

def append_user (run : RunState) (text : String) : RunState :=
    let m : Message := { role := Role.user, content := [Content.text text] } in
    let history2 : List Message := List.append run.session.history [m] in
    let s2 : Session := { (run.session) with history := history2 } in
    let r2 : RunState := { run with session := s2 } in
    r2

// ── The status/prompt line ─────────────────────────────────────────────

/// The one line before every read: the `auto` warning (the trust
/// setting must never pass unremarked), the mode, the provider/model,
/// the turn budget, and the token spend from the session's own
/// accounting, followed by dumb mode's own `"> "` prompt. `tui_app.mo`'s
/// status bar reuses `Dumb.status_fields` for everything up to that
/// prompt -- the input box IS the prompt there -- so the two UIs never
/// drift on what the status line shows. Mode-colored through the
/// theme's status code when colors are on.
def prompt_line (st : WeaverState) : String :=
    let plain : String := Dumb.status_fields st ++ "> " in
    if Bool.not st.colors
    then plain
    else
        let code : String := theme_status_code st.mode in
        String.concat code (String.concat plain "\u{1b}[0m")

/// Everything `prompt_line` shows except the trailing `"> "` prompt.
pub def Dumb.status_fields (st : WeaverState) : String :=
    auto_warning st.mode
        ++ "["
        ++ Mode.show st.mode
        ++ "] "
        ++ st.provider
        ++ "/"
        ++ st.run.session.config.model
        ++ " | turns "
        ++ I64.to_string st.run.session.turns
        ++ "/"
        ++ I64.to_string st.budget
        ++ " | tokens in "
        ++ I64.to_string st.run.session.spent.input_tokens
        ++ ", out "
        ++ I64.to_string st.run.session.spent.output_tokens
        ++ ", cached "
        ++ I64.to_string st.run.session.spent.cached_tokens

/// `auto` mode is a trust setting, not a sandbox -- say so while it
/// is on.
def auto_warning (mode : Mode) : String :=
    if Mode.warns_auto mode then "WARNING: auto mode -- tools run unasked. " else ""

// ── helpers ─────────────────────────────────────────────────────────────

def mk_step (st : WeaverState) (again : Bool) : Step :=
    let s : Step := { state := st, again := again } in
    s
