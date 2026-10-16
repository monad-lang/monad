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
use weaver::commands {WeaverState, Effect, Commands.dispatch}
use weaver::gate {Gate.weaver}
use weaver::policy {Mode, Mode.show, Mode.warns_auto}
use init::transformers {ResultT}

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
    let _ <- write (prompt_line st);
    let line <- read unit;
    let step <- step_of read write st line;
    if step.again then Dumb.run read write step.state else IO.pure step.state
}

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
    let e <- Commands.dispatch line st;
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

def turn_result (write : String -> IO Unit) (st : WeaverState) (r : Result String RunState) : IO Step :=
    match r {
        Result.err e => turn_err write st e,
        Result.ok run2 => turn_ok write st run2,
    }

/// A provider or wire failure keeps the session as it was: the input
/// is not lost to the transcript, the user simply retries.
def turn_err (write : String -> IO Unit) (st : WeaverState) (e : String) : IO Step := do {
    let _ <- write (String.concat "error: " (String.concat e "\n"));
    IO.pure (mk_step st true)
}

/// The turn's text reached stdout live through `emit`; all that is
/// left here is ending its line and returning the advanced state.
/// (The struct update lives in `advance_run`, not here: `{ x with
/// .. }` parses only in a plain body, not inside a do-block.)
def turn_ok (write : String -> IO Unit) (st : WeaverState) (run2 : RunState) : IO Step := do {
    let _ <- write "\n";
    IO.pure (mk_step (advance_run st run2) true)
}

def advance_run (st : WeaverState) (run2 : RunState) : WeaverState :=
    let st2 : WeaverState := { st with run := run2 } in
    st2

/// Append the user message, rebuild the gate for the CURRENT mode (the
/// gate closes over the mode it was built with), and drive the loop to
/// the end of the turn -- the returned `RunState` carries the advanced
/// session, the spent budget and the grown always-cache.
def drive (read : Unit -> IO (Option String)) (write : String -> IO Unit) (st : WeaverState) (text : String) : ResultT String IO RunState := do {
    let gated : RunState := gate_for st.mode read write st.run;
    let ready : RunState := append_user gated text;
    drive_loop ready
}

/// `Loop.run_state`'s shape minus the projection: `Agent.exec` gives
/// back the WHOLE `RunState`, and Weaver needs it -- the always-cache
/// lives there and must survive across inputs.
def drive_loop (run : RunState) : ResultT String IO RunState := do {
    let p <- Agent.exec Loop.iterate run;
    ResultT.mk (return (Result.ok (run_of_pair p)))
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

/// The one line before every read, the dumb-mode twin of the TUI's
/// status bar: the `auto` warning (the trust setting must never pass
/// unremarked), the mode, the provider/model, the turn budget, and the
/// token spend from the session's own accounting.
def prompt_line (st : WeaverState) : String :=
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
        ++ "> "

/// `auto` mode is a trust setting, not a sandbox -- say so while it
/// is on.
def auto_warning (mode : Mode) : String :=
    if Mode.warns_auto mode then "WARNING: auto mode -- tools run unasked. " else ""

// ── helpers ─────────────────────────────────────────────────────────────

def mk_step (st : WeaverState) (again : Bool) : Step :=
    let s : Step := { state := st, again := again } in
    s
