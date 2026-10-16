/// Weaver's slash-command table -- weaver.md Phase 3 (completed in
/// Phase 6): input starting with `/` routes here before it ever
/// reaches the model. Each command is a value in a `BTreeMap` keyed by
/// its name -- the same shape as shuttle's `ToolRegistry`, the
/// deliberate pre-Loom-`Strand` fallback (plugin-framework Phase 2
/// rewiring will be a diff, not a rewrite: same handler signature, one
/// mount site).
///
/// The interactive state lives here (not in `dumb.mo`) because the
/// commands are its only other writer: the dumb loop threads it,
/// commands change it. The session, registry, budget and always-cache
/// ride inside shuttle's `RunState` -- Elm state, there is no `IORef`
/// -- and Weaver's own knobs (mode, preset name, the total turn
/// budget) sit beside it.
use shuttle::provider {ProviderConfig}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session, Session.save, Session.load}
use shuttle::agent {RunState}
use shuttle::context {usage_zero}
use shuttle::tool {ToolSpec}
use weaver::policy {Mode, Mode.show, Mode.parse}
use weaver::gate {cap_name}
use weaver::providers {Weaver.preset}
use std::map {BTreeMap}
use std::list {List.intercalate}

/// Everything the interactive session carries between inputs.
/// `run` is shuttle's own state (session, registry, turn budget, gate,
/// always-cache) so the whole turn loop advances it; `budget` is the
/// TOTAL for the session (what `/resume` recomputes `turns_left`
/// against); `quit` is the `/quit` flag the loop ends on.
pub struct State {
    run : RunState,
    mode : Mode,
    provider : String,
    budget : I64,
    quit : Bool,
}

/// One command's outcome: the advanced state and the line(s) to print.
/// The caller owns the printing -- a command talks only through this.
pub struct Effect {
    state : State,
    output : String,
}

/// One table entry -- a uniform signature, the Phase 7 rewiring point.
pub struct Command {
    run : String -> State -> IO Effect,
}

pub def Effect.ok (st : State) (output : String) : Effect :=
    let e : Effect := { state := st, output := output } in
    e

/// The command table. `/mcp` and `/plan` join in Phase 6 (settings
/// and mounts), not yet.
pub def command_table : BTreeMap String Command :=
    Map.insert "/clear" (Command.mk cmd_clear)
        (Map.insert "/help" (Command.mk cmd_help)
        (Map.insert "/mode" (Command.mk cmd_mode)
        (Map.insert "/model" (Command.mk cmd_model)
        (Map.insert "/provider" (Command.mk cmd_provider)
        (Map.insert "/quit" (Command.mk cmd_quit)
        (Map.insert "/resume" (Command.mk cmd_resume)
        (Map.insert "/save" (Command.mk cmd_save)
        (Map.insert "/tools" (Command.mk cmd_tools)
            BTreeMap.empty))))))))

/// Route one `/`-line: split at the first space, look the command up,
/// run it. Unknown names get `/help`'s hint, not silence.
pub def Commands.dispatch (line : String) (st : State) : IO Effect :=
    match split_command line {
        Pair.pair cmd arg =>
            match Map.lookup cmd command_table {
                Option.some c => dispatch_command c arg st,
                Option.none => unknown_effect cmd st,
            },
    }

/// Apply a table entry. The handler is bound out of the struct first:
/// `c.run arg st` at the call site would desugar the field access as a
/// receiver call (`Command.run c`) and misapply -- the same reason
/// `loop.mo` binds `run` out of `ToolImpl` before calling it.
def dispatch_command (c : Command) (arg : String) (st : State) : IO Effect :=
    match c {
        { run, .. } => run arg st
    }

/// `"/mode plan"` -> `("/mode", "plan")`: the command word keeps its
/// leading `/`, the argument is trimmed, and either half may be empty.
def split_command (line : String) : Pair String String :=
    match first_space line 0 {
        Result.err _ => Pair.pair line "",
        Result.ok sp => Pair.pair (String.slice line 0 sp) (String.trim (String.drop (sp + 1) line)),
    }

/// The index of the first space in `s` at or after `i`, or `err` when
/// there is none. `#[terminating]`: `i` counts up to the length.
#[terminating]
def first_space (s : String) (i : I64) : Result String I64 :=
    if String.length s < i + 1
    then Result.err "no space"
    else if String.slice s i 1 == " "
    then Result.ok i
    else first_space s (i + 1)

// ── The commands ───────────────────────────────────────────────────────

/// `/mode` with no argument shows; with one of the four names, sets.
/// The gate is rebuilt by the dumb loop from the mode before every
/// turn, so a mode change takes effect on the very next model call.
def cmd_mode (arg : String) (st : State) : IO Effect :=
    if String.is_empty arg
    then IO.pure (Effect.ok st (String.concat "mode: " (Mode.show st.mode)))
    else mode_of arg st

def mode_of (arg : String) (st : State) : IO Effect :=
    match Mode.parse arg {
        Option.none =>
            IO.pure (Effect.ok st (String.concat "unknown mode: " (String.concat arg " (manual | plan | allow_edit | auto)"))),
        Option.some m =>
            let st2 : State := set_mode st m in
            IO.pure (Effect.ok st2 (String.concat "mode: " (Mode.show m))),
    }

/// `/model` with no argument shows the current model; with a name, it
/// swaps the session config's model (the wire, key and host stay).
def cmd_model (arg : String) (st : State) : IO Effect :=
    if String.is_empty arg
    then IO.pure (Effect.ok st (String.concat "model: " st.run.session.config.model))
    else
        let st2 : State := set_model st arg in
        IO.pure (Effect.ok st2 (String.concat "model: " arg))

/// `/provider` with no argument shows the preset name; with one of the
/// five names, it swaps the whole config (wire, key and host with it)
/// and keeps the model name.
def cmd_provider (arg : String) (st : State) : IO Effect :=
    if String.is_empty arg
    then IO.pure (Effect.ok st (String.concat "provider: " st.provider))
    else provider_of arg st

def provider_of (arg : String) (st : State) : IO Effect :=
    match Weaver.preset arg st.run.session.config.model {
        Result.err e => IO.pure (Effect.ok st e),
        Result.ok cfg =>
            let st2 : State := set_config st cfg arg in
            IO.pure (Effect.ok st2 (String.concat "provider: " arg)),
    }

/// `/tools`: every registered tool with its capability tag -- what the
/// gate will consult before each of them runs.
def cmd_tools (arg : String) (st : State) : IO Effect :=
    let lines : List String := List.map (tool_line st.run.reg) (ToolRegistry.specs st.run.reg) in
    IO.pure (Effect.ok st (String.concat "tools: " (List.intercalate ", " lines)))

def tool_line (reg : ToolRegistry) (spec : ToolSpec) : String :=
    match ToolRegistry.lookup spec.name reg {
        Option.some impl => String.concat spec.name (String.concat " (" (String.concat (cap_name impl.cap) ")")),
        Option.none => spec.name,
    }

/// `/save <file>`: checkpoint the session (shuttle's `Session.save`).
def cmd_save (arg : String) (st : State) : IO Effect :=
    if String.is_empty arg
    then IO.pure (Effect.ok st "usage: /save <file>")
    else do {
        let r <- Session.save st.run.session arg;
        save_result arg st r
    }

def save_result (file : String) (st : State) (r : Result String Unit) : IO Effect :=
    match r {
        Result.err e => IO.pure (Effect.ok st (String.concat "save failed: " e)),
        Result.ok _ => IO.pure (Effect.ok st (String.concat "saved " file)),
    }

/// `/resume <file>`: continue a saved session. The turn budget SPANS
/// both halves (shuttle's own semantics): the remaining budget is the
/// total minus the turns the loaded session already took.
def cmd_resume (arg : String) (st : State) : IO Effect :=
    if String.is_empty arg
    then IO.pure (Effect.ok st "usage: /resume <file>")
    else do {
        let r <- Session.load arg;
        resume_result arg st r
    }

def resume_result (file : String) (st : State) (r : Result String Session) : IO Effect :=
    match r {
        Result.err e => IO.pure (Effect.ok st (String.concat "resume failed: " e)),
        Result.ok s => resume_ok file st s,
    }

def resume_ok (file : String) (st : State) (s : Session) : IO Effect :=
    let remaining : I64 := st.budget - s.turns in
    let st2 : State := set_session st s remaining in
    if remaining < 1
    then IO.pure (Effect.ok st2 (String.concat "resumed " (String.concat file " -- the whole turn budget is already spent")))
    else IO.pure (Effect.ok st2 (String.concat "resumed " file))

/// `/clear`: drop the transcript and the accounting, keep the config
/// and the tools. The turn budget resets to the full amount.
def cmd_clear (arg : String) (st : State) : IO Effect :=
    let base : Session := st.run.session in
    let fresh : Session := { base with history := List.empty, turns := 0, spent := usage_zero } in
    let st2 : State := set_session st fresh st.budget in
    IO.pure (Effect.ok st2 "cleared")

/// `/quit`: the loop's exit flag. Disposal (MCP servers) is the
/// entry's job -- the command only says stop.
def cmd_quit (arg : String) (st : State) : IO Effect :=
    let st2 : State := set_quit st in
    IO.pure (Effect.ok st2 "bye")

/// `/help`: the whole table, one line per command.
def cmd_help (arg : String) (st : State) : IO Effect :=
    IO.pure (Effect.ok st help_text)

def help_text : String :=
    List.intercalate "\n" [
        "/mode [manual|plan|allow_edit|auto]  show or set the approval mode",
        "/model [name]                        show or set the model",
        "/provider [ollama|mistral|openrouter|anthropic|mock]  show or set the provider",
        "/tools                               list tools with their capability tags",
        "/save <file>                         checkpoint the session",
        "/resume <file>                       continue a saved session (budget spans both halves)",
        "/clear                               drop the transcript and reset the budget",
        "/help                                this table",
        "/quit                                exit (MCP servers are disposed)",
    ]

def unknown_effect (cmd : String) (st : State) : IO Effect :=
    IO.pure (Effect.ok st (String.concat "unknown command: " (String.concat cmd " (try /help)")))

// ── State updates ──────────────────────────────────────────────────────
// Every update binds an annotated local (the bare `{ x with ... }` in an
// argument position is a checker hazard), and every nested update goes
// through its own def so no pattern is more than one constructor deep.

def set_mode (st : State) (m : Mode) : State :=
    let st2 : State := { st with mode := m } in
    st2

def set_quit (st : State) : State :=
    let st2 : State := { st with quit := true } in
    st2

def set_model (st : State) (model : String) : State :=
    let cfg2 : ProviderConfig := { (st.run.session.config) with model := model } in
    let s2 : Session := { (st.run.session) with config := cfg2 } in
    let run2 : RunState := { (st.run) with session := s2 } in
    let st2 : State := { st with run := run2 } in
    st2

def set_config (st : State) (cfg : ProviderConfig) (provider : String) : State :=
    let s2 : Session := { (st.run.session) with config := cfg } in
    let run2 : RunState := { (st.run) with session := s2 } in
    let st2 : State := { st with run := run2, provider := provider } in
    st2

/// Swap the whole session and recompute the remaining budget from the
/// total: `turns_left := max 0 (budget - session.turns)`.
def set_session (st : State) (s : Session) (budget : I64) : State :=
    let remaining : I64 := if budget - s.turns < 0 then 0 else budget - s.turns in
    let run2 : RunState := { (st.run) with session := s, turns_left := remaining } in
    let st2 : State := { st with run := run2 } in
    st2
