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
///
/// Phase 9: a dispatch is `IO (Result WeaverError Effect)` -- a FAILED
/// command is the `Result.err`, not an output line that happens to
/// start with `save failed:`. The error carries no state, so the
/// caller's stands untouched (session intact); the caller classifies
/// it through `WeaverError.recoverable`.
use shuttle::provider {ProviderConfig}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session, Session.save, Session.load}
use shuttle::agent {RunState}
use shuttle::context {usage_zero}
use shuttle::tool {ToolSpec}
use weaver::policy {Mode, Mode.show, Mode.parse, Mode.approve_plan}
use weaver::gate {cap_name}
use weaver::providers {Weaver.preset}
use weaver::error {WeaverError}
use std::map {BTreeMap}
use std::list {List.intercalate}

/// Everything the interactive session carries between inputs.
/// `run` is shuttle's own state (session, registry, turn budget, gate,
/// always-cache) so the whole turn loop advances it; `budget` is the
/// TOTAL for the session (what `/resume` recomputes `turns_left`
/// against); `mcps` is the mounted `--mcp` servers' commands (what
/// `/mcp` lists); `keys` is the merged `[api_keys]` table (what
/// `/provider` re-resolves a swap's direct key from -- weaver.md Phase
/// 10); `quit` is the `/quit` flag the loop ends on; `fatal` is the
/// non-recoverable error that ended the run early, if one did
/// (`main` exits 1 when it is set).
pub struct WeaverState {
    run : RunState,
    mode : Mode,
    provider : String,
    budget : I64,
    mcps : List String,
    keys : BTreeMap String String,
    quit : Bool,
    fatal : Option WeaverError := Option.none,
}

/// One command's outcome: the advanced state and the line(s) to print.
/// The caller owns the printing -- a command talks only through this.
/// This is the SUCCESS shape only: a failure is the dispatch's
/// `Result.err` and never builds an `Effect`.
pub struct Effect {
    state : WeaverState,
    output : String,
}

/// One table entry -- a uniform signature, the Phase 7 rewiring point.
pub struct SlashCommand {
    run : String -> WeaverState -> IO (Result WeaverError Effect),
}

pub def Effect.ok (st : WeaverState) (output : String) : Effect :=
    let e : Effect := { state := st, output := output } in
    e

/// Every handler's success shape: the effect, wrapped in the typed
/// `Result` the dispatch contract speaks. (NOT `ok` -- the bare name
/// collides with the `Result.ok` constructor at evaluation time: the
/// checker resolves the local def, the evaluator does not, and every
/// call misapplies the constructor instead.)
def respond (st : WeaverState) (output : String) : IO (Result WeaverError Effect) :=
    IO.pure (Result.ok (Effect.ok st output))

/// The command table -- the whole `/`-surface, weaver.md Phase 6's
/// final shape.
pub def command_table : BTreeMap String SlashCommand :=
    Map.insert "/clear" (SlashCommand.mk cmd_clear)
        (Map.insert "/help" (SlashCommand.mk cmd_help)
        (Map.insert "/mcp" (SlashCommand.mk cmd_mcp)
        (Map.insert "/mode" (SlashCommand.mk cmd_mode)
        (Map.insert "/model" (SlashCommand.mk cmd_model)
        (Map.insert "/plan" (SlashCommand.mk cmd_plan)
        (Map.insert "/provider" (SlashCommand.mk cmd_provider)
        (Map.insert "/quit" (SlashCommand.mk cmd_quit)
        (Map.insert "/resume" (SlashCommand.mk cmd_resume)
        (Map.insert "/save" (SlashCommand.mk cmd_save)
        (Map.insert "/tools" (SlashCommand.mk cmd_tools)
            BTreeMap.empty))))))))))

/// Route one `/`-line: split at the first space, look the command up,
/// run it. Unknown names get `/help`'s hint, not silence.
pub def Commands.dispatch (line : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match split_command line {
        Pair.pair cmd arg =>
            match Map.lookup cmd command_table {
                Option.some c => dispatch_command c arg st,
                Option.none => unknown_effect cmd st,
            },
    }

/// Apply a table entry. The handler is bound out of the struct first:
/// `c.run arg st` at the call site would desugar the field access as a
/// receiver call (`SlashCommand.run c`) and misapply -- the same reason
/// `loop.mo` binds `run` out of `ToolImpl` before calling it.
def dispatch_command (c : SlashCommand) (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
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
def cmd_mode (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then respond st (String.concat "mode: " (Mode.show st.mode))
    else mode_of arg st

def mode_of (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match Mode.parse arg {
        Option.none =>
            respond st (String.concat "unknown mode: " (String.concat arg " (manual | plan | allow_edit | auto)")),
        Option.some m =>
            let st2 : WeaverState := set_mode st m in
            respond st2 (String.concat "mode: " (Mode.show m)),
    }

/// `/model` with no argument shows the current model; with a name, it
/// swaps the session config's model (the wire, key and host stay).
def cmd_model (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then respond st (String.concat "model: " st.run.session.config.model)
    else
        let st2 : WeaverState := set_model st arg in
        respond st2 (String.concat "model: " arg)

/// `/provider` with no argument shows the preset name; with one of the
/// five names, it swaps the whole config (wire, key and host with it)
/// and keeps the model name. Phase 10: the NEW provider's direct key
/// re-resolves from the merged `[api_keys]` table the state carries.
def cmd_provider (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then respond st (String.concat "provider: " st.provider)
    else provider_of arg st

/// An unknown provider name is a `config` error: the run's
/// configuration is wrong, not its files or its wire.
def provider_of (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match Weaver.preset arg st.run.session.config.model st.keys {
        Result.err e => IO.pure (Result.err (WeaverError.config e)),
        Result.ok cfg =>
            let st2 : WeaverState := set_config st cfg arg in
            respond st2 (String.concat "provider: " arg),
    }

/// `/tools`: every registered tool with its capability tag -- what the
/// gate will consult before each of them runs.
def cmd_tools (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    let lines : List String := List.map (tool_line st.run.reg) (ToolRegistry.specs st.run.reg) in
    respond st (String.concat "tools: " (List.intercalate ", " lines))

def tool_line (reg : ToolRegistry) (spec : ToolSpec) : String :=
    match ToolRegistry.lookup spec.name reg {
        Option.some impl => String.concat spec.name (String.concat " (" (String.concat (cap_name impl.cap) ")")),
        Option.none => spec.name,
    }

/// `/mcp`: the mounted `--mcp` servers, or the hint for mounting one.
def cmd_mcp (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    respond st (mcp_line st.mcps)

def mcp_line (mcps : List String) : String :=
    if strings_empty mcps
    then "mcp: none mounted (--mcp <executable>, repeatable)"
    else String.concat "mcp: " (List.intercalate ", " mcps)

def strings_empty (xs : List String) : Bool :=
    match xs { List.empty => true, _ => false }

/// `/plan` with no argument is the plan-mode status line; `/plan
/// approve [manual|allow_edit]` is the one CONSTRAINED mode transition
/// (policy.mo's `Mode.approve_plan`): plan mode ends at the mode the
/// approving user names, and any other mode has no plan to approve.
def cmd_plan (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then respond st (plan_status st.mode)
    else plan_arg arg st

def plan_status (m : Mode) : String :=
    match m {
        Mode.plan => "plan mode: only read tools run; produce the plan, then /plan approve [manual|allow_edit]",
        _ => String.concat "not in plan mode (mode: " (String.concat (Mode.show m) "); switch with /mode plan"),
    }

def plan_arg (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match split_command arg {
        Pair.pair word rest =>
            if word == "approve"
            then plan_approve (String.trim rest) st
            else respond st "usage: /plan | /plan approve [manual|allow_edit]",
    }

/// The approval itself: only `manual` and `allow_edit` are acceptable
/// landings -- `/plan approve auto` would be a one-word trust
/// escalation, and the gate's whole point is that it costs more than
/// that.
def plan_approve (target : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if Bool.not (is_landing target)
    then respond st "plan approval drops to manual or allow_edit"
    else approve_to (landing target) st

def is_landing (target : String) : Bool :=
    String.is_empty target || target == "manual" || target == "allow_edit"

def landing (target : String) : Mode :=
    match Mode.parse target {
        Option.some m => m,
        Option.none => Mode.manual,
    }

def approve_to (target : Mode) (st : WeaverState) : IO (Result WeaverError Effect) :=
    let st2 : WeaverState := set_mode st (Mode.approve_plan target st.mode) in
    if mode_eq st.mode Mode.plan
    then respond st2 (String.concat "plan approved -- mode: " (Mode.show target))
    else respond st2 (String.concat "no plan to approve -- mode: " (Mode.show st2.mode))

def mode_eq (a : Mode) (b : Mode) : Bool :=
    match a {
        Mode.manual => match b { Mode.manual => true, _ => false },
        Mode.plan => match b { Mode.plan => true, _ => false },
        Mode.allow_edit => match b { Mode.allow_edit => true, _ => false },
        Mode.auto => match b { Mode.auto => true, _ => false },
    }

/// `/save <file>`: checkpoint the session (shuttle's `Session.save`).
/// A write failure is an `io` error -- the file the user named could
/// not be written; the session stands.
def cmd_save (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then respond st "usage: /save <file>"
    else do {
        let r <- Session.save st.run.session arg;
        save_result arg st r
    }

def save_result (file : String) (st : WeaverState) (r : Result String Unit) : IO (Result WeaverError Effect) :=
    match r {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok _ => respond st (String.concat "saved " file),
    }

/// `/resume <file>`: continue a saved session. The turn budget SPANS
/// both halves (shuttle's own semantics): the remaining budget is the
/// total minus the turns the loaded session already took. A load
/// failure is an `io` error; the live session stands untouched.
def cmd_resume (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then respond st "usage: /resume <file>"
    else do {
        let r <- Session.load arg;
        resume_result arg st r
    }

def resume_result (file : String) (st : WeaverState) (r : Result String Session) : IO (Result WeaverError Effect) :=
    match r {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok s => resume_ok file st s,
    }

def resume_ok (file : String) (st : WeaverState) (s : Session) : IO (Result WeaverError Effect) :=
    let remaining : I64 := st.budget - s.turns in
    let st2 : WeaverState := set_session st s st.budget in
    if remaining < 1
    then respond st2 (String.concat "resumed " (String.concat file " -- the whole turn budget is already spent"))
    else respond st2 (String.concat "resumed " file)

/// `/clear`: drop the transcript and the accounting, keep the config
/// and the tools. The turn budget resets to the full amount.
def cmd_clear (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    let base : Session := st.run.session in
    let fresh : Session := { base with history := List.empty, turns := 0, spent := usage_zero } in
    let st2 : WeaverState := set_session st fresh st.budget in
    respond st2 "cleared"

/// `/quit`: the loop's exit flag. Disposal (MCP servers) is the
/// entry's job -- the command only says stop.
def cmd_quit (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    let st2 : WeaverState := set_quit st in
    respond st2 "bye"

/// `/help`: the whole table, one line per command.
def cmd_help (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    respond st help_text

def help_text : String :=
    List.intercalate "\n" [
        "/mode [manual|plan|allow_edit|auto]  show or set the approval mode",
        "/model [name]                        show or set the model",
        "/provider [ollama|mistral|openrouter|anthropic|mock]  show or set the provider",
        "/plan [approve manual|allow_edit]    plan-mode status; approve drops plan mode",
        "/tools                               list tools with their capability tags",
        "/mcp                                 list mounted MCP servers",
        "/save <file>                         checkpoint the session",
        "/resume <file>                       continue a saved session (budget spans both halves)",
        "/clear                               drop the transcript and reset the budget",
        "/help                                this table",
        "/quit                                exit (MCP servers are disposed)",
    ]

def unknown_effect (cmd : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    respond st (String.concat "unknown command: " (String.concat cmd " (try /help)"))

// ── WeaverState updates ──────────────────────────────────────────────────────
// Every update binds an annotated local (the bare `{ x with ... }` in an
// argument position is a checker hazard), and every nested update goes
// through its own def so no pattern is more than one constructor deep.

def set_mode (st : WeaverState) (m : Mode) : WeaverState :=
    let st2 : WeaverState := { st with mode := m } in
    st2

def set_quit (st : WeaverState) : WeaverState :=
    let st2 : WeaverState := { st with quit := true } in
    st2

/// Record the non-recoverable error that ended the run: the dumb loop
/// sets it, `main` reads it for the exit code.
def set_fatal (st : WeaverState) (e : WeaverError) : WeaverState :=
    let st2 : WeaverState := { st with fatal := Option.some e } in
    st2

def set_model (st : WeaverState) (model : String) : WeaverState :=
    let cfg2 : ProviderConfig := { (st.run.session.config) with model := model } in
    let s2 : Session := { (st.run.session) with config := cfg2 } in
    let run2 : RunState := { (st.run) with session := s2 } in
    let st2 : WeaverState := { st with run := run2 } in
    st2

def set_config (st : WeaverState) (cfg : ProviderConfig) (provider : String) : WeaverState :=
    let s2 : Session := { (st.run.session) with config := cfg } in
    let run2 : RunState := { (st.run) with session := s2 } in
    let st2 : WeaverState := { st with run := run2, provider := provider } in
    st2

/// Swap the whole session and recompute the remaining budget from the
/// total: `turns_left := max 0 (budget - session.turns)`.
def set_session (st : WeaverState) (s : Session) (budget : I64) : WeaverState :=
    let remaining : I64 := if budget - s.turns < 0 then 0 else budget - s.turns in
    let run2 : RunState := { (st.run) with session := s, turns_left := remaining } in
    let st2 : WeaverState := { st with run := run2 } in
    st2
