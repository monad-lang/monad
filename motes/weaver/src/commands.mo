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
use weaver::providers {Weaver.preset, Weaver.model_error, Weaver.repair_session_model}
use weaver::error {WeaverError}
use weaver::store {
    StoreState, Store.new_session, Store.latest_session, Store.load_session,
    Store.import_session, Store.session_dir, Store.base_name,
}
use std::path {Path, Path.of, Path.parent}
use std::io {IO.is_dir}
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
    /// The dumb UI's palette switch: `NO_COLOR` (or a future --no-color)
    /// turns it off; the TUI always colors its own screen. Spell it at
    /// every WeaverState literal -- an omitted non-defaulted field has
    /// been seen to check clean and fill garbage at runtime.
    colors : Bool := true,
    /// The active session directory, when persistence is available; none
    /// degrades to the pre-store in-memory behaviour.
    store : Option StoreState,
}

/// What a command did to the transcript: ordinary output appends,
/// `/clear` and `/resume` replace the window with another session's.
pub type TranscriptChange {
    keep,
    reset,
}

/// One command's outcome: the advanced state, the line(s) to print, and
/// whether the transcript window is replaced. The caller owns the
/// printing -- a command talks only through this. This is the SUCCESS
/// shape only: a failure is the dispatch's `Result.err`.
pub struct Effect {
    state : WeaverState,
    output : String,
    transcript : TranscriptChange,
}

/// One table entry -- a uniform signature, the Phase 7 rewiring point.
pub struct SlashCommand {
    run : String -> WeaverState -> IO (Result WeaverError Effect),
}

pub def Effect.ok (st : WeaverState) (output : String) : Effect :=
    let e : Effect := { state := st, output := output, transcript := TranscriptChange.keep } in
    e

/// A command that switched sessions: the caller loads the new window.
pub def Effect.reset (st : WeaverState) (output : String) : Effect :=
    let e : Effect := { state := st, output := output, transcript := TranscriptChange.reset } in
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
        (Map.insert "/h" (SlashCommand.mk cmd_help)
        (Map.insert "/help" (SlashCommand.mk cmd_help)
        (Map.insert "/mcp" (SlashCommand.mk cmd_mcp)
        (Map.insert "/mode" (SlashCommand.mk cmd_mode)
        (Map.insert "/model" (SlashCommand.mk cmd_model)
        (Map.insert "/plan" (SlashCommand.mk cmd_plan)
        (Map.insert "/provider" (SlashCommand.mk cmd_provider)
        (Map.insert "/q" (SlashCommand.mk cmd_quit)
        (Map.insert "/quit" (SlashCommand.mk cmd_quit)
        (Map.insert "/resume" (SlashCommand.mk cmd_resume)
        (Map.insert "/save" (SlashCommand.mk cmd_save)
        (Map.insert "/tools" (SlashCommand.mk cmd_tools)
            BTreeMap.empty))))))))))))

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
    else match Weaver.model_error st.provider arg {
        Option.some e => respond st (String.concat "model unchanged: " e),
        Option.none =>
            let st2 : WeaverState := set_model st arg in
            respond st2 (String.concat "model: " arg),
    }

/// `/provider [name] [model]`: with no argument shows the preset name;
/// with a name it swaps the whole config (wire, key and host with it) and
/// uses that provider's DEFAULT model unless the second word names one --
/// the old provider's model is never carried across. Phase 10: the NEW
/// provider's direct key re-resolves from the merged `[api_keys]` table.
def cmd_provider (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then respond st (String.concat "provider: " st.provider)
    else provider_of arg st

/// An unknown provider name stays a session-local refusal (command
/// output, state untouched): an argument typo must not kill an
/// otherwise healthy interactive session -- that is what a config
/// error's fatal classification would do. The STARTUP path keeps its
/// own fatal shape for the same misspelling. A model that the new
/// provider does not serve is refused the same way.
def provider_of (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match split_command arg {
        Pair.pair name model =>
            match Weaver.preset name model st.keys {
                Result.err e => respond st e,
                Result.ok cfg => match Weaver.model_error name cfg.model {
                    Option.some e => respond st (String.concat "provider unchanged: " e),
                    Option.none =>
                        let st2 : WeaverState := set_config st cfg name in
                        respond st2 (String.concat "provider: " (String.concat name (String.concat " (model " (String.concat cfg.model ")")))),
                },
            },
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

/// `/resume [<id|file>]`: continue a saved session. No argument picks
/// the newest session (`meta.updated`). A directory or a session id
/// under the root opens that directory in place; anything else is a
/// shuttle checkpoint file, imported into a fresh directory. The turn
/// budget SPANS both halves (the remaining budget is the total minus
/// the turns the loaded session already took).
def cmd_resume (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then resume_latest st
    else match Path.of arg {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok p => resume_path st p arg,
    }

def resume_latest (st : WeaverState) : IO (Result WeaverError Effect) :=
    match st.store {
        Option.none => respond st "session persistence unavailable (HOME unset or ~/.weaver/sessions unwritable)",
        Option.some s => resume_latest_store st s,
    }

def resume_latest_store (st : WeaverState) (s : StoreState) : IO (Result WeaverError Effect) := do {
    let l <- Store.latest_session s.root;
    match l {
        Option.none => respond st "no saved sessions",
        Option.some id => resume_dir st (Store.session_dir s.root id) id,
    }
}

def resume_path (st : WeaverState) (p : Path) (label : String) : IO (Result WeaverError Effect) := do {
    let isd <- IO.is_dir p;
    if isd then resume_dir st p label else resume_by_id st label;
}

def resume_by_id (st : WeaverState) (label : String) : IO (Result WeaverError Effect) :=
    match st.store {
        Option.none => resume_file st label,
        Option.some s => resume_by_id_store st s label,
    }

def resume_by_id_store (st : WeaverState) (s : StoreState) (label : String) : IO (Result WeaverError Effect) := do {
    let cand : Path := Store.session_dir s.root label;
    let isd <- IO.is_dir cand;
    if isd then resume_dir st cand label else resume_file st label;
}

def resume_dir (st : WeaverState) (p : Path) (label : String) : IO (Result WeaverError Effect) := do {
    let r <- Store.load_session p;
    match r {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok s => IO.pure (Result.ok (resume_effect st s (store_for_dir p st) label)),
    }
}

def resume_file (st : WeaverState) (label : String) : IO (Result WeaverError Effect) := do {
    let r <- Session.load label;
    match r {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok s => resume_import st s label,
    }
}

def resume_import (st : WeaverState) (s : Session) (label : String) : IO (Result WeaverError Effect) :=
    match st.store {
        Option.none => IO.pure (Result.ok (resume_effect st s Option.none label)),
        Option.some old => resume_import_into st s old label,
    }

def resume_import_into (st : WeaverState) (s : Session) (old : StoreState) (label : String) : IO (Result WeaverError Effect) := do {
    let r <- Store.import_session old.root s;
    match r {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok ns => IO.pure (Result.ok (resume_effect st s (Option.some ns) label)),
    }
}

/// The budget spans halves and the resumed config re-resolves the
/// CURRENT provider's direct key (a checkpoint never carries one).
def resume_effect (st : WeaverState) (s : Session) (store : Option StoreState) (label : String) : Effect :=
    match Weaver.repair_session_model st.provider s {
        Pair.pair fixed note =>
            let keyed : Session := rekey_session st fixed in
            let st2 : WeaverState := set_session st keyed st.budget in
            let st3 : WeaverState := set_store st2 store in
            let base : String := String.concat "resumed " label in
            let out : String := match note {
                Option.none => base,
                Option.some n => String.concat base (String.concat " -- warning: " n),
            } in
            if st.budget - s.turns < 1
            then Effect.reset st3 (String.concat out " -- the whole turn budget is already spent")
            else Effect.reset st3 out,
    }

def rekey_session (st : WeaverState) (s : Session) : Session :=
    let s2 : Session := { s with config := rekey_config st s.config } in
    s2

/// The store for a directory opened in place: keep the CURRENT root so
/// `/clear` afterwards creates a sibling where `--resume` would, and
/// fall back to the directory's parent when no store is open.
def store_for_dir (p : Path) (st : WeaverState) : Option StoreState :=
    match st.store {
        Option.some cur => Option.some (store_at_root cur.root p),
        Option.none => store_at_parent p,
    }

def store_at_root (root : Path) (dir : Path) : StoreState :=
    let s : StoreState := { root := root, dir := dir, id := Store.base_name dir } in
    s

def store_at_parent (p : Path) : Option StoreState :=
    match Path.parent p {
        Option.none => Option.none,
        Option.some root => Option.some (store_at_root root p),
    }

/// The redaction contract's other half: a save file carries only
/// `api_key_env` (the direct key must never cross a `/save`), so the
/// resumed config re-resolves the CURRENT provider's direct key from
/// the merged `[api_keys]` table (the state's `keys`), env-second as
/// everywhere else.
def rekey_config (st : WeaverState) (cfg : ProviderConfig) : ProviderConfig :=
    { cfg with api_key := Map.lookup st.provider st.keys }

/// `/clear`: drop the transcript and the accounting, keep the config
/// and the tools. The turn budget resets to the full amount. With a
/// store, a NEW session directory starts and the old one stays
/// resumable.
def cmd_clear (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    let base : Session := st.run.session in
    let fresh : Session := clear_session base in
    let st2 : WeaverState := set_session st fresh st.budget in
    match st.store {
        Option.none => IO.pure (Result.ok (Effect.reset st2 "cleared")),
        Option.some s => clear_with_store st2 s fresh,
    }

def clear_session (s : Session) : Session :=
    let s2 : Session := { s with history := List.empty, turns := 0, spent := usage_zero } in
    s2

def clear_with_store (st : WeaverState) (s : StoreState) (fresh : Session) : IO (Result WeaverError Effect) := do {
    let r <- Store.new_session s.root fresh;
    match r {
        Result.err e => IO.pure (Result.ok (Effect.reset (set_store st Option.none) (String.concat "cleared (persistence disabled: " (String.concat e ")")))),
        Result.ok ns => IO.pure (Result.ok (Effect.reset (set_store st (Option.some ns)) "cleared")),
    }
}

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
        "/provider [ollama|mistral|openrouter|anthropic|mock] [model]  show or set the provider",
        "/plan [approve manual|allow_edit]    plan-mode status; approve drops plan mode",
        "/tools                               list tools with their capability tags",
        "/mcp                                 list mounted MCP servers",
        "/save <file>                         checkpoint the session as a JSON file",
        "/resume [<id|file>]                  continue a session (newest by default)",
        "/clear                               start a new session and reset the budget",
        "/help (or /h)                        this table",
        "/quit (or /q)                        exit (MCP servers are disposed)",
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
def set_store (st : WeaverState) (s : Option StoreState) : WeaverState :=
    let st2 : WeaverState := { st with store := s } in
    st2

def set_session (st : WeaverState) (s : Session) (budget : I64) : WeaverState :=
    let remaining : I64 := if budget - s.turns < 0 then 0 else budget - s.turns in
    // A session switch clears the `always` cache: the approval is
    // per-session by definition, and `/clear`/`/resume` start a new one.
    let run2 : RunState := { (st.run) with session := s, turns_left := remaining, always := List.empty } in
    let st2 : WeaverState := { st with run := run2 } in
    st2
