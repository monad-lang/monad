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
use shuttle::message {Message, Usage}
use weaver::usage {Usage.delta}
use shuttle::message_types {Role, Content}
use shuttle::agent {RunState}
use shuttle::context {usage_zero}
use shuttle::tool {ToolSpec}
use shuttle::gate {Capability}
use weaver::policy {Mode, Mode.show, Mode.parse, Mode.approve_plan}
use weaver::gate {cap_name}
use weaver::providers {Weaver.preset, Weaver.config_for, Weaver.preferred_model, Weaver.model_for, Weaver.provider_of}
use weaver::catalog {Catalog.fetch, Catalog.lookup, Catalog.remember, Catalog.render, Catalog.note}
use weaver::compact {Compact.threshold, Compact.should_compact, Compact.estimate, Compact.compact, Compact.Outcome}
use weaver::error {WeaverError, WeaverError.of_shuttle}
use weaver::store {
    StoreState, Store.new_session, Store.latest_session, Store.load_session,
    Store.import_session, Store.session_dir, Store.base_name, Store.record_compacted,
    Store.read_plan, Store.write_plan,
    SessionInfo, TitleField, StoreMeta, Store.list_sessions, Store.read_meta, Store.write_title,
    Store.derive_name, Store.derive_description,
}
use std::path {Path, Path.of, Path.parent, Path.to_string}
use std::io {IO.is_dir, IO.current_time_nano}
use std::map {Map, BTreeMap}
use std::list {List.intercalate}
use std::ref {Ref}
use parsec::number {parse_i64}
use weaver::permissions {
    PermGrant, PermScope, Permissions.get, Permissions.add, Permissions.revoke,
    Permissions.revoke_cap, Permissions.clear, PermGrant.describe, Permissions.render,
}
use weaver::settings {SettingsUpdate, Settings.save}
use weaver::procs {ProcEntry, ProcEntry.line, Procs.list, Procs.kill}
use weaver::logs {Logs.latest_path, Logs.tail, Logs.detect_crash}

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
    /// Autocompact's estimate: `context_window * compact_at / 100`
    /// estimated tokens; a zero window disables it.
    context_window : I64,
    compact_at : I64,
    /// The last plan-mode assistant text (`/plan`'s display, persisted
    /// in the session store's meta).
    plan : Option String := Option.none,
    /// The real prompt size of the last model call -- `Usage.input_tokens`
    /// of that request, cached tokens included. The status line and
    /// autocompact prefer it over the byte estimate.
    last_context : I64 := 0,
    /// Session approval grants: weaver owns them (shuttle's per-capability
    /// `always` cache stays empty), so `/permissions` can inspect and
    /// clear them. None in tests/headless states.
    grants : Option (Ref (List PermGrant)) := Option.none,
    /// The directory a `repo` grant is scoped to (`PWD` at startup).
    /// Lexical scope, not a sandbox.
    workspace_root : Option String := Option.none,
    mcps : List String,
    keys : BTreeMap String String,
    /// The last model list fetched per provider (`/model` with
    /// no argument, a `/provider` choice). The API is the authority; this
    /// is only the session's cache of its answer.
    catalog : BTreeMap String (List String),
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
    /// A model list the TUI should show as a picker (none in dumb mode,
    /// which prints `output` instead).
    picker : Option (List String) := Option.none,
}

/// One table entry -- a uniform signature, the Phase 7 rewiring point.
pub struct SlashCommand {
    run : String -> WeaverState -> IO (Result WeaverError Effect),
}

pub def Effect.ok (st : WeaverState) (output : String) : Effect :=
    let e : Effect := { state := st, output := output, transcript := TranscriptChange.keep, picker := Option.none } in
    e

/// A command that switched sessions: the caller loads the new window.
pub def Effect.reset (st : WeaverState) (output : String) : Effect :=
    let e : Effect := { state := st, output := output, transcript := TranscriptChange.reset, picker := Option.none } in
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
    Map.insert "/budget" (SlashCommand.mk cmd_budget)
        (Map.insert "/clear" (SlashCommand.mk cmd_clear)
        (Map.insert "/compact" (SlashCommand.mk cmd_compact)
        (Map.insert "/h" (SlashCommand.mk cmd_help)
        (Map.insert "/help" (SlashCommand.mk cmd_help)
        (Map.insert "/mcp" (SlashCommand.mk cmd_mcp)
        (Map.insert "/mode" (SlashCommand.mk cmd_mode)
        (Map.insert "/model" (SlashCommand.mk cmd_model)
        (Map.insert "/name" (SlashCommand.mk cmd_name)
        (Map.insert "/describe" (SlashCommand.mk cmd_describe)
        (Map.insert "/permissions" (SlashCommand.mk cmd_permissions)
        (Map.insert "/settings" (SlashCommand.mk cmd_settings)
        (Map.insert "/plan" (SlashCommand.mk cmd_plan)
        (Map.insert "/provider" (SlashCommand.mk cmd_provider)
        (Map.insert "/q" (SlashCommand.mk cmd_quit)
        (Map.insert "/quit" (SlashCommand.mk cmd_quit)
        (Map.insert "/resume" (SlashCommand.mk cmd_resume)
        (Map.insert "/save" (SlashCommand.mk cmd_save)
        (Map.insert "/log" (SlashCommand.mk cmd_log)
        (Map.insert "/processes" (SlashCommand.mk cmd_processes)
        (Map.insert "/procs" (SlashCommand.mk cmd_processes)
        (Map.insert "/thinking" (SlashCommand.mk cmd_thinking)
        (Map.insert "/tools" (SlashCommand.mk cmd_tools)
            BTreeMap.empty))))))))))))))))))))))

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

/// `/budget [n]` -- the session's total MODEL-CALL budget. A turn is
/// one model call, so a tool-using turn spends several; the total spans
/// a save/resume. Raising it mid-session is the way out of a spent
/// budget without `/clear` losing the conversation.
def cmd_budget (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then respond st (budget_line st)
    else match parse_i64 arg {
        Option.none => respond st (String.concat "budget: "
            (String.concat arg " is not a number (usage: /budget <n>)")),
        Option.some n =>
            let used : I64 := st.run.session.turns in
            if n < used
            then
                let used_text : String := I64.to_string used in
                let msg : String := String.concat "budget: "
                    (String.concat arg (String.concat " is below the "
                        (String.concat used_text " turns already spent"))) in
                respond st msg
            else
                let st2 : WeaverState := set_budget st n in
                respond st2 (budget_line st2),
    }

// ── Plan capture ───────────────────────────────────────────────────────
// `/plan` shows the plan-mode turn's text even after the mode dropped, so
// the text is captured when the turn lands instead of re-derived later.

#[partial]
def content_text (cs : List Content) (acc : String) : String :=
    match cs {
        List.empty => acc,
        List.cons c rest =>
            match c {
                Content.text s => content_text rest (String.concat acc s),
                _ => content_text rest acc,
            },
    }

def assistant_text (m : Message) : Option String :=
    match m.role {
        Role.assistant =>
            let t : String := String.trim (content_text m.content "") in
            if String.is_empty t then Option.none else Option.some t,
        _ => Option.none,
    }

#[partial]
def last_assistant_go (ms : List Message) : Option String :=
    match ms {
        List.empty => Option.none,
        List.cons m rest =>
            match last_assistant_go rest {
                Option.some t => Option.some t,
                Option.none => assistant_text m,
            },
    }

/// The last non-empty assistant text in a history (the plan a plan-mode
/// turn produced).
pub def Commands.last_assistant_text (history : List Message) : Option String :=
    last_assistant_go history

pub def Commands.set_plan (st : WeaverState) (p : Option String) : WeaverState :=
    let st2 : WeaverState := { st with plan := p } in
    st2

/// The messages appended after the first `before` entries (the turn's
/// own delta).
#[partial]
def turn_delta (before : I64) (ms : List Message) : List Message :=
    if before < 1 then ms
    else match ms {
        List.empty => List.empty,
        List.cons _ rest => turn_delta (before - 1) rest,
    }

/// The assistant text a plan-mode turn produced, if any. Only the turn's
/// own delta is scanned: a turn that ends without assistant text (a
/// tool-only turn at the cap, or a stopped one) must not capture an
/// earlier turn's message as "the plan". The mode is read from the
/// PRE-turn state (a turn cannot change it).
pub def Commands.plan_after_turn (st : WeaverState) (before : I64) (r : Result WeaverError RunState) : Option String :=
    match st.mode {
        Mode.plan => match r {
            Result.err _ => Option.none,
            Result.ok run2 => Commands.last_assistant_text (turn_delta before run2.session.history),
        },
        _ => Option.none,
    }

/// The turn's LAST model call's prompt size -- the number the next
/// request's size is judged by. The turn's summed delta is only a
/// fallback: a tool-using turn re-sends the whole prompt per call, so the
/// sum overstates the context several-fold and made autocompact fire (and
/// the status bar read) far too early.
pub def Commands.turn_context (spent_before : Usage) (last : Usage) (run2 : RunState) : I64 :=
    let d : Usage := Usage.delta run2.session.spent spent_before in
    if last.input_tokens < 1 then d.input_tokens else last.input_tokens

/// The next request's likely prompt size: the larger of the byte
/// heuristic and the real size of the last model call. The heuristic
/// sees tool schemas the per-message estimate misses; the real number
/// catches a provider whose tokenizer differs from bytes/4.
pub def Commands.context_used (st : WeaverState) : I64 :=
    let est : I64 := Compact.estimate st.run.session in
    if I64.gt st.last_context est then st.last_context else est

pub def Commands.context_percent (st : WeaverState) : I64 :=
    let window : I64 := st.context_window in
    if I64.lt window 1 then 0 else (Commands.context_used st) * 100 / window

/// `budget: 7/100 turns used (93 left)` -- used/total/left in one line,
/// so the status bar and `/budget` agree.
def budget_line (st : WeaverState) : String :=
    String.concat "budget: "
        (String.concat (I64.to_string st.run.session.turns)
            (String.concat "/"
                (String.concat (I64.to_string st.budget)
                    (String.concat " turns used ("
                        (String.concat (I64.to_string st.run.turns_left) " left)")))))

/// `/model` with no argument lists what the provider serves (and opens
/// the TUI picker); with a name, it swaps the session config's model
/// (the wire, key and host stay) and notes when the cached list lacks
/// it.
def cmd_model (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then show_models st
    else match Catalog.lookup st.provider st.catalog {
        Option.none => respond (Commands.set_model st arg) (String.concat "model: " arg),
        Option.some models => match Catalog.note st.provider models arg {
            Option.none => respond (Commands.set_model st arg) (String.concat "model: " arg),
            Option.some note => respond (Commands.set_model st arg)
                (String.concat "model: " (String.concat arg (String.concat "\n" note))),
        },
    }

/// The cached list when there is one, else one fetch; a provider that
/// cannot be reached still leaves `/model` usable (the current name is
/// shown with the reason the list is missing).
def show_models (st : WeaverState) : IO (Result WeaverError Effect) :=
    match Catalog.lookup st.provider st.catalog {
        Option.some models => IO.pure (Result.ok (models_effect st st.provider models)),
        Option.none => do {
            let fresh <- Catalog.fetch st.run.session.config;
            match fresh {
                Result.err e => respond st (String.concat "model: "
                    (String.concat st.run.session.config.model
                        (String.concat "\nmodel list unavailable: " e))),
                Result.ok models => IO.pure (Result.ok (models_effect st st.provider models)),
            }
        },
    }

/// Cache the fetched list and shape the output/picker.
def models_effect (st : WeaverState) (provider : String) (models : List String) : Effect :=
    let cat : BTreeMap String (List String) := Catalog.remember provider models st.catalog in
    let st2 : WeaverState := { st with catalog := cat } in
    let out : String := Catalog.render provider models st2.run.session.config.model in
    let pick : Option (List String) := if catalog_empty models then Option.none else Option.some models in
    let e : Effect := { state := st2, output := out, transcript := TranscriptChange.keep, picker := pick } in
    e

def catalog_empty (models : List String) : Bool :=
    match models {
        List.empty => true,
        List.cons _ _ => false,
    }

/// `/provider [name] [model]`: with no argument shows the preset name;
/// with a name it swaps the whole config (wire, key and host with it).
/// An explicit model is used as given; without one the provider's
/// fetched list chooses (or, offline, its preferred name does). Phase
/// 10: the NEW provider's direct key re-resolves from the merged
/// `[api_keys]` table.
def cmd_provider (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then respond st (String.concat "provider: " st.provider)
    else provider_of arg st

/// An unknown provider name stays a session-local refusal (command
/// output, state untouched): an argument typo must not kill an
/// otherwise healthy interactive session -- that is what a config
/// error's fatal classification would do.
def provider_of (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match split_command arg {
        Pair.pair name model =>
            if Bool.not (String.is_empty model)
            then explicit_model name model st
            else provider_no_model name st
    }

/// An explicit model is used exactly as given: no fetch, no name check.
def explicit_model (name : String) (model : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match Weaver.config_for name model st.keys {
        Result.err e => respond st e,
        Result.ok cfg => respond (set_config st (inherit_thinking st cfg) name) (provider_output name cfg),
    }

/// No model argument: a cached list chooses; without one the preferred
/// name keeps the switch offline, and only a provider with no preference
/// at all (openrouter) asks the API.
def provider_no_model (name : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match Catalog.lookup name st.catalog {
        Option.some models => match Weaver.model_for name models {
            Result.err e => respond st e,
            Result.ok chosen => provider_with name chosen models st,
        },
        Option.none => match Weaver.preferred_model name {
            Result.ok p => match Weaver.config_for name p st.keys {
                Result.err e => respond st e,
                Result.ok cfg => respond (set_config st (inherit_thinking st cfg) name) (provider_output name cfg),
            },
            Result.err _ => provider_fetch name st,
        },
    }

/// Fetch the target provider's list, choose from it, and cache it. A
/// failure refuses the switch rather than guessing a vendor-qualified
/// name.
def provider_fetch (name : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match Weaver.config_for name "" st.keys {
        Result.err e => respond st e,
        Result.ok base_cfg => do {
            let fresh <- Catalog.fetch base_cfg;
            match fresh {
                Result.err e => respond st (String.concat "provider unchanged: " e),
                Result.ok models => match Weaver.model_for name models {
                    Result.err e => respond st e,
                    Result.ok chosen => provider_with name chosen models st,
                },
            }
        },
    }

def provider_with (name : String) (chosen : String) (models : List String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match Weaver.config_for name chosen st.keys {
        Result.err e => respond st e,
        Result.ok cfg =>
            let cat : BTreeMap String (List String) := Catalog.remember name models st.catalog in
            let with_cat : WeaverState := { st with catalog := cat } in
            let st2 : WeaverState := set_config with_cat (inherit_thinking st cfg) name in
            respond st2 (provider_output name cfg),
    }

def provider_output (name : String) (cfg : ProviderConfig) : String :=
    String.concat "provider: "
        (String.concat name
            (String.concat " (model " (String.concat cfg.model ")")))

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


// ── /processes (dumb mode's snapshot; the TUI opens the monitor) ───────

#[partial]
def find_proc (id : String) (xs : List ProcEntry) : Option ProcEntry :=
    match xs {
        List.empty => Option.none,
        List.cons e rest => if e.id == id then Option.some e else find_proc id rest,
    }

def kill_proc_one (e : ProcEntry) : IO String := do {
    let r <- Procs.kill e;
    match r {
        Result.ok msg => IO.pure msg,
        Result.err msg => IO.pure (String.concat "kill: " msg),
    }
}

def kill_proc (id : String) (xs : List ProcEntry) : IO String :=
    match find_proc id xs {
        Option.none => IO.pure (String.concat "unknown process: " id),
        Option.some e => kill_proc_one e,
    }

def cmd_processes (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) := do {
    let entries <- Procs.list;
    let now <- IO.current_time_nano;
    let trimmed : String := String.trim arg;
    if String.is_empty trimmed
    then
        let text : String := if List.is_empty entries
            then "processes: none"
            else String.concat_list (List.map (fn (e : ProcEntry) => ProcEntry.line e now) entries) in
        respond st text
    else if String.starts_with "kill " trimmed
    then do {
        let id : String := String.trim (String.drop 5 trimmed);
        let msg <- kill_proc id entries;
        respond st msg
    }
    else respond st "usage: /processes [kill <id>]"
}


// ── /log (the debug log path + tail + crash note) ──────────────────────

def crash_in_dir (parent : Option Path) (path : String) : IO (Option String) :=
    match parent {
        Option.some d => Logs.detect_crash d path,
        Option.none => IO.pure Option.none,
    }

def crash_note (crash : Option String) : String :=
    match crash {
        Option.some m => String.concat m "\n",
        Option.none => "",
    }

def log_summary (path : String) : IO String := do {
    let tail <- Logs.tail path 20;
    let parent : Option Path := Path.parent (Path.path path);
    let crash <- crash_in_dir parent path;
    let note : String := crash_note crash;
    let body : String := if String.is_empty (String.trim tail) then "(empty log)" else tail;
    IO.pure (String.concat "log: " (String.concat path (String.concat "\n" (String.concat note body))))
}

def cmd_log (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) := do {
    let p <- Logs.latest_path;
    match p {
        Option.none => respond st "log: no log file (WEAVER_LOG=off?)",
        Option.some path => do {
            let text <- log_summary path;
            respond st text
        },
    }
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
    then respond st (plan_show st)
    else plan_arg arg st

/// The plan to display: the captured text, else the last assistant
/// message (a plan-mode turn that has not landed, or a session written
/// before the plan was persisted).
pub def Commands.current_plan (st : WeaverState) : Option String :=
    match st.plan {
        Option.some p => Option.some p,
        Option.none => Commands.last_assistant_text st.run.session.history,
    }

/// Plan-mode status, then the plan itself when there is one. The status
/// line stays first so the existing contract (and its tests) hold when
/// no plan exists.
def plan_show (st : WeaverState) : String :=
    let status : String := plan_status st.mode in
    match Commands.current_plan st {
        Option.none => status,
        Option.some p => String.concat status (String.concat "\n\nplan:\n" p),
    }

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

/// `/resume [<id|file>]`: continue a saved session. No argument LISTS
/// the saved sessions -- a bare resume of `meta.updated` would reload
/// the session already open, since a turn bumps its `updated`. (The TUI
/// intercepts the bare command and opens the picker dialog instead.)
/// A directory or a session id under the root opens that directory in
/// place; anything else is a shuttle checkpoint file, imported into a
/// fresh directory. The turn budget SPANS both halves (the remaining
/// budget is the total minus the turns the loaded session already took).
def cmd_resume (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then list_sessions_effect st
    else match Path.of arg {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok p => resume_path st p arg,
    }

// ── the session list ───────────────────────────────────────────────────

/// `1 turn` / `N turns` -- one spelling for both the line UI and the
/// TUI picker's hint.
pub def Commands.turns_label (n : I64) : String :=
    if n == 1 then "1 turn" else String.concat (I64.to_string n) " turns"

/// One picker/list row: `[current] name -- description (N turns · model) id`.
def session_line (current : String) (i : SessionInfo) : String :=
    let id : String := i.id in
    let name : String := i.name in
    let desc : String := i.description in
    let turns : I64 := i.turns in
    let model : String := i.model in
    let mark : String := if String.beq current id then "[current] " else "          " in
    let label : String := if String.is_empty desc then name else String.concat name (String.concat " -- " desc) in
    let stats : String := String.concat (Commands.turns_label turns) (String.concat " · " model) in
    String.concat "  " (String.concat mark (String.concat label
        (String.concat "  (" (String.concat stats (String.concat ") " id)))))

/// One page of the `/resume` picker: the sessions on it plus whether
/// newer/older pages exist. Pure, so the TUI's paging is unit-testable
/// without a terminal.
pub struct SessionPage {
    page : I64,
    rows : List SessionInfo,
    has_newer : Bool,
    has_older : Bool,
}

#[partial]
def page_len (xs : List SessionInfo) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _ rest => 1 + page_len rest,
    }

#[partial]
def page_take (n : I64) (xs : List SessionInfo) : List SessionInfo :=
    if n < 1 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (page_take (n - 1) rest),
    }

#[partial]
def page_drop (n : I64) (xs : List SessionInfo) : List SessionInfo :=
    if n < 1 then xs
    else match xs {
        List.empty => xs,
        List.cons _ rest => page_drop (n - 1) rest,
    }

pub def Commands.session_page (page_size : I64) (page : I64) (infos : List SessionInfo) : SessionPage :=
    let size : I64 := if page_size < 1 then 1 else page_size in
    let p : I64 := if page < 0 then 0 else page in
    let start : I64 := p * size in
    let total : I64 := page_len infos in
    let rows : List SessionInfo := page_take size (page_drop start infos) in
    let end : I64 := start + page_len rows in
    let newer : Bool := I64.gt p 0 in
    let older : Bool := I64.lt end total in
    let sp : SessionPage := { page := p, rows := rows, has_newer := newer, has_older := older } in
    sp

#[partial]
def session_lines_go (current : String) (infos : List SessionInfo) (acc : List String) : List String :=
    match infos {
        List.empty => List.reverse acc,
        List.cons i rest => session_lines_go current rest (List.cons (session_line current i) acc),
    }

def sessions_text (s : StoreState) (infos : List SessionInfo) : String :=
    let root : String := Path.to_string s.root in
    let current : String := s.id in
    let head : String := String.concat "sessions under " (String.concat root " (newest first):") in
    let body : String := List.intercalate "\n" (session_lines_go current infos List.empty) in
    String.concat head (String.concat "\n" (String.concat body
        "\nresume one with /resume <id> (the TUI's bare /resume opens a picker)"))

def list_sessions_effect (st : WeaverState) : IO (Result WeaverError Effect) :=
    match st.store {
        Option.none => respond st "session persistence unavailable (HOME unset or ~/.weaver/sessions unwritable)",
        Option.some s => do {
            let infos <- Store.list_sessions s.root;
            match infos {
                List.empty => respond st "no saved sessions",
                List.cons _ _ => respond st (sessions_text s infos),
            }
        },
    }

// ── /name and /describe ────────────────────────────────────────────────

def title_label (f : TitleField) : String :=
    match f {
        TitleField.title_name => "name",
        TitleField.title_description => "description",
    }

def title_stored (f : TitleField) (m : StoreMeta) : Option String :=
    match f {
        TitleField.title_name => m.name,
        TitleField.title_description => m.description,
    }

def title_derived (f : TitleField) (st : WeaverState) : Option String :=
    let s : Session := st.run.session in
    match f {
        TitleField.title_name => Store.derive_name s,
        TitleField.title_description => Store.derive_description s,
    }

def title_show (f : TitleField) (st : WeaverState) (m : StoreMeta) : IO (Result WeaverError Effect) :=
    let stored : Option String := title_stored f m in
    match stored {
        Option.some v => respond st (String.concat (title_label f) (String.concat ": " v)),
        Option.none => match title_derived f st {
            Option.some v => respond st (String.concat (title_label f) (String.concat ": " v)),
            Option.none => respond st (String.concat (title_label f)
                ": (none yet -- it derives from the first user message, and the description from the first assistant reply)"),
        },
    }

def title_set (f : TitleField) (st : WeaverState) (dir : Path) (text : String) : IO (Result WeaverError Effect) := do {
    let value : Option String := if String.beq text "-" then Option.none else Option.some text;
    let w <- Store.write_title dir f value;
    match w {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok _ => do {
            let msg : String := match value {
                Option.none => String.concat (title_label f) " cleared (it re-derives on the next turn)",
                Option.some v => String.concat (title_label f) (String.concat ": " v),
            };
            respond st msg
        },
    }
}

/// `/name [<text>|-]` (and `/describe`): show the effective value, set
/// it, or clear it back to the derived one.
def cmd_title (f : TitleField) (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) := do {
    let text : String := String.trim arg;
    match st.store {
        Option.none => respond st (String.concat (title_label f) ": session persistence unavailable"),
        Option.some s => do {
            let meta_r <- Store.read_meta s.dir;
            match meta_r {
                Result.err e => IO.pure (Result.err (WeaverError.io e)),
                Result.ok m =>
                    if String.is_empty text
                    then title_show f st m
                    else title_set f st s.dir text,
            }
        },
    }
}

def cmd_name (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    cmd_title TitleField.title_name arg st

def cmd_describe (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    cmd_title TitleField.title_description arg st

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
        Result.ok s => do {
            // A session switch starts with no grants; the captured plan
            // travels with the session directory.
            let _ <- Permissions.clear st.grants;
            let plan <- Store.read_plan p;
            let e0 : Effect := resume_effect st s (store_for_dir p st) label;
            let st1 : WeaverState := Commands.set_plan e0.state plan;
            let e1 : Effect := { e0 with state := st1 };
            IO.pure (Result.ok e1)
        }
    }
}

def resume_file (st : WeaverState) (label : String) : IO (Result WeaverError Effect) := do {
    let r <- Session.load label;
    match r {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok s => resume_import st s label,
    }
}

/// A checkpoint file never carries a weaver plan (it is shuttle's
/// session format), so the resumed state starts with none.
def resume_import (st : WeaverState) (s : Session) (label : String) : IO (Result WeaverError Effect) :=
    match st.store {
        Option.none => do {
            let _ <- Permissions.clear st.grants;
            IO.pure (Result.ok (plan_cleared (resume_effect st s Option.none label)))
        },
        Option.some old => resume_import_into st s old label,
    }

def plan_cleared (e : Effect) : Effect :=
    let st1 : WeaverState := Commands.set_plan e.state Option.none in
    let e1 : Effect := { e with state := st1 } in
    e1

def resume_import_into (st : WeaverState) (s : Session) (old : StoreState) (label : String) : IO (Result WeaverError Effect) := do {
    let r <- Store.import_session old.root s;
    match r {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok ns => do {
            let _ <- Permissions.clear st.grants;
            IO.pure (Result.ok (plan_cleared (resume_effect st s (Option.some ns) label)))
        },
    }
}

/// The budget spans halves and the resumed config re-resolves the
/// CURRENT provider's direct key (a checkpoint never carries one).
def resume_effect (st : WeaverState) (s : Session) (store : Option StoreState) (label : String) : Effect :=
    let keyed : Session := rekey_session st s in
    // The resumed session talks to ITS provider: the label and the
    // catalogue follow the saved config, not the flag this run started
    // with.
    let prov : String := Weaver.provider_of st.provider s.config in
    let st2 : WeaverState := set_session st keyed st.budget in
    let st3 : WeaverState := { st2 with provider := prov } in
    let st4 : WeaverState := set_store st3 store in
    let out : String := String.concat "resumed " label in
    if st.budget - s.turns < 1
    then Effect.reset st4 (String.concat out " -- the whole turn budget is already spent")
    else Effect.reset st4 out

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
    let prov : String := Weaver.provider_of st.provider cfg in
    { cfg with api_key := Map.lookup prov st.keys }

/// `/clear`: drop the transcript and the accounting, keep the config
/// and the tools. The turn budget resets to the full amount. With a
/// store, a NEW session directory starts and the old one stays
/// resumable.
def cmd_clear (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) := do {
    let base : Session := st.run.session;
    let fresh : Session := clear_session base;
    // A new session has no plan: the old one belongs to the session that
    // produced it (and its store directory, when persistence is on).
    let st2 : WeaverState := Commands.set_plan (set_session st fresh st.budget) Option.none;
    let _ <- Permissions.clear st.grants;
    match st.store {
        Option.none => IO.pure (Result.ok (Effect.reset st2 "cleared")),
        Option.some s => clear_with_store st2 s fresh,
    }
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
/// `/compact [instructions]`: summarize the context now. The summary
/// replaces the model's history (a system message plus a recent tail);
/// the visible transcript is untouched.
def cmd_compact (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) := do {
    let threshold : I64 := Compact.threshold st.context_window st.compact_at;
    let r <- Compact.compact st.run.session.config st.run.session threshold arg;
    match r {
        Result.err e => return (Result.err (WeaverError.of_shuttle e)),
        Result.ok out => do {
            let st2 : WeaverState := apply_compact st out;
            let note <- record_compact st.store out;
            return (Result.ok (Effect.ok st2 (compact_message out note)))
        }
    }
}

/// The compacted session as state (the same seam autocompact uses).
def apply_compact (st : WeaverState) (out : Compact.Outcome) : WeaverState :=
    // Bind the base first: a struct update on a field access (`{ st.run
    // with ... }`) parses under the self-hosted compiler but not the
    // Rust host, which the CI completeness step runs.
    let base : RunState := st.run in
    let run2 : RunState := { base with session := out.session } in
    // The compacted context is the new baseline; the pre-compaction
    // request size would keep the status line (and the next autocompact
    // check) at the old, too-large number.
    let st2 : WeaverState := { st with run := run2, last_context := out.tokens } in
    st2

/// Persist a compacted history into the session store (a no-op without
/// one); the error, when any, is reported but the compaction stands.
def record_compact (store : Option StoreState) (out : Compact.Outcome) : IO (Option String) :=
    match store {
        Option.none => IO.pure Option.none,
        Option.some s => do {
            let r <- Store.record_compacted s out.session;
            match r {
                Result.err e => IO.pure (Option.some e),
                Result.ok _ => IO.pure Option.none,
            }
        },
    }

def compact_message (out : Compact.Outcome) (note : Option String) : String :=
    let base : String := String.concat "compacted: "
        (String.concat (I64.to_string out.before) (String.concat " → "
        (String.concat (I64.to_string out.after) (String.concat " messages (~"
        (String.concat (I64.to_string out.tokens) " tokens)"))))) in
    match note {
        Option.none => base,
        Option.some e => String.concat base (String.concat " (history not saved: " (String.concat e ")")),
    }

/// Autocompact: before a turn, when the estimate crosses the configured
/// threshold, summarize and return the compacted state plus a note for
/// the transcript. A failed summarization leaves the session untouched
/// and only notes it -- a turn must still run.
pub def Commands.autocompact (st : WeaverState) : IO (Pair WeaverState (Option String)) := do {
    let threshold : I64 := Compact.threshold st.context_window st.compact_at;
    // The REAL last request size wins when it is larger than the byte
    // heuristic: a provider's tokenizer is the authority on how close the
    // next send is to the window.
    if I64.lt threshold 1 || I64.lt (Commands.context_used st) threshold
    then return (Pair.pair st Option.none)
    else do {
        let r <- Compact.compact st.run.session.config st.run.session threshold "";
        match r {
            Result.err e => return (Pair.pair st (Option.some (String.concat "context compaction failed: " e))),
            Result.ok out => do {
                let st2 : WeaverState := apply_compact st out;
                let note <- record_compact st.store out;
                return (Pair.pair st2 (Option.some (compact_message out note)))
            }
        }
    }
}

/// `/thinking [on|off]`: ask for the provider's reasoning channel
/// (Anthropic extended thinking; an OpenAI-compatible server streams
/// `reasoning_content` when it has one regardless). The flag rides the
/// session config, so a `/provider` switch inherits it and a save keeps
/// it.
def cmd_thinking (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if String.is_empty arg
    then respond st (thinking_state_text st)
    else if String.beq arg "on" then respond (set_thinking st true) "thinking: on"
    else if String.beq arg "off" then respond (set_thinking st false) "thinking: off"
    else respond st "thinking: on | off"

def thinking_state_text (st : WeaverState) : String :=
    if st.run.session.config.thinking then "thinking: on" else "thinking: off"

def set_thinking (st : WeaverState) (b : Bool) : WeaverState :=
    let cfg : ProviderConfig := st.run.session.config in
    let cfg2 : ProviderConfig := { cfg with thinking := b } in
    let cur : Session := st.run.session in
    let sess : Session := { cur with config := cfg2 } in
    let base : RunState := st.run in
    let run2 : RunState := { base with session := sess } in
    let st2 : WeaverState := { st with run := run2 } in
    st2

// ── /settings ──────────────────────────────────────────────────────────

pub type SettingKind {
    setting_cycle,
    setting_toggle,
    setting_number,
}

pub struct SettingRow {
    key : String,
    label : String,
    value : String,
    kind : SettingKind,
}

/// The editable settings, in display order. Provider/model are NOT here:
/// they already have `/provider` and `/model` (the model row opens the
/// picker); saving still writes their current values.
pub def Commands.setting_rows (st : WeaverState) : List SettingRow :=
    let cfg : ProviderConfig := st.run.session.config in
    let think_text : String := if cfg.thinking then "on" else "off" in
    let r0 : SettingRow := { key := "mode", label := "Approval mode", value := Mode.show st.mode, kind := SettingKind.setting_cycle } in
    let r1 : SettingRow := { key := "thinking", label := "Reasoning channel", value := think_text, kind := SettingKind.setting_toggle } in
    let r2 : SettingRow := { key := "max_tokens", label := "Output budget", value := I64.to_string cfg.max_tokens, kind := SettingKind.setting_number } in
    let r3 : SettingRow := { key := "max_turns", label := "Turn budget", value := I64.to_string st.budget, kind := SettingKind.setting_number } in
    let r4 : SettingRow := { key := "context_window", label := "Context window", value := I64.to_string st.context_window, kind := SettingKind.setting_number } in
    let r5 : SettingRow := { key := "compact_at", label := "Autocompact at (%)", value := I64.to_string st.compact_at, kind := SettingKind.setting_number } in
    [r0, r1, r2, r3, r4, r5]

/// Apply one setting by name. A value the knob rejects is an ordinary
/// command-output error (the session stays as it was).
pub def Commands.apply_setting (st : WeaverState) (key : String) (value : String) : Result String (Pair WeaverState String) :=
    if key == "mode"
    then match Mode.parse (String.trim value) {
        Option.none => Result.err (String.concat "unknown mode: " value),
        Option.some m => Result.ok (Pair.pair (set_mode st m) (String.concat "mode: " (Mode.show m))),
    }
    else if key == "thinking"
    then if Bool.or (value == "on") (value == "true")
        then Result.ok (Pair.pair (set_thinking st true) "thinking: on")
        else if Bool.or (value == "off") (value == "false")
        then Result.ok (Pair.pair (set_thinking st false) "thinking: off")
        else Result.err "thinking: on | off"
    else if key == "max_tokens"
    then match parse_i64 value {
        Option.none => Result.err "max_tokens must be a number",
        Option.some n =>
            if I64.lt n 16 then Result.err "max_tokens must be at least 16"
            else Result.ok (Pair.pair (set_max_tokens st n) (String.concat "max_tokens: " (I64.to_string n))),
    }
    else if key == "max_turns"
    then match parse_i64 value {
        Option.none => Result.err "max_turns must be a number",
        Option.some n =>
            if I64.lt n st.run.session.turns
            then Result.err "max_turns cannot be below the turns already spent"
            else Result.ok (Pair.pair (set_budget st n) (budget_line (set_budget st n))),
    }
    else if key == "context_window"
    then match parse_i64 value {
        Option.none => Result.err "context_window must be a number (0 disables autocompact)",
        Option.some n =>
            if I64.lt n 0 then Result.err "context_window cannot be negative"
            else Result.ok (Pair.pair (set_window st n) (String.concat "context_window: " (I64.to_string n))),
    }
    else if key == "compact_at"
    then match parse_i64 value {
        Option.none => Result.err "compact_at must be a percentage",
        Option.some n =>
            if Bool.or (I64.lt n 0) (I64.gt n 100) then Result.err "compact_at must be 0..100"
            else Result.ok (Pair.pair (set_compact_at st n) (String.concat "compact_at: " (String.concat (I64.to_string n) "%"))),
    }
    else Result.err (String.concat "unknown setting: "
        (String.concat key " (mode | thinking | max_tokens | max_turns | context_window | compact_at)"))

#[partial]
def next_above (cur : I64) (ladder : List I64) : Option I64 :=
    match ladder {
        List.empty => Option.none,
        List.cons x rest => if I64.gt x cur then Option.some x else next_above cur rest,
    }

def ladder_next (cur : I64) (ladder : List I64) : I64 :=
    match next_above cur ladder {
        Option.some x => x,
        Option.none => match ladder {
            List.empty => cur,
            List.cons first _ => first,
        },
    }

/// Step a setting to its next curated value (the dialog's Enter). A
/// numeric ladder wraps to its lowest rung; free text is `/settings
/// <key> <value>`.
pub def Commands.cycle_setting (st : WeaverState) (key : String) : Result String (Pair WeaverState String) :=
    let cfg : ProviderConfig := st.run.session.config in
    if key == "mode"
    then Commands.apply_setting st key (Mode.show (Mode.cycle st.mode))
    else if key == "thinking"
    then Commands.apply_setting st key (if cfg.thinking then "off" else "on")
    else if key == "max_tokens"
    then Commands.apply_setting st key (I64.to_string (ladder_next cfg.max_tokens [1024, 2048, 4096, 8192, 16384]))
    else if key == "max_turns"
    then Commands.apply_setting st key (I64.to_string (ladder_next st.budget [20, 40, 100, 200, 500]))
    else if key == "context_window"
    then Commands.apply_setting st key (I64.to_string (ladder_next st.context_window [32768, 65536, 128000, 200000, 1000000]))
    else if key == "compact_at"
    then Commands.apply_setting st key (I64.to_string (ladder_next st.compact_at [50, 60, 70, 80, 90]))
    else Result.err (String.concat "unknown setting: " key)

def settings_update (st : WeaverState) : SettingsUpdate :=
    let cfg : ProviderConfig := st.run.session.config in
    let u : SettingsUpdate := {
        mode := Option.some (Mode.show st.mode),
        provider := Option.some st.provider,
        model := Option.some cfg.model,
        max_turns := Option.some st.budget,
        thinking := Option.some cfg.thinking,
        max_tokens := Option.some cfg.max_tokens,
        context_window := Option.some st.context_window,
        compact_at := Option.some st.compact_at,
    } in
    u

def settings_text (st : WeaverState) : String :=
    let rows : List String := List.map (fn (r : SettingRow) => String.concat "  " (String.concat r.label (String.concat ": " r.value))) (Commands.setting_rows st) in
    let cfg : ProviderConfig := st.run.session.config in
    let head : String := String.concat "settings: " (String.concat st.provider (String.concat "/" cfg.model)) in
    let body : String := String.concat head (String.concat "\n" (List.intercalate "\n" rows)) in
    String.concat body "\n  /settings <key> <value> | save project|global"

def cmd_settings (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) := do {
    let trimmed : String := String.trim arg;
    if String.is_empty trimmed
    then respond st (settings_text st)
    else match split_command trimmed {
        Pair.pair word rest =>
            if word == "save"
            then settings_save (String.trim rest) st
            else match Commands.apply_setting st word (String.trim rest) {
                Result.err e => respond st e,
                Result.ok pr => match pr { Pair.pair st2 out => respond st2 out },
            },
    }
}

def settings_save (target : String) (st : WeaverState) : IO (Result WeaverError Effect) := do {
    let r <- Settings.save target (settings_update st);
    match r {
        Result.ok msg => respond st msg,
        Result.err e => respond st e,
    }
}

// ── /permissions ───────────────────────────────────────────────────────

def cap_parse (s : String) : Option Capability :=
    if s == "read" then Option.some Capability.read
    else if s == "write" then Option.some Capability.write
    else if s == "exec" then Option.some Capability.exec
    else if s == "net" then Option.some Capability.net
    else Option.none

/// `here`/`repo` is the scoped grant; `any`/`anywhere` is the whole
/// session; omitted defaults to `here` (the safer one).
def scope_parse (s : String) : Option PermScope :=
    if Bool.or (s == "here") (s == "repo") then Option.some PermScope.repo
    else if Bool.or (s == "any") (s == "anywhere") then Option.some PermScope.anywhere
    else if String.is_empty s then Option.some PermScope.repo
    else Option.none

/// `/permissions` -- list, pre-grant, or revoke the session's approval
/// grants. The grants are weaver's own (shuttle's `always` cache stays
/// empty), so this command is the whole management surface.
def cmd_permissions (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) := do {
    let trimmed : String := String.trim arg;
    if String.is_empty trimmed
    then do {
        let gs <- Permissions.get st.grants;
        respond st (permissions_text st gs)
    }
    else permissions_arg trimmed st
}

def permissions_arg (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match split_command arg {
        Pair.pair word rest =>
            if word == "revoke"
            then permissions_revoke (String.trim rest) st
            else if word == "allow"
            then permissions_allow (String.trim rest) st
            else respond st "usage: /permissions | allow <cap> [here|any] | revoke <cap|all> [here|any]",
    }

def permissions_allow (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    match split_command arg {
        Pair.pair cap_s scope_s =>
            match cap_parse cap_s {
                Option.none => respond st (String.concat "unknown capability: " (String.concat cap_s " (read | write | exec | net)")),
                Option.some cap =>
                    match scope_parse scope_s {
                        Option.none => respond st "unknown scope: here | any",
                        Option.some scope => do {
                            let g : PermGrant := { cap := cap, scope := scope };
                            let _ <- Permissions.add st.grants g;
                            respond st (String.concat "permissions: added " (PermGrant.describe g))
                        },
                    },
            },
    }

def permissions_revoke (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    if arg == "all"
    then do {
        let _ <- Permissions.clear st.grants;
        respond st "permissions: all grants revoked"
    }
    else match split_command arg {
        Pair.pair cap_s scope_s =>
            match cap_parse cap_s {
                Option.none => respond st (String.concat "unknown capability: " (String.concat cap_s " (read | write | exec | net)")),
                Option.some cap =>
                    if String.is_empty scope_s
                    then do {
                        // No scope named: both of this capability's grants.
                        let _ <- Permissions.revoke_cap st.grants cap;
                        respond st (String.concat "permissions: revoked all " (String.concat (cap_name cap) ""))
                    }
                    else match scope_parse scope_s {
                        Option.none => respond st "unknown scope: here | any",
                        Option.some scope => do {
                            let _ <- Permissions.revoke st.grants cap scope;
                            let g : PermGrant := { cap := cap, scope := scope };
                            respond st (String.concat "permissions: revoked " (PermGrant.describe g))
                        },
                    },
            },
    }

pub def permissions_text (st : WeaverState) (gs : List PermGrant) : String :=
    Permissions.render st.workspace_root (Mode.show st.mode) gs

def set_max_tokens (st : WeaverState) (n : I64) : WeaverState :=
    let cfg : ProviderConfig := st.run.session.config in
    let cfg2 : ProviderConfig := { cfg with max_tokens := n } in
    let cur : Session := st.run.session in
    let sess : Session := { cur with config := cfg2 } in
    let base : RunState := st.run in
    let run2 : RunState := { base with session := sess } in
    let st2 : WeaverState := { st with run := run2 } in
    st2

def set_window (st : WeaverState) (n : I64) : WeaverState :=
    let st2 : WeaverState := { st with context_window := n } in
    st2

def set_compact_at (st : WeaverState) (n : I64) : WeaverState :=
    let st2 : WeaverState := { st with compact_at := n } in
    st2

/// A provider switch keeps the session's reasoning preference and output
/// budget: the new preset's own values are replaced by the ones the user
/// chose.
def inherit_thinking (st : WeaverState) (cfg : ProviderConfig) : ProviderConfig :=
    let cur : ProviderConfig := st.run.session.config in
    let cfg2 : ProviderConfig := { cfg with thinking := cur.thinking, max_tokens := cur.max_tokens } in
    cfg2

def cmd_quit (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    let st2 : WeaverState := set_quit st in
    respond st2 "bye"

/// `/help`: the whole table, one line per command.
def cmd_help (arg : String) (st : WeaverState) : IO (Result WeaverError Effect) :=
    respond st help_text

def help_text : String :=
    List.intercalate "\n" [
        "/mode [manual|plan|allow_edit|auto]  show or set the approval mode",
        "/budget [n]                          show or raise the model-call budget",
        "/model [name]                        show/pick or set the model",
        "/provider [ollama|mistral|openrouter|anthropic|mock] [model]  show or set the provider",
        "/plan [approve manual|allow_edit]    show the current plan; approve drops plan mode",
        "/permissions [allow|revoke ...]      list or manage session approval grants",
        "/settings [<key> <value>|save project|global]  change or save settings",
        "/tools                               list tools with their capability tags",
        "/processes [kill <id>]               list background tasks",
        "/thinking [on|off]                   show or set the reasoning channel",
        "/log                                 the debug log path, tail and crash note",
        "/mcp                                 list mounted MCP servers",
        "/save <file>                         checkpoint the session as a JSON file",
        "/resume [<id|file>]                  list saved sessions (TUI picker) or continue an id/file",
        "/name [<text>|-]                     show, set or clear this session's name",
        "/describe [<text>|-]                 show, set or clear this session's description",
        "/clear                               start a new session and reset the budget",
        "/compact [instructions]              summarize the context and keep a recent tail",
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

/// Raise the total budget and recompute the remaining turns from it --
/// the same `max 0 (total - spent)` rule `/resume` uses.
def set_budget (st : WeaverState) (n : I64) : WeaverState :=
    let remaining : I64 := if n - st.run.session.turns < 0 then 0 else n - st.run.session.turns in
    let run2 : RunState := { (st.run) with turns_left := remaining } in
    let st2 : WeaverState := { st with budget := n, run := run2 } in
    st2

def set_quit (st : WeaverState) : WeaverState :=
    let st2 : WeaverState := { st with quit := true } in
    st2

/// Record the non-recoverable error that ended the run: the dumb loop
/// sets it, `main` reads it for the exit code.
def set_fatal (st : WeaverState) (e : WeaverError) : WeaverState :=
    let st2 : WeaverState := { st with fatal := Option.some e } in
    st2

pub def Commands.set_model (st : WeaverState) (model : String) : WeaverState :=
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
    // A session switch clears the `always` cache (the approval is
    // per-session by definition) and the last request's real size: the
    // new session's context is unknown until its first turn, and a stale
    // number from the old one makes the next autocompact summarize a
    // one-message history.
    let run2 : RunState := { (st.run) with session := s, turns_left := remaining, always := List.empty } in
    let st2 : WeaverState := { st with run := run2, last_context := 0 } in
    st2
