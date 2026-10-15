/// The CLI -- agent-skills.md Phase 8. Hand-rolled over `clap::args`
/// primitives rather than `#[derive_cli]`, because `--mcp` is repeatable
/// and the derive's v1 surface is Bool flags + positionals only.
///
/// `shuttle run "<task>"` drives the indexed loop (loop.mo) against a
/// provider preset (presets.mo), with the built-in file/search/shell
/// tools mounted plus one proxy tool per tool of every `--mcp` server.
/// `--save` checkpoints the final session, `--resume` continues one;
/// `--max-turns` is the budget for the WHOLE session, both halves of a
/// save/resume.
///
/// Verification surface: the self-hosted compiled backend (`monad run
/// <file> -- args`, which forwards program arguments after the path, or
/// `monad build` then run the binary). The Rust host is bootstrap-only;
/// see loop.mo's KNOWN GAP.
use init::transformers {ResultT}
use json::json {Json}
use clap::args {*}
use parsec::number {parse_i64}
use mcp_client::protocol {McpClientInfo, McpTool}
use mcp_client::server {McpServer, Server.connect, Server.list_tools, Server.call, Server.dispose}
use std::ansi {colored, Color}
use std::io {IO.println, IO.write_stderr, IO.write_stdout, IO.flush_stdout}
use std::list {List.intercalate}
use shuttle::message_types {Role, Content}
use shuttle::message {Message}
use shuttle::provider {ProviderConfig, Provider.silent_emit}
use shuttle::presets {
    ProviderConfig.ollama, ProviderConfig.mistral,
    ProviderConfig.openrouter, ProviderConfig.anthropic,
}
use shuttle::registry {ToolRegistry}
use shuttle::agent {RunState}
use shuttle::loop {Loop.run, Loop.run_state}
use shuttle::session {Session, Session.load, Session.save}
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::tools::file_tools {ReadTool.impl}
use shuttle::tools::search_tools {GrepTool.impl, GlobTool.impl}
use shuttle::tools::shell_tools {ShellTool.impl}

def usage : String :=
    List.intercalate "\n" [
        "usage: shuttle run \"<task>\"",
        "  --provider ollama|mistral|openrouter|anthropic  (default ollama)",
        "  --model <name>    (defaults: ollama qwen2.5-coder, mistral mistral-large-latest,",
        "                    anthropic claude-opus-5; openrouter requires it)",
        "  --max-turns <n>   (default 10, total across a save/resume)",
        "  --stream, -s      (print assistant text live as it arrives)",
        "  --mcp <exe>       (repeatable; bare executable, no arguments yet)",
        "  --resume <file>   (continue a saved session)",
        "  --save <file>     (checkpoint the final session)",
    ]

def system_prompt : String := "You are a helpful coding assistant."

/// `IO.write_stderr` does not append a newline; every one-line
/// diagnostic this CLI prints goes through here.
def write_errln (s : String) : IO Unit :=
    IO.write_stderr (String.concat s "\n")

/// How this run identifies itself to MCP servers in the `initialize`
/// handshake (`mcp_client::protocol`'s `McpClientInfo`).
def client_info : McpClientInfo := { name := "shuttle", version := "0.1.0" }

// ── Argument parsing ──────────────────────────────────────────────────

/// The raw tokens, before defaults or validation. Parsing itself
/// cannot fail (every flag has a default), so error detection is a
/// validation pass over the filled struct -- `error` carries the one
/// thing parsing CAN see, an extra positional.
struct CliArgs {
    provider : String,
    model : String,
    max_turns_str : String,
    resume : String,
    save : String,
    mcps : List String,
    task : String,
    stream : Bool,
    error : String,
}

/// A validated run: provider config resolved, budget parsed, task set.
struct RunPlan {
    cfg : ProviderConfig,
    max_turns : I64,
    resume : String,
    save : String,
    mcps : List String,
    task : String,
    stream : Bool,
}

/// Flags first, each `take_opt` stripping its tokens so the next stage
/// sees the rest; `--mcp` loops until it stops finding one; the task is
/// the positional left after every flag is gone. `--stream`/`-s` is a
/// Bool flag, taken before everything else.
def parse_args (args : List String) : CliArgs :=
    match Cli.take_flag "stream" "s" args {
        Cli.FlagResult.flag_result stream rest => parse_provider stream rest,
    }

def parse_provider (stream : Bool) (args : List String) : CliArgs :=
    match Cli.take_opt "provider" "" "ollama" args {
        Cli.OptResult.opt_result provider rest => parse_model stream provider rest,
    }

def parse_model (stream : Bool) (provider : String) (args : List String) : CliArgs :=
    match Cli.take_opt "model" "" "" args {
        Cli.OptResult.opt_result model rest => parse_max_turns stream provider model rest,
    }

def parse_max_turns (stream : Bool) (provider : String) (model : String) (args : List String) : CliArgs :=
    match Cli.take_opt "max-turns" "" "10" args {
        Cli.OptResult.opt_result n rest => parse_resume stream provider model n rest,
    }

def parse_resume (stream : Bool) (provider : String) (model : String) (max_turns_str : String) (args : List String) : CliArgs :=
    match Cli.take_opt "resume" "" "" args {
        Cli.OptResult.opt_result resume rest => parse_save stream provider model max_turns_str resume rest,
    }

def parse_save (stream : Bool) (provider : String) (model : String) (max_turns_str : String) (resume : String) (args : List String) : CliArgs :=
    match Cli.take_opt "save" "" "" args {
        Cli.OptResult.opt_result save rest => parse_mcps stream provider model max_turns_str resume save [] rest,
    }

/// Repeatable `--mcp`: keep taking until absent. Accumulated in order
/// with `List.append` (there is no `List.reverse`), which is fine at
/// the size a command line can hold.
#[partial]
def parse_mcps (stream : Bool) (provider : String) (model : String) (max_turns_str : String) (resume : String) (save : String) (mcps : List String) (args : List String) : CliArgs :=
    match Cli.take_opt "mcp" "" "" args {
        Cli.OptResult.opt_result v rest =>
            if String.is_empty v
            then parse_task stream provider model max_turns_str resume save mcps rest
            else parse_mcps stream provider model max_turns_str resume save (List.append mcps [v]) rest,
    }

def parse_task (stream : Bool) (provider : String) (model : String) (max_turns_str : String) (resume : String) (save : String) (mcps : List String) (args : List String) : CliArgs :=
    match Cli.take_positional args {
        Cli.PosResult.pos_result task rest => parse_extra stream provider model max_turns_str resume save mcps task rest,
    }

/// A second positional is a typo, not a task; it lands in `error`.
def parse_extra (stream : Bool) (provider : String) (model : String) (max_turns_str : String) (resume : String) (save : String) (mcps : List String) (task : Option String) (args : List String) : CliArgs :=
    match Cli.take_positional args {
        Cli.PosResult.pos_result extra _ =>
            let c : CliArgs := {
                provider := provider, model := model, max_turns_str := max_turns_str,
                resume := resume, save := save, mcps := mcps,
                task := task_of task, stream := stream, error := extra_error extra,
            } in
            c,
    }

def task_of (task : Option String) : String :=
    match task {
        Option.some t => t,
        Option.none => "",
    }

def extra_error (extra : Option String) : String :=
    match extra {
        Option.some x => String.concat "unexpected extra argument: " x,
        Option.none => "",
    }

// ── Validation ────────────────────────────────────────────────────────

/// `--model` defaults per provider; OpenRouter has no default because
/// its model names are vendor-qualified (`mistralai/mistral-large`).
def resolve_model (provider : String) (model : String) : Result String String :=
    if Bool.not (String.is_empty model) then Result.ok model
    else if provider == "ollama" then Result.ok "qwen2.5-coder"
    else if provider == "mistral" then Result.ok "mistral-large-latest"
    else if provider == "anthropic" then Result.ok "claude-opus-5"
    else if provider == "openrouter" then Result.err "openrouter needs --model (vendor-qualified, e.g. mistralai/mistral-large)"
    else Result.err (String.concat "unknown provider: " provider)

def resolve_cfg (provider : String) (model : String) : Result String ProviderConfig :=
    if provider == "ollama" then Result.ok (ProviderConfig.ollama model)
    else if provider == "mistral" then Result.ok (ProviderConfig.mistral model)
    else if provider == "openrouter" then Result.ok (ProviderConfig.openrouter model)
    else if provider == "anthropic" then Result.ok (ProviderConfig.anthropic model)
    else Result.err (String.concat "unknown provider: " provider)

def plan_of (c : CliArgs) : Result String RunPlan :=
    if Bool.not (String.is_empty c.error) then Result.err c.error
    else match resolve_model c.provider c.model {
        Result.err e => Result.err e,
        Result.ok model => plan_of_model c model,
    }

def plan_of_model (c : CliArgs) (model : String) : Result String RunPlan :=
    match resolve_cfg c.provider model {
        Result.err e => Result.err e,
        Result.ok cfg => plan_of_cfg c cfg,
    }

def plan_of_cfg (c : CliArgs) (cfg : ProviderConfig) : Result String RunPlan :=
    match parse_i64 c.max_turns_str {
        Option.none => Result.err "--max-turns must be a number",
        Option.some n => plan_of_turns c cfg n,
    }

def plan_of_turns (c : CliArgs) (cfg : ProviderConfig) (n : I64) : Result String RunPlan :=
    if n < 1 then Result.err "--max-turns must be at least 1"
    else if String.is_empty c.task then Result.err usage
    else plan_done c cfg n

def plan_done (c : CliArgs) (cfg : ProviderConfig) (n : I64) : Result String RunPlan :=
    let p : RunPlan := {
        cfg := cfg, max_turns := n, resume := c.resume, save := c.save,
        mcps := c.mcps, task := c.task, stream := c.stream,
    } in
    Result.ok p

// ── MCP mounting ──────────────────────────────────────────────────────

/// One proxy `ToolImpl` per `McpTool`: the model calls it like any
/// built-in, the impl forwards to `tools/call` on the captured session.
///
/// The session value ADVANCES per call (`next_id`), and there is no
/// `IORef`, so this closure re-issues from the same captured value and
/// the id counter stands still. Safe on this transport: requests are
/// strictly sequential and `Stdio.request` waits for the response
/// frame carrying its own id, so a repeated id cannot meet its
/// predecessor's outstanding reply.
///
/// A transport error is a `ResultT.err`, which the loop's `run_tool`
/// turns into an `is_error := true` tool_result the model can see --
/// same contract as the built-in tools.
def mcp_proxy_run (server : McpServer) (tool : String) : String -> Json -> ResultT String IO Content :=
    fn (call_id : String) (input : Json) => ResultT.mk (do {
        let r <- Server.call server tool input;
        return (match r {
            Result.err e => Result.err (String.concat "mcp call failed: " e),
            Result.ok p => match p {
                Pair.pair _ res => Result.ok (Content.tool_result call_id res.text res.is_error),
            },
        })
    })

def mcp_tool_impl (server : McpServer) (t : McpTool) : ToolImpl :=
    let spec : ToolSpec := { name := t.name, description := t.description, schema := t.schema } in
    let impl : ToolImpl := { spec := spec, run := mcp_proxy_run server t.name } in
    impl

#[partial]
def register_mcp_tools (reg : ToolRegistry) (server : McpServer) (tools : List McpTool) : ToolRegistry :=
    match tools {
        List.empty => reg,
        List.cons t rest => register_mcp_tools (ToolRegistry.register (mcp_tool_impl server t) reg) server rest,
    }

/// Mount every `--mcp` command, in order. On any failure the already
/// mounted servers are disposed before the error returns (a failed
/// connect/list has already torn its own child down -- the stdio
/// module's failure-is-teardown contract).
#[partial]
def mount_all (client : McpClientInfo) (cmds : List String) (reg : ToolRegistry) (servers : List McpServer) : IO (Result String (Pair ToolRegistry (List McpServer))) :=
    match cmds {
        List.empty => return (Result.ok (Pair.pair reg servers)),
        List.cons cmd rest => do {
            let c <- Server.connect client cmd [];
            mount_connected client rest reg servers c
        },
    }

def mount_connected (client : McpClientInfo) (rest : List String) (reg : ToolRegistry) (servers : List McpServer) (c : Result String McpServer) : IO (Result String (Pair ToolRegistry (List McpServer))) :=
    match c {
        Result.err e => mount_fail servers (String.concat "mcp connect failed: " e),
        Result.ok m => mount_list client rest reg servers m,
    }

#[partial]
def mount_list (client : McpClientInfo) (rest : List String) (reg : ToolRegistry) (servers : List McpServer) (m : McpServer) : IO (Result String (Pair ToolRegistry (List McpServer))) := do {
    let r <- Server.list_tools m;
    mount_listed client rest reg servers m r
}

#[partial]
def mount_listed (client : McpClientInfo) (rest : List String) (reg : ToolRegistry) (servers : List McpServer) (m : McpServer) (r : Result String (Pair McpServer (List McpTool))) : IO (Result String (Pair ToolRegistry (List McpServer))) :=
    match r {
        Result.err e => mount_fail servers (String.concat "mcp tools/list failed: " e),
        Result.ok p => match p {
            Pair.pair m2 tools => mount_all client rest (register_mcp_tools reg m2 tools) (List.cons m2 servers),
        },
    }

def mount_fail (servers : List McpServer) (e : String) : IO (Result String (Pair ToolRegistry (List McpServer))) := do {
    let _ <- dispose_all servers;
    return (Result.err e)
}

#[partial]
def dispose_all (servers : List McpServer) : IO Unit :=
    match servers {
        List.empty => IO.pure unit,
        List.cons m rest => do {
            let _ <- Server.dispose m;
            dispose_all rest
        },
    }

// ── The run ───────────────────────────────────────────────────────────

def default_registry : ToolRegistry :=
    ToolRegistry.register ShellTool.impl
        (ToolRegistry.register GlobTool.impl
            (ToolRegistry.register GrepTool.impl
                (ToolRegistry.register ReadTool.impl ToolRegistry.empty)))

def user_message (task : String) : Message :=
    let m : Message := { role := Role.user, content := [Content.text task] } in
    m

// ── Live output ───────────────────────────────────────────────────────

/// One text fragment to stdout, flushed per fragment: a fragment is
/// the unit the user watches for, and an unflushed buffer would
/// batch them back into one silent lump.
def stdout_emit (t : String) : IO Unit := do {
    IO.write_stdout t;
    IO.flush_stdout
}

/// The run's text sink. `--stream` prints fragments live (and the
/// final answer is then NOT reprinted); without it the run stays
/// quiet and the final answer prints once at the end.
def plan_emit (plan : RunPlan) : String -> IO Unit :=
    if plan.stream then stdout_emit else Provider.silent_emit

pub def main (args : List String) : IO I64 :=
    match args {
        List.cons hd rest =>
            if hd == "run" then main_run rest
            else do { write_errln usage; return 1 },
        List.empty => do { write_errln usage; return 1 },
    }

def main_run (rest : List String) : IO I64 :=
    match plan_of (parse_args rest) {
        Result.err e => do { write_errln e; return 1 },
        Result.ok plan => run_plan plan,
    }

def run_plan (plan : RunPlan) : IO I64 := do {
    let r <- mount_all client_info plan.mcps default_registry [];
    mounted_plan plan r
}

/// `mount_all` disposes the mounted servers itself on error, so both
/// arms here hand back an exit code and nothing else.
def mounted_plan (plan : RunPlan) (r : Result String (Pair ToolRegistry (List McpServer))) : IO I64 :=
    match r {
        Result.err e => do { write_errln e; return 1 },
        Result.ok p => match p {
            Pair.pair reg servers => start_run plan reg servers,
        },
    }

/// Fresh run or resume. A resume keeps the loaded session's turns and
/// `spent` accounting (the budget is `--max-turns` MINUS the turns
/// already taken) by driving `Loop.run_state` over a `RunState` built
/// from the loaded value, instead of `Loop.run`'s fresh-session path.
def start_run (plan : RunPlan) (reg : ToolRegistry) (servers : List McpServer) : IO I64 :=
    if String.is_empty plan.resume
    then run_fresh plan reg servers
    else run_resumed plan reg servers

def run_fresh (plan : RunPlan) (reg : ToolRegistry) (servers : List McpServer) : IO I64 := do {
    let r <- ResultT.run (Loop.run plan.cfg reg system_prompt [user_message plan.task] plan.max_turns (plan_emit plan));
    finish_run plan servers r
}

def run_resumed (plan : RunPlan) (reg : ToolRegistry) (servers : List McpServer) : IO I64 := do {
    let ld <- Session.load plan.resume;
    resumed_loaded plan reg servers ld
}

def resumed_loaded (plan : RunPlan) (reg : ToolRegistry) (servers : List McpServer) (ld : Result String Session) : IO I64 :=
    match ld {
        Result.err e => fail_disposed servers (String.concat "resume failed: " e),
        Result.ok s => resumed_budget plan reg servers s,
    }

def resumed_budget (plan : RunPlan) (reg : ToolRegistry) (servers : List McpServer) (s : Session) : IO I64 :=
    let budget : I64 := plan.max_turns - s.turns in
    if budget < 1
    then fail_disposed servers "resumed session already used the whole --max-turns budget (raise --max-turns)"
    else resumed_state plan reg servers s budget

def resumed_state (plan : RunPlan) (reg : ToolRegistry) (servers : List McpServer) (s : Session) (budget : I64) : IO I64 := do {
    let s2 : Session := { s with history := List.append s.history [user_message plan.task] };
    let st : RunState := { session := s2, reg := reg, turns_left := budget, emit := plan_emit plan };
    let r <- ResultT.run (Loop.run_state st);
    finish_run plan servers r
}

def finish_run (plan : RunPlan) (servers : List McpServer) (r : Result String Session) : IO I64 :=
    match r {
        Result.err e => fail_disposed servers (String.concat "error: " e),
        Result.ok session => report plan servers session,
    }

def fail_disposed (servers : List McpServer) (e : String) : IO I64 := do {
    let _ <- dispose_all servers;
    write_errln e;
    return 1
}

// ── Reporting ─────────────────────────────────────────────────────────

def report (plan : RunPlan) (servers : List McpServer) (session : Session) : IO I64 := do {
    let s <- maybe_save plan session;
    report_saved plan servers session s
}

def maybe_save (plan : RunPlan) (session : Session) : IO (Result String Unit) :=
    if String.is_empty plan.save
    then return (Result.ok unit)
    else Session.save session plan.save

def report_saved (plan : RunPlan) (servers : List McpServer) (session : Session) (s : Result String Unit) : IO I64 :=
    match s {
        Result.err e => fail_disposed servers (String.concat "save failed: " e),
        Result.ok _ => report_print plan servers session,
    }

def report_print (plan : RunPlan) (servers : List McpServer) (session : Session) : IO I64 := do {
    if plan.stream then IO.pure unit else print_answer session;
    let dim <- colored (usage_line session) Color.bright_black;
    IO.println dim;
    let _ <- dispose_all servers;
    return 0
}

/// The final answer print that is NOT made in stream mode: the text
/// already reached stdout fragment by fragment through `emit`, so
/// reprinting it whole would double every answer.
def print_answer (session : Session) : IO Unit := do {
    let answer := last_assistant session.history;
    if String.is_empty answer
    then IO.println "(no assistant reply)"
    else IO.println answer
}

/// `[turns: N | tokens in/out/cached]` from the session's own
/// accounting -- `spent` accumulated over the whole run, `turns`
/// counting every model call.
def usage_line (session : Session) : String :=
    String.concat "[turns: " (String.concat (I64.to_string session.turns)
    (String.concat " | tokens in " (String.concat (I64.to_string session.spent.input_tokens)
    (String.concat ", out " (String.concat (I64.to_string session.spent.output_tokens)
    (String.concat ", cached " (String.concat (I64.to_string session.spent.cached_tokens) "]")))))))

def is_assistant (m : Message) : Bool :=
    match m.role {
        Role.assistant => true,
        _ => false,
    }

def content_text (c : Content) : String :=
    match c {
        Content.text s => s,
        _ => "",
    }

#[partial]
def message_text (m : Message) : String :=
    String.concat_all (List.map content_text m.content)

/// The LAST assistant message's text: a later assistant message wins
/// over an earlier one, even when the earlier one is the only message
/// whose text is nonempty.
#[partial]
def last_assistant (history : List Message) : String :=
    match history {
        List.empty => "",
        List.cons m rest =>
            let later := last_assistant rest in
            if is_assistant m && String.is_empty later then message_text m else later,
    }
