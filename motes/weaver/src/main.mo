/// Weaver's entry -- weaver.md Phase 3: parse the provider/model and
/// budget flags, mount the MCP servers (disposal on EVERY exit path --
/// a failed mount, EOF and `/quit` all tear the children down), build
/// the registry and the initial state, and hand control to the dumb
/// loop. Line I/O only: the TUI is Phase 4, gated on terminal-ui's
/// missing natives.
///
/// The MCP mount machinery is Weaver's port of shuttle `main.mo`'s --
/// it is package-private there, and Weaver is exactly the consumer the
/// seam was left for. `--mcp` is repeatable, bare executable, same
/// contract; proxy tools are tagged `exec` (a server's catalogue is
/// arbitrary code), the conservative default Weaver's settings
/// (Phase 6) override per server.
use clap::args {}
use parsec::number {parse_i64}
use mcp_client::protocol {McpClientInfo, McpTool}
use mcp_client::server {McpServer, Server.connect, Server.list_tools, Server.call, Server.dispose}
use shuttle::gate {Capability, Gate, Gate.auto}
use shuttle::registry {ToolRegistry}
use shuttle::agent {RunState}
use shuttle::session {Session}
use shuttle::context {usage_zero}
use shuttle::provider {ProviderConfig}
use shuttle::message_types {Content}
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::tools::file_tools {ReadTool.impl, WriteTool.impl, EditTool.impl}
use shuttle::tools::search_tools {GrepTool.impl, GlobTool.impl}
use shuttle::tools::shell_tools {ShellTool.impl}
use weaver::commands {State}
use weaver::dumb {Dumb.run}
use weaver::policy {Mode}
use weaver::providers {Weaver.preset}
use weaver::settings {Settings, Settings.load, Settings.cap_of}
use init::transformers {ResultT}
use json::json {Json}
use std::io {IO.write_stdout, IO.flush_stdout, IO.read_line, IO.write_stderr}

/// The registry Weaver ships: all six built-ins (a coding agent's
/// whole point is the write/edit pair; shuttle's own CLI ships only
/// the read-side four) plus every `--mcp` mount's proxies.
def weaver_registry : ToolRegistry :=
    ToolRegistry.register ShellTool.impl
        (ToolRegistry.register EditTool.impl
            (ToolRegistry.register WriteTool.impl
                (ToolRegistry.register GlobTool.impl
                    (ToolRegistry.register GrepTool.impl
                        (ToolRegistry.register ReadTool.impl ToolRegistry.empty)))))

def system_prompt : String :=
    "You are Weaver, an interactive coding assistant. Inspect the workspace with read, grep and glob before changing anything; prefer edit over write for existing files; explain what you are about to do before doing it."

/// `IO.write_stderr` does not append a newline; every one-line
/// diagnostic this entry prints goes through here.
def write_errln (s : String) : IO Unit :=
    IO.write_stderr (String.concat s "\n")

/// The single stdout sink: the prompt, the streamed model text and the
/// command output all go through one flushed write, so piped runs see
/// each fragment as it happens.
def stdout_write (s : String) : IO Unit := do {
    IO.write_stdout s;
    IO.flush_stdout
}

/// How this run identifies itself to MCP servers in the `initialize`
/// handshake.
def client_info : McpClientInfo := { name := "weaver", version := "0.1.0" }

// ── Argument parsing ───────────────────────────────────────────────────

/// The raw tokens; parsing itself cannot fail (every flag defaults to
/// empty = unset), so error detection is a validation pass over the
/// filled struct. An unset flag falls to the settings file, then the
/// built-in default -- the resolution order `settings.mo` owns.
struct CliArgs {
    provider : String,
    model : String,
    max_turns_str : String,
    mcps : List String,
    error : String,
}

/// A validated start: provider config resolved, budget parsed.
struct Plan {
    provider : String,
    cfg : ProviderConfig,
    max_turns : I64,
    mcps : List String,
}

def parse_args (args : List String) : CliArgs :=
    match Cli.take_opt "provider" "" "" args {
        Cli.OptResult.opt_result provider rest => parse_model provider rest,
    }

def parse_model (provider : String) (args : List String) : CliArgs :=
    match Cli.take_opt "model" "" "" args {
        Cli.OptResult.opt_result model rest => parse_max_turns provider model rest,
    }

def parse_max_turns (provider : String) (model : String) (args : List String) : CliArgs :=
    match Cli.take_opt "max-turns" "" "" args {
        Cli.OptResult.opt_result n rest => parse_mcps provider model n [] rest,
    }

/// Repeatable `--mcp`: keep taking until absent.
#[partial]
def parse_mcps (provider : String) (model : String) (max_turns_str : String) (mcps : List String) (args : List String) : CliArgs :=
    match Cli.take_opt "mcp" "" "" args {
        Cli.OptResult.opt_result v rest =>
            if String.is_empty v
            then parse_done provider model max_turns_str mcps rest
            else parse_mcps provider model max_turns_str (List.append mcps [v]) rest,
    }

/// An interactive entry has no positional arguments (the tasks come
/// from stdin), so the FIRST one found is the whole error -- it fails
/// the run, and the message says what to remove.
#[partial]
def parse_done (provider : String) (model : String) (max_turns_str : String) (mcps : List String) (args : List String) : CliArgs :=
    match Cli.take_positional args {
        Cli.PosResult.pos_result extra rest => parse_extra_step (cli_of provider model max_turns_str mcps) extra,
    }

def cli_of (provider : String) (model : String) (max_turns_str : String) (mcps : List String) : CliArgs :=
    let c : CliArgs := { provider := provider, model := model, max_turns_str := max_turns_str, mcps := mcps, error := "" } in
    c

def parse_extra_step (c : CliArgs) (extra : Option String) : CliArgs :=
    match extra {
        Option.some x =>
            let c2 : CliArgs := { c with error := String.concat "unexpected argument: " x } in
            c2,
        Option.none => c,
    }

/// The start plan, resolved RUNTIME -> PROJECT -> GLOBAL -> default:
/// a flag always wins over a settings file, a settings file over the
/// built-in floor (ollama / the provider's default model / 40 turns).
def plan_of (s : Settings) (c : CliArgs) : Result String Plan :=
    if Bool.not (String.is_empty c.error)
    then Result.err c.error
    else
        let provider : String := resolve_provider s c.provider in
        let model : String := resolve_model s c.model in
        match Weaver.preset provider model {
            Result.err e => Result.err e,
            Result.ok cfg => plan_turns s c provider cfg,
        }

def resolve_provider (s : Settings) (flag : String) : String :=
    if String.is_empty flag
    then match s.provider { Option.some p => p, Option.none => "ollama" }
    else flag

/// "" reaches `Weaver.preset` as-is: the preset itself falls back to
/// the provider's default model.
def resolve_model (s : Settings) (flag : String) : String :=
    if String.is_empty flag
    then match s.model { Option.some m => m, Option.none => "" }
    else flag

def plan_turns (s : Settings) (c : CliArgs) (provider : String) (cfg : ProviderConfig) : Result String Plan :=
    match resolve_max_turns s c.max_turns_str {
        Result.err e => Result.err e,
        Result.ok n => plan_done provider cfg n c.mcps,
    }

def resolve_max_turns (s : Settings) (flag : String) : Result String I64 :=
    if String.is_empty flag
    then turn_cap (match s.max_turns { Option.some n => n, Option.none => 40 })
    else match parse_i64 flag {
        Option.some n => turn_cap n,
        Option.none => Result.err "--max-turns must be a number",
    }

def turn_cap (n : I64) : Result String I64 :=
    if n < 1 then Result.err "--max-turns must be at least 1" else Result.ok n

def plan_done (provider : String) (cfg : ProviderConfig) (n : I64) (mcps : List String) : Result String Plan :=
    let p : Plan := { provider := provider, cfg := cfg, max_turns := n, mcps := mcps } in
    Result.ok p

// ── MCP mounting (shuttle main.mo's machinery, ported) ─────────────────

/// A mounted server's proxy tools default to `exec` -- a server's
/// catalogue is arbitrary code -- unless settings override it for this
/// server, the per-server trust decision `.weaver/config.toml`'s
/// `mcp_caps` records.
def server_cap (s : Settings) (cmd : String) : Capability :=
    match Settings.cap_of cmd s {
        Option.some c => c,
        Option.none => Capability.exec,
    }

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

def mcp_tool_impl (server : McpServer) (t : McpTool) (cap : Capability) : ToolImpl :=
    let spec : ToolSpec := { name := t.name, description := t.description, schema := t.schema } in
    let impl : ToolImpl := { spec := spec, cap := cap, run := mcp_proxy_run server t.name } in
    impl

#[partial]
def register_mcp_tools (reg : ToolRegistry) (server : McpServer) (cap : Capability) (tools : List McpTool) : ToolRegistry :=
    match tools {
        List.empty => reg,
        List.cons t rest => register_mcp_tools (ToolRegistry.register (mcp_tool_impl server t cap) reg) server cap rest,
    }

/// The names already registered -- built-ins plus every earlier mount.
def taken_names (reg : ToolRegistry) : List String :=
    List.map (fn (t : ToolSpec) => t.name) (ToolRegistry.specs reg)

#[partial]
def name_taken (name : String) (taken : List String) : Bool :=
    match taken {
        List.empty => false,
        List.cons n rest => if n == name then true else name_taken name rest,
    }

#[partial]
def collision_walk (taken : List String) (tools : List McpTool) : List String :=
    match tools {
        List.empty => List.empty,
        List.cons t rest =>
            let taken2 : List String := List.append taken [t.name] in
            if name_taken t.name taken
            then List.append [t.name] (collision_walk taken2 rest)
            else collision_walk taken2 rest,
    }

#[partial]
def warn_collisions (reg : ToolRegistry) (tools : List McpTool) : IO Unit :=
    warn_each (collision_walk (taken_names reg) tools)

#[partial]
def warn_each (names : List String) : IO Unit :=
    match names {
        List.empty => IO.pure unit,
        List.cons n rest => do {
            write_errln (String.concat "warning: mcp tool '" (String.concat n "' shadows an existing tool of the same name; the mcp tool wins"));
            warn_each rest
        }
    }

/// Mount every `--mcp` command, in order. On any failure the already
/// mounted servers are disposed before the error returns (a failed
/// connect/list has already torn its own child down -- the stdio
/// module's failure-is-teardown contract).
#[partial]
def mount_all (client : McpClientInfo) (cmds : List String) (s : Settings) (reg : ToolRegistry) (servers : List McpServer) : IO (Result String (Pair ToolRegistry (List McpServer))) :=
    match cmds {
        List.empty => IO.pure (Result.ok (Pair.pair reg servers)),
        List.cons cmd rest => do {
            let c <- Server.connect client cmd [];
            mount_connected client rest s (server_cap s cmd) reg servers c
        },
    }

def mount_connected (client : McpClientInfo) (rest : List String) (s : Settings) (cap : Capability) (reg : ToolRegistry) (servers : List McpServer) (c : Result String McpServer) : IO (Result String (Pair ToolRegistry (List McpServer))) :=
    match c {
        Result.err e => mount_fail servers (String.concat "mcp connect failed: " e),
        Result.ok m => mount_list client rest s cap reg servers m,
    }

#[partial]
def mount_list (client : McpClientInfo) (rest : List String) (s : Settings) (cap : Capability) (reg : ToolRegistry) (servers : List McpServer) (m : McpServer) : IO (Result String (Pair ToolRegistry (List McpServer))) := do {
    let r <- Server.list_tools m;
    mount_listed client rest s cap reg servers m r
}

#[partial]
def mount_listed (client : McpClientInfo) (rest : List String) (s : Settings) (cap : Capability) (reg : ToolRegistry) (servers : List McpServer) (m : McpServer) (r : Result String (Pair McpServer (List McpTool))) : IO (Result String (Pair ToolRegistry (List McpServer))) :=
    match r {
        Result.err e => mount_fail servers (String.concat "mcp tools/list failed: " e),
        Result.ok p => match p {
            Pair.pair m2 tools => do {
                let _ <- warn_collisions reg tools;
                mount_all client rest s (register_mcp_tools reg m2 cap tools) (List.cons m2 servers)
            },
        },
    }

def mount_fail (servers : List McpServer) (e : String) : IO (Result String (Pair ToolRegistry (List McpServer))) := do {
    let _ <- dispose_all servers;
    IO.pure (Result.err e)
}

#[partial]
def dispose_all (servers : List McpServer) : IO Unit :=
    match servers {
        List.empty => IO.pure unit,
        List.cons m rest => do {
            let _ <- Server.dispose m;
            dispose_all rest
        }
    }

// ── The session ────────────────────────────────────────────────────────

/// The initial interactive state: a fresh session (nothing spent, no
/// history), the whole budget ahead, the settings' mode (manual is the
/// safe default; `/mode` changes it), and a gate rebuilt from the mode
/// before every turn -- `Gate.auto` here is never consulted.
def initial_state (p : Plan) (reg : ToolRegistry) (s : Settings) : State :=
    let session : Session := { config := p.cfg, system_prompt := system_prompt, tools := ToolRegistry.specs reg, history := List.empty, turns := 0, spent := usage_zero } in
    let run : RunState := { session := session, reg := reg, turns_left := p.max_turns, emit := stdout_write, gate := Gate.auto, always := List.empty } in
    let st : State := { run := run, mode := initial_mode s, provider := p.provider, budget := p.max_turns, mcps := p.mcps, quit := false } in
    st

/// The mode the session starts in: the settings' `mode` key when it parses,
/// `manual` otherwise -- a settings file must never land the session in
/// an unsafe mode by accident of a typo.
def initial_mode (s : Settings) : Mode :=
    match s.mode { Option.some m => m, Option.none => Mode.manual }

pub def main (args : List String) : IO I64 := do {
    let settings <- Settings.load;
    main_plan settings (parse_args args)
}

def main_plan (s : Settings) (c : CliArgs) : IO I64 :=
    match plan_of s c {
        Result.err e => do { write_errln e; return 1 },
        Result.ok p => run_plan p s,
    }

def run_plan (p : Plan) (s : Settings) : IO I64 := do {
    let r <- mount_all client_info p.mcps s weaver_registry [];
    mounted_plan p s r
}

/// `mount_all` disposes the mounted servers itself on error, so both
/// arms here hand back an exit code and nothing else.
def mounted_plan (p : Plan) (s : Settings) (r : Result String (Pair ToolRegistry (List McpServer))) : IO I64 :=
    match r {
        Result.err e => do { write_errln e; return 1 },
        Result.ok pr => match pr {
            Pair.pair reg servers => start_loop p s reg servers,
        },
    }

/// The one place the interactive session ends, whatever ended it: EOF
/// on stdin, `/quit`, or a crashed loop -- the mounted MCP servers come
/// down on every path.
def start_loop (p : Plan) (s : Settings) (reg : ToolRegistry) (servers : List McpServer) : IO I64 := do {
    let st : State := initial_state p reg s;
    let _ <- Dumb.run (fn (_ : Unit) => IO.read_line) stdout_write st;
    let _ <- dispose_all servers;
    return 0
}
