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
use mcp_client::protocol {McpClientInfo, McpTool}
use mcp_client::server {McpServer, Server.connect, Server.list_tools, Server.call, Server.dispose}
use shuttle::gate {Capability, Gate, Gate.auto}
use shuttle::registry {ToolRegistry}
use shuttle::agent {RunState, silent_sleep, silent_usage, silent_stop}
use shuttle::session {Session, Session.load}
use shuttle::context {usage_zero}
use shuttle::provider {ProviderConfig}
use shuttle::message_types {Content}
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::tools::file_tools {ReadTool.impl, WriteTool.impl, EditTool.impl}
use shuttle::tools::search_tools {GrepTool.impl, GlobTool.impl}
use shuttle::tools::shell_tools {ShellTool.impl}
use clap::parse {Cli.run}
// Wildcards: the derive's defs (decode_weavercli) are macro-generated,
// and a named import of one does not resolve in the self-hosted loader.
use weaver::cli {*}
use weaver::cli_spec {
    weaver_cli_spec, WeaverCli.provider_text, WeaverCli.model_text, WeaverCli.max_turns_of,
    WeaverCli.resume_text, WeaverCli.resume_asked, WeaverCli.cont_of, WeaverCli.no_color_of,
    WeaverCli.mcps, WeaverCli.version,
}
use weaver::commands {WeaverState, Commands.set_plan}
use weaver::monad_tools {MonadCheck.tool, MonadEval.tool}
use lang::module {ModuleInfoCache, module_info_cache_empty}
use weaver::store {
    StoreState, TLine, TLine.plain, TLine.user_line, Transcript,
    Store.sessions_root, Store.ensure_root, Store.new_session, Store.load_session,
    Store.import_session, Store.session_dir, Store.latest_session, Store.startup_transcript,
    Store.base_name, Store.append_transcript, Store.append_note, Store.read_live, Store.discard_live,
    Store.read_plan,
    Transcript.empty, Transcript.append, Transcript.next_block,
}
use weaver::theme {theme_split_lines}
use weaver::dumb {Dumb.run, Dumb.poll_sleep}
use weaver::policy {Mode}
use weaver::providers {
    Weaver.preset, Weaver.provider_of, Weaver.default_max_tokens,
    Weaver.default_max_turns, Weaver.default_window,
}
use std::map {BTreeMap}
use std::ref {Ref, Ref.new}
use weaver::permissions {PermGrant}
use weaver::settings {Settings, Settings.load, Settings.cap_of, Settings.validate}
use weaver::error {WeaverError, WeaverError.show}
use weaver::tui_app {Tui.run_resumed}
use log::logger {Logger}
use weaver::logs {LogSetup, Logs.setup, Logs.finish, Logs.info, Logs.error}
use weaver::process_tools {
    StartProcessTool.impl, ReadProcessTool.impl, KillProcessTool.impl, ListProcessesTool.impl,
}
use weaver::procs {Procs.shutdown}
use init::transformers {ResultT}
use json::json {Json}
use std::io {IO.write_stdout, IO.flush_stdout, IO.read_line, IO.write_stderr, IO.get_env, IO.is_dir}
use std::stream {StreamError}
use std::path {Path, Path.of}
use std::list {List.intercalate, List.length}
use std::map {Map}

/// The registry Weaver ships: all six built-ins (a coding agent's whole
/// point is the write/edit pair; shuttle's own CLI ships only the
/// read-side four) plus the Monad-aware tools and every `--mcp` mount's
/// proxies. The checker cache and eval buffer are per-session Refs
/// (created in `run_plan`), so one session's checks warm each other and
/// `monad_eval` definitions accumulate.
def weaver_registry (check_cache : Ref ModuleInfoCache) (eval_buf : Ref (List String)) (root : Option String) : ToolRegistry :=
    ToolRegistry.register (MonadEval.tool eval_buf check_cache root)
        (ToolRegistry.register (MonadCheck.tool check_cache root)
            (ToolRegistry.register StartProcessTool.impl
                (ToolRegistry.register ReadProcessTool.impl
                    (ToolRegistry.register KillProcessTool.impl
                        (ToolRegistry.register ListProcessesTool.impl
                            (ToolRegistry.register ShellTool.impl
                                (ToolRegistry.register EditTool.impl
                                    (ToolRegistry.register WriteTool.impl
                                        (ToolRegistry.register GlobTool.impl
                                            (ToolRegistry.register GrepTool.impl
                                                (ToolRegistry.register ReadTool.impl ToolRegistry.empty)))))))))))

def system_prompt : String :=
    "You are Weaver, an interactive coding assistant. Inspect the workspace with read, grep and glob before changing anything; prefer edit over write for existing files; explain what you are about to do before doing it. For Monad code, use monad_check to type-check a file or snippet and monad_eval to try expressions in the self-hosted interpreter (pure programs only)."

/// `IO.write_stderr` does not append a newline; every one-line
/// diagnostic this entry prints goes through here.
def write_errln (s : String) : IO Unit :=
    IO.write_stderr (String.concat s "\n")

/// The single stdout sink: the prompt, the streamed model text and the
/// command output all go through one flushed write, so piped runs see
/// each fragment as it happens. The reserved out-of-band tags the loop
/// and providers ride `emit` with are handled here: activity status is
/// dropped (the line UI has no live row) and reasoning is printed
/// without its control bytes.
def stdout_write (s : String) : IO Unit :=
    if String.starts_with "\u{1}activity\u{2}" s
    then IO.pure unit
    else do {
        let thinking_tag : String := "\u{1}thinking\u{2}";
        let text : String :=
            if String.starts_with thinking_tag s
            then String.slice s (String.length thinking_tag) (String.length s - String.length thinking_tag)
            else s;
        IO.write_stdout text;
        IO.flush_stdout
    }

/// How this run identifies itself to MCP servers in the `initialize`
/// handshake.
def client_info : McpClientInfo := { name := "weaver", version := WeaverCli.version }

/// A validated start: provider config resolved, budget parsed.
struct Plan {
    provider : String,
    cfg : ProviderConfig,
    max_turns : I64,
    mcps : List String,
    resume : String,
    cont : Bool,
    /// Autocompact: the estimated-token threshold is
    /// `context_window * compact_at / 100`; a zero window disables it.
    context_window : I64,
    compact_at : I64,
    /// Startup warnings the run should show, one per line: settings
    /// problems (unknown keys, parse failures), a configured model that
    /// did not belong to the provider, and the crash note.
    model_note : Option String,
}

/// The start plan, resolved RUNTIME -> PROJECT -> GLOBAL -> default:
/// a flag always wins over a settings file, a settings file over the
/// built-in floor (ollama / the provider's default model / the
/// provider-aware turn and window defaults).
/// Phase 9: a bad plan is a `config` error -- the run was misshapen
/// before it started, and `main` exits 1 on it.
def plan_of (s : Settings) (ws : List WeaverError) (c : WeaverCli) : Result WeaverError Plan :=
    match Settings.validate s {
        Result.err e => Result.err (WeaverError.config e),
        Result.ok _ => plan_validated s ws c,
    }

def plan_validated (s : Settings) (ws : List WeaverError) (c : WeaverCli) : Result WeaverError Plan :=
    if Bool.and (WeaverCli.cont_of c) (WeaverCli.resume_asked c)
    then Result.err (WeaverError.config "--resume and --continue are mutually exclusive")
    else
        let provider : String := resolve_provider s (WeaverCli.provider_text c) in
        let model : String := resolve_model s (WeaverCli.model_text c) in
        // Settings warnings (unknown keys, parse failures) ride the same
        // startup note, so the TUI shows them in its first block instead
        // of losing them behind the alternate screen.
        let base : Option String := warnings_note ws in
        // The configured model is used as-is: whether the provider serves
        // it is the provider's answer (/models asks), never a name table's.
        match Weaver.preset provider model s.api_keys {
            Result.err e => Result.err (WeaverError.config e),
            Result.ok cfg => plan_turns s c provider (effective_cfg s cfg) base,
        }

/// Settings warnings as note lines, in order; `none` when there are
/// none.
#[partial]
def warning_lines (ws : List WeaverError) (acc : List String) : List String :=
    match ws {
        List.empty => List.reverse acc,
        List.cons w rest => warning_lines rest (List.cons (String.concat "warning: " (WeaverError.show w)) acc),
    }

def warnings_note (ws : List WeaverError) : Option String :=
    match ws {
        List.empty => Option.none,
        List.cons _ _ => Option.some (List.intercalate "\n" (warning_lines ws List.empty)),
    }

/// The settings' runtime knobs (reasoning channel, output budget)
/// applied to a resolved config: one place, so startup and `/provider`
/// agree on the defaults. The output budget floors at weaver's own
/// default, not the preset's 512 -- `/provider` preserves it through
/// `inherit_thinking`, and `/settings` changes it live.
def effective_cfg (s : Settings) (cfg : ProviderConfig) : ProviderConfig :=
    let cfg1 : ProviderConfig := match s.thinking {
        Option.none => cfg,
        Option.some b => { cfg with thinking := b },
    } in
    match s.max_tokens {
        Option.none => { cfg1 with max_tokens := Weaver.default_max_tokens },
        Option.some n => { cfg1 with max_tokens := n },
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

def plan_turns (s : Settings) (c : WeaverCli) (provider : String) (cfg : ProviderConfig) (note : Option String) : Result WeaverError Plan :=
    match resolve_max_turns s (WeaverCli.max_turns_of c) {
        Result.err e => Result.err (WeaverError.config e),
        Result.ok n => plan_done provider cfg n c note (resolve_window s provider) (resolve_compact_at s),
    }

/// The context window the autocompact estimate is a fraction of. No
/// provider API reports one, so an explicit setting wins and the
/// provider's own default is the floor; 0 disables autocompact.
def resolve_window (s : Settings) (provider : String) : I64 :=
    match s.context_window {
        Option.some n => n,
        Option.none => Weaver.default_window provider,
    }

def resolve_compact_at (s : Settings) : I64 :=
    match s.compact_at { Option.some n => n, Option.none => 80 }

/// `--max-turns` is an `I64` in the derived CLI, so a non-number is
/// already a usage error (exit 2) before this runs; the settings file's
/// value takes the same floor.
def resolve_max_turns (s : Settings) (flag : Option I64) : Result String I64 :=
    match flag {
        Option.some n => turn_cap n,
        Option.none => turn_cap (match s.max_turns { Option.some n => n, Option.none => Weaver.default_max_turns }),
    }

def turn_cap (n : I64) : Result String I64 :=
    if n < 1 then Result.err "--max-turns must be at least 1" else Result.ok n

def plan_done (provider : String) (cfg : ProviderConfig) (n : I64) (c : WeaverCli) (note : Option String) (window : I64) (compact_at : I64) : Result WeaverError Plan :=
    let p : Plan := { provider := provider, cfg := cfg, max_turns := n, mcps := WeaverCli.mcps c, resume := WeaverCli.resume_text c, cont := WeaverCli.cont_of c, context_window := window, compact_at := compact_at, model_note := note } in
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
/// module's failure-is-teardown contract). Phase 9: a failed mount is
/// an `mcp` error -- fatal by classification, `main` exits 1 on it.
#[partial]
def mount_all (client : McpClientInfo) (cmds : List String) (s : Settings) (reg : ToolRegistry) (servers : List McpServer) : IO (Result WeaverError (Pair ToolRegistry (List McpServer))) :=
    match cmds {
        List.empty => IO.pure (Result.ok (Pair.pair reg servers)),
        List.cons cmd rest => do {
            let c <- Server.connect client cmd [];
            mount_connected client rest s (server_cap s cmd) reg servers c
        },
    }

def mount_connected (client : McpClientInfo) (rest : List String) (s : Settings) (cap : Capability) (reg : ToolRegistry) (servers : List McpServer) (c : Result String McpServer) : IO (Result WeaverError (Pair ToolRegistry (List McpServer))) :=
    match c {
        Result.err e => mount_fail servers (String.concat "mcp connect failed: " e),
        Result.ok m => mount_list client rest s cap reg servers m,
    }

#[partial]
def mount_list (client : McpClientInfo) (rest : List String) (s : Settings) (cap : Capability) (reg : ToolRegistry) (servers : List McpServer) (m : McpServer) : IO (Result WeaverError (Pair ToolRegistry (List McpServer))) := do {
    let r <- Server.list_tools m;
    mount_listed client rest s cap reg servers m r
}

#[partial]
def mount_listed (client : McpClientInfo) (rest : List String) (s : Settings) (cap : Capability) (reg : ToolRegistry) (servers : List McpServer) (m : McpServer) (r : Result String (Pair McpServer (List McpTool))) : IO (Result WeaverError (Pair ToolRegistry (List McpServer))) :=
    match r {
        Result.err e => mount_fail servers (String.concat "mcp tools/list failed: " e),
        Result.ok p => match p {
            Pair.pair m2 tools => do {
                let _ <- warn_collisions reg tools;
                mount_all client rest s (register_mcp_tools reg m2 cap tools) (List.cons m2 servers)
            },
        },
    }

def mount_fail (servers : List McpServer) (e : String) : IO (Result WeaverError (Pair ToolRegistry (List McpServer))) := do {
    let _ <- dispose_all servers;
    IO.pure (Result.err (WeaverError.mcp e))
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

/// A fresh session: nothing spent, no history.
def fresh_session (p : Plan) (reg : ToolRegistry) : Session :=
    let s : Session := { config := p.cfg, system_prompt := system_prompt, tools := ToolRegistry.specs reg, history := List.empty, turns := 0, spent := usage_zero } in
    s

/// The loaded session with its key re-resolved from this run's settings
/// (a checkpoint never carries one). The saved model is kept as-is: it
/// was what that session ran with, and availability is the provider's
/// answer, not a name table's. The key comes from the provider the
/// SAVED config talks to, not from this run's flag: a session resumed
/// without `--provider` still sends to the vendor it was saved under.
def rekey_loaded (p : Plan) (s : Settings) (sess : Session) : Pair Session (Option String) :=
    let cfg0 : ProviderConfig := sess.config in
    let prov : String := Weaver.provider_of p.provider cfg0 in
    let cfg2 : ProviderConfig := { cfg0 with api_key := Map.lookup prov s.api_keys } in
    let sess2 : Session := { sess with config := cfg2 } in
    Pair.pair sess2 Option.none

/// The initial interactive state: the opened session, the remaining
/// budget, the settings' mode (manual is the safe default; `/mode`
/// changes it), and a gate rebuilt from the mode before every turn --
/// `Gate.auto` here is never consulted.
def initial_state (p : Plan) (reg : ToolRegistry) (s : Settings) (colors : Bool) (store : Option StoreState) (session : Session) (grants : Option (Ref (List PermGrant))) (root : Option String) : WeaverState :=
    let left : I64 := if p.max_turns - session.turns < 0 then 0 else p.max_turns - session.turns in
    let run : RunState := { session := session, reg := reg, turns_left := left, emit := stdout_write, gate := Gate.auto, always := List.empty, retries := 3, sleep_ms := Dumb.poll_sleep, on_usage := silent_usage, should_stop := silent_stop, stopped := false } in
    let prov : String := Weaver.provider_of p.provider session.config in
    let st : WeaverState := { run := run, mode := initial_mode s, provider := prov, budget := p.max_turns, context_window := p.context_window, compact_at := p.compact_at, plan := Option.none, last_context := 0, grants := grants, workspace_root := root, mcps := p.mcps, keys := s.api_keys, catalog := BTreeMap.empty, quit := false, colors := colors, fatal := Option.none, store := store } in
    st

/// The mode the session starts in: the settings' `mode` key when it parses,
/// `manual` otherwise -- a settings file must never land the session in
/// an unsafe mode by accident of a typo.
def initial_mode (s : Settings) : Mode :=
    match s.mode { Option.some m => m, Option.none => Mode.manual }

/// The dumb UI's palette switch: `NO_COLOR` set anywhere is off --
/// the informal standard; there is no tty probe (a piped consumer sets
/// NO_COLOR) and no other env/CLI surface.
def colors_probe : IO Bool := do {
    let nc <- IO.get_env "NO_COLOR";
    return (match nc { Option.none => true, Option.some _ => false })
}

pub def main (args : List String) : IO I64 := do {
    let setup <- Logs.setup;
    let _ <- Logs.info setup.log (String.concat "ev=process_start argv=" (I64.to_string (List.length args)));
    let colors_on_main <- colors_probe;
    let loaded <- Settings.load;
    let _ <- warn_settings setup.log loaded.warnings;
    let _ <- warn_project_keys loaded.project_keys;
    let code <- Cli.run weaver_cli_spec args decode_weavercli (fn (c : WeaverCli) => main_plan setup colors_on_main loaded.settings loaded.warnings c);
    Logs.finish setup.log code;
    IO.pure code
}

/// Phase 9's settings visibility: parse failures and unknown keys are
/// logged here and ride the startup note -- the TUI's first transcript
/// block, or stderr for the line-based fallback. They no longer write
/// stderr directly, which the TUI's alternate screen hid.
#[partial]
def warn_one (log : Option Logger) (w : WeaverError) (rest : List WeaverError) : IO Unit := do {
    Logs.info log (String.concat "ev=settings_warning " (WeaverError.show w));
    warn_settings log rest
}

#[partial]
def warn_settings (log : Option Logger) (ws : List WeaverError) : IO Unit :=
    match ws {
        List.empty => IO.pure unit,
        List.cons w rest => warn_one log w rest,
    }

/// Phase 10's one startup line: api keys that came from the PROJECT
/// file are plaintext in a repo -- the deliberate act the entry
/// represents is worth naming, once, so the user knows what landed on
/// disk. (The global file is the recommended home for keys; no warning
/// for it.)
def warn_project_keys (names : List String) : IO Unit :=
    match names {
        List.empty => IO.pure unit,
        List.cons _ _ =>
            write_errln (String.concat "warning: api key(s) for " (String.concat (List.intercalate ", " names) " came from .weaver/config.toml -- plaintext on disk; ~/.weaver/config.toml is the recommended home")),
    }

def main_plan (setup : LogSetup) (colors : Bool) (s : Settings) (ws : List WeaverError) (c : WeaverCli) : IO I64 :=
    let effective : Bool := Bool.and colors (Bool.not (WeaverCli.no_color_of c)) in
    match plan_of s ws c {
        Result.err e => do {
            write_errln (String.concat "error: " (WeaverError.show e));
            Logs.error setup.log (String.concat "ev=config_error " (WeaverError.show e));
            return 1
        },
        Result.ok p => run_plan setup effective p s,
    }

def run_plan (setup : LogSetup) (colors : Bool) (p : Plan) (s : Settings) : IO I64 := do {
    let cache <- Ref.new module_info_cache_empty;
    let empty_buf : List String := List.empty;
    let eval_buf <- Ref.new empty_buf;
    let root <- workspace_root_probe;
    let r <- mount_all client_info p.mcps s (weaver_registry cache eval_buf root) [];
    mounted_plan setup colors p s r
}

/// `mount_all` disposes the mounted servers itself on error, so both
/// arms here hand back an exit code and nothing else.
def mounted_plan (setup : LogSetup) (colors : Bool) (p : Plan) (s : Settings) (r : Result WeaverError (Pair ToolRegistry (List McpServer))) : IO I64 :=
    match r {
        Result.err e => do {
            write_errln (String.concat "error: " (WeaverError.show e));
            Logs.error setup.log (String.concat "ev=mount_error " (WeaverError.show e));
            return 1
        },
        Result.ok pr => match pr {
            Pair.pair reg servers => start_loop setup colors p s reg servers,
        },
    }

/// A start with its optional store and the startup note (the
/// persistence degradation warning, when there is one).
struct OpenedSession {
    store : Option StoreState,
    session : Session,
    note : Option String,
}

/// The one place the interactive session ends, whatever ended it: EOF
/// on stdin, `/quit`, or a crashed loop -- the mounted MCP servers come
/// down on every path. `Tui.run_resumed` auto-detects a tty (via the
/// same `enter_raw_mode` degrade `terminal.mo` already documents) and
/// falls back to the line-based `Dumb.run` when stdin is not one.
/// Phase 9: the exit code follows the state -- a fatal error recorded
/// mid-session exits 1.
def start_loop (setup : LogSetup) (colors : Bool) (p : Plan) (s : Settings) (reg : ToolRegistry) (servers : List McpServer) : IO I64 := do {
    let root_opt <- Store.sessions_root;
    let opened <- open_session root_opt p s reg;
    match opened {
        Result.err e => fail_started servers e,
        Result.ok o => run_opened setup colors p s reg servers (with_model_note p.model_note o),
    }
}

/// The provider-model warning rides the session note: one line in the TUI's
/// first transcript block, and stderr for the line-based fallback.
def with_model_note (note : Option String) (o : OpenedSession) : OpenedSession :=
    match note {
        Option.none => o,
        Option.some n =>
            let combined : Option String := match o.note {
                Option.none => Option.some n,
                Option.some old => Option.some (String.concat n (String.concat "\n" old)),
            } in
            { o with note := combined },
    }

def fail_started (servers : List McpServer) (e : WeaverError) : IO I64 := do {
    write_errln (String.concat "error: " (WeaverError.show e));
    let _ <- dispose_all servers;
    return 1
}

/// The workspace root a `repo` grant is scoped to, from `PWD` (there is
/// no cwd/realpath native). Unset means repo scope is not offered.
def workspace_root_probe : IO (Option String) := do {
    let pwd <- IO.get_env "PWD";
    match pwd {
        Option.none => IO.pure Option.none,
        Option.some p =>
            if String.is_empty p then IO.pure Option.none else IO.pure (Option.some p),
    }
}

/// The plan a resumed session last captured, when persistence is on.
def stored_plan (store : Option StoreState) : IO (Option String) :=
    match store {
        Option.none => IO.pure Option.none,
        Option.some s => Store.read_plan s.dir,
    }

def run_opened (setup : LogSetup) (colors : Bool) (p : Plan) (s : Settings) (reg : ToolRegistry) (servers : List McpServer) (o : OpenedSession) : IO I64 := do {
    let _ <- announce_crash setup.crash;
    let empty_grants : List PermGrant := List.empty;
    let grants <- Ref.new empty_grants;
    let root <- workspace_root_probe;
    let plan <- stored_plan o.store;
    let st0 : WeaverState := initial_state p reg s colors o.store o.session (Option.some grants) root;
    let st : WeaverState := Commands.set_plan st0 plan;
    let _ <- Logs.info setup.log (String.concat "ev=session_open session=" (session_label o));
    let tr0 <- startup_transcript o;
    let ran_tui <- Tui.run_resumed setup.log st tr0;
    let _ <- if Bool.not ran_tui then announce_note o else IO.pure unit;
    let final <- run_fallback ran_tui st;
    let _ <- Procs.shutdown;
    let _ <- dispose_all servers;
    exit_of final
}

/// The degradation note rides the transcript for the TUI (where the
/// first frame shows it) and stderr for the line-based fallback.
def announce_note (o : OpenedSession) : IO Unit :=
    match o.note {
        Option.none => IO.pure unit,
        Option.some n => IO.write_stderr (String.concat "warning: " (String.concat n "\n")),
    }

/// The startup note with a store: persisted, so the in-memory transcript
/// and the store index stay in step (an in-memory-only note disabled
/// persistence for the whole session with "transcript log out of sync").
def stored_startup (s : StoreState) (tr : Transcript) (note : Option String) : IO Transcript :=
    match note {
        Option.none => IO.pure tr,
        Option.some n => Store.append_note s tr (List.map TLine.plain (theme_split_lines n)),
    }

def startup_transcript (o : OpenedSession) : IO Transcript :=
    match o.store {
        Option.none => IO.pure (note_block Transcript.empty o.note),
        Option.some s => do {
            let tr <- Store.startup_transcript s.dir;
            let live <- Store.read_live s;
            let tr2 <- absorb_live s tr live;
            stored_startup s tr2 o.note
        },
    }

/// A `live.txt` left behind by a crash: shown as a read-only block, then
/// persisted so it appears once, and never fed to the model.
def absorb_live (s : StoreState) (tr : Transcript) (live : Option String) : IO Transcript :=
    match live {
        Option.none => IO.pure tr,
        Option.some text => do {
            let block : List TLine := Transcript.next_block tr (List.cons (TLine.plain "[interrupted turn output]") (List.map TLine.plain (theme_split_lines text)));
            let total : I64 := tr.total;
            let r <- Store.append_transcript s.dir total block;
            let tr2 : Transcript := Transcript.append tr block;
            // Show the residue either way; delete it only once it is
            // durable (it is the only copy of the interrupted output).
            match r {
                Result.err _ => IO.pure tr2,
                Result.ok _ => absorb_kept s tr2,
            }
        },
    }

def absorb_kept (s : StoreState) (tr : Transcript) : IO Transcript := do {
    let _ <- Store.discard_live s;
    IO.pure tr
}

def note_block (tr : Transcript) (note : Option String) : Transcript :=
    match note {
        Option.none => tr,
        Option.some n =>
            let block : List TLine := Transcript.next_block tr (List.map TLine.plain (theme_split_lines n)) in
            Transcript.append tr block,
    }

def resume_requested (p : Plan) : Bool :=
    Bool.or (Bool.not (String.is_empty p.resume)) p.cont

def open_session (root_opt : Option Path) (p : Plan) (s : Settings) (reg : ToolRegistry) : IO (Result WeaverError OpenedSession) :=
    match root_opt {
        Option.none => open_no_root p reg,
        Option.some root => open_with_root root p s reg,
    }

def open_no_root (p : Plan) (reg : ToolRegistry) : IO (Result WeaverError OpenedSession) :=
    if resume_requested p
    then IO.pure (Result.err (WeaverError.config "session persistence unavailable: HOME is unset or unwritable"))
    else IO.pure (Result.ok (degraded "session persistence unavailable (HOME unset); this run is in-memory" p reg))

def open_with_root (root : Path) (p : Plan) (s : Settings) (reg : ToolRegistry) : IO (Result WeaverError OpenedSession) := do {
    let ok <- Store.ensure_root root;
    if Bool.not ok then open_unwritable p reg
    else if resume_requested p then resume_open root p s
    else fresh_open root p reg
}

def open_unwritable (p : Plan) (reg : ToolRegistry) : IO (Result WeaverError OpenedSession) :=
    if resume_requested p
    then IO.pure (Result.err (WeaverError.config "session persistence unavailable: the sessions root is not writable"))
    else IO.pure (Result.ok (degraded "session persistence unavailable (the sessions root is not writable); this run is in-memory" p reg))

def degraded (note : String) (p : Plan) (reg : ToolRegistry) : OpenedSession :=
    let o : OpenedSession := { store := Option.none, session := fresh_session p reg, note := Option.some note } in
    o

def opened (store : Option StoreState) (s : Session) : OpenedSession :=
    let o : OpenedSession := { store := store, session := s, note := Option.none } in
    o

def opened_note (store : Option StoreState) (s : Session) (note : Option String) : OpenedSession :=
    let o : OpenedSession := { store := store, session := s, note := note } in
    o

def fresh_open (root : Path) (p : Plan) (reg : ToolRegistry) : IO (Result WeaverError OpenedSession) := do {
    let sess : Session := fresh_session p reg;
    let r <- Store.new_session root sess;
    match r {
        Result.err e => IO.pure (Result.ok (degraded (String.concat "session persistence disabled: " e) p reg)),
        Result.ok st => IO.pure (Result.ok (opened (Option.some st) sess)),
    }
}

def store_at (root : Path) (dir : Path) : StoreState :=
    let s : StoreState := { root := root, dir := dir, id := Store.base_name dir } in
    s

def resume_open (root : Path) (p : Plan) (s : Settings) : IO (Result WeaverError OpenedSession) :=
    if p.cont then resume_latest root p s else resume_token root p s

def resume_latest (root : Path) (p : Plan) (s : Settings) : IO (Result WeaverError OpenedSession) := do {
    let l <- Store.latest_session root;
    match l {
        Option.none => IO.pure (Result.err (WeaverError.config "no saved sessions")),
        Option.some id => resume_dir root (Store.session_dir root id) p s,
    }
}

def resume_token (root : Path) (p : Plan) (s : Settings) : IO (Result WeaverError OpenedSession) :=
    match Path.of p.resume {
        Result.err e => IO.pure (Result.err (WeaverError.config e)),
        Result.ok path => resume_token_path root path p s,
    }

def resume_token_path (root : Path) (path : Path) (p : Plan) (s : Settings) : IO (Result WeaverError OpenedSession) := do {
    let isd <- IO.is_dir path;
    if isd then resume_dir root path p s
    else resume_token_candidate root p s
}

def resume_token_candidate (root : Path) (p : Plan) (s : Settings) : IO (Result WeaverError OpenedSession) := do {
    let cand : Path := Store.session_dir root p.resume;
    let isd <- IO.is_dir cand;
    if isd then resume_dir root cand p s else resume_file root p s
}

def resume_dir (root : Path) (dir : Path) (p : Plan) (s : Settings) : IO (Result WeaverError OpenedSession) := do {
    let r <- Store.load_session dir;
    match r {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok sess => match rekey_loaded p s sess {
            Pair.pair sess2 note => IO.pure (Result.ok (opened_note (Option.some (store_at root dir)) sess2 note)),
        },
    }
}

def resume_file (root : Path) (p : Plan) (s : Settings) : IO (Result WeaverError OpenedSession) := do {
    let r <- Session.load p.resume;
    match r {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok sess => resume_import_file root p s sess,
    }
}

def resume_import_file (root : Path) (p : Plan) (s : Settings) (sess : Session) : IO (Result WeaverError OpenedSession) := do {
    let imp <- Store.import_session root sess;
    match imp {
        Result.err e => IO.pure (Result.err (WeaverError.io e)),
        Result.ok st => match rekey_loaded p s sess {
            Pair.pair sess2 note => IO.pure (Result.ok (opened_note (Option.some st) sess2 note)),
        },
    }
}

/// The session's id (its directory's base name), or "-" without a store.
def session_label (o : OpenedSession) : String :=
    match o.store {
        Option.some s => Store.base_name s.dir,
        Option.none => "-",
    }

/// One stderr line for a detected crash (the log carries the details).
def announce_crash (crash : Option String) : IO Unit :=
    match crash {
        Option.none => IO.pure unit,
        Option.some c => IO.write_stderr (String.concat "warning: " (String.concat c "\n")),
    }

/// The crash warning rides the same startup note as the model warning.
def with_crash_note (crash : Option String) (o : OpenedSession) : OpenedSession :=
    match crash {
        Option.none => o,
        Option.some c =>
            let combined : Option String := match o.note {
                Option.none => Option.some c,
                Option.some old => Option.some (String.concat c (String.concat "\n" old)),
            } in
            { o with note := combined },
    }

def exit_of (st : WeaverState) : IO I64 :=
    match st.fatal {
        Option.some _ => IO.pure 1,
        Option.none => IO.pure 0,
    }

def run_fallback (ran_tui : Bool) (st : WeaverState) : IO WeaverState :=
    if ran_tui
    then IO.pure st
    else Dumb.run Option.none (fn (_ : Unit) => read_stdin_line) stdout_write st

/// The dumb loop's line source. A stdin read error ends the session like
/// end of input, but is named on stderr first rather than passing for it.
def read_stdin_line : IO (Option String) := do {
    let r <- IO.read_line;
    line_or_reported r
}

def line_or_reported (r : Result StreamError (Option String)) : IO (Option String) :=
    match r {
        Result.ok line => IO.pure line,
        Result.err e => do {
            IO.write_stderr ("weaver: reading stdin failed: " ++ e.message ++ "\n");
            return Option.none
        }
    }
