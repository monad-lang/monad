/// Compiled-only, env-gated against the real Anthropic API --
/// mirroring `ollama_e2e_tests.mo`'s gating pattern. Trivially passes
/// when the env var is unset, so it never runs in the offline sweep.
///
/// Actually reaching `api.anthropic.com` needs TWO things this repo
/// does not have yet, both documented rather than hidden:
///   * TLS -- `moose` speaks plaintext HTTP/1.1 only, so a gated-on
///     run today fails at the transport layer. This waits on
///     `library-ideas/tls.md` (agent-skills.md Phase 1); nothing in
///     the wire or loop changes when it lands.
///   * the Rust host's `Loop.run` lowering gap (same header note as
///     `ollama_e2e_tests.mo`) -- run it with a self-hosted/compiled
///     `monad` binary.
///
/// Run it with MONAD_SHUTTLE_ANTHROPIC_TESTS=1, ANTHROPIC_API_KEY set,
/// and (once TLS exists) a self-hosted/compiled `monad`; the model
/// comes from SHUTTLE_ANTHROPIC_MODEL (default claude-opus-5, the
/// plan's own default).
use std::test {Test.write_fixture}
use init::transformers {ResultT}
use shuttle::message_types {Role, Content}
use shuttle::message {Message}
use shuttle::provider {ProviderConfig, Wire, Provider.silent_emit}
use shuttle::gate {Gate, Gate.auto}
use shuttle::registry {ToolRegistry}
use shuttle::loop {Loop.run}
use shuttle::tools::file_tools {ReadTool.impl}
use std::io {IO.get_env}
use std::process {process_id}
use std::list {List.any}

def sentinel : String := "SHUTTLE_ANTHROPIC_E2E_SENTINEL_42"

/// PID-qualified so two sessions' test runs sharing this filesystem's
/// /tmp never collide on the same path.
def fixture_path : String := String.concat "/tmp/shuttle_anthropic_e2e_fixture_" (String.concat (I64.to_string process_id) ".txt")

def write_fixture : IO Unit := do {
    do { let _w <- Test.write_fixture (Path.path fixture_path) sentinel; return unit }
}

def e2e_registry : ToolRegistry := ToolRegistry.register ReadTool.impl ToolRegistry.empty

def e2e_config (model : String) : ProviderConfig :=
    { base_url := "https://api.anthropic.com", model := model, api_key_env := "ANTHROPIC_API_KEY", max_tokens := 512, wire := Wire.anthropic }

def e2e_task_message : Message :=
    { role := Role.user, content := [Content.text (String.concat "Use the read tool to read " fixture_path)] }

def history_mentions_sentinel (history : List Message) : Bool :=
    List.any message_mentions_sentinel history

def message_mentions_sentinel (m : Message) : Bool :=
    match m { Message.mk role content => List.any content_mentions_sentinel content }

def content_mentions_sentinel (c : Content) : Bool :=
    match c {
        Content.text s => String.contains s sentinel,
        Content.tool_result _ output _ => String.contains output sentinel,
        _ => false,
    }

def run_e2e : IO Bool := do {
    write_fixture;
    let model_opt <- IO.get_env "SHUTTLE_ANTHROPIC_MODEL";
    let model := match model_opt {
        Option.some m => m,
        Option.none => "claude-opus-5",
    };
    let r <- ResultT.run (Loop.run (e2e_config model) e2e_registry "You are a helpful coding assistant with a read tool." [e2e_task_message] 6 Provider.silent_emit Gate.auto);
    return (match r {
        Result.ok session => history_mentions_sentinel session.history,
        Result.err _ => false,
    })
}

#[test]
def test_anthropic_e2e_tool_result_reaches_final_answer : IO Bool := do {
    let gate <- IO.get_env "MONAD_SHUTTLE_ANTHROPIC_TESTS";
    match gate {
        Option.none => return true,
        Option.some _ => run_e2e,
    }
}
