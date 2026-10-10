/// Compiled-only, env-gated against a real local Ollama server --
/// `tcp_*` natives are self-hosted-backend only (agent-skills.md's
/// Known Limitation #1), so this cannot run under the Rust host
/// interpreter, matching `motes/tls/src/tests/e2e_tests.mo`'s own
/// gating pattern. Trivially passes when the env var is unset, so it
/// never runs in the offline sweep.
///
/// Even gated off, this file does not currently LOWER under the Rust
/// host: calling `Loop.run` from any file outside `loop.mo` hits the
/// same `MatchTraversalMismatch` documented in that module's own
/// header, with no mitigation found. Verifying this file at all
/// -- gate on or off -- needs the self-hosted/compiled toolchain,
/// not `monad check`/`monad test` on this host.
use init::transformers {ResultT}
use shuttle::message_types {Role, Content}
use shuttle::message {Message}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::loop {Loop.run}
use shuttle::tools::file_tools {ReadTool.impl}
use std::io {IO.get_env}
use std::path {Path.of}
use std::io {IO.write_file}
use std::process {process_id}

def sentinel : String := "SHUTTLE_E2E_SENTINEL_42"

/// PID-qualified so two sessions' test runs sharing this filesystem's
/// /tmp never collide on the same path.
def fixture_path : String := String.concat "/tmp/shuttle_ollama_e2e_fixture_" (String.concat (I64.to_string process_id) ".txt")

def write_fixture : IO Unit := do {
    match Path.of fixture_path {
        Result.ok p => IO.write_file p sentinel,
        Result.err _ => return unit,
    }
}

def e2e_registry : ToolRegistry := ToolRegistry.register ReadTool.impl ToolRegistry.empty

def e2e_config : ProviderConfig :=
    { base_url := "http://localhost:11434", model := "qwen2.5-coder", api_key_env := "SHUTTLE_UNUSED_API_KEY", max_tokens := 512, wire := Wire.openai }

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
    let r <- ResultT.run (Loop.run e2e_config e2e_registry "You are a helpful coding assistant with a read tool." [e2e_task_message] 6);
    return (match r {
        Result.ok history => history_mentions_sentinel history,
        Result.err _ => false,
    })
}

#[test]
def test_ollama_e2e_tool_result_reaches_final_answer : IO Bool := do {
    let gate <- IO.get_env "MONAD_SHUTTLE_OLLAMA_TESTS";
    match gate {
        Option.none => return true,
        Option.some _ => run_e2e,
    }
}
