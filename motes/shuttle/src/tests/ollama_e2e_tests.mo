/// Compiled-only, env-gated against a real local Ollama server --
/// `tcp_*` natives are self-hosted-backend only (agent-skills.md's
/// Known Limitation #1), so this cannot run under the Rust host
/// interpreter, matching `motes/tls/src/tests/e2e_tests.mo`'s own
/// gating pattern. Trivially passes when the env var is unset, so it
/// never runs in the offline sweep.
///
/// Run it with MONAD_SHUTTLE_OLLAMA_TESTS=1 and a self-hosted/compiled
/// `monad` binary; the model comes from SHUTTLE_OLLAMA_MODEL (default
/// qwen2.5-coder) and must be one whose /api/tags entry lists the
/// `tools` capability (qwen3:latest verified 2026-10-13).
///
/// Even gated off, this file does not currently LOWER under the Rust
/// host: calling `Loop.run` from any file outside `loop.mo` hits the
/// same `MatchTraversalMismatch` documented in that module's own
/// header, with no mitigation found -- a Rust-host lowering gap only;
/// the loop is verified live under the self-hosted toolchain.
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

def sentinel : String := "SHUTTLE_E2E_SENTINEL_42"

/// PID-qualified so two sessions' test runs sharing this filesystem's
/// /tmp never collide on the same path.
def fixture_path : String := String.concat "/tmp/shuttle_ollama_e2e_fixture_" (String.concat (I64.to_string process_id) ".txt")

def write_fixture : IO Unit := do {
    do { let _w <- Test.write_fixture fixture_path sentinel; return unit }
}

def e2e_registry : ToolRegistry := ToolRegistry.register ReadTool.impl ToolRegistry.empty

/// The model is parameterized via `SHUTTLE_OLLAMA_MODEL` so a machine
/// with a different local pull can run the e2e without a multi-GB
/// blind pull; the default keeps the model this test was written
/// against. Tool calling needs a model whose /api/tags entry lists
/// the `tools` capability.
def e2e_config (model : String) : ProviderConfig :=
    { base_url := "http://localhost:11434", model := model, api_key_env := "SHUTTLE_UNUSED_API_KEY", max_tokens := 512, wire := Wire.openai }

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
    let model_opt <- IO.get_env "SHUTTLE_OLLAMA_MODEL";
    let model := match model_opt {
        Option.some m => m,
        Option.none => "qwen2.5-coder",
    };
    let r <- ResultT.run (Loop.run (e2e_config model) e2e_registry "You are a helpful coding assistant with a read tool." [e2e_task_message] 6 Provider.silent_emit Gate.auto);
    return (match r {
        Result.ok session => history_mentions_sentinel session.history,
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
