/// Compiled-only, env-gated against the real Mistral AI and OpenRouter
/// APIs -- one file for both because they share everything but the
/// constants: both are OpenAI-compatible chat completions endpoints
/// reached through the same `wire/openai.mo` adapter, so this is the
/// Ollama/Anthropic e2e shape parameterized over `presets.mo`.
/// Mirrors `ollama_e2e_tests.mo`'s gating pattern; trivially passes
/// when the env var is unset, so it never runs in the offline sweep.
///
/// Actually reaching either host needs the same two things the
/// Anthropic e2e documents:
///   * TLS -- `moose` speaks plaintext HTTP/1.1 only, so a gated-on
///     run today fails at the transport layer. Waits on
///     `library-ideas/tls.md`; nothing in the wire, presets or loop
///     changes when it lands.
///   * the Rust host's `Loop.run` lowering gap (same header note as
///     `ollama_e2e_tests.mo`) -- run with a self-hosted/compiled
///     `monad` binary.
///
/// Run the Mistral half with MONAD_SHUTTLE_MISTRAL_TESTS=1,
/// MISTRAL_API_KEY set, and the model from SHUTTLE_MISTRAL_MODEL
/// (default mistral-large-latest). Run the OpenRouter half with
/// MONAD_SHUTTLE_OPENROUTER_TESTS=1, OPENROUTER_API_KEY set, and the
/// model from SHUTTLE_OPENROUTER_MODEL -- no default: OpenRouter
/// model names are vendor-qualified (e.g. mistralai/mistral-large)
/// and a blind default could pull a model the account cannot use, so
/// the test reports false rather than guessing.
use init::transformers {ResultT}
use shuttle::message_types {Role, Content}
use shuttle::message {Message}
use shuttle::provider {ProviderConfig, Provider.silent_emit}
use shuttle::presets {ProviderConfig.mistral, ProviderConfig.openrouter}
use shuttle::registry {ToolRegistry}
use shuttle::loop {Loop.run}
use shuttle::tools::file_tools {ReadTool.impl}
use std::io {IO.get_env}
use std::path {Path.of}
use std::io {IO.write_file}
use std::process {process_id}
use std::list {List.any}

def sentinel : String := "SHUTTLE_OPENAI_COMPAT_E2E_SENTINEL_42"

/// PID-qualified so two sessions' test runs sharing this filesystem's
/// /tmp never collide on the same path.
def fixture_path : String := String.concat "/tmp/shuttle_openai_compat_e2e_fixture_" (String.concat (I64.to_string process_id) ".txt")

def write_fixture : IO Unit := do {
    match Path.of fixture_path {
        Result.ok p => IO.write_file p sentinel,
        Result.err _ => return unit,
    }
}

def e2e_registry : ToolRegistry := ToolRegistry.register ReadTool.impl ToolRegistry.empty

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

def run_e2e (cfg : ProviderConfig) : IO Bool := do {
    write_fixture;
    let r <- ResultT.run (Loop.run cfg e2e_registry "You are a helpful coding assistant with a read tool." [e2e_task_message] 6 Provider.silent_emit);
    return (match r {
        Result.ok session => history_mentions_sentinel session.history,
        Result.err _ => false,
    })
}

/// The model from SHUTTLE_MISTRAL_MODEL, defaulting to the preset's
/// own documented default.
def mistral_model : IO String := do {
    let model_opt <- IO.get_env "SHUTTLE_MISTRAL_MODEL";
    return (match model_opt {
        Option.some m => m,
        Option.none => "mistral-large-latest",
    })
}

#[test]
def test_mistral_e2e_tool_result_reaches_final_answer : IO Bool := do {
    let gate <- IO.get_env "MONAD_SHUTTLE_MISTRAL_TESTS";
    match gate {
        Option.none => return true,
        Option.some _ => do {
            let model <- mistral_model;
            run_e2e (ProviderConfig.mistral model)
        },
    }
}

#[test]
def test_openrouter_e2e_tool_result_reaches_final_answer : IO Bool := do {
    let gate <- IO.get_env "MONAD_SHUTTLE_OPENROUTER_TESTS";
    match gate {
        Option.none => return true,
        Option.some _ => do {
            let model_opt <- IO.get_env "SHUTTLE_OPENROUTER_MODEL";
            // See the header: no blind default. An unset model var
            // reports false rather than pulling a model the
            // account may not be able to use.
            match model_opt {
                Option.none => return false,
                Option.some model => run_e2e (ProviderConfig.openrouter model),
            }
        },
    }
}
