/// Minimal entry point -- just enough to drive the Ollama e2e test
/// (`tests/ollama_e2e_tests.mo`). Not Phase 8's full `#[derive_cli]`
/// CLI surface (`--provider`/`--model`/`--mcp`/`--resume`), which is
/// out of scope for this plan.
use init::transformers {ResultT}
use shuttle::message_types {Role, Content}
use shuttle::message {Message}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::loop {Loop.run}
use shuttle::tools::file_tools {ReadTool.impl}
use shuttle::tools::search_tools {GrepTool.impl, GlobTool.impl}
use std::io {IO.println, IO.write_stderr}

def default_registry : ToolRegistry :=
    ToolRegistry.register GlobTool.impl
        (ToolRegistry.register GrepTool.impl
            (ToolRegistry.register ReadTool.impl ToolRegistry.empty))

def ollama_config (model : String) : ProviderConfig :=
    { base_url := "http://localhost:11434", model := model, api_key_env := "SHUTTLE_UNUSED_API_KEY", max_tokens := 1024, wire := Wire.openai }

def user_message (task : String) : Message :=
    { role := Role.user, content := [Content.text task] }

def run_task (task : String) (model : String) : IO I64 := do {
    let r <- ResultT.run (Loop.run (ollama_config model) default_registry "You are a helpful coding assistant." [user_message task] 10);
    match r {
        Result.ok _ => do { IO.println "done"; return 0 },
        Result.err e => do { IO.write_stderr (String.concat "error: " e); return 1 },
    }
}

pub def main (args : List String) : IO I64 :=
    match args {
        List.cons task rest =>
            match rest {
                List.cons model _ => run_task task model,
                List.empty => run_task task "qwen2.5-coder",
            },
        List.empty => do { IO.write_stderr "usage: shuttle <task> [model]"; return 1 },
    }
