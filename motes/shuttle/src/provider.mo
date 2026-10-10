/// `ProviderConfig` and `Provider.send` -- the one seam between
/// shuttle's own normalized `Message`/`Turn` and a concrete wire
/// format. Only the `openai` wire exists today (Phase 2's unblocked
/// entry point, per agent-skills.md Design 4); `anthropic`/`mock` are
/// named so `loop.mo` and tests can already branch on `Wire`, with
/// their own bodies landing in later phases.
use shuttle::message {Message, Turn}
use shuttle::tool {ToolSpec}
use init::transformers {ResultT}
use openai::client {OpenAI.complete}
use shuttle::wire::openai {OpenAI.encode_request, OpenAI.decode_response}

pub type Wire {
    openai,
    anthropic,
    mock,
}

pub struct ProviderConfig {
    base_url : String,
    model : String,
    api_key_env : String,
    max_tokens : I64,
    wire : Wire,
}

def send_openai (cfg : ProviderConfig) (system : String) (tools : List ToolSpec) (history : List Message) : ResultT String IO Turn := do {
    let api_key <- ResultT.lift (IO.get_env cfg.api_key_env);
    let req := OpenAI.encode_request cfg.model cfg.max_tokens system tools history;
    let resp <- OpenAI.complete cfg.base_url api_key req;
    ResultT.mk (return (OpenAI.decode_response resp))
}

/// Send one turn's request through `cfg.wire`. `mock`/`anthropic`
/// error rather than silently falling through to `openai` -- a caller
/// that selects a wire this plan hasn't built yet should see that
/// named, not get an unrelated provider's answer.
pub def Provider.send (cfg : ProviderConfig) (system : String) (tools : List ToolSpec) (history : List Message) : ResultT String IO Turn :=
    match cfg.wire {
        Wire.openai => send_openai cfg system tools history,
        Wire.anthropic => ResultT.mk (return (Result.err "anthropic wire not implemented (Phase 6)")),
        Wire.mock => ResultT.mk (return (Result.err "Provider.send does not drive the mock wire -- call wire::mock directly")),
    }
