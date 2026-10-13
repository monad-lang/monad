/// `ProviderConfig` and `Provider.send` -- the one seam between
/// shuttle's own normalized `Message`/`Turn` and a concrete wire
/// format. The `openai` wire is Phase 2's unblocked entry point
/// (agent-skills.md Design 4) and the `anthropic` wire is Phase 6's
/// (fixture-tested; actually REACHING `api.anthropic.com` waits on
/// `library-ideas/tls.md`, since `moose` speaks plaintext only);
/// `mock` is named so `loop.mo` and tests can branch on `Wire`, with
/// its body still landing later.
use shuttle::message {Message, Turn}
use shuttle::tool {ToolSpec}
use init::transformers {ResultT}
use openai::client {OpenAI.complete}
use shuttle::wire::openai {OpenAI.encode_request, OpenAI.decode_response}
use anthropic::client {Anthropic.complete}
use anthropic::types {MessagesRequest, MessagesResponse}
use shuttle::wire::anthropic {Anthropic.encode_request, Anthropic.decode_response}

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

/// The anthropic key is REQUIRED, not `Option` -- a missing env var
/// errors here, named, rather than sending an empty `x-api-key` the
/// wire would reject with a less legible 401.
def anthropic_send_step (cfg : ProviderConfig) (key_opt : Option String) (req : MessagesRequest) : ResultT String IO MessagesResponse :=
    match key_opt {
        Option.none =>
            ResultT.mk (return (Result.err (String.concat "anthropic: no API key in env: " cfg.api_key_env))),
        Option.some key => Anthropic.complete cfg.base_url key req,
    }

def send_anthropic (cfg : ProviderConfig) (system : String) (tools : List ToolSpec) (history : List Message) : ResultT String IO Turn := do {
    let key_opt <- ResultT.lift (IO.get_env cfg.api_key_env);
    let req := Anthropic.encode_request cfg.model cfg.max_tokens system tools history;
    let resp <- anthropic_send_step cfg key_opt req;
    ResultT.mk (return (Anthropic.decode_response resp))
}

/// Send one turn's request through `cfg.wire`. `mock` errors rather
/// than silently falling through to a real provider -- a caller that
/// selects a wire this plan hasn't built yet should see that named,
/// not get an unrelated provider's answer.
pub def Provider.send (cfg : ProviderConfig) (system : String) (tools : List ToolSpec) (history : List Message) : ResultT String IO Turn :=
    match cfg.wire {
        Wire.openai => send_openai cfg system tools history,
        Wire.anthropic => send_anthropic cfg system tools history,
        Wire.mock => ResultT.mk (return (Result.err "Provider.send does not drive the mock wire -- call wire::mock directly")),
    }
