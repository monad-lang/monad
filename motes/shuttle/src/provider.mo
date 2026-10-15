/// `ProviderConfig` and `Provider.send` -- the one seam between
/// shuttle's own normalized `Message`/`Turn` and a concrete wire
/// format. The `openai` wire is Phase 2's unblocked entry point
/// (agent-skills.md Design 4), the `anthropic` wire is Phase 6's
/// (fixture-tested; `api.anthropic.com` is reachable now that
/// `motes/tls` landed), and `mock` is `wire/mock.mo`'s scripted
/// provider -- the loop's only offline backend.
///
/// `Wire`/`ProviderConfig` also carry hand-written JSON codecs here:
/// a session checkpoint serializes the config it ran with, and this
/// file has no `reflect_type_info!` invocation, so its own constructors
/// are safe to reference (see `message_types.mo`'s header for the
/// capture-pass limitation that forces that split elsewhere).
use shuttle::message {Message, Turn}
use shuttle::tool {ToolSpec}
use init::transformers {ResultT}
use json::json {
    Json, Json.make_object, Json.make_str, Json.make_num_int,
    Json.get_object, Json.get_str, Json.get_num_i64, Json.object_get,
}
use std::map {BTreeMap}
use openai::client {OpenAI.complete}
use shuttle::wire::openai {OpenAI.encode_request, OpenAI.decode_response}
use anthropic::client {Anthropic.complete}
use anthropic::types {MessagesRequest, MessagesResponse}
use shuttle::wire::anthropic {Anthropic.encode_request, Anthropic.decode_response}
use shuttle::wire::mock {Mock.send}

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

def wire_tag (w : Wire) : String :=
    match w {
        Wire.openai => "openai",
        Wire.anthropic => "anthropic",
        Wire.mock => "mock",
    }

pub def Wire.serialize_json (w : Wire) : Json := Json.make_str (wire_tag w)

def wire_of_tag (s : String) : Result String Wire :=
    if s == "openai" then Result.ok Wire.openai
    else if s == "anthropic" then Result.ok Wire.anthropic
    else if s == "mock" then Result.ok Wire.mock
    else Result.err (String.concat "unknown wire: " s)

pub def Wire.deserialize_json (j : Json) : Result String Wire :=
    match Json.get_str j {
        Result.err e => Result.err e,
        Result.ok s => wire_of_tag s,
    }

pub def ProviderConfig.serialize_json (c : ProviderConfig) : Json :=
    Json.make_object
        (Map.insert "base_url" (Json.make_str c.base_url)
        (Map.insert "model" (Json.make_str c.model)
        (Map.insert "api_key_env" (Json.make_str c.api_key_env)
        (Map.insert "max_tokens" (Json.make_num_int c.max_tokens)
        (Map.insert "wire" (Wire.serialize_json c.wire)
        BTreeMap.empty)))))

def config_field (obj : BTreeMap String Json) (name : String) : Result String Json :=
    match Json.object_get name obj {
        Option.some j => Result.ok j,
        Option.none => Result.err (String.concat "config: missing field: " name),
    }

def config_str_field (obj : BTreeMap String Json) (name : String) : Result String String :=
    match config_field obj name {
        Result.err e => Result.err e,
        Result.ok j => Json.get_str j,
    }

def config_int_field (obj : BTreeMap String Json) (name : String) : Result String I64 :=
    match config_field obj name {
        Result.err e => Result.err e,
        Result.ok j => Json.get_num_i64 (Json.get_num j),
    }

def config_of_object (obj : BTreeMap String Json) : Result String ProviderConfig :=
    match config_str_field obj "base_url" {
        Result.err e => Result.err e,
        Result.ok base_url =>
            match config_str_field obj "model" {
                Result.err e => Result.err e,
                Result.ok model =>
                    match config_str_field obj "api_key_env" {
                        Result.err e => Result.err e,
                        Result.ok api_key_env =>
                            match config_int_field obj "max_tokens" {
                                Result.err e => Result.err e,
                                Result.ok max_tokens =>
                                    match config_field obj "wire" {
                                        Result.err e => Result.err e,
                                        Result.ok wj => match Wire.deserialize_json wj {
                                            Result.err e => Result.err e,
                                            Result.ok wire =>
                                                let c : ProviderConfig := { base_url := base_url, model := model, api_key_env := api_key_env, max_tokens := max_tokens, wire := wire } in
                                                Result.ok c,
                                        },
                                    },
                            },
                    },
            },
    }

pub def ProviderConfig.deserialize_json (j : Json) : Result String ProviderConfig :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj => config_of_object obj,
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

/// Send one turn's request through `cfg.wire`. The mock arm serves the
/// scripted provider (`wire/mock.mo`) rather than erroring: the mock
/// wire is the loop's offline backend and the only one the loop tests
/// can drive without a network.
pub def Provider.send (cfg : ProviderConfig) (system : String) (tools : List ToolSpec) (history : List Message) : ResultT String IO Turn :=
    match cfg.wire {
        Wire.openai => send_openai cfg system tools history,
        Wire.anthropic => send_anthropic cfg system tools history,
        Wire.mock => Mock.send tools history,
    }
