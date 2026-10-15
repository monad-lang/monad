/// Wire-faithful types for the OpenAI-compatible chat-completions API --
/// Ollama and Mistral AI both speak this unchanged. Deliberately NOT
/// shuttle's own normalized `Message`/`Turn` shape: this mote knows
/// nothing about "tools," "turns," or an agent loop, only the JSON this
/// specific API actually sends and expects. `ToolCall.arguments` stays
/// the raw JSON STRING the wire sends -- decoding it a second time is a
/// harness-level concern (`motes/shuttle`'s adapter), not this mote's.
///
/// `ToolCall`/`ToolDef` and their HAND-WRITTEN codecs live in the
/// sibling `tool.mo`, not here: the wire nests both under a
/// `"function"` key (`{"type":"function","function":{...}}`), which
/// the derive cannot emit or read, and a hand-written def in the SAME
/// file as a `reflect_type_info!` invocation (every derive below is
/// one) cannot reference the file's own constructors or use
/// `{ .. }` struct patterns. See `tool.mo`'s header for the
/// live-verified reason the nested shape is load-bearing.
use json::json {Json}
use json::serde_backend {derive_json_serialize, derive_json_deserialize}
use openai::tool {ToolCall, ToolDef}

pub struct ChatMessage {
    role : String,
    content : Option String,
    /// Defaults to empty on decode: a plain-text assistant turn carries
    /// NO `tool_calls` key on the wire (a real Ollama body), and the
    /// derive's absent-key rule is "declared default, else `none` for
    /// `Option` fields, else a hard decode error" -- this default is
    /// what keeps the live loop from dying on every non-tool turn.
    tool_calls : List ToolCall := List.empty,
    tool_call_id : Option String,
    name : Option String,
}

derive_json_serialize! ChatMessage
derive_json_deserialize! ChatMessage

pub struct ChatRequest {
    model : String,
    messages : List ChatMessage,
    tools : List ToolDef,
    max_tokens : Option I64,
    /// `true` switches the endpoint to SSE streaming. Defaults to false on
    /// decode for the same reason as `ChatMessage.tool_calls`: a real
    /// non-streaming request body carries no `stream` key, and the
    /// derive's absent-key rule is "declared default, else error".
    stream : Bool := false,
}

derive_json_serialize! ChatRequest
derive_json_deserialize! ChatRequest

pub struct ApiUsage {
    prompt_tokens : I64,
    completion_tokens : I64,
}

derive_json_serialize! ApiUsage
derive_json_deserialize! ApiUsage

pub struct Choice {
    message : ChatMessage,
    finish_reason : String,
}

derive_json_serialize! Choice
derive_json_deserialize! Choice

pub struct ChatResponse {
    choices : List Choice,
    usage : ApiUsage,
}

derive_json_serialize! ChatResponse
derive_json_deserialize! ChatResponse
