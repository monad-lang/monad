/// Wire-faithful types for the OpenAI-compatible chat-completions API --
/// Ollama and Mistral AI both speak this unchanged. Deliberately NOT
/// shuttle's own normalized `Message`/`Turn` shape: this mote knows
/// nothing about "tools," "turns," or an agent loop, only the JSON this
/// specific API actually sends and expects. `ToolCall.arguments` stays
/// the raw JSON STRING the wire sends -- decoding it a second time is a
/// harness-level concern (`motes/shuttle`'s adapter), not this mote's.
use json::json {Json}
use json::serde_backend {derive_json_serialize, derive_json_deserialize}

pub struct ToolCall {
    id : String,
    name : String,
    arguments : String,
}

derive_json_serialize! ToolCall
derive_json_deserialize! ToolCall

pub struct ChatMessage {
    role : String,
    content : Option String,
    tool_calls : List ToolCall,
    tool_call_id : Option String,
    name : Option String,
}

derive_json_serialize! ChatMessage
derive_json_deserialize! ChatMessage

pub struct ToolDef {
    name : String,
    description : String,
    parameters : Json,
}

derive_json_serialize! ToolDef
derive_json_deserialize! ToolDef

pub struct ChatRequest {
    model : String,
    messages : List ChatMessage,
    tools : List ToolDef,
    max_tokens : Option I64,
}

derive_json_serialize! ChatRequest
derive_json_deserialize! ChatRequest

pub struct Usage {
    prompt_tokens : I64,
    completion_tokens : I64,
}

derive_json_serialize! Usage
derive_json_deserialize! Usage

pub struct Choice {
    message : ChatMessage,
    finish_reason : String,
}

derive_json_serialize! Choice
derive_json_deserialize! Choice

pub struct ChatResponse {
    choices : List Choice,
    usage : Usage,
}

derive_json_serialize! ChatResponse
derive_json_deserialize! ChatResponse
