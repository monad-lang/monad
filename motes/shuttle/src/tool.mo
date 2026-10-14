/// Tool specs and the registry -- agent-skills.md Design 1's explicit
/// non-Loom fallback: a plain `BTreeMap String ToolImpl`, so the loop
/// does not change when Loom Phase 3 integration lands later.
use json::json {Json}
use json::serde_backend {derive_json_serialize, derive_json_deserialize}
use init::transformers {ResultT}
use shuttle::message_types {Content}
use std::map {}

pub struct ToolSpec {
    name : String,
    description : String,
    schema : Json,
}

derive_json_serialize! ToolSpec
derive_json_deserialize! ToolSpec

/// `run`'s return type is `ResultT String IO Content`, not a bare `IO
/// Content`: a tool failure is a `Result.err` short-circuit through the
/// loop's own `ResultT`, not an ad hoc `Content.tool_result.is_error`
/// flag threaded by hand at every call site.
///
/// `run` takes the model's `tool_use` id FIRST, before the input JSON:
/// the tool_result it returns must echo that id (both wires map it
/// straight to the wire's `tool_use_id`/`tool_call_id`, and both APIs
/// validate the pairing against the assistant turn), so the impl needs
/// the real id, not a name hardcoded at registration.
pub struct ToolImpl {
    spec : ToolSpec,
    run : String -> Json -> ResultT String IO Content,
}
