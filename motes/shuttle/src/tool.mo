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
pub struct ToolImpl {
    spec : ToolSpec,
    run : Json -> ResultT String IO Content,
}
