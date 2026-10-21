/// The `task` tool's arguments -- split from subagent.mo for the derive
/// capture rule the other tool arg modules record.
use json::serde_backend {derive_json_serialize, derive_json_deserialize}

pub struct TaskArgs {
    prompt : String,
    max_turns : I64,
}

derive_json_serialize! TaskArgs
derive_json_deserialize! TaskArgs
