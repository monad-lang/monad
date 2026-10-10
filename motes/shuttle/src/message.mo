/// The harness's own normalized transcript: `Message`/`Usage`/`Turn`,
/// all structs with derived codecs. `Role`/`Content`/`StopReason` live
/// in `message_types.mo` (see that file's own note on why they must be
/// in a different file than any `reflect_type_info!` invocation).
use shuttle::message_types {Role, Content, StopReason}
use json::serde_backend {derive_json_serialize, derive_json_deserialize}

pub struct Message {
    role : Role,
    content : List Content,
}

derive_json_serialize! Message
derive_json_deserialize! Message

pub struct Usage {
    input_tokens : I64,
    output_tokens : I64,
    cached_tokens : I64,
}

derive_json_serialize! Usage
derive_json_deserialize! Usage

pub struct Turn {
    message : Message,
    usage : Usage,
    stop : StopReason,
}

derive_json_serialize! Turn
derive_json_deserialize! Turn
