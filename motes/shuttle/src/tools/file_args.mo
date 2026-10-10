/// `ReadArgs`/`WriteArgs`/`EditArgs` -- split from `file.mo` for the
/// same reason `message_types.mo` is split from `message.mo`: a
/// top-level function in the SAME FILE as a `reflect_type_info!`
/// invocation cannot reference a derived function (here,
/// `*.deserialize_json`) generated for a type ALSO declared in that
/// file -- "unbound variable", even though the function is real.
use json::serde_backend {derive_json_serialize, derive_json_deserialize}

pub struct ReadArgs {
    path : String,
}

derive_json_serialize! ReadArgs
derive_json_deserialize! ReadArgs

pub struct WriteArgs {
    path : String,
    content : String,
}

derive_json_serialize! WriteArgs
derive_json_deserialize! WriteArgs

pub struct EditArgs {
    path : String,
    expected_content : String,
    new_content : String,
}

derive_json_serialize! EditArgs
derive_json_deserialize! EditArgs
