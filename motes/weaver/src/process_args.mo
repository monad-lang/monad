/// The background-process tools' argument structs -- split from the
/// implementation (`process_tools.mo`) for the same derive/capture reason
/// `shell_args.mo` records.
use json::serde_backend {derive_json_serialize, derive_json_deserialize}

pub struct StartProcessArgs {
    command : String,
    cwd : String,
}

derive_json_serialize! StartProcessArgs
derive_json_deserialize! StartProcessArgs

pub struct ReadProcessArgs {
    id : String,
}

derive_json_serialize! ReadProcessArgs
derive_json_deserialize! ReadProcessArgs

pub struct KillProcessArgs {
    id : String,
}

derive_json_serialize! KillProcessArgs
derive_json_deserialize! KillProcessArgs
