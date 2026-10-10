/// `GrepArgs`/`GlobArgs` -- split from `search.mo` for the same
/// capture-pass reason `file_args.mo` is split from `file.mo`.
use json::serde_backend {derive_json_serialize, derive_json_deserialize}

pub struct GrepArgs {
    pattern : String,
    path : String,
}

derive_json_serialize! GrepArgs
derive_json_deserialize! GrepArgs

pub struct GlobArgs {
    pattern : String,
    path : String,
}

derive_json_serialize! GlobArgs
derive_json_deserialize! GlobArgs
