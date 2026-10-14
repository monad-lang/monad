/// `ShellArgs` -- split from `shell.mo` for the same reason `file_args.mo`
/// is split from `file.mo`: a top-level function in the SAME FILE as a
/// `reflect_type_info!` invocation cannot reference a derived function
/// (here, `ShellArgs.deserialize_json`) generated for a type ALSO
/// declared in that file -- "unbound variable", even though the function
/// is real.
use json::serde_backend {derive_json_serialize, derive_json_deserialize}

pub struct ShellArgs {
    command : String,
}

derive_json_serialize! ShellArgs
derive_json_deserialize! ShellArgs
