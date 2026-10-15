/// The session -- agent-skills.md Phase 5's checkpointable transcript:
/// everything a run carries EXCEPT the pieces that cannot be
/// serialized. The tool registry (closures) and the turn budget live in
/// `agent.mo`'s `RunState`, which WRAPS a `Session`; checkpointing is
/// `Session.save` of the inner value, resume is `Session.load` plus a
/// fresh registry and a recomputed budget.
///
/// Codecs are hand-written, not derived, for the same reason
/// `message_types.mo`'s are: keeping this file free of
/// `reflect_type_info!` means every function here may reference its
/// own constructors safely (the capture-pass limitation is per-file).
/// File-backed JSON, not a binary format -- the same decision
/// `todo-app-architecture.md` records for the same missing-`IORef`
/// reason: the transcript is a value, and a checkpoint is that value
/// written down.
use json::json {
    Json, Json.parse, Json.to_string, Json.ParseError.to_string,
    Json.make_object, Json.make_array, Json.make_str, Json.make_num_int,
    Json.get_object, Json.get_array, Json.get_str, Json.get_num_i64,
    Json.object_get,
}
use std::map {BTreeMap}
use std::io {IO.read_file, IO.write_file, IO.file_exists}
use std::path {Path.of, Path.to_string}
use shuttle::provider {ProviderConfig}
use shuttle::tool {ToolSpec}
use shuttle::message {Message, Usage}

pub struct Session {
    config : ProviderConfig,
    system_prompt : String,
    tools : List ToolSpec,
    history : List Message,
    turns : I64,
    spent : Usage,
}

pub def Session.serialize_json (s : Session) : Json :=
    Json.make_object
        (Map.insert "config" (ProviderConfig.serialize_json s.config)
        (Map.insert "system_prompt" (Json.make_str s.system_prompt)
        (Map.insert "tools" (Json.make_array (List.map ToolSpec.serialize_json s.tools))
        (Map.insert "history" (Json.make_array (List.map Message.serialize_json s.history))
        (Map.insert "turns" (Json.make_num_int s.turns)
        (Map.insert "spent" (Usage.serialize_json s.spent)
        BTreeMap.empty))))))

#[partial]
def decode_tools (js : List Json) : Result String (List ToolSpec) :=
    match js {
        List.empty => Result.ok List.empty,
        List.cons j rest =>
            match ToolSpec.deserialize_json j {
                Result.err e => Result.err e,
                Result.ok t =>
                    match decode_tools rest {
                        Result.err e => Result.err e,
                        Result.ok ts => Result.ok (List.cons t ts),
                    },
            },
    }

#[partial]
def decode_messages (js : List Json) : Result String (List Message) :=
    match js {
        List.empty => Result.ok List.empty,
        List.cons j rest =>
            match Message.deserialize_json j {
                Result.err e => Result.err e,
                Result.ok m =>
                    match decode_messages rest {
                        Result.err e => Result.err e,
                        Result.ok ms => Result.ok (List.cons m ms),
                    },
            },
    }

def session_field (obj : BTreeMap String Json) (name : String) : Result String Json :=
    match Json.object_get name obj {
        Option.some j => Result.ok j,
        Option.none => Result.err (String.concat "session: missing field: " name),
    }

// One step per def, the "helper per level" style `message_types.mo` and
// `motes/mcp_client/src/protocol.mo` use: patterns are one constructor
// deep and an 8-deep nested match outruns what the parser reliably
// takes, so each field gets its own step. `obj` threads through every
// step so each can look up the next field.
def session_spent_step (obj : BTreeMap String Json) (config : ProviderConfig) (system_prompt : String) (tools : List ToolSpec) (history : List Message) (turns : I64) : Result String Session :=
    match session_field obj "spent" {
        Result.err e => Result.err e,
        Result.ok uj => match Usage.deserialize_json uj {
            Result.err e => Result.err e,
            Result.ok spent =>
                let s : Session := { config := config, system_prompt := system_prompt, tools := tools, history := history, turns := turns, spent := spent } in
                Result.ok s,
        },
    }

def session_turns_step (obj : BTreeMap String Json) (config : ProviderConfig) (system_prompt : String) (tools : List ToolSpec) (history : List Message) : Result String Session :=
    match session_field obj "turns" {
        Result.err e => Result.err e,
        Result.ok nj => match Json.get_num_i64 (Json.get_num nj) {
            Result.err e => Result.err e,
            Result.ok turns => session_spent_step obj config system_prompt tools history turns,
        },
    }

def session_history_step (obj : BTreeMap String Json) (config : ProviderConfig) (system_prompt : String) (tools : List ToolSpec) : Result String Session :=
    match session_field obj "history" {
        Result.err e => Result.err e,
        Result.ok hj => match Json.get_array hj {
            Result.err e => Result.err e,
            Result.ok history_js => match decode_messages history_js {
                Result.err e => Result.err e,
                Result.ok history => session_turns_step obj config system_prompt tools history,
            },
        },
    }

def session_tools_step (obj : BTreeMap String Json) (config : ProviderConfig) (system_prompt : String) : Result String Session :=
    match session_field obj "tools" {
        Result.err e => Result.err e,
        Result.ok tj => match Json.get_array tj {
            Result.err e => Result.err e,
            Result.ok tool_js => match decode_tools tool_js {
                Result.err e => Result.err e,
                Result.ok tools => session_history_step obj config system_prompt tools,
            },
        },
    }

def session_prompt_step (obj : BTreeMap String Json) (config : ProviderConfig) : Result String Session :=
    match session_field obj "system_prompt" {
        Result.err e => Result.err e,
        Result.ok sj => match Json.get_str sj {
            Result.err e => Result.err e,
            Result.ok system_prompt => session_tools_step obj config system_prompt,
        },
    }

def session_config_step (obj : BTreeMap String Json) (cj : Json) : Result String Session :=
    match ProviderConfig.deserialize_json cj {
        Result.err e => Result.err e,
        Result.ok config => session_prompt_step obj config,
    }

def session_of_object (obj : BTreeMap String Json) : Result String Session :=
    match session_field obj "config" {
        Result.err e => Result.err e,
        Result.ok cj => session_config_step obj cj,
    }

pub def Session.deserialize_json (j : Json) : Result String Session :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj => session_of_object obj,
    }

def save_at (s : Session) (p : Path) : IO (Result String Unit) := do {
    IO.write_file p (Json.to_string (Session.serialize_json s));
    return (Result.ok unit)
}

def save_failed (e : String) : IO (Result String Unit) := do {
    return (Result.err e)
}

/// Checkpoint a session to `file` as JSON. Overwrites; a session file
/// is the LATEST state of a run, not an append-only log.
pub def Session.save (s : Session) (file : String) : IO (Result String Unit) :=
    match Path.of file {
        Result.err e => save_failed e,
        Result.ok p => save_at s p,
    }

def load_missing (path : String) : IO (Result String Session) := do {
    return (Result.err (String.concat "session file not found: " path))
}

def load_read (p : Path) : IO (Result String Session) := do {
    let text <- IO.read_file p;
    return (load_parse text)
}

def load_parse (text : String) : Result String Session :=
    match Json.parse text {
        Result.err pe => Result.err (Json.ParseError.to_string pe),
        Result.ok j => Session.deserialize_json j,
    }

def load_at (p : Path) : IO (Result String Session) := do {
    let exists <- IO.file_exists p;
    if exists then load_read p else load_missing (Path.to_string p)
}

/// Resume: load a session from `file`. A caller resuming a run pairs
/// the loaded session with a FRESH tool registry -- the registry is
/// closures and never round-trips; `session.tools` records what the
/// run HAD, so a mismatch with the fresh registry is the caller's
/// signal to re-mount what the transcript references.
pub def Session.load (file : String) : IO (Result String Session) :=
    match Path.of file {
        Result.err e => load_failed e,
        Result.ok p => load_at p,
    }

def load_failed (e : String) : IO (Result String Session) := do {
    return (Result.err e)
}
