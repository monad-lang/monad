/// The mock wire -- agent-skills.md Design 3's "scripted `List Turn`; the
/// only backend the loop tests need". A scripted provider serves one
/// `Turn` per model call from a JSON file, so the ENTIRE tool-use loop
/// (encode, dispatch, tool_result, re-ask, final answer) is testable
/// with no network, no provider, and no TLS -- the offline stand-in for
/// the env-gated Ollama e2e.
///
/// The script is a JSON array of serialized `Turn`s (the same codec a
/// session file uses). The turn served is indexed by the number of
/// assistant messages already in the history: every model call appends
/// exactly one assistant message, so each call advances the script by
/// exactly one, statelessly -- the provider itself holds no cursor.
///
/// The script path is `SHUTTLE_MOCK_TURNS` when set, else a PID-qualified
/// default (`/tmp/shuttle_mock_turns_<pid>.json`). A test process cannot
/// set its own environment, so the default is the path tests write; a
/// human driver can point the env var anywhere.
use json::json {Json, Json.parse, Json.ParseError.to_string, Json.get_array}
use shuttle::message {Message, Turn}
use shuttle::message_types {Role}
use shuttle::tool {ToolSpec}
use init::transformers {ResultT}
use std::io {IO.get_env, IO.read_file, IO.file_exists}
use std::path {Path.of, Path.to_string}
use std::process {process_id}

def default_script_path : String :=
    String.concat "/tmp/shuttle_mock_turns_" (String.concat (I64.to_string process_id) ".json")

def mock_script_path : IO String := do {
    let env <- IO.get_env "SHUTTLE_MOCK_TURNS";
    return (match env {
        Option.some p => p,
        Option.none => default_script_path,
    })
}

def is_assistant (m : Message) : Bool :=
    match m {
        { role, .. } => match role { Role.assistant => true, _ => false },
    }

#[partial]
def assistant_count (history : List Message) : I64 :=
    match history {
        List.empty => 0,
        List.cons m rest => (if is_assistant m then 1 else 0) + assistant_count rest,
    }

def mock_missing (path : String) : IO (Result String String) := do {
    return (Result.err (String.concat "mock wire: no script at " (String.concat path " (write a JSON array of serialized Turns)")))
}

def mock_read_at (p : Path) : IO (Result String String) := do {
    let text <- IO.read_file p;
    return (Result.ok text)
}

def mock_load_at (p : Path) : IO (Result String String) := do {
    let exists <- IO.file_exists p;
    if exists then mock_read_at p else mock_missing (Path.to_string p)
}

def mock_load (file : String) : IO (Result String String) :=
    match Path.of file {
        Result.err e => mock_load_err e,
        Result.ok p => mock_load_at p,
    }

def mock_load_err (e : String) : IO (Result String String) := do {
    return (Result.err e)
}

#[partial]
def mock_pick_walk (turns : List Json) (pos : I64) (index : I64) : Result String Turn :=
    match turns {
        List.empty => Result.err (String.concat "mock wire: script has no turn at index " (I64.to_string index)),
        List.cons j rest =>
            if pos == index then Turn.deserialize_json j
            else mock_pick_walk rest (pos + 1) index,
    }

def mock_pick (j : Json) (index : I64) : Result String Turn :=
    match Json.get_array j {
        Result.err e => Result.err e,
        Result.ok turns => mock_pick_walk turns 0 index,
    }

def mock_parse (text : String) (index : I64) : Result String Turn :=
    match Json.parse text {
        Result.err pe => Result.err (Json.ParseError.to_string pe),
        Result.ok j => mock_pick j index,
    }

def mock_decode (loaded : Result String String) (index : I64) : Result String Turn :=
    match loaded {
        Result.err e => Result.err e,
        Result.ok text => mock_parse text index,
    }

/// Serve the next scripted turn. `tools` is accepted and ignored: the
/// script author decides what the model "asks for", including tool_use
/// blocks naming tools the caller did not register (the loop's
/// unknown-tool path is part of what this wire can exercise).
/// `ResultT.mk` around a plain IO do-block -- the same shape as
/// `loop.mo`'s `run_tool`, and NOT a `ResultT` do-block: its binds
/// dispatch `Monad (ResultT String IO)` at run time, which the test
/// driver's synthesis failed to resolve for this module.
pub def Mock.send (tools : List ToolSpec) (history : List Message) : ResultT String IO Turn :=
    ResultT.mk (do {
        let file <- mock_script_path;
        let loaded <- mock_load file;
        return (mock_decode loaded (assistant_count history))
    })
