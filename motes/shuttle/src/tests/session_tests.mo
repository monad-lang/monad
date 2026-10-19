/// Tests for `motes/shuttle/src/session.mo` -- Phase 5's checkpoint
/// round-trip: save a session to a PID-qualified scratch file, load it
/// back, and assert the transcript (including a thinking block's
/// API-authored signature), the config, the turn count and the
/// accumulated usage all survive. A missing file is a named error.
use std::test {Test.read_fixture_or}
use shuttle::session {Session}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::tool {ToolSpec}
use shuttle::message {Message, Usage}
use shuttle::message_types {Role, Content}
use json::json {Json}
use std::process {process_id}
use std::list {List.any, List.length}

def session_path : String :=
    String.concat "/tmp/shuttle_session_test_" (String.concat (I64.to_string process_id) ".json")

def missing_path : String :=
    String.concat "/tmp/shuttle_session_test_missing_" (String.concat (I64.to_string process_id) ".json")

def test_config : ProviderConfig :=
    { base_url := "http://localhost:11434", model := "test-model", api_key_env := "SHUTTLE_UNUSED_KEY", max_tokens := 64, wire := Wire.mock }

def echo_spec : ToolSpec := { name := "echo", description := "echoes its input", schema := Json.make_null }

def test_tools : List ToolSpec := [echo_spec]

def user_msg : Message := { role := Role.user, content := [Content.text "please echo"] }

def thinking_msg : Message := { role := Role.assistant, content := [Content.thinking "let me think" "sig-abc123"] }

def test_history : List Message := [user_msg, thinking_msg]

def test_spent : Usage := { input_tokens := 3, output_tokens := 30, cached_tokens := 1 }

def test_session : Session :=
    { config := test_config, system_prompt := "You are a test.", tools := test_tools, history := test_history, turns := 2, spent := test_spent }

def content_keeps_signed_thinking (c : Content) : Bool :=
    match c {
        Content.thinking s signature => s == "let me think" && signature == "sig-abc123",
        _ => false,
    }

#[partial]
def history_keeps_signed_thinking (history : List Message) : Bool :=
    match history {
        List.empty => false,
        List.cons m rest =>
            match m {
                { content, .. } => List.any content_keeps_signed_thinking content || history_keeps_signed_thinking rest,
            },
    }

def roundtrip_loaded (loaded : Result String Session) : Bool :=
    match loaded {
        Result.err _ => false,
        Result.ok s =>
            s.system_prompt == "You are a test."
                && s.turns == 2
                && s.spent.input_tokens == 3 && s.spent.output_tokens == 30 && s.spent.cached_tokens == 1
                && s.config.model == "test-model"
                && List.length s.history == 2
                && history_keeps_signed_thinking s.history,
    }

def roundtrip_result (saved : Result String Unit) (loaded : Result String Session) : Bool :=
    match saved {
        Result.err _ => false,
        Result.ok _ => roundtrip_loaded loaded,
    }

#[test]
def test_session_save_load_roundtrip : IO Bool := do {
    let saved <- Session.save test_session session_path;
    let loaded <- Session.load session_path;
    return (roundtrip_result saved loaded)
}

#[test]
def test_session_load_missing_file_is_an_error : IO Bool := do {
    let loaded <- Session.load missing_path;
    return (match loaded {
        Result.err e => String.contains e "not found",
        Result.ok _ => false,
    })
}

#[test]
def test_session_codec_roundtrips_in_memory : Bool :=
    match Session.deserialize_json (Session.serialize_json test_session) {
        Result.err _ => false,
        Result.ok s => s.turns == 2 && s.config.model == "test-model" && List.length s.history == 2,
    }

// ── Phase 10: a direct key never crosses the save seam ──────────────────

/// A config carrying a DIRECT key -- what `[api_keys]` in Weaver's
/// settings files resolves to. The trap (weaver.md Design 8): a
/// `Session.save` file lands in /tmp and project dirs, so the key
/// material must stay out of it -- save keeps only `api_key_env`, and
/// a resumed session re-resolves its key from settings/env at startup.
def keyed_config : ProviderConfig := { base_url := "http://localhost:11434", model := "keyed-model", api_key_env := "SHUTTLE_UNUSED_KEY", api_key := Option.some "sk-redacted-test-key-material", max_tokens := 64, wire := Wire.mock }

def keyed_session : Session := { test_session with config := keyed_config }

def keyed_path : String :=
    String.concat "/tmp/shuttle_session_test_keyed_" (String.concat (I64.to_string process_id) ".json")

/// A raw text read: the redaction test greps the saved file itself,
/// not a re-decode of it.
def read_text (path : String) : IO String :=
    Test.read_fixture_or path ""

/// The pinned redaction: a session whose config carries a direct key
/// saves to a file that contains no key material.
#[test]
def test_session_save_omits_direct_api_key : IO Bool := do {
    let saved <- Session.save keyed_session keyed_path;
    let text <- read_text keyed_path;
    return (match saved {
        Result.err _ => false,
        Result.ok _ => Bool.not (String.contains text "sk-redacted-test-key-material"),
    })
}

/// The codec agrees in memory: a round-tripped config carries no
/// direct key, whatever a hand-edited file might try to inject.
#[test]
def test_config_codec_drops_direct_key : Bool :=
    match ProviderConfig.deserialize_json (ProviderConfig.serialize_json keyed_config) {
        Result.err _ => false,
        Result.ok c => match c.api_key {
            Option.some _ => false,
            Option.none => true,
        },
    }
