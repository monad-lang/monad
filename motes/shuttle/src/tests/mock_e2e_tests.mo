/// The offline loop e2e -- the scripted mock wire (`wire/mock.mo`)
/// driving the ENTIRE indexed tool-use loop with no network: script
/// turn 1 asks for the `echo` tool, the loop dispatches it through a
/// real `ToolImpl`, script turn 2 is the final answer. This is the
/// Phase 5 regression gate for the `Agent` monad reimplementations
/// (`agent.mo`/`loop.mo`), and it is what makes every future loop
/// change testable without a live provider.
///
/// The script is written to the mock wire's PID-qualified default path
/// (`/tmp/shuttle_mock_turns_<pid>.json`) -- a test process cannot set
/// its own environment, so that default is the contract; see
/// `wire/mock.mo`'s header. The fixture path here computes the same
/// string, so the two must move together.
use init::transformers {ResultT}
use shuttle::message_types {Role, Content, StopReason}
use shuttle::message {Message, Usage, Turn}
use shuttle::provider {ProviderConfig, Wire, Provider.silent_emit}
use shuttle::registry {ToolRegistry}
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::loop {Loop.run}
use shuttle::session {Session}
use json::json {Json, Json.make_array, Json.make_str, Json.to_string}
use std::io {IO.write_file, IO.read_file}
use std::path {Path.of}
use std::process {process_id}
use std::list {List.any, List.length}

def sentinel : String := "SHUTTLE_MOCK_SENTINEL_7"

def script_path : String :=
    String.concat "/tmp/shuttle_mock_turns_" (String.concat (I64.to_string process_id) ".json")

// ── The scripted provider's two turns ──────────────────────────────────

def scripted_input : Json := Json.make_str "payload"

def turn_1_message : Message :=
    { role := Role.assistant, content := [Content.tool_use "call_1" "echo" scripted_input] }

def turn_1_usage : Usage := { input_tokens := 1, output_tokens := 10, cached_tokens := 0 }

def scripted_turn_1 : Turn := { message := turn_1_message, usage := turn_1_usage, stop := StopReason.tool_use_stop }

def turn_2_message : Message :=
    { role := Role.assistant, content := [Content.text (String.concat "the echo tool said: " sentinel)] }

def turn_2_usage : Usage := { input_tokens := 2, output_tokens := 20, cached_tokens := 0 }

def scripted_turn_2 : Turn := { message := turn_2_message, usage := turn_2_usage, stop := StopReason.end_turn }

def mock_script : Json :=
    Json.make_array [Turn.serialize_json scripted_turn_1, Turn.serialize_json scripted_turn_2]

def write_script : IO Unit := do {
    match Path.of script_path {
        Result.ok p => IO.write_file p (Json.to_string mock_script),
        Result.err _ => return unit,
    }
}

// ── The echo tool: a real ToolImpl, the only moving part the loop
// owns besides the provider seam itself. ──────────────────────────

def echo_spec : ToolSpec := { name := "echo", description := "echoes its JSON input back as text", schema := Json.make_null }

def echo_run (id : String) (input : Json) : ResultT String IO Content :=
    ResultT.mk (return (Result.ok (Content.tool_result id (Json.to_string input) false)))

def echo_impl : ToolImpl := { spec := echo_spec, run := echo_run }

def mock_registry : ToolRegistry := ToolRegistry.register echo_impl ToolRegistry.empty

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "SHUTTLE_UNUSED_KEY", max_tokens := 8, wire := Wire.mock }

def user_message : Message := { role := Role.user, content := [Content.text "please echo"] }

// ── Assertions ─────────────────────────────────────────────────────────

def content_mentions (needle : String) (c : Content) : Bool :=
    match c {
        Content.text s => String.contains s needle,
        Content.tool_result _ output _ => String.contains output needle,
        _ => false,
    }

def message_mentions (needle : String) (m : Message) : Bool :=
    match m { { content, .. } => List.any (content_mentions needle) content }

#[partial]
def history_mentions (needle : String) (history : List Message) : Bool :=
    match history {
        List.empty => false,
        List.cons m rest => message_mentions needle m || history_mentions needle rest,
    }

/// The loop's Phase 5 accounting: the session's `spent` is the sum of
/// both scripted turns' usage, and `turns` counts the model calls.
def session_shape_ok (s : Session) : Bool :=
    s.turns == 2
        && s.spent.input_tokens == 3
        && s.spent.output_tokens == 30
        && List.length s.history == 4
        && history_mentions "payload" s.history
        && history_mentions sentinel s.history

#[test]
def test_mock_loop_dispatches_tool_and_finishes : IO Bool := do {
    write_script;
    let r <- ResultT.run (Loop.run mock_config mock_registry "You are a test harness." [user_message] 6 Provider.silent_emit);
    return (match r {
        Result.ok s => session_shape_ok s,
        Result.err _ => false,
    })
}

/// The turn-cap end, offline: a budget of ONE against the tool_use
/// script turn stops the run as a normal `Result.ok` -- the session is
/// kept with `turns` at the cap, and the history's LAST message is the
/// tool result (the shape the CLI's cap-stop note keys off). The old
/// loop errored here, losing the session.
#[test]
def test_mock_loop_cap_ends_normally_with_the_session : IO Bool := do {
    write_script;
    let r <- ResultT.run (Loop.run mock_config mock_registry "You are a test harness." [user_message] 1 Provider.silent_emit);
    return (match r {
        Result.err _ => false,
        Result.ok s => s.turns == 1 && last_is_tool s.history,
    })
}

#[partial]
def last_is_tool (history : List Message) : Bool :=
    match history {
        List.empty => false,
        List.cons m rest =>
            if List.length rest == 0 then is_tool_message m else last_is_tool rest,
    }

def is_tool_message (m : Message) : Bool :=
    match m.role {
        Role.tool => true,
        _ => false,
    }

/// The unknown-tool path, offline: the script asks for a tool the
/// registry does not have, and the loop must answer with an
/// `is_error` tool_result naming it -- not abort the run.
def unknown_tool_message : Message :=
    { role := Role.assistant, content := [Content.tool_use "call_9" "not_a_tool" scripted_input] }

def scripted_unknown_turn : Turn := {
    message := unknown_tool_message,
    usage := turn_1_usage,
    stop := StopReason.tool_use_stop,
}

def mock_script_with_unknown : Json :=
    Json.make_array [Turn.serialize_json scripted_unknown_turn, Turn.serialize_json scripted_turn_2]

def write_script_with_unknown : IO Unit := do {
    match Path.of script_path {
        Result.ok p => IO.write_file p (Json.to_string mock_script_with_unknown),
        Result.err _ => return unit,
    }
}

#[test]
def test_mock_loop_answers_unknown_tool_with_is_error : IO Bool := do {
    write_script_with_unknown;
    let r <- ResultT.run (Loop.run mock_config mock_registry "You are a test harness." [user_message] 6 Provider.silent_emit);
    return (match r {
        Result.ok s => history_mentions "unknown tool: not_a_tool" s.history,
        Result.err _ => false,
    })
}

// ── Streaming through the loop, offline ────────────────────────────────

/// The tap-file `emit` sink, `openai/src/tests/stream_tests.mo`'s
/// pattern: append the fragment to the tap. Read-modify-write because
/// `std::io` has no append mode and no `IORef` -- a single-threaded
/// test makes the race moot.
def tap_path : String :=
    String.concat "/tmp/shuttle_mock_tap_" (String.concat (I64.to_string process_id) ".txt")

def emit_tap (t : String) : IO Unit :=
    match Path.of tap_path {
        Result.ok p =>
            Monad.bind (IO.read_file p) (fn old => IO.write_file p (String.concat old t)),
        Result.err _ => return unit,
    }

def reset_tap : IO Unit :=
    match Path.of tap_path {
        Result.ok p => IO.write_file p "",
        Result.err _ => return unit,
    }

def read_tap : IO String :=
    match Path.of tap_path {
        Result.ok p => IO.read_file p,
        Result.err _ => return "TAP-READ-FAILED",
    }

def turn_2_text : String := String.concat "the echo tool said: " sentinel

/// The emission contract, end to end through the whole loop: the
/// tool_use turn emits NOTHING (only text reaches `emit`), the final
/// turn's text is emitted exactly once and whole, and nothing else.
/// The mock wire's one-shot-per-turn emission makes "exactly once"
/// checkable as plain string equality against the tap.
#[test]
def test_mock_loop_emits_text_turn_only : IO Bool := do {
    write_script;
    reset_tap;
    let r <- ResultT.run (Loop.run mock_config mock_registry "You are a test harness." [user_message] 6 emit_tap);
    match r {
        Result.err _ => return false,
        Result.ok _ => do {
            let tap <- read_tap;
            return (tap == turn_2_text)
        },
    }
}

/// The regression guard for the sink being observation-only: a run
/// with a live `emit` and a silent one must produce byte-identical
/// sessions -- the callback contract must never leak into the loop's
/// own accounting, history or serialization.
#[test]
def test_mock_loop_streamed_and_silent_sessions_identical : IO Bool := do {
    write_script;
    reset_tap;
    let r1 <- ResultT.run (Loop.run mock_config mock_registry "You are a test harness." [user_message] 6 emit_tap);
    match r1 {
        Result.err _ => return false,
        Result.ok s1 => do {
            let r2 <- ResultT.run (Loop.run mock_config mock_registry "You are a test harness." [user_message] 6 Provider.silent_emit);
            match r2 {
                Result.err _ => return false,
                Result.ok s2 =>
                    let j1 : String := Json.to_string (Session.serialize_json s1) in
                    let j2 : String := Json.to_string (Session.serialize_json s2) in
                    return (j1 == j2),
            }
        }
    }
}
