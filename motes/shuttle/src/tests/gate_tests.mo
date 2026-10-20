/// The approval-gate seam tests -- weaver.md Phase 1's regression gate:
/// the loop consults a `Gate` before every `impl.run`, a denial is an
/// `is_error` tool_result the model sees (NOT a loop-killing
/// `Result.err`), and an `always` answer is cached per capability so
/// the gate is asked once per capability, not once per pick. All
/// offline against the scripted mock wire (`wire/mock.mo`), the same
/// PID-path contract `mock_e2e_tests.mo` documents: a test process
/// cannot set its own environment, so the wire's PID-qualified default
/// script path is the contract.
use std::test {Test.write_fixture, Test.append_fixture, Test.read_fixture_or}
use init::transformers {ResultT}
use shuttle::message_types {Role, Content, StopReason}
use shuttle::message {Message, Usage, Turn}
use shuttle::provider {ProviderConfig, Wire, Provider.silent_emit}
use shuttle::registry {ToolRegistry}
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability, Pick, Approval, Gate}
use shuttle::loop {Loop.run}
use json::json {Json, Json.make_str, Json.make_array, Json.to_string}
use std::process {process_id}
use std::list {List.length}

def script_path : String :=
    String.concat "/tmp/shuttle_mock_turns_" (String.concat (I64.to_string process_id) ".json")

// ── The scripted provider's two turns ──────────────────────────────────

def scripted_input : Json := Json.make_str "payload"

def turn_1_usage : Usage := { input_tokens := 1, output_tokens := 10, cached_tokens := 0 }

def turn_2_usage : Usage := { input_tokens := 2, output_tokens := 20, cached_tokens := 0 }

def final_text : String := "the stamp went through"

def final_turn_message : Message :=
    { role := Role.assistant, content := [Content.text final_text] }

def scripted_final_turn : Turn := { message := final_turn_message, usage := turn_2_usage, stop := StopReason.end_turn }

/// The two-pick turn: one assistant message asking for `stamp` twice,
/// Design 3's parallel-tool-call shape -- what makes the
/// ask-once-per-capability short-circuit observable in ONE turn.
def two_pick_message : Message :=
    { role := Role.assistant, content := [
        Content.tool_use "call_1" "stamp" scripted_input,
        Content.tool_use "call_2" "stamp" scripted_input,
    ] }

def scripted_two_pick_turn : Turn := { message := two_pick_message, usage := turn_1_usage, stop := StopReason.tool_use_stop }

// ── The `stamp` tool: a write-capability tool with no side effects ────

def stamp_spec : ToolSpec := { name := "stamp", description := "stamps its input", schema := Json.make_null }

def stamp_run (id : String) (input : Json) : ResultT String IO Content :=
    ResultT.mk (return (Result.ok (Content.tool_result id "STAMPED" false)))

def stamp_impl : ToolImpl := { spec := stamp_spec, cap := Capability.write, run := stamp_run }

def gate_registry : ToolRegistry := ToolRegistry.register stamp_impl ToolRegistry.empty

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "SHUTTLE_UNUSED_KEY", max_tokens := 8, wire := Wire.mock }

def user_message : Message := { role := Role.user, content := [Content.text "please stamp"] }

// ── Script writing ─────────────────────────────────────────────────────

def write_script (turns : List Json) : IO Unit := do {
    let script : Json := Json.make_array turns;
    do { let _w <- Test.write_fixture (Path.path script_path) (Json.to_string script); return unit }
}

/// Turn 1 asks for `stamp` once; turn 2 is the final answer.
def one_pick_message : Message :=
    { role := Role.assistant, content := [Content.tool_use "call_1" "stamp" scripted_input] }

def scripted_one_pick_turn : Turn :=
    { message := one_pick_message, usage := turn_1_usage, stop := StopReason.tool_use_stop }

def one_pick_script : IO Unit :=
    write_script [
        Turn.serialize_json scripted_one_pick_turn,
        Turn.serialize_json scripted_final_turn,
    ]

/// Turn 1 asks for `stamp` twice in one message; turn 2 is the final answer.
def two_pick_script : IO Unit :=
    write_script [
        Turn.serialize_json scripted_two_pick_turn,
        Turn.serialize_json scripted_final_turn,
    ]

// ── The tap file: the gate's ask-count record ──────────────────────────
// The `mock_e2e_tests.mo` read-modify-write tap pattern: append per ask,
// read whole at the end -- "x" is one ask, "xx" is two. There is no
// `IORef`; a single-threaded test process makes the race moot.

def tap_path : String :=
    String.concat "/tmp/shuttle_gate_tap_" (String.concat (I64.to_string process_id) ".txt")

def gate_tap : IO Unit :=
    do { let _w <- Test.append_fixture (Path.path tap_path) "x"; return unit }

def reset_tap : IO Unit :=
    do { let _w <- Test.write_fixture (Path.path tap_path) ""; return unit }

def read_tap : IO String :=
    Test.read_fixture_or (Path.path tap_path) "TAP-READ-FAILED"

// ── The gates under test ────────────────────────────────────────────────

/// Denies every pick, with a reason the model must be able to read back.
def deny_ask (p : Pick) : IO Approval :=
    return (Approval.deny "not allowed in this test")

def deny_gate : Gate := { ask := deny_ask, precheck := fn (_ : Pick) => IO.pure Option.none }

/// Answers `once` for every pick and records each ask in the tap.
def once_ask (p : Pick) : IO Approval := do {
    let _ <- gate_tap;
    return Approval.once
}

def once_gate : Gate := { ask := once_ask, precheck := fn (_ : Pick) => IO.pure Option.none }

/// Answers `always` for every pick and records each ask in the tap --
/// the loop's per-capability cache is what must keep the tap at one "x".
def always_ask (p : Pick) : IO Approval := do {
    let _ <- gate_tap;
    return Approval.always
}

def always_gate : Gate := { ask := always_ask, precheck := fn (_ : Pick) => IO.pure Option.none }

// ── Assertions ─────────────────────────────────────────────────────────

def content_mentions (needle : String) (c : Content) : Bool :=
    match c {
        Content.text s => String.contains s needle,
        Content.tool_result _ output _ => String.contains output needle,
        _ => false,
    }

def message_mentions (needle : String) (m : Message) : Bool :=
    match m { { content, .. } => any_mentions needle content }

#[partial]
def any_mentions (needle : String) (cs : List Content) : Bool :=
    match cs {
        List.empty => false,
        List.cons c rest => content_mentions needle c || any_mentions needle rest,
    }

#[partial]
def history_mentions (needle : String) (history : List Message) : Bool :=
    match history {
        List.empty => false,
        List.cons m rest => message_mentions needle m || history_mentions needle rest,
    }

// ── The tests ──────────────────────────────────────────────────────────

/// A denial is an `is_error` tool_result the model sees and the run
/// continues: turn 2 still arrives, the final answer is appended, and
/// the transcript carries the `denied:` reason.
#[test]
def test_deny_gate_yields_is_error_tool_result_the_model_sees : IO Bool := do {
    let _ <- one_pick_script;
    let r <- ResultT.run (Loop.run mock_config gate_registry "You are a test harness." [user_message] 6 Provider.silent_emit deny_gate);
    return (match r {
        Result.err _ => false,
        Result.ok s =>
            s.turns == 2
                && history_mentions "denied: not allowed in this test" s.history
                && history_mentions final_text s.history,
    })
}

/// `once` asks the gate once PER PICK: two parallel `stamp` calls in one
/// turn means two asks (tap "xx") and both tools ran.
#[test]
def test_once_gate_asks_once_per_pick : IO Bool := do {
    let _ <- two_pick_script;
    let _ <- reset_tap;
    let r <- ResultT.run (Loop.run mock_config gate_registry "You are a test harness." [user_message] 6 Provider.silent_emit once_gate);
    match r {
        Result.err _ => return false,
        Result.ok s => do {
            let tap <- read_tap;
            return (tap == "xx"
                && s.turns == 2
                && history_mentions "STAMPED" s.history
                && Bool.not (history_mentions "denied:" s.history))
        }
    }
}

/// `always` is cached per CAPABILITY: the second `stamp` pick in the same
/// turn never reaches the gate (tap "x"), and both tools still ran.
#[test]
def test_always_gate_short_circuits_the_second_pick : IO Bool := do {
    let _ <- two_pick_script;
    let _ <- reset_tap;
    let r <- ResultT.run (Loop.run mock_config gate_registry "You are a test harness." [user_message] 6 Provider.silent_emit always_gate);
    match r {
        Result.err _ => return false,
        Result.ok s => do {
            let tap <- read_tap;
            return (tap == "x"
                && s.turns == 2
                && history_mentions "STAMPED" s.history
                && Bool.not (history_mentions "denied:" s.history))
        }
    }
}

/// `Gate.auto`, the headless default, never blocks: the pick runs with
/// no observable denial and the session shape matches the ungated loop.
#[test]
def test_auto_gate_runs_every_pick : IO Bool := do {
    let _ <- two_pick_script;
    let r <- ResultT.run (Loop.run mock_config gate_registry "You are a test harness." [user_message] 6 Provider.silent_emit Gate.auto);
    return (match r {
        Result.err _ => false,
        Result.ok s =>
            s.turns == 2
                && history_mentions "STAMPED" s.history
                && Bool.not (history_mentions "denied:" s.history)
                && List.length s.history == 4,
    })
}
