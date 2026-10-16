/// Weaver's offline e2e -- weaver.md Phase 3: the whole dumb loop against
/// the scripted mock wire, through `Dumb.run`'s own read/write seams. The
/// input stream is a JSON array of lines served one per read through a
/// read-modify-write cursor file (no `IORef`; the single-threaded race is
/// moot, shuttle's tap pattern); the gate answers through the SAME seam
/// the loop reads, so approvals are scriptable without a tty.
///
/// One scripted session exercises the Phase 3 spine end to end: a
/// manual-mode approval answered `y` (the tool runs, `STAMPED` lands in
/// the transcript), one answered `n` (a `denied:` tool_result the model
/// sees), `/mode plan` mid-session, and a plan-mode pick refused by the
/// POLICY before any input is consumed -- the cursor is the proof it
/// never reached the read seam.
use init::transformers {ResultT}
use shuttle::agent {RunState}
use shuttle::context {usage_zero}
use shuttle::gate {Capability, Gate}
use shuttle::message {Message, Usage, Turn}
use shuttle::message_types {Role, Content, StopReason}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use shuttle::tool {ToolSpec, ToolImpl}
use weaver::commands {State}
use weaver::dumb {Dumb.run}
use weaver::policy {Mode}
use json::json {Json, Json.parse, Json.get_array, Json.get_str, Json.make_str, Json.make_array, Json.make_null, Json.to_string}
use parsec::number {parse_i64}
use std::io {IO.write_file, IO.read_file, IO.file_exists}
use std::path {Path.of}
use std::process {process_id}

// ── The PID-qualified file set ─────────────────────────────────────────
// Same contract as shuttle's mock tests: a test process cannot set its
// own environment, so the wire's PID-default script path is the one this
// file writes.

def pid : String := I64.to_string process_id

def script_path : String :=
    String.concat "/tmp/shuttle_mock_turns_" (String.concat pid ".json")

def inputs_path : String :=
    String.concat "/tmp/weaver_inputs_" (String.concat pid ".json")

def cursor_path : String :=
    String.concat "/tmp/weaver_cursor_" (String.concat pid ".txt")

def tap_path : String :=
    String.concat "/tmp/weaver_tap_" (String.concat pid ".txt")

def write_text (path : String) (text : String) : IO Unit :=
    match Path.of path {
        Result.ok p => IO.write_file p text,
        Result.err _ => IO.pure unit,
    }

// ── The scripted wire: three tool asks, three answers ─────────────────

def scripted_input : Json := Json.make_str "payload"

def usage_n (n : I64) : Usage := { input_tokens := n, output_tokens := n * 10, cached_tokens := 0 }

def tool_turn_message (call_id : String) : Message :=
    { role := Role.assistant, content := [Content.tool_use call_id "stamp" scripted_input] }

def text_turn_message (s : String) : Message :=
    { role := Role.assistant, content := [Content.text s] }

def tool_turn (call_id : String) (n : I64) : Turn :=
    { message := tool_turn_message call_id, usage := usage_n n, stop := StopReason.tool_use_stop }

def text_turn (s : String) (n : I64) : Turn :=
    { message := text_turn_message s, usage := usage_n n, stop := StopReason.end_turn }

/// Six turns, indexed by assistant count: each `go` is one tool ask plus
/// one final answer, and the whole session spans three inputs.
def write_wire_script : IO Unit :=
    write_text script_path (Json.to_string (Json.make_array [
        Turn.serialize_json (tool_turn "call_1" 1),
        Turn.serialize_json (text_turn "done one" 2),
        Turn.serialize_json (tool_turn "call_3" 3),
        Turn.serialize_json (text_turn "done two" 4),
        Turn.serialize_json (tool_turn "call_5" 5),
        Turn.serialize_json (text_turn "done three" 6),
    ]))

// ── The scripted input stream ──────────────────────────────────────────
// Lines in file order: user text, gate answers and slash commands all
// ride the one seam, so "what the user typed" and "what they answered"
// are indistinguishable to the loop -- exactly as a tty is.

def input_lines : List String := ["go", "y", "again", "n", "/mode plan", "go"]

def write_inputs : IO Unit :=
    write_text inputs_path
        (Json.to_string (Json.make_array (List.map (fn (s : String) => Json.make_str s) input_lines)))

/// The read seam: serve line `cursor`, then store `cursor + 1`. Past the
/// end is EOF (`Option.none`), the loop's own session end. The `Unit`
/// parameter is load-bearing: a naked `IO (Option String)` value is
/// performed ONCE, at the point it is passed (the compiled backend's
/// `RawIO.io` is a strict box), so the parameterized def re-evaluates
/// this body on every call.
def scripted_read (u : Unit) : IO (Option String) := do {
    let idx <- read_cursor;
    serve idx
}

def read_cursor : IO I64 :=
    match Path.of cursor_path {
        Result.ok p => read_cursor_at p,
        Result.err _ => IO.pure 0,
    }

def read_cursor_at (p : Path) : IO I64 := do {
    let exists <- IO.file_exists p;
    cursor_step p exists
}

def cursor_step (p : Path) (exists : Bool) : IO I64 :=
    if Bool.not exists then IO.pure 0 else read_cursor_text p

def read_cursor_text (p : Path) : IO I64 := do {
    let text <- IO.read_file p;
    return (cursor_of_text text)
}

def cursor_of_text (text : String) : I64 :=
    match parse_i64 (String.trim text) {
        Option.some n => n,
        Option.none => 0,
    }

def serve (idx : I64) : IO (Option String) :=
    match Path.of inputs_path {
        Result.ok p => serve_at p idx,
        Result.err _ => IO.pure Option.none,
    }

def serve_at (p : Path) (idx : I64) : IO (Option String) := do {
    let text <- IO.read_file p;
    serve_input text idx
}

def serve_input (text : String) (idx : I64) : IO (Option String) :=
    match input_of text idx {
        Option.none => IO.pure Option.none,
        Option.some s => advance idx s,
    }

def advance (idx : I64) (s : String) : IO (Option String) := do {
    let _ <- write_text cursor_path (I64.to_string (idx + 1));
    IO.pure (Option.some s)
}

def input_of (text : String) (idx : I64) : Option String :=
    match Json.parse text {
        Result.err _ => Option.none,
        Result.ok j => match Json.get_array j {
            Result.err _ => Option.none,
            Result.ok xs => input_at_walk xs 0 idx,
        },
    }

#[partial]
def input_at_walk (xs : List Json) (pos : I64) (idx : I64) : Option String :=
    match xs {
        List.empty => Option.none,
        List.cons j rest =>
            if pos == idx
            then match Json.get_str j { Result.ok s => Option.some s, Result.err _ => Option.none }
            else input_at_walk rest (pos + 1) idx,
    }

// ── The write seam: one tap file ───────────────────────────────────────

/// Everything the loop prints -- prompt lines, approval prompts, command
/// output, streamed turn text -- appended to one file, read whole at the
/// end. The same read-modify-write pattern as the cursor.
def tap_write (s : String) : IO Unit :=
    match Path.of tap_path {
        Result.ok p => tap_at p s,
        Result.err _ => IO.pure unit,
    }

def tap_at (p : Path) (s : String) : IO Unit :=
    Monad.bind (IO.read_file p) (fn old => IO.write_file p (String.concat old s))

def read_tap : IO String :=
    match Path.of tap_path {
        Result.ok p => IO.read_file p,
        Result.err _ => IO.pure "TAP-READ-FAILED",
    }

// ── The `stamp` tool: write-cap, side-effect-free (shuttle gate_tests') ──

def stamp_spec : ToolSpec := { name := "stamp", description := "stamps its input", schema := Json.make_null }

def stamp_run (id : String) (input : Json) : ResultT String IO Content :=
    ResultT.mk (return (Result.ok (Content.tool_result id "STAMPED" false)))

def stamp_impl : ToolImpl := { spec := stamp_spec, cap := Capability.write, run := stamp_run }

def stamp_registry : ToolRegistry := ToolRegistry.register stamp_impl ToolRegistry.empty

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY", max_tokens := 8, wire := Wire.mock }

// ── The initial state (main.mo's shape, offline) ───────────────────────

def budget : I64 := 6

def fresh_session : Session := {
    config := mock_config,
    system_prompt := "You are a test harness.",
    tools := ToolRegistry.specs stamp_registry,
    history := List.empty,
    turns := 0,
    spent := usage_zero,
}

def initial_run : RunState := {
    session := fresh_session,
    reg := stamp_registry,
    turns_left := budget,
    emit := tap_write,
    gate := Gate.auto,
    always := List.empty,
}

def initial_state : State := {
    run := initial_run,
    mode := Mode.manual,
    provider := "mock",
    budget := budget,
    quit := false,
}

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

def mode_is_plan (m : Mode) : Bool :=
    match m { Mode.plan => true, _ => false }

/// The whole session's shape: the `/mode` took, EOF ended it (not
/// `/quit`), six model calls across three inputs (the session and its
/// accounting persisted), every final answer arrived, both gate answers
/// reached the transcript as `denied:`/`STAMPED` tool_results, the plan
/// refusal is the policy's own reason, the cursor proves the plan pick
/// consumed no input, and the tap proves the gate actually prompted.
def final_state_ok (st : State) (cursor : I64) (tap : String) : Bool :=
    mode_is_plan st.mode
        && Bool.not st.quit
        && st.run.session.turns == budget
        && st.run.session.spent.input_tokens == 21
        && st.run.session.spent.output_tokens == 210
        && history_mentions "STAMPED" st.run.session.history
        && history_mentions "denied: declined by user" st.run.session.history
        && history_mentions "denied: plan mode: only read tools run" st.run.session.history
        && history_mentions "done one" st.run.session.history
        && history_mentions "done two" st.run.session.history
        && history_mentions "done three" st.run.session.history
        && cursor == 6
        && String.contains tap "[approve]"
        && String.contains tap "mode: plan"

// ── The test ────────────────────────────────────────────────────────────

#[test]
def test_dumb_e2e_manual_approval_and_plan_refusal : IO Bool := do {
    let _ <- write_wire_script;
    let _ <- write_inputs;
    let _ <- write_text cursor_path "0";
    let _ <- write_text tap_path "";
    let st <- Dumb.run scripted_read tap_write initial_state;
    let cursor <- read_cursor;
    let tap <- read_tap;
    return (final_state_ok st cursor tap)
}
