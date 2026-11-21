/// A `max_tokens` stop that left nothing usable: one resend at a raised
/// budget, and a cut-off tool call is never kept. The mock wire serves
/// the same turn to the resend (it picks by history), which is enough to
/// see the resend happen, its usage counted and the tool call dropped.
use std::path {Path}
use std::test {Test.write_fixture, Test.append_fixture, Test.read_fixture_or}
use init::transformers {ResultT}
use shuttle::message_types {Role, Content, StopReason}
use shuttle::message {Message, Usage, Turn}
use shuttle::provider {ProviderConfig, Wire, Provider.silent_emit}
use shuttle::gate {Gate.auto}
use shuttle::registry {ToolRegistry}
use shuttle::loop {
    Loop.initial_state, Loop.iterate, Loop.truncated_unusable, Loop.raised_budget, Loop.drop_truncated_tool_use,
    Loop.kept_budget, Loop.should_continue_cutoff, Loop.continue_prompt
}
use shuttle::agent {Agent.exec, RunState}
use json::json {Json, Json.make_array, Json.make_str, Json.to_string}
use std::process {process_id}
use std::list {List.any, List.filter}

def script_path : String :=
    String.concat "/tmp/shuttle_mock_turns_" (String.concat (I64.to_string process_id) ".json")

def tap_path : String :=
    String.concat "/tmp/shuttle_trunc_tap_" (String.concat (I64.to_string process_id) ".txt")

def emit_tap (t : String) : IO Unit :=
    do { let _w <- Test.append_fixture (Path.path tap_path) t; return unit }

def reset_tap : IO Unit :=
    do { let _w <- Test.write_fixture (Path.path tap_path) ""; return unit }

def read_tap : IO String :=
    Test.read_fixture_or (Path.path tap_path) "TAP-READ-FAILED"

def usage_10 : Usage := { input_tokens := 5, output_tokens := 10, cached_tokens := 0 }

def turn_of (content : List Content) (stop : StopReason) : Turn :=
    let m : Message := { role := Role.assistant, content := content } in
    let t : Turn := { message := m, usage := usage_10, stop := stop } in
    t

def cut_tool_call : Turn :=
    let cut : Content := Content.tool_use "call_1" "echo" (Json.make_str "{\"pa") in
    turn_of [Content.thinking "planning" "", cut] StopReason.max_tokens

def write_script (t : Turn) : IO Unit := write_scripts [t]

def write_scripts (ts : List Turn) : IO Unit :=
    let text : String := Json.to_string (Json.make_array (List.map (fn (t : Turn) => Turn.serialize_json t) ts)) in
    do { let _w <- Test.write_fixture (Path.path script_path) text; return unit }

def cut_text : Turn := turn_of [Content.text "the first half"] StopReason.max_tokens

def done_text : Turn := turn_of [Content.text " and the rest"] StopReason.end_turn

def is_stop (want : StopReason) (got : Option StopReason) : Bool :=
    match got {
        Option.none => false,
        Option.some r => StopReason.tag r == StopReason.tag want,
    }

def is_user (m : Message) : Bool :=
    match m.role { Role.user => true, _ => false }

def first_text (cs : List Content) : String :=
    match cs {
        List.empty => "",
        List.cons c _ => match c { Content.text t => t, _ => "" },
    }

def last_user_text (history : List Message) : String :=
    match List.reverse (List.filter is_user history) {
        List.empty => "",
        List.cons m _ => first_text m.content,
    }

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "SHUTTLE_UNUSED_KEY", max_tokens := 8,
        wire := Wire.mock, thinking := false }

def auto_config : ProviderConfig := { mock_config with max_tokens_auto := true }

def user_config : ProviderConfig := { mock_config with max_tokens_auto := false }

def user_message : Message := { role := Role.user, content := [Content.text "go"] }

def run_with (ceiling : I64) (continues : I64) : IO (Result String RunState) := do {
    let st0 : RunState := Loop.initial_state mock_config ToolRegistry.empty "sys" [user_message] 4 emit_tap Gate.auto;
    let st : RunState := { st0 with output_ceiling := ceiling, continue_cutoffs := continues };
    let r <- ResultT.run (Agent.exec Loop.iterate st);
    return (match r {
        Result.ok p => match p { Pair.pair s _ => Result.ok s },
        Result.err e => Result.err e,
    })
}

def run_with_ceiling (ceiling : I64) : IO (Result String RunState) := run_with ceiling 0

def is_some (o : Option I64) : Bool :=
    match o { Option.some _ => true, Option.none => false }

def is_tool_use (c : Content) : Bool :=
    match c { Content.tool_use _ _ _ => true, _ => false }

#[partial]
def any_tool_use (history : List Message) : Bool :=
    match history {
        List.empty => false,
        List.cons m rest => Bool.or (List.any is_tool_use m.content) (any_tool_use rest),
    }

#[test]
def test_truncated_unusable_shapes : Bool :=
    Loop.truncated_unusable cut_tool_call
        && Loop.truncated_unusable (turn_of [Content.thinking "only reasoning" ""] StopReason.max_tokens)
        && Bool.not (Loop.truncated_unusable (turn_of [Content.text "half an answer"] StopReason.max_tokens))
        && Bool.not (Loop.truncated_unusable (turn_of [] StopReason.end_turn))

#[test]
def test_raised_budget_doubles_up_to_the_ceiling : Bool :=
    Loop.raised_budget 8192 65536 == 16384
        && Loop.raised_budget 8192 10000 == 10000
        && Loop.raised_budget 8192 0 == 0

#[test]
def test_a_cut_tool_call_is_dropped : Bool :=
    let t : Turn := Loop.drop_truncated_tool_use cut_tool_call in
    List.length t.message.content == 1

#[test]
def test_a_finished_tool_call_is_kept : Bool :=
    let t0 : Turn := turn_of [Content.tool_use "call_1" "echo" (Json.make_str "x")] StopReason.tool_use_stop in
    let t : Turn := Loop.drop_truncated_tool_use t0 in
    List.length t.message.content == 1

/// Ceiling 16 over max_tokens 8: one resend (announced, usage counted
/// twice), and the stored history keeps no tool call.
#[test]
def test_an_unusable_cut_off_is_resent_once : IO Bool := do {
    write_script cut_tool_call;
    reset_tap;
    let r <- run_with_ceiling 16;
    let tap <- read_tap;
    return (match r {
        Result.err _ => false,
        Result.ok s =>
            String.contains tap "output limit 8 -> 16"
                && s.session.spent.output_tokens == 20
                && s.session.turns == 1
                && Bool.not (any_tool_use s.session.history),
    })
}

/// Ceiling 0 (the default): no resend, but the cut tool call is still dropped.
#[test]
def test_no_ceiling_no_resend : IO Bool := do {
    write_script cut_tool_call;
    reset_tap;
    let r <- run_with_ceiling 0;
    let tap <- read_tap;
    return (match r {
        Result.err _ => false,
        Result.ok s =>
            Bool.not (String.contains tap "output limit")
                && s.session.spent.output_tokens == 10
                && Bool.not (any_tool_use s.session.history),
    })
}

#[test]
def test_should_continue_only_a_cut_with_text : Bool :=
    Loop.should_continue_cutoff 1 cut_text
        && Bool.not (Loop.should_continue_cutoff 0 cut_text)
        && Bool.not (Loop.should_continue_cutoff 1 done_text)
        && Bool.not (Loop.should_continue_cutoff 1 (turn_of [Content.thinking "reasoning" ""] StopReason.max_tokens))

/// A reply cut off mid-text is continued: the history gains the continue
/// line and the second half, and the run ends normally.
#[test]
def test_a_cut_text_reply_is_continued : IO Bool := do {
    write_scripts [cut_text, done_text];
    reset_tap;
    let r <- run_with 0 1;
    let tap <- read_tap;
    return (match r {
        Result.err _ => false,
        Result.ok s =>
            String.contains tap "continuing"
                && s.session.turns == 2
                && List.length s.session.history == 4
                && last_user_text s.session.history == Loop.continue_prompt
                && is_stop StopReason.end_turn s.last_stop
                && s.continue_cutoffs == 0,
    })
}

/// No continuations left: the cut reply is the final answer, as before.
#[test]
def test_no_continues_no_continuation : IO Bool := do {
    write_scripts [cut_text, done_text];
    reset_tap;
    let r <- run_with 0 0;
    let tap <- read_tap;
    return (match r {
        Result.err _ => false,
        Result.ok s =>
            Bool.not (String.contains tap "continuing")
                && s.session.turns == 1
                && is_stop StopReason.max_tokens s.last_stop,
    })
}

/// A continuation cut off again stops once the allowance is spent, and the
/// run still reports the cut-off.
#[test]
def test_a_continuation_cut_again_stops : IO Bool := do {
    write_scripts [cut_text, cut_text, done_text];
    reset_tap;
    let r <- run_with 0 1;
    return (match r {
        Result.err _ => false,
        Result.ok s => s.session.turns == 2 && is_stop StopReason.max_tokens s.last_stop,
    })
}

/// The raised budget is kept only after a resend that worked, and only when
/// weaver chose the budget.
#[test]
def test_kept_budget_rules : Bool :=
    let kept : Option I64 := Loop.kept_budget auto_config 16 cut_tool_call done_text in
    let kept_ok : Bool := match kept { Option.some n => n == 16, Option.none => false } in
    let user_kept : Bool := is_some (Loop.kept_budget user_config 16 cut_tool_call done_text) in
    let cut_again : Bool := is_some (Loop.kept_budget auto_config 16 cut_tool_call cut_tool_call) in
    let no_resend : Bool := is_some (Loop.kept_budget auto_config 16 cut_text done_text) in
    let no_ceiling : Bool := is_some (Loop.kept_budget auto_config 0 cut_tool_call done_text) in
    kept_ok && Bool.not user_kept && Bool.not cut_again && Bool.not no_resend && Bool.not no_ceiling
