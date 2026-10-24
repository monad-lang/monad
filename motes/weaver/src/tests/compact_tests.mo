/// Compaction's pure half: the threshold arithmetic, the estimate, the
/// user-boundary split (a kept tail may never begin with an orphan tool
/// result), and the summary prompt's shape.
use weaver::compact {
    Compact.threshold, Compact.estimate, Compact.should_compact,
    Compact.keep_budget, Compact.keep_tail, Compact.summary_prompt,
}
use shuttle::message {Message, Usage}
use shuttle::message_types {Role, Content}
use shuttle::session {Session}
use shuttle::provider {ProviderConfig, Wire}
use std::list {List.length}

def test_cfg : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "K", max_tokens := 8, wire := Wire.mock, thinking := false }

def usage0 : Usage := { input_tokens := 0, output_tokens := 0, cached_tokens := 0 }

def session_with (history : List Message) : Session :=
    { config := test_cfg, system_prompt := "sys", tools := List.empty, history := history, turns := 0, spent := usage0 }

def user_msg (s : String) : Message :=
    { role := Role.user, content := [Content.text s] }

def assistant_msg (s : String) : Message :=
    { role := Role.assistant, content := [Content.text s] }

def tool_msg (s : String) : Message :=
    { role := Role.tool, content := [Content.tool_result "call_1" s false] }

#[test]
def test_threshold_is_a_percentage_of_the_window : Bool :=
    Compact.threshold 128000i64 80i64 == 102400i64
        && Compact.threshold 0i64 80i64 == 0i64
        && Compact.threshold 1000i64 0i64 == 0i64

#[test]
def test_zero_window_disables_autocompact : Bool :=
    let s : Session := session_with [user_msg "hello"] in
    Bool.not (Compact.should_compact (Compact.threshold 0i64 80i64) s)

#[test]
def test_should_compact_when_the_estimate_crosses : Bool :=
    let big : String := String.repeat "x" 4000i64 in
    let s : Session := session_with [user_msg big] in
    // ~1000 tokens of history plus the prefix, against a 10-token
    // threshold: over it.
    Compact.should_compact 10i64 s

#[test]
def test_estimate_counts_the_system_prefix : Bool :=
    let s : Session := session_with List.empty in
    Compact.estimate s > 0i64

#[test]
def test_keep_budget_is_a_fifth : Bool :=
    Compact.keep_budget 1000i64 == 200i64 && Compact.keep_budget 4i64 == 1i64

/// The kept tail starts at a USER message: never an orphan tool result,
/// never mid tool_use/result pair.
#[test]
def test_keep_tail_starts_at_a_user_message : Bool :=
    let history : List Message := [
        user_msg "one",
        assistant_msg "working",
        tool_msg "output",
        assistant_msg "done",
        user_msg "two",
        assistant_msg "second",
    ] in
    let tail : List Message := Compact.keep_tail history 4i64 in
    match tail {
        List.cons m _ => match m.role { Role.user => List.length tail == 2i64, _ => false },
        List.empty => false,
    }

#[test]
def test_keep_tail_is_empty_when_nothing_fits : Bool :=
    let history : List Message := [tool_msg "orphan"] in
    List.length (Compact.keep_tail history 1i64) == 0i64

#[test]
def test_summary_prompt_carries_roles_and_instructions : Bool :=
    let history : List Message := [user_msg "fix the build", assistant_msg "on it"] in
    let p : String := Compact.summary_prompt history "focus on the CI failure" in
    String.contains p "user: fix the build"
        && String.contains p "assistant: on it"
        && String.contains p "focus on the CI failure"
