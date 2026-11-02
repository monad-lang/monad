/// The loop's out-of-band tool-error events: one per FAILED call, none for
/// a successful one. A `true` literal pattern on the error flag matched
/// every result compiled, so each successful call was logged as an error.
use shuttle::loop {tool_error_events}
use shuttle::message_types {Content}
use std::list {List.length}

#[test]
def test_a_successful_result_emits_no_error_event : Bool :=
    List.length (tool_error_events ["read"] [Content.tool_result "t1" "fine" false]) == 0

#[test]
def test_a_failed_result_emits_one_error_event : Bool :=
    match tool_error_events ["read"] [Content.tool_result "t1" "boom" true] {
        List.cons e rest => String.contains e "read" && String.contains e "boom" && List.is_empty rest,
        List.empty => false,
    }

#[test]
def test_only_the_failed_calls_emit : Bool :=
    let cs : List Content := [Content.tool_result "a" "ok" false, Content.tool_result "b" "bad" true, Content.tool_result "c" "ok" false] in
    List.length (tool_error_events ["one", "two", "three"] cs) == 1
