/// Tests for `motes/shuttle/src/context.mo` -- Phase 5's accounting,
/// trimming and cached prefix. Pure value tests, no IO.
use shuttle::context {usage_zero, usage_add, usage_total, estimate_tokens, trim, cached_prefix, stub_tool_results}
use shuttle::message {Message, Usage}
use shuttle::message_types {Role, Content}
use shuttle::tool {ToolSpec}
use json::json {Json}
use std::list {List.length}

#[test]
def test_usage_zero_is_all_zero : Bool :=
    let u : Usage := usage_zero in
    u.input_tokens == 0 && u.output_tokens == 0 && u.cached_tokens == 0

#[test]
def test_usage_add_sums_fields : Bool :=
    let a : Usage := { input_tokens := 1, output_tokens := 2, cached_tokens := 3 } in
    let b : Usage := { input_tokens := 10, output_tokens := 20, cached_tokens := 30 } in
    let s : Usage := usage_add a b in
    s.input_tokens == 11 && s.output_tokens == 22 && s.cached_tokens == 33

#[test]
def test_usage_total_is_input_plus_output : Bool :=
    let u : Usage := { input_tokens := 7, output_tokens := 5, cached_tokens := 3 } in
    usage_total u == 12

#[test]
def test_estimate_tokens_is_a_quarter_of_the_bytes : Bool :=
    estimate_tokens "abcd" == 2 && estimate_tokens "" == 1

def big_chunk : String := "0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"

def big_output : String := String.concat big_chunk (String.concat big_chunk big_chunk)

def old_tool_message : Message :=
    { role := Role.tool, content := [Content.tool_result "call_1" big_output false] }

def plain_message : Message :=
    { role := Role.assistant, content := [Content.text "short"] }

def newest_tool_message : Message :=
    { role := Role.tool, content := [Content.tool_result "call_2" "keep me readable" false] }

#[test]
def test_trim_is_a_noop_under_budget : Bool :=
    let history : List Message := [old_tool_message, newest_tool_message] in
    List.length (trim 100000 history) == 2

def first_of_content (cs : List Content) : Option Content :=
    match cs {
        List.cons c _ => Option.some c,
        List.empty => Option.none,
    }

def message_first_content (m : Message) : Option Content :=
    match m { { content, .. } => first_of_content content }

def tool_result_output (c : Content) : String :=
    match c { Content.tool_result _ output _ => output, _ => "" }

def trimmed_oldest_output (ms : List Message) : String :=
    match ms {
        List.cons m _ => match message_first_content m { Option.some c => tool_result_output c, Option.none => "" },
        List.empty => "",
    }

#[partial]
def last_message (ms : List Message) : Option Message :=
    match ms {
        List.empty => Option.none,
        List.cons m rest =>
            if List.length rest == 0 then Option.some m else last_message rest,
    }

def newest_output (ms : List Message) : String :=
    match last_message ms {
        Option.some m => match message_first_content m { Option.some c => tool_result_output c, Option.none => "" },
        Option.none => "",
    }

#[test]
def test_trim_stubs_oldest_tool_results_and_keeps_newest : Bool :=
    let history : List Message := [old_tool_message, plain_message, newest_tool_message] in
    let trimmed : List Message := trim 10 history in
    trimmed_oldest_output trimmed == "[trimmed by the shuttle context manager]"
        && String.contains (newest_output trimmed) "keep me readable"
        && List.length trimmed == 3

#[test]
def test_stub_tool_results_keeps_is_error_false : Bool :=
    match message_first_content (stub_tool_results old_tool_message) {
        Option.some c => match c {
            Content.tool_result _ output is_error => String.contains output "trimmed" && Bool.not is_error,
            _ => false,
        },
        Option.none => false,
    }

#[test]
def test_cached_prefix_is_byte_stable_and_names_its_tools : Bool :=
    let spec : ToolSpec := { name := "grep", description := "search", schema := Json.make_null } in
    let p1 : String := cached_prefix "you are a test" [spec] in
    let p2 : String := cached_prefix "you are a test" [spec] in
    p1 == p2 && String.contains p1 "grep" && String.contains p1 "you are a test"
