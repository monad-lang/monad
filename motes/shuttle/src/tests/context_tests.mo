/// Tests for `motes/shuttle/src/context.mo` -- Phase 5's accounting,
/// trimming and cached prefix. Pure value tests, no IO.
use shuttle::context {
    usage_zero, usage_add, usage_total, estimate_tokens, trim, cached_prefix, stub_tool_results, history_tokens
}
use shuttle::agent {silent_send_history}
use shuttle::message {Message, Usage}
use shuttle::message_types {Role, Content}
use shuttle::tool {ToolSpec}
use json::json {Json}
use std::list {}

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

def old_error_message : Message :=
    { role := Role.tool, content := [Content.tool_result "call_err" big_output true] }

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
def test_stub_tool_results_keeps_the_error_flag : Bool :=
    match message_first_content (stub_tool_results old_tool_message) {
        Option.some c => match c {
            Content.tool_result _ output is_error => String.contains output "trimmed" && Bool.not is_error,
            _ => false,
        },
        Option.none => false,
    }

#[test]
def test_stub_tool_results_keeps_a_real_error_flag : Bool :=
    match message_first_content (stub_tool_results old_error_message) {
        Option.some c => match c {
            Content.tool_result _ output is_error => String.contains output "trimmed" && is_error,
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

// ── the request projection's identity default ─────────────────────────
// `RunState.send_history` (shuttle::agent) is the per-REQUEST projection
// of the history handed to the wire. Its default must be the IDENTITY, so
// a headless shuttle run sends byte-for-byte what it stored; weaver is the
// only installer, and it installs `Context.trim`.

/// The identity: same length, same messages (the second element keeps its
/// text, so a reordering or a drop would show).
#[test]
def test_silent_send_history_is_the_identity : Bool :=
    let h : List Message := [old_tool_message, plain_message, newest_tool_message] in
    let sent : List Message := silent_send_history h in
    List.length sent == List.length h
        && nth_output sent 0 == big_output
        && nth_output sent 1 == "short"
        && nth_output sent 2 == "keep me readable"

/// The `n`th message's first content block, rendered as text (a tool
/// result's output, or a text block's text). No `BEq` on `Message`
/// exists, so the projection tests compare through this.
#[partial]
def nth_output (ms : List Message) (n : I64) : String :=
    match ms {
        List.empty => "",
        List.cons m rest => if n < 1i64 then first_block_text m else nth_output rest (n - 1i64),
    }

def first_block_text (m : Message) : String :=
    match message_first_content m {
        Option.some c => match c {
            Content.text s => s,
            Content.tool_result _ output _ => output,
            _ => "",
        },
        Option.none => "",
    }

#[test]
def test_silent_send_history_leaves_an_empty_history_empty : Bool :=
    List.length (silent_send_history List.empty) == 0i64

/// A non-identity projection changes only what ONE call sends; the stored
/// history is never rewritten (the store's turn-delta accounting assumes
/// it is append-only).
#[test]
def test_a_projection_does_not_touch_the_stored_history : Bool :=
    let h : List Message := [old_tool_message, plain_message, newest_tool_message] in
    let before : I64 := List.length h in
    let projected : List Message := trim 5 h in
    List.length h == before
        && List.length projected == before
        && nth_output projected 0 == "[trimmed by the shuttle context manager]"
        && nth_output projected 2 == "keep me readable"

// ── trim cuts the OLDEST prefix, in stable steps ──────────────────────
// Each `big_tool` is ~76 estimated tokens and saves ~65 when stubbed. With
// a budget of 300 the five-result history (~385) must save 175, rounded up
// to the 90-token step: 180, i.e. the three OLDEST results.

def big_tool (id : String) : Message :=
    { role := Role.tool, content := [Content.tool_result id big_output false] }

def five_big : List Message :=
    [big_tool "a", big_tool "b", big_tool "c", big_tool "d", big_tool "e"]

def is_stub (ms : List Message) (n : I64) : Bool :=
    nth_output ms n == "[trimmed by the shuttle context manager]"

#[test]
def test_trim_stubs_the_oldest_and_keeps_the_recent : Bool :=
    let t : List Message := trim 300 (List.append five_big [newest_tool_message]) in
    is_stub t 0 && is_stub t 1 && is_stub t 2
        && nth_output t 3 == big_output && nth_output t 4 == big_output
        && nth_output t 5 == "keep me readable"

#[test]
def test_trim_fits_the_budget : Bool :=
    let t : List Message := trim 300 (List.append five_big [newest_tool_message]) in
    I64.lt (history_tokens t) 301i64

/// A small append leaves the cut where it was: the sent prefix is
/// byte-stable, so a provider's prompt cache still hits.
#[test]
def test_trim_cut_is_stable_under_a_small_append : Bool :=
    let t : List Message := trim 300 (List.append five_big [plain_message, newest_tool_message]) in
    is_stub t 2 && nth_output t 3 == big_output && nth_output t 5 == "short"

/// Enough growth crosses the next step and moves the cut forward.
#[test]
def test_trim_cut_advances_after_a_step_of_growth : Bool :=
    let t : List Message := trim 300 (List.append five_big [big_tool "f", newest_tool_message]) in
    is_stub t 4 && nth_output t 5 == big_output && nth_output t 6 == "keep me readable"

/// The newest message is never stubbed, even when it alone is over budget.
#[test]
def test_trim_never_stubs_the_newest : Bool :=
    let t : List Message := trim 10 [big_tool "a", big_tool "z"] in
    is_stub t 0 && nth_output t 1 == big_output
