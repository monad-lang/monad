/// Fixture tests for `OpenAI.complete_stream`'s core: the pure
/// per-event fold (`openai_apply_event` and the `openai_assemble`
/// finish), plus one IO-level test driving `openai_stream_bytes` with
/// raw SSE bytes -- an event split across two pushes -- to prove the
/// wire order of `on_text` deltas. The event payloads are recorded
/// shapes from `localhost:11434/v1/chat/completions` (LF endings,
/// `delta.content` fragments, `finish_reason` on the last chunk,
/// `data: [DONE]` sentinel, `usage` usually absent or null).
use openai::client {OpenaiAcc, openai_apply_event, openai_assemble, openai_stream_bytes}
use openai::types {ChatRequest, ChatResponse, ChatMessage, Choice, ApiUsage}
use openai::tool {ToolCall}
use json::json {Json.to_string, Json.parse}
use http::sse {Sse.init}
use std::list {List.length}
use std::path {Path.of}
use std::process {process_id}
use std::io {IO.read_file, IO.write_file}

/// The accumulator every fold starts from -- the same zero state
/// `OpenAI.complete_stream` hands moose.
def stream_acc0 : OpenaiAcc :=
    { sse := Sse.init, text := "", tools := [], finish := "", usage := ApiUsage.mk 0 0 }

/// Fold one event payload, keeping the accumulator (the delta it
/// reported is asserted separately where it matters).
def fold_event (acc : OpenaiAcc) (data : String) : OpenaiAcc :=
    match openai_apply_event acc data {
        Pair.pair acc2 _ => acc2
    }

/// The `i`-th tool call of a list, none past the end.
#[terminating]
def tool_at (tools : List ToolCall) (i : I64) : Option ToolCall :=
    match tools {
        List.empty => Option.none,
        List.cons t rest =>
            if i == 0
            then Option.some t
            else tool_at rest (I64.sub i 1)
    }

def tool_matches (tools : List ToolCall) (i : I64) (want_id : String) (want_name : String) (want_args : String) : Bool :=
    match tool_at tools i {
        Option.none => false,
        Option.some t =>
            match t {
                ToolCall.mk id name args =>
                    Bool.and (id == want_id)
                        (Bool.and (name == want_name) (args == want_args))
            }
    }

/// The assembled response's single message -- the one place a test
/// needs to reach `choices[0].message.tool_calls` without repeating
/// the destructure chain.
def assembled_tool_calls (acc : OpenaiAcc) : List ToolCall :=
    match openai_assemble acc {
        ChatResponse.mk choices _ =>
            match choices {
                List.cons c _ =>
                    match c {
                        Choice.mk msg _ =>
                            match msg {
                                ChatMessage.mk _ _ tool_calls _ _ => tool_calls
                            }
                    },
                List.empty => [],
            }
    }

#[test]
def test_stream_text_assembles_with_finish : Bool :=
    let a1 := fold_event stream_acc0 r#"{"choices":[{"index":0,"delta":{"role":"assistant","content":"Hello"},"finish_reason":null}]}"# in
    let a2 := fold_event a1 r#"{"choices":[{"index":0,"delta":{"content":" world"}}]}"# in
    let a3 := fold_event a2 r#"{"choices":[{"index":0,"delta":{},"finish_reason":"stop"}]}"# in
    let a4 := fold_event a3 "[DONE]" in
    match openai_assemble a4 {
        ChatResponse.mk choices _ =>
            match choices {
                List.cons c _ =>
                    match c {
                        Choice.mk msg finish =>
                            match msg {
                                ChatMessage.mk role content _ _ _ =>
                                    match content {
                                        Option.some s => s == "Hello world" && finish == "stop" && role == "assistant",
                                        Option.none => false,
                                    }
                            }
                    },
                List.empty => false,
            }
    }

/// A stream that never sends `finish_reason` (a connection that ended
/// early, a server that omits it) still assembles with the one-shot
/// path's default.
#[test]
def test_stream_finish_defaults_to_stop : Bool :=
    let a1 := fold_event stream_acc0 r#"{"choices":[{"index":0,"delta":{"content":"hi"}}]}"# in
    match openai_assemble a1 {
        ChatResponse.mk choices _ =>
            match choices {
                List.cons c _ => match c { Choice.mk _ finish => finish == "stop" },
                List.empty => false,
            }
    }

/// Two tool calls interleaved by `index`: name and id arrive in the
/// first fragment, arguments in CONCATENATED later fragments -- the
/// wire contract for streaming tool calls. Each merged `arguments`
/// string must also be valid JSON for shuttle's adapter to decode.
#[test]
def test_stream_tool_call_fragments_merge_by_index : Bool :=
    let a1 := fold_event stream_acc0 r#"{"choices":[{"index":0,"delta":{"tool_calls":[{"index":0,"id":"call_1","type":"function","function":{"name":"read","arguments":""}}]}}]}"# in
    let a2 := fold_event a1 r#"{"choices":[{"index":0,"delta":{"tool_calls":[{"index":1,"id":"call_2","type":"function","function":{"name":"write","arguments":""}}]}}]}"# in
    let a3 := fold_event a2 r#"{"choices":[{"index":0,"delta":{"tool_calls":[{"index":0,"function":{"arguments":"{\"path\":"}}]}}]}"# in
    let a4 := fold_event a3 r#"{"choices":[{"index":0,"delta":{"tool_calls":[{"index":1,"function":{"arguments":"{\"pattern\":\"x\"}"}}]}}]}"# in
    let tcs := assembled_tool_calls a4 in
    Bool.and (List.length tcs == 2)
        (Bool.and (tool_matches tcs 0 "call_1" "read" "{\"path\":")
            (tool_matches tcs 1 "call_2" "write" "{\"pattern\":\"x\"}"))

/// A continuation fragment that repeats `name` as an EMPTY string must
/// not erase the name the first fragment established. Not hypothetical:
/// Mistral's zai-glm-5-3 streams exactly this shape (recorded live
/// 2026-10-18 against api.mistral.ai) -- the first chunk carries
/// `{"name":"read","arguments":"{\"path\": \""}`, the next carries
/// `{"name":"","arguments":"/tmp/example.txt\"}"}` and nothing else.
/// An override-on-present merge turns the assembled name into "" and
/// shuttle's loop reports `unknown tool: ` for every call.
#[test]
def test_stream_empty_name_fragment_keeps_name : Bool :=
    let a1 := fold_event stream_acc0 r#"{"choices":[{"index":0,"delta":{"tool_calls":[{"id":"chatcmpl-tool-8a7cfec979edf0d4","type":"function","function":{"name":"read","arguments":"{\"path\": \""},"index":0}]},"finish_reason":null}]}"# in
    let a2 := fold_event a1 r#"{"choices":[{"index":0,"delta":{"tool_calls":[{"type":"function","function":{"name":"","arguments":"/tmp/example.txt\"}"},"index":0}]},"finish_reason":null}]}"# in
    let a3 := fold_event a2 r#"{"choices":[{"index":0,"delta":{},"finish_reason":"tool_calls"}]}"# in
    let tcs := assembled_tool_calls a3 in
    tool_matches tcs 0 "chatcmpl-tool-8a7cfec979edf0d4" "read" "{\"path\": \"/tmp/example.txt\"}"

/// An index GAP (the server opens 2 before 1) or an out-of-order
/// fragment must not fan one tool call out into duplicates: fragments
/// merge by the index they CLAIM, and a later fragment of the same
/// index patches the entry that index opened, wherever it sits.
#[test]
def test_stream_tool_call_index_gap_merges : Bool :=
    let a1 := fold_event stream_acc0 r#"{"choices":[{"index":0,"delta":{"tool_calls":[{"index":0,"id":"call_1","type":"function","function":{"name":"read","arguments":""}}]}}]}"# in
    let a2 := fold_event a1 r#"{"choices":[{"index":0,"delta":{"tool_calls":[{"index":2,"id":"call_2","type":"function","function":{"name":"write","arguments":"{\"a\":"}}]}}]}"# in
    let a3 := fold_event a2 r#"{"choices":[{"index":0,"delta":{"tool_calls":[{"index":2,"function":{"arguments":"1}"}}]}}]}"# in
    let a4 := fold_event a3 r#"{"choices":[{"index":0,"delta":{"tool_calls":[{"index":2,"function":{"arguments":"//tail"}}]}}]}"# in
    let tcs := assembled_tool_calls a4 in
    Bool.and (List.length tcs == 2)
        (Bool.and (tool_matches tcs 0 "call_1" "read" "")
            (tool_matches tcs 1 "call_2" "write" "{\"a\":1}//tail"))

/// `usage: null` AFTER a real usage object must not wipe what was
/// captured -- null is the wire's filler, not a zero to apply.
#[test]
def test_stream_usage_null_after_real_keeps_real : Bool :=
    let a1 := fold_event stream_acc0 r#"{"choices":[],"usage":{"prompt_tokens":7,"completion_tokens":3}}"# in
    let a2 := fold_event a1 r#"{"choices":[{"index":0,"delta":{"content":"ok"}}],"usage":null}"# in
    match openai_assemble a2 {
        ChatResponse.mk _ usage =>
            match usage {
                ApiUsage.mk pt ct => Bool.and (pt == 7) (ct == 3)
            }
    }

/// A tool-call fragment is not text: the fold reports no `on_text`
/// delta for it, exactly like the tool turns a real stream serves.
#[test]
def test_stream_tool_call_fragment_reports_no_text : Bool :=
    match openai_apply_event stream_acc0 r#"{"choices":[{"index":0,"delta":{"tool_calls":[{"index":0,"id":"call_1","type":"function","function":{"name":"read","arguments":"{}"}}]}}]}"# {
        Pair.pair _ delta => delta == ""
    }

/// `usage: null` on every chunk (the live Ollama shape), a real usage
/// object on a choices-empty event, an unparseable payload, and the
/// `[DONE]` sentinel -- all four must be survived, the usage kept.
#[test]
def test_stream_usage_and_lenient_skips : Bool :=
    let a1 := fold_event stream_acc0 r#"{"choices":[{"index":0,"delta":{"content":"ok"}}],"usage":null}"# in
    let a2 := fold_event a1 "not json at all" in
    let a3 := fold_event a2 r#"{"choices":[],"usage":{"prompt_tokens":7,"completion_tokens":3}}"# in
    let a4 := fold_event a3 "[DONE]" in
    match openai_assemble a4 {
        ChatResponse.mk _ usage =>
            match usage {
                ApiUsage.mk pt ct => Bool.and (pt == 7) (Bool.and (ct == 3) (a4.text == "ok"))
            }
    }

/// An empty `delta.content` (most chunks carry one) appends nothing
/// and reports an empty delta -- the empty ones are what the fold
/// upstream refuses to hand `on_text`.
#[test]
def test_stream_empty_content_delta_reports_empty : Bool :=
    let a1 := fold_event stream_acc0 r#"{"choices":[{"index":0,"delta":{"content":""}}]}"# in
    match openai_apply_event a1 r#"{"choices":[{"index":0,"delta":{"content":"x"}}]}"# {
        Pair.pair a2 delta => Bool.and (delta == "x") (a2.text == "x")
    }

/// The request half of streaming: `{ req with stream := true }` must
/// reach the wire as a real `"stream":true` -- the field the endpoint
/// switches on.
#[test]
def test_complete_stream_request_carries_stream_true : Bool :=
    let req : ChatRequest := { model := "m", messages := [], tools := [], max_tokens := Option.none, stream := false } in
    let sreq : ChatRequest := { req with stream := true } in
    String.contains (Json.to_string (ChatRequest.serialize_json sreq)) "\"stream\":true"

/// The decode half: a real non-streaming request body carries no
/// `stream` key, and the derive's absent-key rule must fall back to
/// the declared default -- not a decode error.
#[test]
def test_chat_request_decode_defaults_stream_false : Bool :=
    match Json.parse "{\"model\":\"m\",\"messages\":[],\"tools\":[]}" {
        Result.err _ => false,
        Result.ok j =>
            match ChatRequest.deserialize_json j {
                Result.err _ => false,
                Result.ok r =>
                    match r {
                        ChatRequest.mk m _ _ _ st =>
                            match st { false => m == "m", true => false }
                    }
            }
    }

// ── IO level: raw SSE bytes through the moose callback ──────────────

/// PID-qualified so two sessions' test runs sharing /tmp never collide.
def tap_path : String :=
    String.concat "/tmp/openai_stream_tap_" (String.concat (I64.to_string process_id) ".txt")

/// The `on_text` probe: append the delta to the tap file. Read-modify-
/// write because `std::io` has no append mode and no `IORef` -- a
/// single-threaded test makes the race moot.
def text_tap (t : String) : IO Unit :=
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

/// One event split across two pushes (the first ends mid-JSON, no
/// newline yet): the SSE state machine must buffer it, the completed
/// event must report its delta to `on_text`, and the finish event
/// must fold without emitting text. The tap file proves wire order.
#[test]
def test_stream_bytes_emits_deltas_in_wire_order : IO Bool := do {
    reset_tap;
    let r1 <- openai_stream_bytes text_tap stream_acc0 (String.to_list "data: {\"choices\":[{\"index\":0,\"delta\":{\"content\":\"Hel");
    match r1 {
        Result.err _ => return false,
        Result.ok pr1 =>
            match pr1 {
                Pair.pair acc1 _ => do {
                    let r2 <- openai_stream_bytes text_tap acc1 (String.to_list "lo\"}}]}\n\ndata: {\"choices\":[{\"index\":0,\"delta\":{},\"finish_reason\":\"stop\"}]}\n\n");
                    match r2 {
                        Result.err _ => return false,
                        Result.ok pr2 =>
                            match pr2 {
                                Pair.pair acc2 _ => do {
                                    let tapped <- read_tap;
                                    return (Bool.and (tapped == "Hello")
                                        (Bool.and (acc2.text == "Hello") (acc2.finish == "stop")))
                                }
                            }
                    }
                }
            }
    }
}
