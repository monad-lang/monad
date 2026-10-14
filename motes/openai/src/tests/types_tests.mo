use openai::types {ChatMessage, ChatRequest, ChatResponse, Choice, ApiUsage}
use openai::tool {ToolCall, ToolDef}
use json::json {Json}

#[test]
def test_chat_request_encode_shape : Bool :=
    let msg : ChatMessage := { role := "user", content := Option.some "hi", tool_calls := [], tool_call_id := Option.none, name := Option.none } in
    let req : ChatRequest := { model := "qwen2.5-coder", messages := [msg], tools := [], max_tokens := Option.none } in
    let j := ChatRequest.serialize_json req in
    String.contains (Json.to_string j) "\"model\":\"qwen2.5-coder\""

#[test]
def test_chat_message_with_tool_call_roundtrip : Bool :=
    let tc : ToolCall := { id := "call_1", name := "grep", arguments := "{\"pattern\":\"foo\"}" } in
    let msg : ChatMessage := { role := "assistant", content := Option.none, tool_calls := [tc], tool_call_id := Option.none, name := Option.none } in
    match ChatMessage.deserialize_json (ChatMessage.serialize_json msg) {
        Result.ok msg2 =>
            match msg2 {
                ChatMessage.mk role content tool_calls tool_call_id name =>
                    match tool_calls {
                        List.cons tc2 _ =>
                            match tc2 { ToolCall.mk id n args => String.beq n "grep" && String.beq args "{\"pattern\":\"foo\"}" },
                        List.empty => false,
                    }
            },
        Result.err _ => false,
    }

#[test]
def test_tool_def_with_json_parameters_roundtrip : Bool :=
    let schema : Json := Json.array [Json.str "object"] in
    let td : ToolDef := { name := "grep", description := "search files", parameters := schema } in
    match ToolDef.deserialize_json (ToolDef.serialize_json td) {
        Result.ok td2 =>
            match td2 { ToolDef.mk name desc params => Json.beq params schema },
        Result.err _ => false,
    }

/// The response direction: a plain-text assistant turn carries NO
/// `tool_calls` key at all (a real Ollama body) -- the decoder must
/// default it to empty, not error. This is the exact gap that
/// short-circuited the first live e2e run.
#[test]
def test_chat_message_deserialize_defaults_missing_tool_calls : Bool :=
    let body := r#"{"role":"assistant","content":"hi"}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match ChatMessage.deserialize_json j {
                Result.err _ => false,
                Result.ok m =>
                    match m {
                        ChatMessage.mk role content tool_calls tool_call_id name =>
                            String.beq role "assistant" && List.is_empty tool_calls,
                    },
            },
    }

#[test]
def test_chat_response_decode : Bool :=
    let body := "{\"choices\":[{\"message\":{\"role\":\"assistant\",\"content\":\"hi\",\"tool_calls\":[],\"tool_call_id\":null,\"name\":null},\"finish_reason\":\"stop\"}],\"usage\":{\"prompt_tokens\":3,\"completion_tokens\":5}}" in
    match Json.parse body {
        Result.ok j =>
            match ChatResponse.deserialize_json j {
                Result.ok resp =>
                    match resp {
                        ChatResponse.mk choices usage =>
                            match choices {
                                List.cons c _ =>
                                    match c { Choice.mk msg reason => String.beq reason "stop" },
                                List.empty => false,
                            }
                    },
                Result.err _ => false,
            },
        Result.err _ => false,
    }

/// The request direction: OpenAI's API wraps every tool definition in
/// `{"type":"function","function":{...}}` -- the flat shape the derive
/// emits is one Ollama's OpenAI-compat layer parses with the function
/// name stripped (verified live: `function.name` came back empty).
#[test]
def test_tool_def_serialize_wraps_in_function_shape : Bool :=
    let td : ToolDef := { name := "read", description := "read a file", parameters := Json.null } in
    let s := Json.to_string (ToolDef.serialize_json td) in
    String.contains s "\"type\":\"function\"" && String.contains s "\"function\"" && String.contains s "\"name\":\"read\""

/// The response direction: a real Ollama/OpenAI response nests the
/// tool call's name and arguments under `function`, and carries
/// `index`/`type` keys a decoder must skip, not choke on. This body is
/// a recorded shape from `localhost:11434/v1/chat/completions`.
#[test]
def test_tool_call_deserialize_reads_wire_nested_function : Bool :=
    let body := r#"{"id":"call_1","index":0,"type":"function","function":{"name":"read","arguments":"{\"path\":\"/tmp/x\"}"}}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match ToolCall.deserialize_json j {
                Result.err _ => false,
                Result.ok tc =>
                    match tc {
                        ToolCall.mk id n args =>
                            String.beq id "call_1" && String.beq n "read" && String.beq args "{\"path\":\"/tmp/x\"}",
                    },
            },
    }

/// The history echo: an assistant message's prior tool calls ride the
/// NEXT request nested under `function`, the same wrapper the tool
/// TABLE needs (verified live, see `tool.mo`'s header). Pinned at the
/// MESSAGE level because `ChatMessage.serialize_json` is DERIVED -- a
/// derive regression would flatten the nesting the live loop depends
/// on, and only a wire-text assertion catches it.
#[test]
def test_chat_message_serialize_wraps_tool_calls_in_function_shape : Bool :=
    let tc : ToolCall := { id := "call_1", name := "read", arguments := "{\"path\":\"a\"}" } in
    let msg : ChatMessage := { role := "assistant", content := Option.none, tool_calls := [tc], tool_call_id := Option.none, name := Option.none } in
    let s := Json.to_string (ChatMessage.serialize_json msg) in
    String.contains s "\"tool_calls\":[{"
        && String.contains s "\"type\":\"function\""
        && String.contains s "\"function\":{\""
        && String.contains s "\"name\":\"read\""
        && String.contains s "\"arguments\":\"{\\\"path\\\":\\\"a\\\"}\""
