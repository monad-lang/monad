use openai::types {ChatMessage, ChatRequest, ChatResponse, Choice, ToolCall, ToolDef, Usage}
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
