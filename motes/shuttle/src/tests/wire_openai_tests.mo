use shuttle::wire::openai {OpenAI.encode_request, OpenAI.decode_response}
use shuttle::message_types {Role, Content, StopReason}
use shuttle::message {Message, Turn, Usage}
use shuttle::tool {ToolSpec}
use openai::types {ChatRequest, ChatMessage, ChatResponse, Choice, ApiUsage}
use openai::tool {ToolCall}
use json::json {Json}
use std::list {List.length}

#[test]
def test_encode_request_system_message_first : Bool :=
    let req := OpenAI.encode_request "qwen" 100 "be helpful" [] [] in
    match req {
        ChatRequest.mk model messages tools max_tokens stream =>
            match messages {
                List.cons m _ =>
                    match m { ChatMessage.mk role content tool_calls tool_call_id name => String.beq role "system" },
                List.empty => false,
            }
    }

/// A `tool` message holding TWO `Content.tool_result`s expands into
/// TWO separate ChatMessages, each with its own tool_call_id -- OpenAI
/// has no notion of one message carrying several tool results.
#[test]
def test_encode_request_splits_multiple_tool_results : Bool :=
    let msg : Message := { role := Role.tool, content := [Content.tool_result "c1" "out1" false, Content.tool_result "c2" "out2" false] } in
    let req := OpenAI.encode_request "qwen" 100 "sys" [] [msg] in
    match req {
        ChatRequest.mk model messages tools max_tokens stream => List.length messages == 3,
    }

/// `tool_calls[].function.arguments` is a JSON STRING that must be
/// parsed a second time -- the decoded `Content.tool_use.input` must
/// be a real object, not the literal string.
def turn_stop_is_tool_use_stop (t : Turn) : Bool :=
    match t { Turn.mk _ _ stop => match stop { StopReason.tool_use_stop => true, _ => false } }

def turn_first_content_is_object_tool_use (t : Turn) : Bool :=
    match t {
        Turn.mk message _ _ =>
            match message {
                Message.mk _ content =>
                    match content {
                        List.cons c _ =>
                            match c {
                                Content.tool_use _ _ input =>
                                    match input { Json.object _ => true, _ => false },
                                _ => false,
                            },
                        List.empty => false,
                    }
            }
    }

#[test]
def test_decode_response_double_decodes_tool_call_arguments : Bool :=
    let tc : ToolCall := { id := "call_1", name := "grep", arguments := "{\"pattern\":\"foo\"}" } in
    let msg : ChatMessage := { role := "assistant", content := Option.none, tool_calls := [tc], tool_call_id := Option.none, name := Option.none } in
    let choice : Choice := { message := msg, finish_reason := "tool_calls" } in
    let usage : ApiUsage := { prompt_tokens := 1, completion_tokens := 1 } in
    let resp : ChatResponse := { choices := [choice], usage := usage } in
    match OpenAI.decode_response resp {
        Result.ok turn => turn_stop_is_tool_use_stop turn && turn_first_content_is_object_tool_use turn,
        Result.err _ => false,
    }

#[test]
def test_decode_response_finish_reason_stop_maps_to_end_turn : Bool :=
    let msg : ChatMessage := { role := "assistant", content := Option.some "hi", tool_calls := [], tool_call_id := Option.none, name := Option.none } in
    let choice : Choice := { message := msg, finish_reason := "stop" } in
    let usage : ApiUsage := { prompt_tokens := 1, completion_tokens := 1 } in
    let resp : ChatResponse := { choices := [choice], usage := usage } in
    match OpenAI.decode_response resp {
        Result.ok turn =>
            match turn { Turn.mk _ _ stop => match stop { StopReason.end_turn => true, _ => false } },
        Result.err _ => false,
    }

/// A request carrying tools must serialize each tool entry in the
/// nested `{"type":"function","function":{...}}` shape -- the flat
/// shape loses the function name on Ollama's OpenAI-compat layer
/// (live-verified; see `motes/openai/src/types.mo`).
#[test]
def test_encode_request_tools_entry_is_nested_function_shape : Bool :=
    let spec : ToolSpec := { name := "read", description := "read a file", schema := Json.null } in
    let req := OpenAI.encode_request "qwen" 100 "sys" [spec] [] in
    let s := Json.to_string (ChatRequest.serialize_json req) in
    String.contains s "\"type\":\"function\"" && String.contains s "\"name\":\"read\""

#[test]
def test_construct_and_match_chat_response_directly : Bool :=
    let msg : ChatMessage := { role := "assistant", content := Option.some "hi", tool_calls := [], tool_call_id := Option.none, name := Option.none } in
    let choice : Choice := { message := msg, finish_reason := "stop" } in
    let usage : ApiUsage := { prompt_tokens := 1, completion_tokens := 1 } in
    let resp : ChatResponse := { choices := [choice], usage := usage } in
    match resp {
        ChatResponse.mk choices u => List.length choices == 1
    }

/// `prompt_tokens_details.cached_tokens` rides through to the
/// normalized `Usage.cached_tokens` (OpenAI's `prompt_tokens` already
/// includes them, so the prompt size is unchanged).
#[test]
def test_decode_response_passes_cached_tokens_through : Bool :=
    let msg : ChatMessage := { role := "assistant", content := Option.some "hi", tool_calls := [], tool_call_id := Option.none, name := Option.none } in
    let choice : Choice := { message := msg, finish_reason := "stop" } in
    let usage : ApiUsage := { prompt_tokens := 10, completion_tokens := 2, cached_tokens := 7 } in
    let resp : ChatResponse := { choices := [choice], usage := usage } in
    match OpenAI.decode_response resp {
        Result.ok turn =>
            match turn {
                Turn.mk _ raw_usage _ =>
                    match raw_usage {
                        Usage.mk in_t out_t cached => in_t == 10 && out_t == 2 && cached == 7,
                    },
            },
        Result.err _ => false,
    }
