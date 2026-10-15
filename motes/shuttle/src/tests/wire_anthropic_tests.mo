/// Adapter-level tests for `wire/anthropic.mo` -- recorded-fixture
/// round-trips per agent-skills.md Phase 6's checklist: a text turn,
/// a parallel-tool-use turn, and a refusal. Response fixtures are
/// recorded wire BODIES (parsed through `MessagesResponse.
/// deserialize_json` first, exactly as `Anthropic.complete` would),
/// so what is asserted is the full wire-to-normal-form path, not just
/// the adapter's own mapping.
use shuttle::wire::anthropic {Anthropic.encode_request, Anthropic.decode_response}
use shuttle::message_types {Role, Content, StopReason}
use shuttle::message {Message, Turn, Usage}
use shuttle::tool {ToolSpec}
use anthropic::types {AnthropicMessage, Block, MessagesRequest, MessagesResponse}
use json::json {Json, Json.parse, Json.to_string}
use std::list {List.length}
use std::map {BTreeMap}

/// A recorded text-turn body, exactly as Anthropic sends it: content
/// is a block ARRAY, `stop_reason` is `end_turn`, and the cold-start
/// `usage` carries no `cache_read_input_tokens` at all.
#[test]
def test_decode_text_turn_fixture : Bool :=
    let body := r#"{"content":[{"type":"text","text":"Hello!"}],"stop_reason":"end_turn","usage":{"input_tokens":10,"output_tokens":5}}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match MessagesResponse.deserialize_json j {
                Result.err _ => false,
                Result.ok resp =>
                    match Anthropic.decode_response resp {
                        Result.err _ => false,
                        Result.ok turn =>
                            match turn {
                                Turn.mk message usage stop =>
                                    match message {
                                        Message.mk role content =>
                                            String.beq (role_tag role) "assistant"
                                                && match content {
                                                    List.cons c _ => match c { Content.text s => String.beq s "Hello!", _ => false },
                                                    List.empty => false,
                                                }
                                                && match stop { StopReason.end_turn => true, _ => false }
                                                && match usage { Usage.mk in_t out_t _ => in_t == 10 && out_t == 5 },
                                    },
                            },
                    },
            },
    }

def role_tag (r : Role) : String :=
    match r {
        Role.system_ => "system",
        Role.user => "user",
        Role.assistant => "assistant",
        Role.tool => "tool",
    }

/// A recorded PARALLEL-tool-use turn: TWO `tool_use` blocks in one
/// assistant message, `stop_reason` `"tool_use"`. Both must decode,
/// each `input` already a real JSON object (no second parse on this
/// wire), and the stop reason must map to `tool_use_stop`.
#[test]
def test_decode_parallel_tool_use_fixture : Bool :=
    let body := r#"{"content":[{"type":"tool_use","id":"toolu_1","name":"read","input":{"path":"a.txt"}},{"type":"tool_use","id":"toolu_2","name":"read","input":{"path":"b.txt"}}],"stop_reason":"tool_use","usage":{"input_tokens":50,"output_tokens":20,"cache_read_input_tokens":12}}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match MessagesResponse.deserialize_json j {
                Result.err _ => false,
                Result.ok resp =>
                    match Anthropic.decode_response resp {
                        Result.err _ => false,
                        Result.ok turn =>
                            match turn {
                                Turn.mk message usage stop =>
                                    match message {
                                        Message.mk _ content =>
                                            List.length content == 2
                                                && both_tool_uses_decode content
                                                && match stop { StopReason.tool_use_stop => true, _ => false }
                                                && match usage { Usage.mk _ _ cached => cached == 12 },
                                    },
                            },
                    },
            },
    }

def both_tool_uses_decode (cs : List Content) : Bool :=
    match cs {
        List.cons c1 rest =>
            match c1 {
                Content.tool_use id1 _ input1 =>
                    String.beq id1 "toolu_1"
                        && match input1 { Json.object _ => true, _ => false }
                        && match rest {
                            List.cons c2 _ =>
                                match c2 {
                                    Content.tool_use id2 _ input2 =>
                                        String.beq id2 "toolu_2"
                                            && match input2 { Json.object _ => true, _ => false },
                                    _ => false,
                                },
                            List.empty => false,
                        },
                _ => false,
            },
        List.empty => false,
    }

/// A recorded REFUSAL: HTTP 200, `stop_reason` `"refusal"` -- it must
/// map to `StopReason.refusal`, NOT surface as an error (Phase 6's
/// own explicit requirement).
#[test]
def test_decode_refusal_is_stop_reason_not_error : Bool :=
    let body := r#"{"content":[{"type":"text","text":"I can't help with that."}],"stop_reason":"refusal","usage":{"input_tokens":10,"output_tokens":5}}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match MessagesResponse.deserialize_json j {
                Result.err _ => false,
                Result.ok resp =>
                    match Anthropic.decode_response resp {
                        Result.err _ => false,
                        Result.ok turn =>
                            match turn {
                                Turn.mk _ _ stop => match stop { StopReason.refusal => true, _ => false },
                            },
                    },
            },
    }

/// ALL `tool_result`s answering one assistant turn go in a SINGLE
/// user message (Design 3's parallel-tool-call rule): a `Role.tool`
/// message with two results encodes as ONE wire message carrying both
/// `tool_result` blocks -- never one message per result, the way the
/// OpenAI adapter must split them.
#[test]
def test_encode_folds_tool_results_into_one_user_message : Bool :=
    let tool_msg : Message := { role := Role.tool, content := [Content.tool_result "toolu_1" "out1" false, Content.tool_result "toolu_2" "out2" false] } in
    let req := Anthropic.encode_request "claude-opus-5" 512 "sys" [] [tool_msg] in
    match req {
        MessagesRequest.mk _ _ _ messages _ _ _ _ =>
            match messages {
                List.cons m _ =>
                    match m {
                        AnthropicMessage.mk role content =>
                            String.beq role "user" && List.length content == 2,
                    },
                List.empty => false,
            },
    }

/// `system` is top-level, never a message: encoding a history that
/// CONTAINS a `Role.system_` message must fold its text into the
/// request's system blocks and keep `messages` free of any system
/// entry.
#[test]
def test_encode_system_folds_top_level : Bool :=
    let sys_msg : Message := { role := Role.system_, content := [Content.text "extra rules"] } in
    let user_msg : Message := { role := Role.user, content := [Content.text "hi"] } in
    let req := Anthropic.encode_request "claude-opus-5" 512 "base system" [] [sys_msg, user_msg] in
    match req {
        MessagesRequest.mk _ _ system messages _ _ _ _ =>
            List.length system == 2
                && List.length messages == 1
                && match messages {
                    List.cons m _ => match m { AnthropicMessage.mk role _ => String.beq role "user" },
                    List.empty => false,
                },
    }

/// The last tool def carries the `cache_control` breakpoint (the
/// stable-prefix rule), and the emitted JSON shows the wire's exact
/// tool shape: flat, `input_schema`, no `function` nesting.
#[test]
def test_encode_marks_last_tool_cache_breakpoint : Bool :=
    let spec1 : ToolSpec := { name := "read", description := "read a file", schema := Json.make_object (Map.insert "type" (Json.make_str "object") BTreeMap.empty) } in
    let spec2 : ToolSpec := { name := "grep", description := "search", schema := Json.make_object (Map.insert "type" (Json.make_str "object") BTreeMap.empty) } in
    let req := Anthropic.encode_request "claude-opus-5" 512 "sys" [spec1, spec2] [] in
    let s := Json.to_string (MessagesRequest.serialize_json req) in
    String.contains s "cache_control"
        && String.contains s "input_schema"
        && Bool.not (String.contains s "function")

/// An assistant turn carrying `tool_use` content re-encodes as an
/// assistant message with `tool_use` blocks -- the history echo the
/// NEXT request must carry so the model sees its own prior calls.
#[test]
def test_encode_assistant_tool_use_history : Bool :=
    let input : Json := Json.make_object (Map.insert "path" (Json.make_str "a.txt") BTreeMap.empty) in
    let asst : Message := { role := Role.assistant, content := [Content.tool_use "toolu_1" "read" input] } in
    let req := Anthropic.encode_request "claude-opus-5" 512 "sys" [] [asst] in
    match req {
        MessagesRequest.mk _ _ _ messages _ _ _ _ =>
            match messages {
                List.cons m _ =>
                    match m {
                        AnthropicMessage.mk role blocks =>
                            String.beq role "assistant"
                                && match blocks {
                                    List.cons b _ => match b { Block.tool_use id _ _ _ => String.beq id "toolu_1", _ => false },
                                    List.empty => false,
                                },
                    },
                List.empty => false,
            },
    }

/// An API-authored thinking block carries a `signature` that must ride
/// the whole loop -- response body to normal form to the NEXT request
/// body -- because the API rejects replayed thinking without it. The
/// full path is the claim: decode to `Content.thinking`, re-encode, and
/// the wire still spells the signature.
#[test]
def test_thinking_signature_round_trips_the_adapter : Bool :=
    let body := r#"{"content":[{"type":"thinking","thinking":"reasoning here","signature":"sig_abc"}],"stop_reason":"end_turn","usage":{"input_tokens":10,"output_tokens":5}}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match MessagesResponse.deserialize_json j {
                Result.err _ => false,
                Result.ok resp =>
                    match Anthropic.decode_response resp {
                        Result.err _ => false,
                        Result.ok turn =>
                            match turn {
                                Turn.mk message _ _ =>
                                    match message {
                                        Message.mk _ content =>
                                            match content {
                                                List.cons c _ =>
                                                    match c {
                                                        Content.thinking _ signature =>
                                                            let asst : Message := { role := Role.assistant, content := [c] } in
                                                            let req := Anthropic.encode_request "claude-opus-5" 512 "sys" [] [asst] in
                                                            String.beq signature "sig_abc"
                                                                && String.contains (Json.to_string (MessagesRequest.serialize_json req)) "\"signature\":\"sig_abc\"",
                                                        _ => false,
                                                    },
                                                List.empty => false,
                                            },
                                    },
                            },
                    },
            },
    }
