/// Wire-level tests for the anthropic mote's hand-written codecs --
/// the wire SHAPE is the claim being tested, so assertions run against
/// the serialized JSON text (recorded-fixture style, per
/// agent-skills.md Phase 6) rather than through a round-trip that
/// could agree with itself while diverging from the wire.
use anthropic::types {Block, AnthropicMessage, AnthropicTool, MessagesRequest, AnthropicUsage, MessagesResponse}
use json::json {Json}
use std::map {BTreeMap}

#[test]
def test_request_minimal_shape_max_tokens_required : Bool :=
    let msg : AnthropicMessage := { role := "user", content := [Block.text "hi" false] } in
    let req : MessagesRequest := { model := "claude-opus-5", max_tokens := 512, system := [], messages := [msg], tools := [], thinking := false, effort := Option.none } in
    let s := Json.to_string (MessagesRequest.serialize_json req) in
    String.contains s "\"max_tokens\":512"
        && Bool.not (String.contains s "\"system\"")
        && Bool.not (String.contains s "\"tools\"")
        && Bool.not (String.contains s "\"thinking\"")
        && Bool.not (String.contains s "\"output_config\"")

#[test]
def test_request_thinking_adaptive_and_effort : Bool :=
    let msg : AnthropicMessage := { role := "user", content := [Block.text "hi" false] } in
    let req : MessagesRequest := { model := "claude-opus-5", max_tokens := 512, system := [], messages := [msg], tools := [], thinking := true, effort := Option.some "high" } in
    let s := Json.to_string (MessagesRequest.serialize_json req) in
    String.contains s "\"thinking\":{\"type\":\"adaptive\"}"
        && String.contains s "\"output_config\":{\"effort\":\"high\"}"

/// The system prompt is a TOP-LEVEL block array, not a message --
/// the single biggest structural difference from the OpenAI wire.
#[test]
def test_request_system_is_top_level_block_array : Bool :=
    let msg : AnthropicMessage := { role := "user", content := [Block.text "hi" false] } in
    let req : MessagesRequest := { model := "claude-opus-5", max_tokens := 512, system := [Block.text "be helpful" true], messages := [msg], tools := [], thinking := false, effort := Option.none } in
    let s := Json.to_string (MessagesRequest.serialize_json req) in
    String.contains s "\"system\":[{\"cache_control\":{\"type\":\"ephemeral\"},\"text\":\"be helpful\",\"type\":\"text\"}]"
        && Bool.not (String.contains s "\"role\":\"system\"")

/// Anthropic's tool table is FLAT -- `{name, description,
/// input_schema}` with NO `function` nesting, the exact opposite of
/// the OpenAI wire's shape (which nesting-live-verified against
/// Ollama on 2026-10-13; see `motes/openai/src/tool.mo`'s header).
#[test]
def test_tool_def_is_flat_with_input_schema : Bool :=
    let schema : Json := Json.make_object (Map.insert "type" (Json.make_str "object") BTreeMap.empty) in
    let tool : AnthropicTool := { name := "grep", description := "search", input_schema := schema, cache := false } in
    let s := Json.to_string (AnthropicTool.serialize_json tool) in
    String.contains s "\"name\":\"grep\""
        && String.contains s "\"input_schema\":{\"type\":\"object\"}"
        && Bool.not (String.contains s "function")

#[test]
def test_tool_use_block_input_stays_json_object : Bool :=
    let input : Json := Json.make_object (Map.insert "pattern" (Json.make_str "foo") BTreeMap.empty) in
    match Block.deserialize_json (Block.serialize_json (Block.tool_use "toolu_1" "grep" input false)) {
        Result.err _ => false,
        Result.ok b =>
            match b {
                Block.tool_use id name decoded_input _ =>
                    String.beq id "toolu_1"
                        && match decoded_input { Json.object _ => true, _ => false },
                _ => false,
            },
    }

/// `is_error` is omitted when false and present when true -- the
/// wire's own convention, and the decode accepts both.
#[test]
def test_tool_result_block_is_error_only_when_true : Bool :=
    let ok_s := Json.to_string (Block.serialize_json (Block.tool_result "toolu_1" "done" false false)) in
    let err_s := Json.to_string (Block.serialize_json (Block.tool_result "toolu_1" "boom" true false)) in
    String.contains ok_s "\"tool_use_id\":\"toolu_1\""
        && Bool.not (String.contains ok_s "is_error")
        && String.contains err_s "\"is_error\":true"

#[test]
def test_tool_result_block_decodes_absent_is_error : Bool :=
    let body := r#"{"type":"tool_result","tool_use_id":"toolu_1","content":"done"}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match Block.deserialize_json j {
                Result.err _ => false,
                Result.ok b =>
                    match b {
                        Block.tool_result tool_use_id content is_error _ =>
                            String.beq tool_use_id "toolu_1" && Bool.not is_error,
                        _ => false,
                    },
            },
    }

/// A recorded response body: a plain text turn. `usage` carries NO
/// `cache_read_input_tokens` on a cold start -- it must default to
/// zero, not fail the whole decode.
#[test]
def test_response_decode_text_turn : Bool :=
    let body := r#"{"content":[{"type":"text","text":"Hello!"}],"stop_reason":"end_turn","usage":{"input_tokens":10,"output_tokens":5}}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match MessagesResponse.deserialize_json j {
                Result.err _ => false,
                Result.ok resp =>
                    match resp {
                        MessagesResponse.mk content stop_reason usage =>
                            match content {
                                List.cons b _ =>
                                    match b {
                                        Block.text s _ => String.beq s "Hello!" && String.beq stop_reason "end_turn",
                                        _ => false,
                                    },
                                List.empty => false,
                            } && match usage { AnthropicUsage.mk in_t out_t cached => in_t == 10 && out_t == 5 && cached == 0 },
                    },
            },
    }

#[test]
def test_response_decode_reports_cache_read_tokens : Bool :=
    let body := r#"{"content":[{"type":"text","text":"hi"}],"stop_reason":"end_turn","usage":{"input_tokens":10,"output_tokens":5,"cache_read_input_tokens":8}}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match MessagesResponse.deserialize_json j {
                Result.err _ => false,
                Result.ok resp =>
                    match resp {
                        MessagesResponse.mk _ _ usage => match usage { AnthropicUsage.mk _ _ cached => cached == 8 },
                    },
            },
    }

/// A thinking block uses the `thinking` KEY (not `text`), matching
/// the wire -- decoding it as `text` would silently drop reasoning
/// turns from the transcript. A harness-authored block carries no
/// `signature`, so serialize omits the field entirely.
#[test]
def test_thinking_block_roundtrip : Bool :=
    let s := Json.to_string (Block.serialize_json (Block.thinking "hmm" "" false)) in
    Bool.not (String.contains s "signature")
        && match Block.deserialize_json (Block.serialize_json (Block.thinking "hmm" "" false)) {
            Result.err _ => false,
            Result.ok b =>
                match b {
                    Block.thinking s _ _ => String.beq s "hmm",
                    _ => false,
                },
        }

/// The API attaches a `signature` to its own thinking blocks and checks
/// it on verbatim replay: decode must read it, and re-encode must emit
/// it byte-for-byte -- dropping it would make replayed thinking 400.
#[test]
def test_thinking_block_carries_its_signature : Bool :=
    let body := r#"{"type":"thinking","thinking":"hmm","signature":"sig_abc"}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match Block.deserialize_json j {
                Result.err _ => false,
                Result.ok b =>
                    match b {
                        Block.thinking s signature _ =>
                            String.beq s "hmm" && String.beq signature "sig_abc"
                                && String.contains (Json.to_string (Block.serialize_json b)) "\"signature\":\"sig_abc\"",
                        _ => false,
                    },
            },
    }

/// `redacted_thinking` is a real block type this mote does not model:
/// response decode SKIPS it rather than failing the whole turn (the
/// alternative loses every response that uses encrypted reasoning).
#[test]
def test_response_decode_skips_unknown_block_types : Bool :=
    let body := r#"{"content":[{"type":"redacted_thinking","data":"enc"},{"type":"text","text":"kept"}],"stop_reason":"end_turn","usage":{"input_tokens":10,"output_tokens":5}}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match MessagesResponse.deserialize_json j {
                Result.err _ => false,
                Result.ok resp =>
                    match resp {
                        MessagesResponse.mk content _ _ =>
                            match content {
                                List.cons b rest =>
                                    match b {
                                        Block.text s _ => String.beq s "kept" && List.is_empty rest,
                                        _ => false,
                                    },
                                List.empty => false,
                            },
                    },
            },
    }

/// `stop_reason` is typed NULLABLE by the API: a response without one
/// decodes as `"end_turn"` (end-of-turn), not a decode failure.
#[test]
def test_response_decode_defaults_missing_stop_reason : Bool :=
    let body := r#"{"content":[{"type":"text","text":"hi"}],"stop_reason":null,"usage":{"input_tokens":10,"output_tokens":5}}"# in
    match Json.parse body {
        Result.err _ => false,
        Result.ok j =>
            match MessagesResponse.deserialize_json j {
                Result.err _ => false,
                Result.ok resp =>
                    match resp {
                        MessagesResponse.mk _ stop_reason _ => String.beq stop_reason "end_turn",
                    },
            },
    }
