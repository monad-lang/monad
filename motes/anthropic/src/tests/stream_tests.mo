/// Fixture tests for `Anthropic.complete_stream`'s core: the pure
/// per-event fold (`anthropic_apply_event` and the `anthropic_assemble`
/// finish), plus one IO-level test driving `anthropic_stream_bytes`
/// with raw SSE bytes -- an event split across two pushes -- to prove
/// the wire order of `on_text` deltas. The event payloads are the
/// Messages API's documented streaming shapes: typed events
/// (`message_start`, `content_block_start/delta/stop`, `message_delta`,
/// `message_stop`), `text_delta` for visible text, `thinking_delta` +
/// `signature_delta` for signed thinking, `input_json_delta`
/// fragments for tool inputs, usage split between `message_start`
/// (input half) and `message_delta` (output half).
use anthropic::client {AnthropicAcc, anthropic_apply_event, anthropic_assemble, anthropic_bad_input, anthropic_stream_bytes}
use anthropic::types {AnthropicMessage, MessagesRequest, MessagesResponse, AnthropicUsage, Block}
use json::json {Json, Json.to_string, Json.parse}
use http::sse {Sse.init}
use std::list {List.length}
use std::path {Path.of}
use std::process {process_id}
use std::io {IO.read_file, IO.write_file}

/// The accumulator every fold starts from -- the same zero state
/// `Anthropic.complete_stream` hands moose.
def stream_acc0 : AnthropicAcc :=
    { sse := Sse.init, blocks := [], stop := "", usage := AnthropicUsage.mk 0 0 0 }

/// Fold one event payload, keeping the accumulator.
def fold_event (acc : AnthropicAcc) (data : String) : AnthropicAcc :=
    match anthropic_apply_event acc data {
        Pair.pair acc2 _ => acc2
    }

/// A plain text turn: usage's input half from `message_start`, text
/// fragments concatenated into one text block, `end_turn` from
/// `message_delta`, and the output half of usage replacing the
/// placeholder from `message_start`.
#[test]
def test_stream_text_turn_assembles : Bool :=
    let a1 := fold_event stream_acc0 r#"{"type":"message_start","message":{"id":"msg_1","role":"assistant","content":[],"usage":{"input_tokens":10,"output_tokens":1}}}"# in
    let a2 := fold_event a1 r#"{"type":"content_block_start","index":0,"content_block":{"type":"text","text":""}}"# in
    let a3 := fold_event a2 r#"{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":"Hello"}}"# in
    let a4 := fold_event a3 r#"{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":" world"}}"# in
    let a5 := fold_event a4 r#"{"type":"content_block_stop","index":0}"# in
    let a6 := fold_event a5 r#"{"type":"message_delta","delta":{"stop_reason":"end_turn","stop_sequence":null},"usage":{"output_tokens":15}}"# in
    let a7 := fold_event a6 r#"{"type":"message_stop"}"# in
    match anthropic_assemble a7 {
        MessagesResponse.mk blocks stop usage =>
            Bool.and (stop == "end_turn")
                (match usage {
                    AnthropicUsage.mk in_t out_t cached =>
                        Bool.and (in_t == 10) (Bool.and (out_t == 15) (cached == 0))
                })
                && match blocks {
                    List.cons b _ => match b { Block.text s _ => s == "Hello world", _ => false },
                    List.empty => false,
                }
    }

/// `message_delta`'s `stop_reason` is the tool-use stop: the assembled
/// response must carry it through for shuttle's adapter to map to
/// `tool_use_stop`.
#[test]
def test_stream_tool_use_stop_reason : Bool :=
    let a1 := fold_event stream_acc0 r#"{"type":"message_delta","delta":{"stop_reason":"tool_use"},"usage":{"output_tokens":20}}"# in
    match anthropic_assemble a1 {
        MessagesResponse.mk _ stop _ => stop == "tool_use"
    }

/// A turn that ends without `message_delta` (a dropped connection)
/// still assembles with the one-shot decode's own default.
#[test]
def test_stream_stop_reason_defaults_to_end_turn : Bool :=
    match anthropic_assemble stream_acc0 {
        MessagesResponse.mk _ stop _ => stop == "end_turn"
    }

/// Signed thinking: fragments concatenate into the block's text, the
/// signature arrives whole in its own delta and must survive verbatim
/// for replay (the API rejects replayed thinking without it).
#[test]
def test_stream_thinking_and_signature : Bool :=
    let a1 := fold_event stream_acc0 r#"{"type":"content_block_start","index":0,"content_block":{"type":"thinking","thinking":""}}"# in
    let a2 := fold_event a1 r#"{"type":"content_block_delta","index":0,"delta":{"type":"thinking_delta","thinking":"step one; "}}"# in
    let a3 := fold_event a2 r#"{"type":"content_block_delta","index":0,"delta":{"type":"thinking_delta","thinking":"step two"}}"# in
    let a4 := fold_event a3 r#"{"type":"content_block_delta","index":0,"delta":{"type":"signature_delta","signature":"sig_abc"}}"# in
    match anthropic_assemble a4 {
        MessagesResponse.mk blocks _ _ =>
            match blocks {
                List.cons b _ =>
                    match b {
                        Block.thinking s signature _ => s == "step one; step two" && signature == "sig_abc",
                        _ => false,
                    },
                List.empty => false,
            }
    }

/// Thinking fragments are SILENT: only `text_delta` ever reports to
/// `on_text` -- the thinking accumulation must not emit.
#[test]
def test_stream_thinking_delta_reports_no_text : Bool :=
    let a1 := fold_event stream_acc0 r#"{"type":"content_block_start","index":0,"content_block":{"type":"thinking","thinking":""}}"# in
    match anthropic_apply_event a1 r#"{"type":"content_block_delta","index":0,"delta":{"type":"thinking_delta","thinking":"hmm"}}"# {
        Pair.pair _ delta => delta == ""
    }

/// Tool use across TWO blocks (text at index 0, tool at index 1):
/// `partial_json` fragments concatenate into the tool's input JSON
/// text, and assembly parses it back to a real object -- the one-shot
/// wire's shape, which shuttle's adapter decodes with no second parse.
#[test]
def test_stream_tool_input_fragments_assemble : Bool :=
    let a1 := fold_event stream_acc0 r#"{"type":"content_block_start","index":0,"content_block":{"type":"text","text":""}}"# in
    let a2 := fold_event a1 r#"{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":"Reading."}}"# in
    let a3 := fold_event a2 r#"{"type":"content_block_start","index":1,"content_block":{"type":"tool_use","id":"toolu_1","name":"read","input":{}}}"# in
    let a4 := fold_event a3 r#"{"type":"content_block_delta","index":1,"delta":{"type":"input_json_delta","partial_json":"{\"path\":"}}"# in
    let a5 := fold_event a4 r#"{"type":"content_block_delta","index":1,"delta":{"type":"input_json_delta","partial_json":"\"/tmp\"}"}}"# in
    match anthropic_assemble a5 {
        MessagesResponse.mk blocks _ _ =>
            match blocks {
                List.cons _ rest =>
                    match rest {
                        List.cons b _ =>
                            match b {
                                Block.tool_use id name input _ =>
                                    id == "toolu_1"
                                        && name == "read"
                                        && match input {
                                            Json.object obj =>
                                                match Json.object_get "path" obj {
                                                    Option.some v => match v { Json.str s => s == "/tmp", _ => false },
                                                    Option.none => false,
                                                },
                                            _ => false,
                                        },
                                _ => false,
                            },
                        List.empty => false,
                    },
                List.empty => false,
            }
    }

#[partial]
def text_at (blocks : List Block) (i : I64) : String :=
    match blocks {
        List.cons b rest =>
            if i == 0
            then match b { Block.text s _ => s, _ => "" }
            else text_at rest (I64.sub i 1),
        List.empty => "",
    }

/// The first assembled text block's text, for the IO-level test that
/// asserts the folded accumulator matches what the tap captured (the
/// accumulator's `blocks` are `Option Block` entries -- wire-index
/// slots -- so the assertion goes through the assembled response).
def assembled_text_of (acc : AnthropicAcc) : String :=
    match anthropic_assemble acc {
        MessagesResponse.mk blocks _ _ => text_at blocks 0
    }

/// An unparseable payload is skipped whole -- the stream survives a
/// garbled event and keeps everything before and after it.
#[test]
def test_stream_unparseable_event_is_skipped : Bool :=
    let a1 := fold_event stream_acc0 r#"{"type":"content_block_start","index":0,"content_block":{"type":"text","text":""}}"# in
    let a2 := fold_event a1 "not json at all" in
    let a3 := fold_event a2 r#"{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":"ok"}}"# in
    match anthropic_assemble a3 {
        MessagesResponse.mk blocks _ _ =>
            match blocks {
                List.cons b _ => match b { Block.text s _ => s == "ok", _ => false },
                List.empty => false,
            }
    }

/// A block type this mote does not model (`redacted_thinking` is
/// already in the wild) occupies its wire index as `Option.none`: the
/// block is absent from the assembled response, and every LATER
/// delta still patches the block ITS index names -- the streaming
/// counterpart of the one-shot decode's per-block skip.
#[test]
def test_stream_unknown_block_keeps_delta_alignment : Bool :=
    let a1 := fold_event stream_acc0 r#"{"type":"content_block_start","index":0,"content_block":{"type":"text","text":""}}"# in
    let a2 := fold_event a1 r#"{"type":"content_block_start","index":1,"content_block":{"type":"redacted_thinking","data":"[encrypted]"}}"# in
    let a3 := fold_event a2 r#"{"type":"content_block_start","index":2,"content_block":{"type":"text","text":""}}"# in
    let a4 := fold_event a3 r#"{"type":"content_block_delta","index":2,"delta":{"type":"text_delta","text":"tail"}}"# in
    match anthropic_assemble a4 {
        MessagesResponse.mk blocks _ _ =>
            Bool.and (List.length blocks == 2)
                (Bool.and (text_at blocks 0 == "")
                    (text_at blocks 1 == "tail"))
    }

/// A truncated tool input (the stream dropped mid-fragment) must be
/// REFUSED at the stream boundary, not assembled as `{}` -- the
/// harness would otherwise execute a tool with guessed-empty
/// arguments. The decision def is pure, so the refusal is testable
/// without a transport.
#[test]
def test_stream_truncated_tool_input_is_refused : Bool :=
    let a1 := fold_event stream_acc0 r#"{"type":"content_block_start","index":0,"content_block":{"type":"tool_use","id":"toolu_1","name":"read","input":{}}}"# in
    let a2 := fold_event a1 r#"{"type":"content_block_delta","index":0,"delta":{"type":"input_json_delta","partial_json":"{\"path\":"}}"# in
    match anthropic_bad_input a2.blocks {
        Option.some e => String.contains e "did not parse",
        Option.none => false,
    }

/// A completed tool input is not refused: the same walk that flags a
/// truncated fragment passes a whole one.
#[test]
def test_stream_complete_tool_input_is_not_refused : Bool :=
    let a1 := fold_event stream_acc0 r#"{"type":"content_block_start","index":0,"content_block":{"type":"tool_use","id":"toolu_1","name":"read","input":{}}}"# in
    let a2 := fold_event a1 r#"{"type":"content_block_delta","index":0,"delta":{"type":"input_json_delta","partial_json":"{\"path\":"}}"# in
    let a3 := fold_event a2 r#"{"type":"content_block_delta","index":0,"delta":{"type":"input_json_delta","partial_json":"\"/tmp\"}"}}"# in
    match anthropic_bad_input a3.blocks {
        Option.some _ => false,
        Option.none => true,
    }

/// `message_start`'s `output_tokens` is a placeholder; the real output
/// count arrives in `message_delta`. A stream that ends without one
/// reports ZERO output, not the placeholder.
#[test]
def test_stream_usage_output_zero_until_message_delta : Bool :=
    let a1 := fold_event stream_acc0 r#"{"type":"message_start","message":{"id":"msg_1","role":"assistant","content":[],"usage":{"input_tokens":10,"output_tokens":1}}}"# in
    match anthropic_assemble a1 {
        MessagesResponse.mk _ _ usage =>
            match usage {
                AnthropicUsage.mk in_t out_t _ => Bool.and (in_t == 10) (out_t == 0)
            }
    }

/// A `text_delta` for a block that never started (or one this mote
/// does not model) reports nothing to `on_text` -- the live output
/// can never diverge from the assembled response.
#[test]
def test_stream_delta_for_unstarted_block_reports_no_text : Bool :=
    match anthropic_apply_event stream_acc0 r#"{"type":"content_block_delta","index":3,"delta":{"type":"text_delta","text":"orphan"}}"# {
        Pair.pair _ delta => delta == ""
    }

/// The request half: `stream` is serialized ONLY when true -- the
/// wire's omission convention for optional segments, and the field
/// `{ req with stream := true }` relies on to switch the endpoint.
#[test]
def test_stream_request_serializes_only_when_true : Bool :=
    let msg : AnthropicMessage := { role := "user", content := [] } in
    let req : MessagesRequest := { model := "claude-opus-5", max_tokens := 512, system := [], messages := [msg], tools := [], thinking := false, effort := Option.none } in
    let s := Json.to_string (MessagesRequest.serialize_json req) in
    let s2 := Json.to_string (MessagesRequest.serialize_json { req with stream := true }) in
    Bool.and (Bool.not (String.contains s "stream")) (String.contains s2 "\"stream\":true")

// ── IO level: raw SSE bytes through the moose callback ──────────────

/// PID-qualified so two sessions' test runs sharing /tmp never collide.
def tap_path : String :=
    String.concat "/tmp/anthropic_stream_tap_" (String.concat (I64.to_string process_id) ".txt")

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

/// A `text_delta` split across two pushes (the first ends mid-JSON,
/// no newline yet), with `event:` lines present exactly as the wire
/// sends them: the SSE state machine must buffer the partial, the
/// completed event must report its delta to `on_text` in order, and
/// `message_stop`/`content_block_stop` must fold silently.
#[test]
def test_stream_bytes_emits_deltas_in_wire_order : IO Bool := do {
    reset_tap;
    let r1 <- anthropic_stream_bytes text_tap stream_acc0 (String.to_list "event: message_start\ndata: {\"type\":\"message_start\",\"message\":{\"usage\":{\"input_tokens\":3,\"output_tokens\":1}}}\n\nevent: content_block_start\ndata: {\"type\":\"content_block_start\",\"index\":0,\"content_block\":{\"type\":\"text\",\"text\":\"\"}}\n\nevent: content_block_delta\ndata: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"Hel");
    match r1 {
        Result.err _ => return false,
        Result.ok pr1 =>
            match pr1 {
                Pair.pair acc1 _ => do {
                    let r2 <- anthropic_stream_bytes text_tap acc1 (String.to_list "lo\"}}\n\nevent: content_block_delta\ndata: {\"type\":\"content_block_delta\",\"index\":0,\"delta\":{\"type\":\"text_delta\",\"text\":\"!\"}}\n\nevent: message_stop\ndata: {\"type\":\"message_stop\"}\n\n");
                    match r2 {
                        Result.err _ => return false,
                        Result.ok pr2 =>
                            match pr2 {
                                Pair.pair acc2 _ => do {
                                    let tapped <- read_tap;
                                    return (Bool.and (tapped == "Hello!")
                                        (assembled_text_of acc2 == "Hello!"))
                                }
                            }
                    }
                }
            }
    }
}
