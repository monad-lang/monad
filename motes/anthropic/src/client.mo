/// A thin, one-shot HTTP call to the Anthropic Messages endpoint,
/// mirroring `motes/openai/src/client.mo`'s shape: `ResultT String IO`
/// so a caller composes it with real do-notation, `base_url` a config
/// level host root parsed to a `Uri` exactly once at the boundary.
///
/// Auth is REQUIRED here, not `Option`: the OpenAI client needs an
/// anonymous mode (a local Ollama), but Anthropic has no anonymous
/// endpoint -- an empty key is a caller error the type forbids, not a
/// request the wire would reject anyway. The key travels in the
/// `x-api-key` header, never `Authorization: Bearer`.
///
/// `refusal` is decoded, not errored: Anthropic reports a refusal as
/// an ordinary HTTP 200 body with `"stop_reason":"refusal"`, so only
/// non-200 statuses take this path's error branch -- the plan's own
/// checklist calls that out as a fact to encode rather than discover
/// in production.
use init::transformers {ResultT}
use json::json {
    Json, Json.to_string, Json.parse, Json.ParseError.to_string, Json.get_str,
    Json.get_object, Json.get_num, Json.get_num_i64, Json.object_get, Json.make_object,
}
use http::types {Headers, Headers.empty, Headers.set, Response, Uri, Status.ok}
use http::uri {Uri.parse}
use http::body {Body.from_text, Body.to_bytes_pure}
use http::sse {Sse.init, Sse.push, SseState, SseEvent}
use moose::client {Client.post, Client.post_stream}
use anthropic::types {MessagesRequest, MessagesResponse, AnthropicUsage, Block}
use std::map {BTreeMap}

def anthropic_headers (api_key : String) : Headers :=
    Headers.set "x-api-key" api_key
        (Headers.set "anthropic-version" "2023-06-01"
            (Headers.set "Content-Type" "application/json" Headers.empty))

def decode_messages_response (r : Response) : Result String MessagesResponse :=
    let text := String.from_list (Body.to_bytes_pure r.body) in
    if U16.beq r.status Status.ok then
        match Json.parse text {
            Result.err e => Result.err (Json.ParseError.to_string e),
            Result.ok j => MessagesResponse.deserialize_json j,
        }
    else
        Result.err (String.concat "anthropic: HTTP "
            (String.concat (U16.to_string r.status)
            (String.concat ": " text)))

def anthropic_complete_io (u : Uri) (headers : Headers) (body_str : String) : IO (Result String MessagesResponse) := do {
    let resp <- Client.post u headers (Body.from_text body_str);
    return (match resp {
        Result.err e => Result.err e,
        Result.ok r => decode_messages_response r,
    })
}

/// POST `{base_url}/v1/messages`. Note this is `https://` territory
/// (`api.anthropic.com`), and `moose` speaks plaintext HTTP/1.1 today
/// -- actually reaching Anthropic waits on `library-ideas/tls.md`.
/// The seam is deliberate: a `base_url` that starts with `https://`
/// is a config-level concern; nothing in this mote changes when TLS
/// lands (agent-skills.md Design 2's own rule).
pub def Anthropic.complete (base_url : String) (api_key : String) (req : MessagesRequest) : ResultT String IO MessagesResponse :=
    let body_str := Json.to_string (MessagesRequest.serialize_json req) in
    let url_str := String.concat base_url "/v1/messages" in
    match Uri.parse url_str {
        Result.err e => ResultT.mk (return (Result.err e)),
        Result.ok u => ResultT.mk (anthropic_complete_io u (anthropic_headers api_key) body_str),
    }

// ── Streaming ──────────────────────────────────────────────────────────
//
// `Anthropic.complete_stream` is `Anthropic.complete` over the SSE
// wire: the request gains `stream := true`, and the response arrives
// as typed events -- `message_start` (usage), `content_block_start`
// (a block opened at an index), `content_block_delta` (text_delta /
// thinking_delta / signature_delta / input_json_delta fragments
// patching that block), `message_delta` (stop_reason, final output
// usage), `content_block_stop`/`message_stop`/`ping` (no payload).
// The per-event work is PURE (`anthropic_apply_event`), so fixture
// tests need no transport; the IO half only feeds the SSE state
// machine and hands text deltas to `on_text`. The return value is
// the SAME `MessagesResponse` shape `Anthropic.complete` returns, so
// shuttle's adapter decodes both paths unchanged.

/// The streaming fold state: the SSE line discipline plus what one
/// response accumulates. `blocks` is indexed by the wire's
/// `content_block` index -- a block is appended by
/// `content_block_start` and patched in place by each delta. Usage
/// starts zeroed: `message_start` carries the input half, and
/// `message_delta` the output half, so either may legitimately never
/// arrive.
struct AnthropicAcc {
    sse : SseState,
    blocks : List Block,
    stop : String,
    usage : AnthropicUsage,
}

/// A string field read leniently: absent, null, or wrong-tag is none
/// -- streaming events legitimately omit most fields.
def anthropic_str_of (key : String) (obj : BTreeMap String Json) : Option String :=
    match Json.object_get key obj {
        Option.none => Option.none,
        Option.some j =>
            match Json.get_str j {
                Result.err _ => Option.none,
                Result.ok s => Option.some s,
            },
    }

/// An int field read leniently: absent or non-numeric is 0.
def anthropic_int_of (key : String) (obj : BTreeMap String Json) : I64 :=
    match Json.object_get key obj {
        Option.none => 0,
        Option.some j =>
            match Json.get_num_i64 (Json.get_num j) {
                Result.err _ => 0,
                Result.ok n => n,
            },
    }

/// The `message_start` usage object: the input half of the turn's
/// accounting (plus the cache counter when the server sends one).
def anthropic_usage_of (j : Json) : AnthropicUsage :=
    match Json.get_object j {
        Result.err _ => AnthropicUsage.mk 0 0 0,
        Result.ok obj =>
            AnthropicUsage.mk (anthropic_int_of "input_tokens" obj) (anthropic_int_of "output_tokens" obj) (anthropic_int_of "cache_read_input_tokens" obj),
    }

/// The accumulated `input_json_delta` partial so far -- `""` before
/// the first fragment (the block-start `input` is always `{}`).
def anthropic_partial_of (input : Json) : String :=
    match input {
        Json.str s => s,
        _ => "",
    }

/// Patch the block at `idx` with one delta object. A delta for a block
/// that never started is dropped -- lenient, same reasoning as every
/// skip in this fold.
#[terminating]
def anthropic_patch_at (blocks : List Block) (idx : I64) (dobj : BTreeMap String Json) : List Block :=
    match blocks {
        List.empty => blocks,
        List.cons b rest =>
            if idx == 0
            then List.cons (anthropic_block_delta b dobj) rest
            else List.cons b (anthropic_patch_at rest (I64.sub idx 1) dobj)
    }

def anthropic_block_delta (b : Block) (dobj : BTreeMap String Json) : Block :=
    match anthropic_str_of "type" dobj {
        Option.none => b,
        Option.some tag => anthropic_block_typed b tag dobj
    }

/// One delta, dispatched by the wire's own `delta.type`. The type tags
/// are positional per block kind: a text delta on a non-text block (or
/// vice versa) leaves the block untouched.
def anthropic_block_typed (b : Block) (tag : String) (dobj : BTreeMap String Json) : Block :=
    if tag == "text_delta"
    then anthropic_block_text b dobj
    else if tag == "thinking_delta"
    then anthropic_block_thinking b dobj
    else if tag == "signature_delta"
    then anthropic_block_signature b dobj
    else if tag == "input_json_delta"
    then anthropic_block_input b dobj
    else b

def anthropic_block_text (b : Block) (dobj : BTreeMap String Json) : Block :=
    match anthropic_str_of "text" dobj {
        Option.none => b,
        Option.some frag =>
            match b {
                Block.text s cache => Block.text (String.concat s frag) cache,
                _ => b,
            },
    }

/// Thinking fragments concatenate, exactly like text -- the signed-
/// thinking round-trip (`signature` preserved verbatim for replay)
/// is `anthropic_block_signature`'s job below.
def anthropic_block_thinking (b : Block) (dobj : BTreeMap String Json) : Block :=
    match anthropic_str_of "thinking" dobj {
        Option.none => b,
        Option.some frag =>
            match b {
                Block.thinking s signature cache => Block.thinking (String.concat s frag) signature cache,
                _ => b,
            },
    }

/// The signature arrives WHOLE in one delta (it is an attestation,
/// not streamed text): it replaces, never concatenates.
def anthropic_block_signature (b : Block) (dobj : BTreeMap String Json) : Block :=
    match anthropic_str_of "signature" dobj {
        Option.none => b,
        Option.some sig =>
            match b {
                Block.thinking s _ cache => Block.thinking s sig cache,
                _ => b,
            },
    }

/// `partial_json` fragments concatenate into the tool input's JSON
/// text; the accumulated string is parsed at ASSEMBLY time (the
/// one-shot wire's `input` is a real object, and the assembled
/// response must match it).
def anthropic_block_input (b : Block) (dobj : BTreeMap String Json) : Block :=
    match anthropic_str_of "partial_json" dobj {
        Option.none => b,
        Option.some frag =>
            match b {
                Block.tool_use id name input cache =>
                    Block.tool_use id name (Json.str (String.concat (anthropic_partial_of input) frag)) cache,
                _ => b,
            },
    }

/// `message_start`: the input usage half.
def anthropic_apply_message_start (acc : AnthropicAcc) (obj : BTreeMap String Json) : AnthropicAcc :=
    match Json.object_get "message" obj {
        Option.none => acc,
        Option.some mj =>
            match Json.get_object mj {
                Result.err _ => acc,
                Result.ok mobj =>
                    match Json.object_get "usage" mobj {
                        Option.none => acc,
                        Option.some uj => AnthropicAcc.mk acc.sse acc.blocks acc.stop (anthropic_usage_of uj),
                    }
            },
    }

/// `content_block_start`: append the block the wire opens. The block
/// JSON is exactly a wire block -- decode it with the one-shot path.
def anthropic_apply_block_start (acc : AnthropicAcc) (obj : BTreeMap String Json) : AnthropicAcc :=
    match Json.object_get "content_block" obj {
        Option.none => acc,
        Option.some bj =>
            match Block.deserialize_json bj {
                Result.err _ => acc,
                Result.ok b => AnthropicAcc.mk acc.sse (List.append acc.blocks (List.singleton b)) acc.stop acc.usage,
            },
    }

/// The text a delta emits to `on_text` -- only `text_delta` ever
/// reports; thinking and tool-input fragments accumulate silently.
def anthropic_text_of (dobj : BTreeMap String Json) : String :=
    match anthropic_str_of "type" dobj {
        Option.some tag =>
            if String.beq tag "text_delta"
            then match anthropic_str_of "text" dobj { Option.some s => s, Option.none => "" }
            else "",
        Option.none => "",
    }

/// `content_block_delta`: patch the block at the wire's index.
def anthropic_apply_block_delta_event (acc : AnthropicAcc) (obj : BTreeMap String Json) : Pair AnthropicAcc String :=
    let idx : I64 := anthropic_int_of "index" obj in
    match Json.object_get "delta" obj {
        Option.none => Pair.pair acc "",
        Option.some dj =>
            match Json.get_object dj {
                Result.err _ => Pair.pair acc "",
                Result.ok dobj =>
                    Pair.pair (AnthropicAcc.mk acc.sse (anthropic_patch_at acc.blocks idx dobj) acc.stop acc.usage) (anthropic_text_of dobj)
            },
    }

/// `message_delta`'s `delta.stop_reason` -- null until the last one.
def anthropic_delta_stop (acc : AnthropicAcc) (obj : BTreeMap String Json) : AnthropicAcc :=
    match Json.object_get "delta" obj {
        Option.none => acc,
        Option.some dj =>
            match Json.get_object dj {
                Result.err _ => acc,
                Result.ok dobj =>
                    match anthropic_str_of "stop_reason" dobj {
                        Option.none => acc,
                        Option.some s => AnthropicAcc.mk acc.sse acc.blocks s acc.usage,
                    }
            },
    }

/// `message_delta`'s top-level `usage` -- the output half only; the
/// input half from `message_start` must survive.
def anthropic_delta_usage (acc : AnthropicAcc) (obj : BTreeMap String Json) : AnthropicAcc :=
    match Json.object_get "usage" obj {
        Option.none => acc,
        Option.some uj =>
            match Json.get_object uj {
                Result.err _ => acc,
                Result.ok uobj =>
                    match acc.usage {
                        AnthropicUsage.mk in_t _ cached =>
                            AnthropicAcc.mk acc.sse acc.blocks acc.stop (AnthropicUsage.mk in_t (anthropic_int_of "output_tokens" uobj) cached)
                    }
            },
    }

/// `message_delta`: stop reason, then the final output usage.
def anthropic_apply_message_delta (acc : AnthropicAcc) (obj : BTreeMap String Json) : AnthropicAcc :=
    anthropic_delta_usage (anthropic_delta_stop acc obj) obj

/// One complete SSE event payload, dispatched by its own `type` field.
/// `content_block_stop`, `message_stop`, and `ping` are consumed here;
/// an unparseable payload is skipped -- the stream's terminator is the
/// CHUNKED body's last chunk (see `http::wire`), not a sentinel event.
def anthropic_apply_event (acc : AnthropicAcc) (data : String) : Pair AnthropicAcc String :=
    match Json.parse data {
        Result.err _ => Pair.pair acc "",
        Result.ok j =>
            match Json.get_object j {
                Result.err _ => Pair.pair acc "",
                Result.ok obj =>
                    match anthropic_str_of "type" obj {
                        Option.none => Pair.pair acc "",
                        Option.some tag => anthropic_apply_typed acc tag obj,
                    }
            }
    }

def anthropic_apply_typed (acc : AnthropicAcc) (tag : String) (obj : BTreeMap String Json) : Pair AnthropicAcc String :=
    if tag == "message_start"
    then Pair.pair (anthropic_apply_message_start acc obj) ""
    else if tag == "content_block_start"
    then Pair.pair (anthropic_apply_block_start acc obj) ""
    else if tag == "content_block_delta"
    then anthropic_apply_block_delta_event acc obj
    else if tag == "message_delta"
    then Pair.pair (anthropic_apply_message_delta acc obj) ""
    else Pair.pair acc ""

/// Fold every event a byte push completed, reporting each non-empty
/// text delta in wire order -- the pure half of the moose callback.
#[terminating]
def anthropic_apply_events (acc : AnthropicAcc) (events : List SseEvent) (out : List String) : Pair AnthropicAcc (List String) :=
    match events {
        List.empty => Pair.pair acc (List.reverse out),
        List.cons ev rest =>
            match anthropic_apply_event acc ev.data {
                Pair.pair acc2 delta =>
                    if delta == ""
                    then anthropic_apply_events acc2 rest out
                    else anthropic_apply_events acc2 rest (List.cons delta out)
            }
    }

/// A tool input's accumulated `partial_json` text back to a real JSON
/// object, matching the one-shot wire (`input` is an object, never a
/// string). Empty stays the block-start `{}`; a parse failure falls
/// back to `{}` rather than killing the stream -- the same leniency
/// trade-off `Block.deserialize_or_skip` documents.
def anthropic_finalize_input (input : Json) : Json :=
    match input {
        Json.str s =>
            if s == ""
            then Json.make_object BTreeMap.empty
            else
                match Json.parse s {
                    Result.err _ => Json.make_object BTreeMap.empty,
                    Result.ok j => j,
                },
        _ => input,
    }

def anthropic_finalize_block (b : Block) : Block :=
    match b {
        Block.tool_use id name input cache => Block.tool_use id name (anthropic_finalize_input input) cache,
        _ => b,
    }

/// Assemble the accumulated stream into the SAME `MessagesResponse`
/// shape `Anthropic.complete` returns. `stop_reason` defaults to
/// `"end_turn"` exactly as the one-shot decode's absent-or-null rule.
/// The HTTP-level `Response` from `Client.post_stream` is discarded
/// by design: the assembled message IS the payload.
def anthropic_assemble (acc : AnthropicAcc) : MessagesResponse :=
    let stop : String :=
        match (acc.stop == "") {
            true => "end_turn",
            false => acc.stop
        } in
    let resp : MessagesResponse :=
        { content := List.map (fn (b : Block) => anthropic_finalize_block b) acc.blocks, stop_reason := stop, usage := acc.usage } in
    resp

/// The moose `on_bytes` callback: bytes in, SSE events out, each text
/// delta to `on_text`, the folded accumulator back. Never fails --
/// bad events are skipped inside `anthropic_apply_event`, and
/// transport errors are returned by `Client.post_stream` itself.
def anthropic_stream_bytes (on_text : String -> IO Unit) (acc : AnthropicAcc) (bytes : List U8) : IO (Result String (Pair AnthropicAcc Unit)) :=
    match Sse.push acc.sse bytes {
        Pair.pair sse2 events =>
            let acc2 : AnthropicAcc := AnthropicAcc.mk sse2 acc.blocks acc.stop acc.usage in
            match anthropic_apply_events acc2 events List.empty {
                Pair.pair acc3 deltas =>
                    Monad.bind (anthropic_emit_all on_text deltas) (fn _ =>
                        Monad.pure (Result.ok (Pair.pair acc3 Unit.unit)))
            }
    }

#[terminating]
def anthropic_emit_all (on_text : String -> IO Unit) (deltas : List String) : IO Unit :=
    match deltas {
        List.empty => Monad.pure Unit.unit,
        List.cons d rest => Monad.bind (on_text d) (fn _ => anthropic_emit_all on_text rest)
    }

def anthropic_stream_io (u : Uri) (headers : Headers) (body_str : String) (on_text : String -> IO Unit) : IO (Result String MessagesResponse) := do {
    let init : AnthropicAcc := { sse := Sse.init, blocks := List.empty, stop := "", usage := AnthropicUsage.mk 0 0 0 };
    let res <- Client.post_stream u headers (Body.from_text body_str) init (fn st bytes => anthropic_stream_bytes on_text st bytes);
    return (match res {
        Result.err e => Result.err e,
        Result.ok pr =>
            match pr {
                Pair.pair acc _ => Result.ok (anthropic_assemble acc)
            }
    })
}

/// POST `{base_url}/v1/messages` with `stream := true` and fold the
/// SSE response as it arrives: every `text_delta` fragment goes to
/// `on_text` in wire order (thinking and tool-input fragments
/// accumulate silently), and the return value is the assembled
/// `MessagesResponse` -- blocks under `content` (thinking signature
/// preserved, tool inputs parsed back to real objects), `stop_reason`
/// (defaulting to `"end_turn"`), and usage merged from
/// `message_start` (input half) and `message_delta` (output half).
pub def Anthropic.complete_stream (base_url : String) (api_key : String) (req : MessagesRequest) (on_text : String -> IO Unit) : ResultT String IO MessagesResponse :=
    let sreq : MessagesRequest := { req with stream := true } in
    let body_str := Json.to_string (MessagesRequest.serialize_json sreq) in
    let url_str := String.concat base_url "/v1/messages" in
    match Uri.parse url_str {
        Result.err e => ResultT.mk (return (Result.err e)),
        Result.ok u => ResultT.mk (anthropic_stream_io u (anthropic_headers api_key) body_str on_text),
    }
