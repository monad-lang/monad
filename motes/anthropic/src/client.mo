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
    Json.get_array, Json.get_object, Json.get_num, Json.get_num_i64, Json.object_get, Json.make_object,
}
use http::types {Headers, Headers.empty, Headers.set, Response, Uri, Status.ok}
use http::uri {Uri.parse}
use http::body {Body.from_text, Body.to_bytes_pure}
use http::sse {Sse.init, Sse.push, SseState, SseEvent}
use moose::client {
    Client.default_stream_idle_ms, Client.default_timeout_ms,
    Client.get_timeout, Client.post_stream_timeout, Client.post_timeout,
}
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
    let resp <- Client.post_timeout u headers (Body.from_text body_str) Client.default_timeout_ms;
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

// ── Listing models ──────────────────────────────────────────────────────

/// The ids in a model list (`{"data":[{"id": …}, …]}`). Pure; a
/// malformed entry fails the whole list.
pub def Anthropic.parse_models (text : String) : Result String (List String) :=
    match Json.parse text {
        Result.err e => Result.err (Json.ParseError.to_string e),
        Result.ok j => anthropic_models_of_json j,
    }

def anthropic_models_of_json (j : Json) : Result String (List String) :=
    match Json.get_object j {
        Result.err e => Result.err (String.concat "models: " e),
        Result.ok o => match Json.object_get "data" o {
            Option.none => Result.err "models: missing data",
            Option.some d => match Json.get_array d {
                Result.err e => Result.err (String.concat "models: " e),
                Result.ok xs => anthropic_model_ids xs 0,
            },
        },
    }

#[terminating]
def anthropic_model_ids (xs : List Json) (i : I64) : Result String (List String) :=
    match xs {
        List.empty => Result.ok List.empty,
        List.cons x rest => match anthropic_model_id x i {
            Result.err e => Result.err e,
            Result.ok id => match anthropic_model_ids rest (i + 1i64) {
                Result.err e => Result.err e,
                Result.ok ids => Result.ok (List.cons id ids),
            },
        },
    }

def anthropic_model_id (j : Json) (i : I64) : Result String String :=
    match Json.get_object j {
        Result.err e => Result.err (String.concat "models: entry " (String.concat (I64.to_string i) (String.concat ": " e))),
        Result.ok o => match Json.object_get "id" o {
            Option.none => Result.err (String.concat "models: entry " (String.concat (I64.to_string i) " has no id")),
            Option.some idj => match Json.get_str idj {
                Result.err e => Result.err (String.concat "models: entry " (String.concat (I64.to_string i) (String.concat ": " e))),
                Result.ok id => Result.ok id,
            },
        },
    }

def anthropic_models_io (u : Uri) (headers : Headers) : IO (Result String (List String)) := do {
    let resp <- Client.get_timeout u headers Client.default_timeout_ms;
    return (match resp {
        Result.err e => Result.err e,
        Result.ok r =>
            let text := String.from_list (Body.to_bytes_pure r.body) in
            if U16.beq r.status Status.ok
            then Anthropic.parse_models text
            else Result.err (String.concat "anthropic: HTTP "
                (String.concat (U16.to_string r.status)
                (String.concat ": " text))),
    })
}

/// GET `{base_url}/v1/models?limit=1000`: Anthropic paginates this
/// endpoint, but its maximum page covers any realistic catalogue; a
/// `has_more` that survives that is ignored for now.
pub def Anthropic.list_models (base_url : String) (api_key : String) : ResultT String IO (List String) :=
    let url_str := String.concat base_url "/v1/models?limit=1000" in
    match Uri.parse url_str {
        Result.err e => ResultT.mk (return (Result.err e)),
        Result.ok u => ResultT.mk (anthropic_models_io u (anthropic_headers api_key)),
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
/// `content_block` index -- every `content_block_start` appends EXACTLY
/// one entry: a decoded block, or `Option.none` for a type this mote
/// does not model (which keeps every later delta's wire index aligned
/// while the block itself is absent from the assembled response).
/// Usage starts zeroed: `message_start` carries the input half (its
/// `output_tokens` is a placeholder and is zeroed here), and
/// `message_delta` the output half, so either may legitimately never
/// arrive.
struct AnthropicAcc {
    sse : SseState,
    blocks : List (Option Block),
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
/// accounting (plus the cache counters when the server sends them).
/// `input_tokens` here is the NON-cached prompt; cache writes are
/// folded in so the wire adapter only has to add cache reads back.
def anthropic_usage_of (j : Json) : AnthropicUsage :=
    match Json.get_object j {
        Result.err _ => AnthropicUsage.mk 0 0 0,
        Result.ok obj =>
            let base : I64 := anthropic_int_of "input_tokens" obj in
            let creation : I64 := anthropic_int_of "cache_creation_input_tokens" obj in
            AnthropicUsage.mk (base + creation)
                (anthropic_int_of "output_tokens" obj)
                (anthropic_int_of "cache_read_input_tokens" obj),
    }

/// The accumulated `input_json_delta` partial so far -- `""` before
/// the first fragment (the block-start `input` is always `{}`).
def anthropic_partial_of (input : Json) : String :=
    match input {
        Json.str s => s,
        _ => "",
    }

/// Patch the block at `idx` with one delta object. A delta for a block
/// that never started -- or for one this mote does not model -- lands
/// on `Option.none` and is dropped: lenient, same reasoning as every
/// skip in this fold.
#[terminating]
def anthropic_patch_at (blocks : List (Option Block)) (idx : I64) (dobj : BTreeMap String Json) : List (Option Block) :=
    match blocks {
        List.empty => blocks,
        List.cons ob rest =>
            if idx == 0
            then List.cons (anthropic_patch_option ob dobj) rest
            else List.cons ob (anthropic_patch_at rest (I64.sub idx 1) dobj)
    }

def anthropic_patch_option (ob : Option Block) (dobj : BTreeMap String Json) : Option Block :=
    match ob {
        Option.some b => Option.some (anthropic_block_delta b dobj),
        Option.none => Option.none,
    }

/// The block the wire opened at `idx`, if it started and this mote
/// models it -- the lookup a delta's REPORT decision is tied to, so
/// `on_text` can never emit text the assembled response lacks.
#[terminating]
def anthropic_block_at (blocks : List (Option Block)) (idx : I64) : Option Block :=
    match blocks {
        List.empty => Option.none,
        List.cons ob rest =>
            if idx == 0 then ob else anthropic_block_at rest (I64.sub idx 1)
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

/// `message_start`: the input usage half. The wire's `output_tokens`
/// here is a placeholder (a token or two); the real output count
/// arrives in `message_delta`'s usage, so the placeholder is zeroed --
/// a stream that ends without `message_delta` reports zero output, not
/// the placeholder.
def anthropic_apply_message_start (acc : AnthropicAcc) (obj : BTreeMap String Json) : AnthropicAcc :=
    match Json.object_get "message" obj {
        Option.none => acc,
        Option.some mj =>
            match Json.get_object mj {
                Result.err _ => acc,
                Result.ok mobj =>
                    match Json.object_get "usage" mobj {
                        Option.none => acc,
                        Option.some uj =>
                            match anthropic_usage_of uj {
                                AnthropicUsage.mk in_t _ cached =>
                                    { acc with usage := AnthropicUsage.mk in_t 0 cached }
                            }
                    }
            }
    }

/// `content_block_start`: append the block the wire opens -- EXACTLY
/// one entry, whatever it is. A known block decodes with the one-shot
/// path; a type this mote does not model (`redacted_thinking` is
/// already in the wild) appends `Option.none`: an entry that keeps
/// every later delta's wire index aligned while the block itself stays
/// absent from the assembled response -- the streaming counterpart of
/// the one-shot decode's per-block `deserialize_or_skip` leniency.
def anthropic_apply_block_start (acc : AnthropicAcc) (obj : BTreeMap String Json) : AnthropicAcc :=
    match Json.object_get "content_block" obj {
        Option.none => acc,
        Option.some bj =>
            { acc with blocks := List.append acc.blocks (List.singleton (anthropic_block_entry bj)) }
    }

def anthropic_block_entry (bj : Json) : Option Block :=
    match Block.deserialize_or_skip bj {
        Result.err _ => Option.none,
        Result.ok ob => ob,
    }

/// The reserved tag thinking fragments carry on `on_text`: the UI
/// routes them to its dim "thinking" surface. The leading control byte
/// cannot occur in model text.
def anthropic_reasoning_delta (frag : String) : String :=
    String.concat "\u{1}thinking\u{2}" frag

/// The fragments a delta reports to `on_text`: a `text_delta` of a
/// text block, or a `thinking_delta` of a thinking block carrying the
/// reserved tag (tool-input fragments still accumulate silently). Only
/// blocks that really started report -- the live output can never
/// diverge from the assembled response.
def anthropic_delta_text (blocks : List (Option Block)) (idx : I64) (dobj : BTreeMap String Json) : List String :=
    match anthropic_block_at blocks idx {
        Option.some b => anthropic_delta_text_of b dobj,
        Option.none => List.empty,
    }

def anthropic_delta_text_of (b : Block) (dobj : BTreeMap String Json) : List String :=
    match b {
        Block.text _ _ =>
            match anthropic_str_of "type" dobj {
                Option.some tag =>
                    if tag == "text_delta"
                    then match anthropic_str_of "text" dobj {
                        Option.some s => [s],
                        Option.none => List.empty,
                    }
                    else List.empty,
                Option.none => List.empty,
            },
        Block.thinking _ _ _ =>
            match anthropic_str_of "type" dobj {
                Option.some tag =>
                    if tag == "thinking_delta"
                    then match anthropic_str_of "thinking" dobj {
                        Option.some s => [anthropic_reasoning_delta s],
                        Option.none => List.empty,
                    }
                    else List.empty,
                Option.none => List.empty,
            },
        _ => List.empty,
    }

/// `content_block_delta`: patch the block at the wire's index.
def anthropic_apply_block_delta_event (acc : AnthropicAcc) (obj : BTreeMap String Json) : Pair AnthropicAcc (List String) :=
    let idx : I64 := anthropic_int_of "index" obj in
    match Json.object_get "delta" obj {
        Option.none => Pair.pair acc List.empty,
        Option.some dj =>
            match Json.get_object dj {
                Result.err _ => Pair.pair acc List.empty,
                Result.ok dobj =>
                    Pair.pair { acc with blocks := anthropic_patch_at acc.blocks idx dobj }
                        (anthropic_delta_text acc.blocks idx dobj)
            }
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
                        Option.some s => { acc with stop := s }
                    }
            }
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
                            { acc with usage := AnthropicUsage.mk in_t (anthropic_int_of "output_tokens" uobj) cached }
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
def anthropic_apply_event (acc : AnthropicAcc) (data : String) : Pair AnthropicAcc (List String) :=
    match Json.parse data {
        Result.err _ => Pair.pair acc List.empty,
        Result.ok j =>
            match Json.get_object j {
                Result.err _ => Pair.pair acc List.empty,
                Result.ok obj =>
                    match anthropic_str_of "type" obj {
                        Option.none => Pair.pair acc List.empty,
                        Option.some tag => anthropic_apply_typed acc tag obj,
                    }
            }
    }

def anthropic_apply_typed (acc : AnthropicAcc) (tag : String) (obj : BTreeMap String Json) : Pair AnthropicAcc (List String) :=
    if tag == "message_start"
    then Pair.pair (anthropic_apply_message_start acc obj) List.empty
    else if tag == "content_block_start"
    then Pair.pair (anthropic_apply_block_start acc obj) List.empty
    else if tag == "content_block_delta"
    then anthropic_apply_block_delta_event acc obj
    else if tag == "message_delta"
    then Pair.pair (anthropic_apply_message_delta acc obj) List.empty
    else Pair.pair acc List.empty

/// Fold every event a byte push completed, reporting each non-empty
/// text delta in wire order -- the pure half of the moose callback.
#[terminating]
def anthropic_apply_events (acc : AnthropicAcc) (events : List SseEvent) (out : List String) : Pair AnthropicAcc (List String) :=
    match events {
        List.empty => Pair.pair acc (List.reverse out),
        List.cons ev rest =>
            match anthropic_apply_event acc ev.data {
                Pair.pair acc2 deltas =>
                    match deltas {
                        List.empty => anthropic_apply_events acc2 rest out,
                        List.cons _ _ => anthropic_apply_events acc2 rest (List.append (List.reverse deltas) out),
                    }
            }
    }

/// A tool input's accumulated `partial_json` text back to a real JSON
/// object, matching the one-shot wire (`input` is an object, never a
/// string). Empty stays the block-start `{}`. A NON-empty text that
/// does not parse never reaches this fallback on the stream path:
/// `anthropic_bad_input` refuses the turn first (executing a tool
/// with guessed-empty arguments is worse than failing the turn), so
/// this `{}` arm serves only a direct `anthropic_assemble` caller.
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

/// The blocks that started and that this mote models, in wire order --
/// what the assembled response carries. `Option.none` entries (unknown
/// block types) are absent here exactly as the one-shot decode's
/// per-block skip omits them.
#[terminating]
def anthropic_present (blocks : List (Option Block)) : List Block :=
    match blocks {
        List.empty => List.empty,
        List.cons ob rest =>
            match ob {
                Option.some b => List.cons b (anthropic_present rest),
                Option.none => anthropic_present rest,
            }
    }

/// A tool input whose accumulated `partial_json` text does not parse:
/// the stream ended mid-fragment (a dropped connection, a truncated
/// chunk). Handing the harness a tool call with guessed-empty
/// arguments to execute is worse than failing the turn, so the stream
/// boundary refuses it, named, before assembly.
def anthropic_input_unparsed (input : Json) : Option String :=
    match input {
        Json.str s =>
            if s == ""
            then Option.none
            else
                match Json.parse s {
                    Result.err _ => Option.some s,
                    Result.ok _ => Option.none,
                },
        _ => Option.none,
    }

#[terminating]
def anthropic_bad_input (blocks : List (Option Block)) : Option String :=
    match blocks {
        List.empty => Option.none,
        List.cons ob rest =>
            match anthropic_bad_input_entry ob {
                Option.some e => Option.some e,
                Option.none => anthropic_bad_input rest
            }
    }

def anthropic_bad_input_entry (ob : Option Block) : Option String :=
    match ob {
        Option.none => Option.none,
        Option.some b => anthropic_bad_input_block b
    }

def anthropic_bad_input_block (b : Block) : Option String :=
    match b {
        Block.tool_use _ name input _ =>
            match anthropic_input_unparsed input {
                Option.some s =>
                    Option.some (String.concat "anthropic: tool input for '"
                        (String.concat name (String.concat "' did not parse: " s))),
                Option.none => Option.none,
            },
        _ => Option.none,
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
        { content := List.map (fn (b : Block) => anthropic_finalize_block b) (anthropic_present acc.blocks), stop_reason := stop, usage := acc.usage } in
    resp

/// The moose `on_bytes` callback: bytes in, SSE events out, each text
/// delta to `on_text`, the folded accumulator back. Never fails --
/// bad events are skipped inside `anthropic_apply_event`, and
/// transport errors are returned by `Client.post_stream` itself.
def anthropic_stream_bytes (on_text : String -> IO Unit) (acc : AnthropicAcc) (bytes : List U8) : IO (Result String (Pair AnthropicAcc Unit)) :=
    match Sse.push acc.sse bytes {
        Pair.pair sse2 events =>
            let acc2 : AnthropicAcc := { acc with sse := sse2 } in
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
    let res <- Client.post_stream_timeout u headers (Body.from_text body_str) Client.default_stream_idle_ms init (fn st bytes => anthropic_stream_bytes on_text st bytes);
    return (match res {
        Result.err e => Result.err e,
        Result.ok pr =>
            match pr {
                Pair.pair acc _ =>
                    match anthropic_bad_input acc.blocks {
                        Option.some e => Result.err e,
                        Option.none => Result.ok (anthropic_assemble acc)
                    }
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
