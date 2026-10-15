/// A thin, one-shot HTTP call to an OpenAI-compatible chat-completions
/// endpoint. `ResultT String IO` so a caller composes it with real
/// do-notation instead of hand-rolled continuation chaining -- see
/// `plans/implementations/agent-skills.md`'s Context point 3.
use init::transformers {ResultT}
use json::json {
    Json, Json.to_string, Json.parse, Json.ParseError.to_string, Json.get_str,
    Json.get_array, Json.get_object, Json.object_get, Json.get_num, Json.get_num_i64,
}
use json::serde_backend {}
use http::types {Headers, Headers.empty, Headers.set, Response, Uri}
use http::uri {Uri.parse}
use http::body {Body.from_text, Body.to_bytes_pure}
use http::sse {Sse.init, Sse.push, SseState, SseEvent}
use moose::client {Client.post, Client.post_stream}
use openai::types {ChatRequest, ChatResponse, ApiUsage, ChatMessage, Choice}
use openai::tool {ToolCall}
use std::map {BTreeMap}

/// Named `ApiUsage`, not `Usage` -- this is a whole-program-scope
/// language (`mote.toml`'s own comment), and a consumer mote almost
/// certainly has its own `Usage` type (shuttle's does: `{input_tokens,
/// output_tokens, cached_tokens}`, a different shape). Two same-named
/// types sharing a same-arity `mk` constructor resolve a QUALIFIED
/// `Usage.mk` pattern ambiguously by bare name once both are loaded
/// together, not by which file imported which -- measured directly
/// (`expected 2 constructor fields, got 0` at run time, not a compile
/// error). A distinct name sidesteps the collision at its root.
pub def ApiUsage.tokens (u : ApiUsage) : Pair I64 I64 :=
    match u { ApiUsage.mk prompt_tokens completion_tokens => Pair.pair prompt_tokens completion_tokens }

def openai_headers (api_key : Option String) : Headers :=
    let base := Headers.set "Content-Type" "application/json" Headers.empty in
    match api_key {
        Option.some key => Headers.set "Authorization" (String.concat "Bearer " key) base,
        Option.none => base,
    }

def decode_chat_response (r : Response) : Result String ChatResponse :=
    let text := String.from_list (Body.to_bytes_pure r.body) in
    match Json.parse text {
        Result.err e => Result.err (Json.ParseError.to_string e),
        Result.ok j => ChatResponse.deserialize_json j,
    }

def openai_complete_io (u : Uri) (headers : Headers) (body_str : String) : IO (Result String ChatResponse) := do {
    let resp <- Client.post u headers (Body.from_text body_str);
    return (match resp {
        Result.err e => Result.err e,
        Result.ok r => decode_chat_response r,
    })
}

/// POST `{base_url}/v1/chat/completions`. `api_key` is `Option.none` for
/// an unauthenticated local server (Ollama); `Option.some key` sends
/// `Authorization: Bearer <key>` (Mistral AI and friends). `base_url`
/// stays a `String` -- it's a config-level host root with a path still
/// to append, not yet a URI -- but the appended, full address is parsed
/// to a `Uri` once here, at the one place a malformed `base_url` can
/// actually fail, rather than threading a raw `String` into `Client.post`.
pub def OpenAI.complete (base_url : String) (api_key : Option String) (req : ChatRequest) : ResultT String IO ChatResponse :=
    let body_str := Json.to_string (ChatRequest.serialize_json req) in
    let url_str := String.concat base_url "/v1/chat/completions" in
    match Uri.parse url_str {
        Result.err e => ResultT.mk (return (Result.err e)),
        Result.ok u => ResultT.mk (openai_complete_io u (openai_headers api_key) body_str),
    }

// ── Streaming ──────────────────────────────────────────────────────────
//
// `OpenAI.complete_stream` is `OpenAI.complete` over an SSE wire: the
// request is the same one, plus `stream := true`, and the response
// arrives as `data: {json}` events -- `choices[0].delta.content` text
// fragments, `delta.tool_calls[]` argument fragments merged by `index`,
// a final `finish_reason`, and (optionally) top-level `usage`. The
// per-event work is PURE (`openai_apply_event` folds one event into an
// `OpenaiAcc` and reports the text delta it produced), so it is
// unit-testable against canned fixture strings with no transport; the
// IO half only shuttles bytes into the SSE state machine and hands
// deltas to `on_text`.

/// The streaming fold state. `sse` is the byte-level line discipline;
/// the rest is what one chat completion accumulates. `usage` starts
/// zeroed because a streaming server often never sends usage at all --
/// the live Ollama probe (2026-10-13) carried none, and the one-shot
/// path's callers tolerate a zeroed usage better than a parse error.
struct OpenaiAcc {
    sse : SseState,
    text : String,
    tools : List ToolCall,
    finish : String,
    usage : ApiUsage,
}

/// A usage object read leniently: missing or non-numeric fields are 0,
/// not errors -- usage is advisory, and a malformed one must not kill
/// an otherwise complete stream.
def openai_usage_of (j : Json) : ApiUsage :=
    match Json.get_object j {
        Result.err _ => ApiUsage.mk 0 0,
        Result.ok obj =>
            match Json.object_get "prompt_tokens" obj {
                Option.none => ApiUsage.mk 0 0,
                Option.some pj =>
                    match Json.get_num_i64 (Json.get_num pj) {
                        Result.err _ => ApiUsage.mk 0 0,
                        Result.ok pt =>
                            match Json.object_get "completion_tokens" obj {
                                Option.none => ApiUsage.mk pt 0,
                                Option.some cj =>
                                    match Json.get_num_i64 (Json.get_num cj) {
                                        Result.err _ => ApiUsage.mk pt 0,
                                        Result.ok ct => ApiUsage.mk pt ct,
                                    }
                            }
                    }
            }
    }

/// A string field read leniently: absent or non-string is none, never
/// an error -- streaming events legitimately omit most fields.
def openai_tc_field (obj : BTreeMap String Json) (key : String) : Option String :=
    match Json.object_get key obj {
        Option.none => Option.none,
        Option.some j =>
            match Json.get_str j {
                Result.err _ => Option.none,
                Result.ok s => Option.some s
            }
    }

/// A field one level down, inside the tool-call's `function` object.
def openai_tc_function_field (obj : BTreeMap String Json) (key : String) : Option String :=
    match Json.object_get "function" obj {
        Option.none => Option.none,
        Option.some fj =>
            match Json.get_object fj {
                Result.err _ => Option.none,
                Result.ok fobj => openai_tc_field fobj key
            }
    }

/// The `index` a delta's tool-call entry claims. Missing defaults to 0
/// -- the first call of a stream is the overwhelmingly common case.
def openai_tc_index (obj : BTreeMap String Json) : I64 :=
    match Json.object_get "index" obj {
        Option.none => 0,
        Option.some ij =>
            match Json.get_num_i64 (Json.get_num ij) {
                Result.err _ => 0,
                Result.ok n => n
            }
    }

/// The first fragment of a tool call: whatever fields this delta carries.
def openai_tool_fresh (obj : BTreeMap String Json) : ToolCall :=
    let id : String := match openai_tc_field obj "id" { Option.some s => s, Option.none => "" } in
    let name : String := match openai_tc_function_field obj "name" { Option.some s => s, Option.none => "" } in
    let args : String := match openai_tc_function_field obj "arguments" { Option.some s => s, Option.none => "" } in
    ToolCall.mk id name args

/// A later fragment of the tool call at this position: `id`/`name`
/// override when present, and an `arguments` fragment CONCATENATES --
/// that is the whole streaming tool-call trick, arguments arrive as
/// JSON text in pieces and the wire contract is simple concatenation.
def openai_tool_patch (t : ToolCall) (obj : BTreeMap String Json) : ToolCall :=
    let id : String := match openai_tc_field obj "id" { Option.some s => s, Option.none => t.id } in
    let name : String := match openai_tc_function_field obj "name" { Option.some s => s, Option.none => t.name } in
    let args : String :=
        match openai_tc_function_field obj "arguments" {
            Option.some frag => String.concat t.arguments frag,
            Option.none => t.arguments
        } in
    ToolCall.mk id name args

/// Merge one tool-call delta into the list at its claimed index.
/// `index` == the list's length appends a fresh entry; below it patches
/// in place; past it (a gap the server should not send) appends anyway
/// -- lenient, the alternative is dropping a real tool call.
#[terminating]
def openai_tools_step (tools : List ToolCall) (idx : I64) (obj : BTreeMap String Json) : List ToolCall :=
    match tools {
        List.empty => List.singleton (openai_tool_fresh obj),
        List.cons t rest =>
            if I64.beq idx 0
            then List.cons (openai_tool_patch t obj) rest
            else List.cons t (openai_tools_step rest (I64.sub idx 1) obj)
    }

/// Fold a `delta.tool_calls` array into the accumulator's tool list.
#[terminating]
def openai_tools_walk (tools : List ToolCall) (entries : List Json) : List ToolCall :=
    match entries {
        List.empty => tools,
        List.cons e rest =>
            match Json.get_object e {
                Result.err _ => openai_tools_walk tools rest,
                Result.ok obj => openai_tools_walk (openai_tools_step tools (openai_tc_index obj) obj) rest
            }
    }

/// The `usage` of a whole event, if it carries one (most carry null).
def openai_apply_usage (acc : OpenaiAcc) (obj : BTreeMap String Json) : OpenaiAcc :=
    match Json.object_get "usage" obj {
        Option.none => acc,
        Option.some uj => OpenaiAcc.mk acc.sse acc.text acc.tools acc.finish (openai_usage_of uj)
    }

/// The `finish_reason` of the event's choice, if it carries one (null
/// in every chunk but the last).
def openai_apply_finish (acc : OpenaiAcc) (cobj : BTreeMap String Json) : OpenaiAcc :=
    match openai_tc_field cobj "finish_reason" {
        Option.none => acc,
        Option.some fr => OpenaiAcc.mk acc.sse acc.text acc.tools fr acc.usage
    }

/// The `tool_calls` half of a delta, if it carries one.
def openai_apply_delta_tools (acc : OpenaiAcc) (dobj : BTreeMap String Json) : OpenaiAcc :=
    match Json.object_get "tool_calls" dobj {
        Option.none => acc,
        Option.some tj =>
            match Json.get_array tj {
                Result.err _ => acc,
                Result.ok entries => OpenaiAcc.mk acc.sse acc.text (openai_tools_walk acc.tools entries) acc.finish acc.usage
            }
    }

/// One `delta` object: appended text (reported back for `on_text`),
/// then any tool-call fragments. `delta.reasoning*` and `delta.role`
/// are ignored on purpose.
def openai_apply_delta (acc : OpenaiAcc) (dobj : BTreeMap String Json) : Pair OpenaiAcc String :=
    match openai_tc_field dobj "content" {
        Option.none => Pair.pair (openai_apply_delta_tools acc dobj) "",
        Option.some s =>
            let acc2 : OpenaiAcc := OpenaiAcc.mk acc.sse (String.concat acc.text s) acc.tools acc.finish acc.usage in
            Pair.pair (openai_apply_delta_tools acc2 dobj) s
    }

/// The event's single choice: finish reason first, then the delta.
def openai_apply_choice (acc : OpenaiAcc) (cobj : BTreeMap String Json) : Pair OpenaiAcc String :=
    let acc1 : OpenaiAcc := openai_apply_finish (openai_apply_usage acc cobj) cobj in
    match Json.object_get "delta" cobj {
        Option.none => Pair.pair acc1 "",
        Option.some dj =>
            match Json.get_object dj {
                Result.err _ => Pair.pair acc1 "",
                Result.ok dobj => openai_apply_delta acc1 dobj
            }
    }

/// One complete SSE event payload. `[DONE]` and unparseable payloads
/// are skipped -- the stream's terminator is the CHUNKED body's last
/// chunk (see `http::wire`), not a sentinel event.
def openai_apply_event (acc : OpenaiAcc) (data : String) : Pair OpenaiAcc String :=
    if data == "[DONE]"
    then Pair.pair acc ""
    else
        match Json.parse data {
            Result.err _ => Pair.pair acc "",
            Result.ok j =>
                match Json.get_object j {
                    Result.err _ => Pair.pair acc "",
                    Result.ok obj =>
                        match Json.object_get "choices" obj {
                            Option.none => Pair.pair (openai_apply_usage acc obj) "",
                            Option.some cj =>
                                match Json.get_array cj {
                                    Result.err _ => Pair.pair (openai_apply_usage acc obj) "",
                                    Result.ok choices =>
                                        match choices {
                                            List.empty => Pair.pair (openai_apply_usage acc obj) "",
                                            List.cons first _ =>
                                                match Json.get_object first {
                                                    Result.err _ => Pair.pair (openai_apply_usage acc obj) "",
                                                    Result.ok cobj => openai_apply_choice (openai_apply_usage acc obj) cobj
                                                }
                                        }
                                }
                        }
                }
        }

/// Fold every event a byte push completed, reporting each non-empty
/// text delta in wire order -- the pure half of `openai_stream_bytes`.
#[terminating]
def openai_apply_events (acc : OpenaiAcc) (events : List SseEvent) (out : List String) : Pair OpenaiAcc (List String) :=
    match events {
        List.empty => Pair.pair acc (List.reverse out),
        List.cons ev rest =>
            match openai_apply_event acc ev.data {
                Pair.pair acc2 delta =>
                    if delta == ""
                    then openai_apply_events acc2 rest out
                    else openai_apply_events acc2 rest (List.cons delta out)
            }
    }

/// The moose `on_bytes` callback: bytes in, SSE events out, each delta
/// to `on_text`, the folded accumulator back. Never fails -- a bad
/// event is skipped inside `openai_apply_event`, and the transport
/// errors moose reports are returned by `Client.post_stream` itself.
def openai_stream_bytes (on_text : String -> IO Unit) (acc : OpenaiAcc) (bytes : List U8) : IO (Result String (Pair OpenaiAcc Unit)) :=
    match Sse.push acc.sse bytes {
        Pair.pair sse2 events =>
            let acc2 : OpenaiAcc := OpenaiAcc.mk sse2 acc.text acc.tools acc.finish acc.usage in
            let stepped := openai_apply_events acc2 events List.empty in
            match stepped {
                Pair.pair acc3 deltas =>
                    Monad.bind (openai_emit_all on_text deltas) (fn _ =>
                        Monad.pure (Result.ok (Pair.pair acc3 Unit.unit)))
            }
    }

#[terminating]
def openai_emit_all (on_text : String -> IO Unit) (deltas : List String) : IO Unit :=
    match deltas {
        List.empty => Monad.pure Unit.unit,
        List.cons d rest => Monad.bind (on_text d) (fn _ => openai_emit_all on_text rest)
    }

/// Assemble the accumulated stream into the SAME `ChatResponse` shape
/// `OpenAI.complete` returns, so a consumer (shuttle's wire adapter)
/// handles both paths with one decoder. The HTTP-level `Response`
/// `Client.post_stream` returns is discarded by design: the assembled
/// chat completion is the payload; the bytes were never a JSON body.
def openai_assemble (acc : OpenaiAcc) : ChatResponse :=
    let content : Option String :=
        match (acc.text == "") {
            true => Option.none,
            false => Option.some acc.text
        } in
    let finish : String :=
        match (acc.finish == "") {
            true => "stop",
            false => acc.finish
        } in
    let msg : ChatMessage := { role := "assistant", content := content, tool_calls := acc.tools, tool_call_id := Option.none, name := Option.none } in
    let choice : Choice := { message := msg, finish_reason := finish } in
    let resp : ChatResponse := { choices := List.singleton choice, usage := acc.usage } in
    resp

def openai_stream_io (u : Uri) (headers : Headers) (body_str : String) (on_text : String -> IO Unit) : IO (Result String ChatResponse) := do {
    let init : OpenaiAcc := { sse := Sse.init, text := "", tools := List.empty, finish := "", usage := ApiUsage.mk 0 0 };
    let res <- Client.post_stream u headers (Body.from_text body_str) init (fn st bytes => openai_stream_bytes on_text st bytes);
    return (match res {
        Result.err e => Result.err e,
        Result.ok pr =>
            match pr {
                Pair.pair acc _ => Result.ok (openai_assemble acc)
            }
    })
}

/// POST `{base_url}/v1/chat/completions` with `stream := true` and fold
/// the SSE response as it arrives: every `delta.content` fragment goes
/// to `on_text` in wire order (empty fragments are not reported), and
/// the return value is the assembled `ChatResponse` -- text under
/// `choices[0].message.content`, merged tool calls under
/// `tool_calls`, `finish_reason`, and usage (zeroed when the server
/// never sends one).
pub def OpenAI.complete_stream (base_url : String) (api_key : Option String) (req : ChatRequest) (on_text : String -> IO Unit) : ResultT String IO ChatResponse :=
    let sreq : ChatRequest := { req with stream := true } in
    let body_str := Json.to_string (ChatRequest.serialize_json sreq) in
    let url_str := String.concat base_url "/v1/chat/completions" in
    match Uri.parse url_str {
        Result.err e => ResultT.mk (return (Result.err e)),
        Result.ok u => ResultT.mk (openai_stream_io u (openai_headers api_key) body_str on_text),
    }
