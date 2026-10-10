/// A thin, one-shot HTTP call to an OpenAI-compatible chat-completions
/// endpoint. `ResultT String IO` so a caller composes it with real
/// do-notation instead of hand-rolled continuation chaining -- see
/// `plans/implementations/agent-skills.md`'s Context point 3.
use init::transformers {ResultT}
use json::json {Json.to_string, Json.parse, Json.ParseError.to_string}
use json::serde_backend {}
use http::types {Headers, Headers.empty, Headers.set, Response, Uri}
use http::uri {Uri.parse}
use http::body {Body.from_text, Body.to_bytes_pure}
use moose::client {Client.post}
use openai::types {ChatRequest, ChatResponse, ApiUsage}

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
