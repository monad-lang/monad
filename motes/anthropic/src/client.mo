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
use json::json {Json.to_string, Json.parse, Json.ParseError.to_string}
use http::types {Headers, Headers.empty, Headers.set, Response, Uri, Status.ok}
use http::uri {Uri.parse}
use http::body {Body.from_text, Body.to_bytes_pure}
use moose::client {Client.post}
use anthropic::types {MessagesRequest, MessagesResponse}

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
