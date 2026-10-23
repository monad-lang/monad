/// The HTTP-status tests for the OpenAI client. The streaming path once
/// discarded moose's `Response` "by design" -- so a 4xx/5xx body (an
/// unknown model, a rejected key) folded into zero SSE events and came
/// back as a SUCCESSFUL empty completion: "(no assistant reply)", exit
/// 0, nothing legible anywhere. Measured live against Mistral (2026-10-
/// 18). `openai_http_error` is the fix's pure half -- these pin it.
use openai::client {openai_http_error, OpenAI.request_json, OpenAI.parse_models}
use openai::types {ChatRequest, ChatMessage}
use openai::tool {ToolCall}
use json::json {Json.to_string}
use http::types {Response, Headers, Headers.empty, HttpVersion, Status.ok}
use http::body {Body.from_text}

/// One response, any status -- bound to an annotated local: a bare
/// struct literal in argument position is a compiled-backend hazard.
def resp_of (status : U16) (body : String) : Response :=
    let r : Response := { status := status, headers := Headers.empty, version := HttpVersion.http1_1, body := Body.from_text body } in
    r

/// A non-200 is `some` error naming the status AND the body -- the body
/// is where the server says WHY (Mistral's `"Invalid model: ..."`).
#[test]
def test_http_error_names_status_and_body : Bool :=
    let r : Response := resp_of 400u16 "{\"message\":\"Invalid model: glm-5-3\"}" in
    match openai_http_error r {
        Option.some e => String.contains e "400" && String.contains e "Invalid model",
        Option.none => false,
    }

/// A 200 is no error -- the success path must reach the SSE fold.
#[test]
def test_http_ok_is_no_error : Bool :=
    let r : Response := resp_of Status.ok "data: {}" in
    match openai_http_error r {
        Option.none => true,
        Option.some _ => false,
    }

// ── The request body's strict-safe shape ────────────────────────────────

def user_msg : ChatMessage := { role := "user", content := Option.some "hi", tool_calls := [], tool_call_id := Option.none, name := Option.none }

def req_of (messages : List ChatMessage) : ChatRequest :=
    let r : ChatRequest := { model := "m", messages := messages, tools := [], max_tokens := Option.some 64 } in
    r

/// Strict servers (Mistral's pydantic validation, live 2026-10-18)
/// refuse a `user` message that carries any of `name`, `tool_call_id`,
/// `tool_calls` -- HTTP 422 `"extra_forbidden"` -- while lenient ones
/// (Ollama, OpenAI) accept the nulls. The wire's own shape has the
/// fields optional: the request encoder omits them when they carry
/// nothing. Measured live: this is the whole difference between a
/// request Mistral answers and one it refuses.
#[test]
def test_request_json_omits_absent_message_optionals : Bool :=
    let body := Json.to_string (OpenAI.request_json (req_of (List.cons user_msg List.empty))) in
    String.contains body "\"role\":\"user\""
        && String.contains body "\"content\":\"hi\""
        && Bool.not (String.contains body "\"name\"")
        && Bool.not (String.contains body "\"tool_call_id\"")
        && Bool.not (String.contains body "\"tool_calls\"")

/// Omitted-when-absent must not become omitted-always: an assistant's
/// tool calls, a tool result's `tool_call_id`, a named message's
/// `name` all ride the request when they carry something.
#[test]
def test_request_json_keeps_present_message_optionals : Bool :=
    let tc : ToolCall := { id := "call_1", name := "read", arguments := "{}" } in
    let assistant : ChatMessage := { role := "assistant", content := Option.none, tool_calls := [tc], tool_call_id := Option.none, name := Option.none } in
    let tool_msg : ChatMessage := { role := "tool", content := Option.some "data", tool_calls := [], tool_call_id := Option.some "call_1", name := Option.none } in
    let named : ChatMessage := { role := "user", content := Option.some "hi", tool_calls := [], tool_call_id := Option.none, name := Option.some "fn" } in
    let msgs : List ChatMessage := List.cons assistant (List.cons tool_msg (List.cons named List.empty)) in
    let body := Json.to_string (OpenAI.request_json (req_of msgs)) in
    String.contains body "\"tool_calls\":[{"
        && String.contains body "\"tool_call_id\":\"call_1\""
        && String.contains body "\"name\":\"fn\""

/// The top-level fields stay unconditional: no strict server has
/// objected to a PRESENT top-level field -- only to message-level
/// extras -- so `model`/`messages`/`tools`/`max_tokens`/`stream` all
/// ride every request.
#[test]
def test_request_json_keeps_top_level_fields : Bool :=
    let body := Json.to_string (OpenAI.request_json (req_of (List.cons user_msg List.empty))) in
    String.contains body "\"model\":\"m\""
        && String.contains body "\"messages\":["
        && String.contains body "\"tools\":[]"
        && String.contains body "\"max_tokens\":64"
        && String.contains body "\"stream\":false"

// ── model listing ──────────────────────────────────────────────────────

#[test]
def test_parse_models_reads_ids : Bool :=
  match OpenAI.parse_models "{\"object\":\"list\",\"data\":[{\"id\":\"a\"},{\"id\":\"b\"}]}" {
    Result.ok ids => ids == ["a", "b"],
    Result.err _ => false,
  }

#[test]
def test_parse_models_accepts_an_empty_list : Bool :=
  match OpenAI.parse_models "{\"data\":[]}" {
    Result.ok ids => ids == [],
    Result.err _ => false,
  }

#[test]
def test_parse_models_rejects_missing_data : Bool :=
  match OpenAI.parse_models "{\"object\":\"list\"}" {
    Result.err e => String.contains e "missing data",
    Result.ok _ => false,
  }

#[test]
def test_parse_models_names_a_malformed_entry : Bool :=
  match OpenAI.parse_models "{\"data\":[{\"id\":\"a\"},{\"object\":\"model\"}]}" {
    Result.err e => String.contains e "entry 1" && String.contains e "has no id",
    Result.ok _ => false,
  }
