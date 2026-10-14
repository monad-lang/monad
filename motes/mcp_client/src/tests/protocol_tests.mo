/// MCP protocol tests: request shapes and response decoding, pure.
///
/// Everything here runs against `protocol.mo` alone -- no `Child`, no
/// pipe, no `sh` peer -- which is the same split `toolkit`'s
/// `jsonrpc_tests.mo` draws: the wire layer is a function over strings,
/// so the wire layer is tested over strings, and the transport tests
/// (`stdio_tests.mo`) only have to cover what the transport itself can
/// break.
///
/// Request builders are asserted by parsing their output back and
/// inspecting fields, not by exact wire text -- key order is a property
/// of the `BTreeMap` under `rpc_object`, and re-pinning it here would
/// make every map change a protocol test failure. The ONE exact-text
/// assertion is the `notifications/initialized` notification, whose
/// entire value is that it is a fixed string on the wire.
///
/// Helper names carry an `mp_` prefix: the whole-program scope is shared
/// with every other mote's tests, and same-named helpers have a
/// documented history of colliding silently.
use json::json {Json}
use mcp_client::protocol {
  McpClientInfo, McpTool, mcp_call_request, mcp_decode_call, mcp_decode_initialize,
  mcp_decode_tools_list, mcp_initialize_request, mcp_initialized_notification,
  mcp_tools_list_request,
}
use std::list {List.length}

// --- Helpers ---

/// The client this suite introduces itself as.
def mp_client : McpClientInfo :=
  { name := "monad-shuttle", version := "0.1.0" }

/// A parsed body, or the null marker on a parse failure -- a request a
/// builder emitted that does not parse is a failure either way.
def mp_parse (s : String) : Json :=
  match Json.parse s {
    Result.err _pe => Json.make_null,
    Result.ok j => j,
  }

/// One object field of `j`, or null when absent.
def mp_field (j : Json) (name : String) : Json :=
  match Json.get_object j {
    Result.err _e => Json.make_null,
    Result.ok obj =>
      match Json.object_get name obj {
        Option.none => Json.make_null,
        Option.some v => v,
      },
  }

/// A string field of `j`, or a marker when absent or ill-typed.
def mp_str (j : Json) (name : String) : String :=
  match Json.get_str (mp_field j name) {
    Result.err _e => "<absent>",
    Result.ok s => s,
  }

/// The numeric id `j` carries, or a value no test expects.
def mp_id (j : Json) : I64 :=
  match Json.get_num_i64 (Json.get_num (mp_field j "id")) {
    Result.err _e => -1,
    Result.ok n => n,
  }

/// A well-formed `initialize` result, the shape a spec-conforming server
/// answers with.
def mp_initialize_result : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"protocolVersion\":\"2025-06-18\",\"capabilities\":{},\"serverInfo\":{\"name\":\"peer\",\"version\":\"1.2.3\"}}}"

/// A well-formed `tools/list` result: one tool with the full catalogue
/// shape, one with neither description nor inputSchema.
def mp_tools_list_result : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":2,\"result\":{\"tools\":[{\"name\":\"echo\",\"description\":\"Echo text\",\"inputSchema\":{\"type\":\"object\"}},{\"name\":\"ping\"}]}}"

/// A well-formed `tools/call` result: two text blocks and `isError` set,
/// pinning both that the FIRST text wins and that the flag travels.
def mp_call_result : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":3,\"result\":{\"content\":[{\"type\":\"text\",\"text\":\"hello\"},{\"type\":\"text\",\"text\":\"second\"}],\"isError\":true}}"

/// The name of the `i`-th tool, or a marker when the list runs short.
#[partial]
def mp_tool_name (ts : List McpTool) (i : I64) : String :=
  match ts {
    List.empty => "<none>",
    List.cons t rest =>
      if I64.beq i 0
      then t.name
      else mp_tool_name rest (I64.sub i 1),
  }

/// The description of the first tool, or a marker when the list is empty.
def mp_first_tool_description (ts : List McpTool) : String :=
  match ts {
    List.empty => "<none>",
    List.cons t _rest => t.description,
  }

// --- Requests ---

#[test]
def test_initialize_request_shape : Bool :=
  let req : Json := mp_parse (mcp_initialize_request (Json.make_num_int 1) mp_client) in
  Bool.and (String.beq (mp_str req "method") "initialize")
    (Bool.and (I64.beq (mp_id req) 1)
      (Bool.and (String.beq (mp_str (mp_field req "params") "protocolVersion") "2025-06-18")
        (Bool.and (String.beq (mp_str (mp_field (mp_field req "params") "clientInfo") "name") "monad-shuttle")
          (String.beq (mp_str (mp_field (mp_field req "params") "clientInfo") "version") "0.1.0"))))

/// The notification is the one message whose ENTIRE value is its exact
/// spelling -- no id, no params, nothing to inspect field by field.
#[test]
def test_initialized_notification_shape : Bool :=
  String.beq mcp_initialized_notification
    "{\"jsonrpc\":\"2.0\",\"method\":\"notifications/initialized\",\"params\":{}}"

#[test]
def test_tools_list_request_shape : Bool :=
  let req : Json := mp_parse (mcp_tools_list_request (Json.make_num_int 7)) in
  Bool.and (String.beq (mp_str req "method") "tools/list") (I64.beq (mp_id req) 7)

#[test]
def test_call_request_carries_tool_and_arguments : Bool :=
  let args : Json :=
    mp_parse "{\"q\":\"needle\"}" in
  let req : Json := mp_parse (mcp_call_request (Json.make_num_int 3) "grep" args) in
  Bool.and (String.beq (mp_str (mp_field req "params") "name") "grep")
    (String.beq (mp_str (mp_field (mp_field req "params") "arguments") "q") "needle")

// --- Response decoding ---

#[test]
def test_decode_initialize : Bool :=
  match mcp_decode_initialize mp_initialize_result {
    Result.err _e => false,
    Result.ok i =>
      Bool.and (String.beq i.name "peer")
        (Bool.and (String.beq i.version "1.2.3")
          (String.beq i.protocol_version "2025-06-18")),
  }

/// A missing `protocolVersion` is a named field error, not a crash and
/// not a silent default -- a server that speaks an unknown version is a
/// server the harness must refuse, not guess at.
#[test]
def test_decode_initialize_missing_protocol_version : Bool :=
  match mcp_decode_initialize "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"serverInfo\":{\"name\":\"peer\",\"version\":\"1\"}}}" {
    Result.err e => String.beq e "missing field: protocolVersion",
    Result.ok _i => false,
  }

#[test]
def test_decode_tools_list : Bool :=
  match mcp_decode_tools_list mp_tools_list_result {
    Result.err _e => false,
    Result.ok tools =>
      Bool.and (I64.beq (List.length tools) 2)
        (Bool.and (String.beq (mp_tool_name tools 0) "echo")
          (Bool.and (String.beq (mp_tool_name tools 1) "ping")
            (String.beq (mp_first_tool_description tools) "Echo text"))),
  }

/// A catalogue entry without a name fails the whole decode rather than
/// being dropped: a tool the harness cannot name is a tool it cannot
/// call, and a partial registry is worse than an error.
#[test]
def test_decode_tools_list_rejects_unnamed_tool : Bool :=
  match mcp_decode_tools_list "{\"jsonrpc\":\"2.0\",\"id\":2,\"result\":{\"tools\":[{\"description\":\"nameless\"}]}}" {
    Result.err _e => true,
    Result.ok _tools => false,
  }

#[test]
def test_decode_call_first_text_and_is_error : Bool :=
  match mcp_decode_call mp_call_result {
    Result.err _e => false,
    Result.ok r =>
      Bool.and (String.beq r.text "hello") r.is_error,
  }

/// A call that answers only in blocks this harness cannot carry still
/// SUCCEEDED -- it decodes as empty text, not as an error.
#[test]
def test_decode_call_without_text_block : Bool :=
  match mcp_decode_call "{\"jsonrpc\":\"2.0\",\"id\":3,\"result\":{\"content\":[{\"type\":\"image\",\"data\":\"...\"}]}}" {
    Result.err _e => false,
    Result.ok r =>
      Bool.and (String.beq r.text "") (Bool.not r.is_error),
  }

/// An error RESPONSE is a decoded answer, not a parse failure -- the
/// whole reason this mote does not reuse `toolkit`'s server-shaped
/// `rpc_parse`, which would call it `unparseable`.
#[test]
def test_error_response_decodes_as_err : Bool :=
  match mcp_decode_call "{\"jsonrpc\":\"2.0\",\"id\":3,\"error\":{\"code\":-32601,\"message\":\"Method not found\"}}" {
    Result.err e => String.beq e "server error: -32601: Method not found",
    Result.ok _r => false,
  }

#[test]
def test_unparseable_body_is_err : Bool :=
  match mcp_decode_initialize "not json at all" {
    Result.err _e => true,
    Result.ok _i => false,
  }

/// Neither `result` nor `error` is a protocol break, reported rather
/// than treated as an empty success.
#[test]
def test_resultless_body_is_err : Bool :=
  match mcp_decode_tools_list "{\"jsonrpc\":\"2.0\",\"id\":2}" {
    Result.err e => String.beq e "response has neither result nor error",
    Result.ok _tools => false,
  }
