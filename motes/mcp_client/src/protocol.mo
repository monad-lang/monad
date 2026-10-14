/// The MCP protocol layer: request bodies in, response bodies out.
///
/// Pure by construction -- nothing here touches a `Child`, a pipe or any
/// other effect, which is the same split `motes/toolkit/src/jsonrpc.mo`
/// draws ("what a message says" vs "where a message ends"). Every request
/// builder returns an UNFRAMED JSON body; `stdio.mo` adds the newline.
/// Every decoder takes a response body as the transport handed it over.
///
/// WHY THIS DOES NOT REUSE `toolkit`'s `rpc_parse`: that function answers a
/// SERVER's question ("must I reply to this?") and its `RpcMessage` type is
/// server-shaped -- a well-formed error RESPONSE (`{"id":1,"error":{...}}`)
/// has no `method`, so it decodes as `unparseable`, which is the wrong
/// answer for a client holding that error. The request ENCODERS are shared
/// (`rpc_encode_request`, `rpc_encode_notification`, `rpc_object`,
/// `rpc_version`); the response decoding is this mote's own, against `Json`
/// directly.
///
/// The tool shape mirrors `motes/shuttle/src/tool.mo`'s `ToolSpec`
/// field-for-field (`name`/`description`/`schema`) on purpose: shuttle
/// cannot be a dependency of this mote (the dependency edge runs the other
/// way, shuttle -> mcp_client), so the later adapter
/// (agent-skills.md Phase 3's plugin mount) is a field-for-field copy, and
/// any drift between the two shapes shows up as a compile error there
/// rather than a silent mismatch here.
use json::json {Json}
use std::map {BTreeMap}
use toolkit::jsonrpc {rpc_encode_notification, rpc_encode_request, rpc_object}

// --- Types ---
//
// One `struct` per wire object this mote decodes, per style rule 1: each
// has exactly one constructor and named fields are the whole point --
// `server.version` reads, `ServerInfo.mk 1 2` does not.

/// Who we are, sent in `initialize`. The harness's own name and version.
pub struct McpClientInfo {
  name : String,
  version : String,
}

/// Who the server is, from the `initialize` result. `capabilities` is
/// deliberately not decoded: this client requires nothing beyond the
/// base protocol's tools, so a capability field it never reads would be
/// a field it cannot keep honest.
pub struct McpServerInfo {
  name : String,
  version : String,
  protocol_version : String,
}

/// One tool from `tools/list` -- the catalogue entry, not the callable.
pub struct McpTool {
  name : String,
  description : String,
  schema : Json,
}

/// One `tools/call` result, flattened to what the harness's
/// `Content.tool_result` can carry: the first text block's text, and the
/// wire's `isError` flag. An image or resource block has no text; such a
/// response decodes as empty text rather than an error, because the call
/// itself succeeded.
pub struct McpCallResult {
  text : String,
  is_error : Bool,
}

/// The protocol version this client asks for. The server echoes the
/// version it will speak in the response, and THAT is what
/// `McpServerInfo.protocol_version` records -- a server may negotiate
/// down, and the client's own constant is not the negotiated answer.
pub def mcp_protocol_version : String := "2025-06-18"

// --- Object field accessors ---
//
// Hand-written per level rather than derived, matching how
// `motes/anthropic/src/types.mo` decodes: patterns are one constructor
// deep, so a walk is one `match` and one helper per level, and every
// decoder is total -- a missing or ill-typed field is a `Result.err`
// naming the field, never a crash.

/// One field of a JSON object, or `Result.err` naming the field.
def mcp_field (obj : BTreeMap String Json) (name : String) : Result String Json :=
  match Json.object_get name obj {
    Option.none => Result.err (String.concat "missing field: " name),
    Option.some j => Result.ok j,
  }

def mcp_str_field (obj : BTreeMap String Json) (name : String) : Result String String :=
  match mcp_field obj name {
    Result.err e => Result.err e,
    Result.ok j => Json.get_str j,
  }

/// A string field that is ABSENT when the value is the empty one --
/// `description`'s own convention in `tools/list`, where a tool may have
/// no description at all. Absent-or-bad decodes as `""` rather than an
/// error, the same leniency `anthropic/src/types.mo`'s `obj_bool_or_false`
/// gives an absent `is_error`.
def mcp_str_or_empty (obj : BTreeMap String Json) (name : String) : String :=
  match Json.object_get name obj {
    Option.none => "",
    Option.some j =>
      match Json.get_str j {
        Result.ok s => s,
        Result.err _e => "",
      },
  }

/// A field that is absent when the value is a placeholder -- `inputSchema`
/// is required by MCP's own spec text but some servers omit it on tools
/// that take no arguments, and `Json.make_null` is what shuttle's own
/// hand-written specs already use for that case (`search_tools.mo`).
def mcp_field_or_null (obj : BTreeMap String Json) (name : String) : Json :=
  match Json.object_get name obj {
    Option.none => Json.make_null,
    Option.some j => j,
  }

/// A bool that is absent when false: the wire's `isError` convention.
def mcp_bool_or_false (obj : BTreeMap String Json) (name : String) : Bool :=
  match Json.object_get name obj {
    Option.none => false,
    Option.some j =>
      match Json.get_bool j {
        Result.ok b => b,
        Result.err _e => false,
      },
  }

// --- Response envelope ---

/// The body of a response, or the error the peer reported.
///
/// A JSON-RPC response is `{"result":...}` or `{"error":{"code",...,
/// "message":...}}` -- the two are mutually exclusive at the envelope
/// level, and an error response is a decoded ANSWER here, not a parse
/// failure. The error's code rides along in the message so the caller can
/// log it without re-parsing.
pub def mcp_result_of (body : String) : Result String Json :=
  match Json.parse body {
    Result.err pe => Result.err (mcp_parse_error_text pe),
    Result.ok j =>
      match Json.get_object j {
        Result.err _e => Result.err "response is not a JSON object",
        Result.ok obj =>
          match Json.object_get "error" obj {
            Option.some e => Result.err (String.concat "server error: " (mcp_error_text e)),
            Option.none =>
              match Json.object_get "result" obj {
                Option.none => Result.err "response has neither result nor error",
                Option.some r => Result.ok r,
              },
          },
      },
  }

/// Render a `Json.ParseError` for an error message, the same spelling
/// `toolkit/src/jsonrpc.mo`'s `rpc_parse_error_text` uses.
def mcp_parse_error_text (pe : Json.ParseError) : String :=
  match pe {
    Json.ParseError.expected e f =>
      String.concat "expected " (String.concat e (String.concat ", found " f)),
    Json.ParseError.generic s => s,
  }

/// An error node's code and message, rendered as one line.
def mcp_error_text (e : Json) : String :=
  match Json.get_object e {
    Result.err _e => "malformed error object",
    Result.ok obj =>
      match mcp_str_field obj "message" {
        Result.err _e => "error without a message",
        Result.ok msg =>
          match Json.get_num_i64 (Json.get_num (mcp_field_or_null obj "code")) {
            Result.err _e => msg,
            Result.ok code => String.concat (I64.to_string code) (String.concat ": " msg),
          },
      },
  }

// --- Requests ---
//
// Every builder returns an UNFRAMED body; `stdio.mo` appends the newline
// and writes it. Ids are `Json` nodes for the same reason
// `jsonrpc.mo` keeps them that way: the response must be matchable to the
// request without either side re-rendering the other's spelling.

/// The `initialize` request: protocol version, no capabilities beyond the
/// base protocol's tools, and who is asking.
pub def mcp_initialize_request (id : Json) (client : McpClientInfo) : String :=
  rpc_encode_request id "initialize"
    (rpc_object [
      Pair.pair "protocolVersion" (Json.make_str mcp_protocol_version),
      Pair.pair "capabilities" (rpc_object List.empty),
      Pair.pair "clientInfo" (rpc_object [
        Pair.pair "name" (Json.make_str client.name),
        Pair.pair "version" (Json.make_str client.version),
      ]),
    ])

/// The `notifications/initialized` notification: no id (answering a
/// notification is a protocol violation), no params. Sent once, after
/// `initialize` succeeds -- the handshake's second half.
pub def mcp_initialized_notification : String :=
  rpc_encode_notification "notifications/initialized" (rpc_object List.empty)

/// The `tools/list` request. The response's `nextCursor` is decoded by
/// nobody yet: this client mounts servers with small catalogues and asks
/// once, so pagination support would be untested code. The cursor is
/// still sent by servers that have one -- ignored, not rejected.
pub def mcp_tools_list_request (id : Json) : String :=
  rpc_encode_request id "tools/list" (rpc_object List.empty)

/// The `tools/call` request: a tool name and its arguments object.
pub def mcp_call_request (id : Json) (tool : String) (args : Json) : String :=
  rpc_encode_request id "tools/call"
    (rpc_object [
      Pair.pair "name" (Json.make_str tool),
      Pair.pair "arguments" args,
    ])

// --- Response decoding ---

/// The `initialize` result: the server's name, version, and the protocol
/// version it will actually speak.
pub def mcp_decode_initialize (body : String) : Result String McpServerInfo :=
  match mcp_result_of body {
    Result.err e => Result.err e,
    Result.ok r =>
      match Json.get_object r {
        Result.err _e => Result.err "initialize result is not an object",
        Result.ok result =>
          match mcp_str_field result "protocolVersion" {
            Result.err e => Result.err e,
            Result.ok pv =>
              match Json.get_object (mcp_field_or_null result "serverInfo") {
                Result.err _e => Result.err "serverInfo is not an object",
                Result.ok info =>
                  match mcp_str_field info "name" {
                    Result.err e => Result.err e,
                    Result.ok name =>
                      match mcp_str_field info "version" {
                        Result.err e => Result.err e,
                        Result.ok v =>
                          // Bound to an annotated local rather than written as
                          // `Result.ok { ... }`: a bare struct literal in
                          // argument position is the recorded self-hosted
                          // checker gap, silent in a dependency module.
                          let info2 : McpServerInfo :=
                            { name := name, version := v, protocol_version := pv } in
                          Result.ok info2,
                      },
                  },
              },
          },
      },
  }

/// The `tools/list` result: every entry in the `tools` array. A missing
/// `name` fails the whole decode rather than silently dropping the tool:
/// a catalogue entry the harness cannot name is a tool it cannot call,
/// and a partial registry is worse than an error.
pub def mcp_decode_tools_list (body : String) : Result String (List McpTool) :=
  match mcp_result_of body {
    Result.err e => Result.err e,
    Result.ok r =>
      match Json.get_object r {
        Result.err _e => Result.err "tools/list result is not an object",
        Result.ok result =>
          match mcp_field result "tools" {
            Result.err e => Result.err e,
            Result.ok tj =>
              match Json.get_array tj {
                Result.err _e => Result.err "tools is not an array",
                Result.ok entries => mcp_decode_tool_entries entries,
              },
          },
      },
  }

#[partial]
def mcp_decode_tool_entries (entries : List Json) : Result String (List McpTool) :=
  match entries {
    List.empty => Result.ok List.empty,
    List.cons j rest =>
      match mcp_decode_tool j {
        Result.err e => Result.err e,
        Result.ok t =>
          match mcp_decode_tool_entries rest {
            Result.err e => Result.err e,
            Result.ok ts => Result.ok (List.cons t ts),
          },
      },
  }

def mcp_decode_tool (j : Json) : Result String McpTool :=
  match Json.get_object j {
    Result.err _e => Result.err "tool entry is not an object",
    Result.ok obj =>
      match mcp_str_field obj "name" {
        Result.err e => Result.err e,
        Result.ok name =>
          // Annotated local, same reason as `mcp_decode_initialize`.
          let t : McpTool :=
            { name := name,
              description := mcp_str_or_empty obj "description",
              schema := mcp_field_or_null obj "inputSchema" } in
          Result.ok t,
      },
  }

/// The `tools/call` result: the first text block's text, and `isError`.
///
/// MCP content blocks are tagged (`{"type":"text","text":...}`); a call
/// may return image or resource blocks this harness cannot carry, so the
/// FIRST text block is the answer and a response with no text block at
/// all decodes as empty text -- the call succeeded, it just said nothing
/// this client can repeat.
pub def mcp_decode_call (body : String) : Result String McpCallResult :=
  match mcp_result_of body {
    Result.err e => Result.err e,
    Result.ok r =>
      match Json.get_object r {
        Result.err _e => Result.err "tools/call result is not an object",
        Result.ok result =>
          // Annotated local, same reason as `mcp_decode_initialize`.
          let r : McpCallResult :=
            { text := mcp_first_text (mcp_field_or_null result "content"),
              is_error := mcp_bool_or_false result "isError" } in
          Result.ok r,
      },
  }

/// The text of the first `text`-typed block in a content array, or "".
///
/// The `type` tag is checked by looking for a `text` FIELD rather than by
/// comparing the tag: `"type":"text"` and a `text` field are the same
/// predicate for well-formed blocks, and a block with a `text` field but
/// a wrong tag is broken in a way that still leaves the text readable --
/// the harness cares what the tool said, not that the server spelled the
/// envelope right.
#[partial]
def mcp_first_text (content : Json) : String :=
  match Json.get_array content {
    Result.err _e => "",
    Result.ok blocks => mcp_first_text_go blocks,
  }

#[partial]
def mcp_first_text_go (blocks : List Json) : String :=
  match blocks {
    List.empty => "",
    List.cons b rest =>
      match Json.get_object b {
        Result.err _e => mcp_first_text_go rest,
        Result.ok obj =>
          match Json.get_str (mcp_field_or_null obj "text") {
            Result.err _e => mcp_first_text_go rest,
            Result.ok s => s,
          },
      },
  }
