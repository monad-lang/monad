/// One mounted MCP server: the handshake, the tool catalogue, teardown.
///
/// This is the composition layer -- `protocol.mo` owns what the messages
/// say, `stdio.mo` owns how they move, and this module owns the SESSION:
/// spawn, `initialize` + `notifications/initialized`, then `tools/list`
/// and `tools/call` over that established transport, then teardown.
///
/// No `IORef`, so the session is a value like the transport is: every
/// operation returns the NEXT `McpServer` alongside its answer, and the
/// id counter rides in the struct (there is nothing else to put it in).
/// Ids are `I64`s rendered as JSON number nodes, which is JSON-RPC's own
/// canonical shape for a client that counts its requests.
///
/// The def-per-stage shape is `motes/moose/src/client.mo`'s own: a
/// monadic bind cannot sit in a match arm, so each `<-` lives in its own
/// def's do-block body and every arm either returns, binds a pure
/// `let ... in`, or calls the next stage's def.
use json::json {Json}
use mcp_client::protocol {
  McpCallResult, McpClientInfo, McpServerInfo, McpTool, mcp_call_request, mcp_decode_call,
  mcp_decode_initialize, mcp_decode_tools_list, mcp_initialized_notification,
  mcp_initialize_request, mcp_tools_list_request,
}
use mcp_client::stdio {
  McpStdio, Stdio.close, Stdio.dispose, Stdio.read_log, Stdio.request, Stdio.send, Stdio.start,
}

/// A mounted server: transport, who the server is, and the next request
/// id. Everything a session needs, in one value, because there is no
/// mutable alternative.
pub struct McpServer {
  io : McpStdio,
  info : McpServerInfo,
  next_id : I64,
}

/// The id `n` denotes, as the JSON node the request envelope carries.
def server_id (n : I64) : Json :=
  Json.make_num_int n

/// Spawn the server and complete the handshake: `initialize`, read the
/// response, then `notifications/initialized`. The FIRST id is consumed
/// by `initialize`, so a fresh session's `next_id` is 2 -- the counter
/// records the conversation.
pub def Server.connect (client : McpClientInfo) (cmd : String) (args : List String) : IO (Result String McpServer) := do {
  let opened <- Stdio.start cmd args;
  server_connect_opened client opened
}

/// The spawn's verdict: the OS error, or a transport to say hello to.
def server_connect_opened (client : McpClientInfo) (opened : Result String McpStdio) : IO (Result String McpServer) :=
  match opened {
    Result.err e => return (Result.err e),
    Result.ok s0 => server_connect_hello client s0,
  }

/// Send `initialize` on the fresh transport.
def server_connect_hello (client : McpClientInfo) (s0 : McpStdio) : IO (Result String McpServer) := do {
  let rr <- Stdio.request s0 (server_id 1) (mcp_initialize_request (server_id 1) client);
  server_connect_reply rr
}

/// The `initialize` request's verdict.
def server_connect_reply (rr : Result String (Pair McpStdio String)) : IO (Result String McpServer) :=
  match rr {
    Result.err e => return (Result.err e),
    Result.ok p => server_connect_pair p,
  }

/// The response frame's two halves: the advanced transport and the body.
def server_connect_pair (p : Pair McpStdio String) : IO (Result String McpServer) :=
  match p {
    Pair.pair s1 body => server_connect_decode s1 body,
  }

/// The handshake body's verdict: a decode error, or who the server is.
/// The decode error is the one handshake exit `Stdio.request`'s own
/// teardown does NOT cover -- the request succeeded and returned a
/// transport -- so this arm disposes it itself (the module doc's
/// failure-is-teardown contract).
def server_connect_decode (s1 : McpStdio) (body : String) : IO (Result String McpServer) :=
  match mcp_decode_initialize body {
    Result.err e => server_connect_decode_err s1 e,
    Result.ok info => server_connect_initialized s1 info,
  }

/// A handshake response that does not decode: kill and reap the child,
/// then report.
def server_connect_decode_err (s1 : McpStdio) (e : String) : IO (Result String McpServer) := do {
  let _dead <- Stdio.dispose s1;
  return (Result.err e)
}

/// Send `notifications/initialized` -- the handshake's second half.
def server_connect_initialized (s1 : McpStdio) (info : McpServerInfo) : IO (Result String McpServer) := do {
  let sent <- Stdio.send s1 mcp_initialized_notification;
  server_connect_finish s1 info sent
}

/// The notification's verdict: the session is mounted, or it never was.
/// The send failure is a RAW `Stdio.send` error (not `Stdio.request`), so
/// this arm owns the child's teardown too -- `s1` rides along for it.
def server_connect_finish (s1 : McpStdio) (info : McpServerInfo) (sent : Result String McpStdio) : IO (Result String McpServer) :=
  match sent {
    Result.err e => server_connect_send_err s1 e,
    Result.ok s2 =>
      // Annotated local: a bare struct literal in argument position is
      // the recorded self-hosted checker gap.
      let m : McpServer := { io := s2, info := info, next_id := 2 } in
      return (Result.ok m),
  }

/// The `notifications/initialized` send failed: kill and reap the child,
/// then report.
def server_connect_send_err (s1 : McpStdio) (e : String) : IO (Result String McpServer) := do {
  let _dead <- Stdio.dispose s1;
  return (Result.err e)
}

/// The id for the next request, and the session with that id consumed.
def server_fresh_id (m : McpServer) : Pair McpServer Json :=
  let m2 : McpServer := { io := m.io, info := m.info, next_id := I64.add m.next_id 1 } in
  Pair.pair m2 (server_id m.next_id)

/// `tools/list`, decoded to the catalogue. On SUCCESS the returned session
/// has the id consumed; on FAILURE the error carries no session at all, so
/// the caller's ORIGINAL value (id not yet consumed) is the only one left.
/// That is safe because a failed request has already killed the transport
/// (see `stdio.mo`'s failure-is-teardown contract) -- there is no live
/// conversation for a reissued id to collide with.
pub def Server.list_tools (m : McpServer) : IO (Result String (Pair McpServer (List McpTool))) :=
  match server_fresh_id m {
    Pair.pair m2 id => server_list_request m2 id,
  }

/// Send `tools/list` on the session's transport.
def server_list_request (m2 : McpServer) (id : Json) : IO (Result String (Pair McpServer (List McpTool))) := do {
  let rr <- Stdio.request m2.io id (mcp_tools_list_request id);
  server_list_reply m2 rr
}

/// The request's verdict.
def server_list_reply (m2 : McpServer) (rr : Result String (Pair McpStdio String)) : IO (Result String (Pair McpServer (List McpTool))) :=
  match rr {
    Result.err e => return (Result.err e),
    Result.ok p => server_list_pair m2 p,
  }

/// The response frame's two halves.
def server_list_pair (m2 : McpServer) (p : Pair McpStdio String) : IO (Result String (Pair McpServer (List McpTool))) :=
  match p {
    Pair.pair s2 body => server_list_decode m2 s2 body,
  }

/// The catalogue's verdict: a decode error, or the tools.
def server_list_decode (m2 : McpServer) (s2 : McpStdio) (body : String) : IO (Result String (Pair McpServer (List McpTool))) :=
  match mcp_decode_tools_list body {
    Result.err e => return (Result.err e),
    Result.ok tools =>
      let m3 : McpServer := { io := s2, info := m2.info, next_id := m2.next_id } in
      return (Result.ok (Pair.pair m3 tools)),
  }

/// `tools/call`, decoded to the result. Same id contract as `list_tools`:
/// consumed on success, and on failure the caller's original value is the
/// one that survives -- safe for the same reason (the transport is dead).
pub def Server.call (m : McpServer) (tool : String) (args : Json) : IO (Result String (Pair McpServer McpCallResult)) :=
  match server_fresh_id m {
    Pair.pair m2 id => server_call_request m2 id tool args,
  }

/// Send `tools/call` on the session's transport.
def server_call_request (m2 : McpServer) (id : Json) (tool : String) (args : Json) : IO (Result String (Pair McpServer McpCallResult)) := do {
  let rr <- Stdio.request m2.io id (mcp_call_request id tool args);
  server_call_reply m2 rr
}

/// The request's verdict.
def server_call_reply (m2 : McpServer) (rr : Result String (Pair McpStdio String)) : IO (Result String (Pair McpServer McpCallResult)) :=
  match rr {
    Result.err e => return (Result.err e),
    Result.ok p => server_call_pair m2 p,
  }

/// The response frame's two halves.
def server_call_pair (m2 : McpServer) (p : Pair McpStdio String) : IO (Result String (Pair McpServer McpCallResult)) :=
  match p {
    Pair.pair s2 body => server_call_decode m2 s2 body,
  }

/// The call's verdict: a decode error, or the tool's result.
def server_call_decode (m2 : McpServer) (s2 : McpStdio) (body : String) : IO (Result String (Pair McpServer McpCallResult)) :=
  match mcp_decode_call body {
    Result.err e => return (Result.err e),
    Result.ok r =>
      let m3 : McpServer := { io := s2, info := m2.info, next_id := m2.next_id } in
      return (Result.ok (Pair.pair m3 r)),
  }

/// Who the server said it is, from the handshake.
pub def Server.info (m : McpServer) : McpServerInfo :=
  m.info

/// One line of the server's stderr log -- `Stdio.read_log`'s contract,
/// reached through the session so a caller holding a server never has
/// to touch the transport directly.
pub def Server.read_log (m : McpServer) : IO (Result String (Option String)) :=
  Stdio.read_log m.io

/// Clean teardown: wait for the server to exit on its own. For a server
/// that will not, `Server.dispose` -- SIGKILL and reap in one call,
/// idempotent so a double disposer is safe.
pub def Server.close (m : McpServer) : IO I64 :=
  Stdio.close m.io

/// Forceful teardown, no status: `Stdio.dispose` kills and reaps in one
/// call, and a killed server's signal death has no exit status to
/// report.
pub def Server.dispose (m : McpServer) : IO Unit :=
  Stdio.dispose m.io
