/// The stdio transport: newline-framed JSON-RPC over a piped `Child`.
///
/// This is the client half of MCP's stdio mode. The framing itself is NOT
/// here -- `motes/toolkit/src/framing.mo`'s `newline_delimited` mode owns
/// "where does a message end", and this module owns "how do bytes get to
/// that framer": `Proc.spawn`'s piped child, `Proc.write` for frames out,
/// `Proc.read_line` for lines in, with the framer deciding when those
/// lines add up to a message.
///
/// NO MUTABLE STATE ANYWHERE: there is no `IORef` in `std`, so the
/// transport is a value -- `McpStdio` -- and every operation returns the
/// next one. The `buf` field carries whatever arrived but is not yet a
/// complete frame; with a line-oriented read beneath it, a frame
/// completes on every line, so the buffer threads empty in practice --
/// but the loop still goes THROUGH the framer rather than assuming that,
/// which keeps one definition of "line" per concern (the framer trims a
/// trailing `\r`; this module does not re-implement that).
///
/// stderr is a SEPARATE pipe end to end and this module never merges it
/// into the frame stream: a server's log line is not a frame, and
/// `Stdio.read_log` is how a caller drains those logs without touching
/// the protocol stream. That separation is `std/src/process.mo`'s own
/// stated reason the piped natives exist.
///
/// FAILURE IS TEARDOWN: every error exit from `Stdio.request` (and the
/// handshake paths in `server.mo`) kills and reaps the child before the
/// error is returned. A request that failed has no recoverable state --
/// half a conversation is not a conversation -- so the contract is: a
/// failed request leaves the child dead, and any stale `McpStdio` /
/// `McpServer` values still naming it report "no such child" if used.
/// That is what makes request failure leak-free.
///
/// The response wait is a BLOCKING read with no timeout (a poll or timer
/// read is new native surface, deliberately out of scope): a server that
/// never answers, or that floods stderr past the spawn pipe's own buffers
/// before answering, hangs the client. Accepted for a trusted,
/// single-flight client; the poll/timeout read is the named follow-up.
use json::json {Json}
use std::map {BTreeMap}
use std::process {Child, Proc.kill, Proc.read_line, Proc.read_stderr_line, Proc.spawn, Proc.wait, Proc.write}
use toolkit::framing {bad_header, frame, framing_read, need_more, newline_delimited}

/// One mounted transport: the child plus the frame buffer.
pub struct McpStdio {
  child : Child,
  buf : String,
}

/// Spawn the server and hold its pipes (as `Stdio.start`; `open` is a reserved word). `Result.err` (with the OS
/// message) when the command could not run -- the caller composes that
/// error; nothing here kills or reaps on failure, because there is
/// nothing to kill or reap yet.
pub def Stdio.start (cmd : String) (args : List String) : IO (Result String McpStdio) := do {
  let r <- Proc.spawn cmd args;
  match r {
    Result.err e => return (Result.err e),
    Result.ok c =>
      // Annotated local: a bare struct literal in argument position is
      // the recorded self-hosted checker gap, silent in a dependency.
      let s : McpStdio := { child := c, buf := "" } in
      return (Result.ok s),
  }
}

/// One frame OUT: the body plus its newline, then the transport.
///
/// A dead peer's EPIPE surfaces here as `Result.err` -- that is the
/// signal to stop talking to this server.
pub def Stdio.send (s : McpStdio) (body : String) : IO (Result String McpStdio) := do {
  let w <- Proc.write s.child (String.concat body "\n");
  match w {
    Result.err e => return (Result.err e),
    Result.ok _n => return (Result.ok s),
  }
}

/// One complete frame IN, or `Result.err` at end of stream.
///
/// EOF mid-message is an ERROR rather than a partial delivery, for the
/// same reason `Proc.read_line` discards a partial line: a frame that
/// never finished is not a message, and half a JSON-RPC body is worse
/// than a clean "the peer went away". `Proc.read_line` itself never
/// yields a partial line, so the `need_more` loop's EOF case is the only
/// way to get here.
pub def Stdio.read_frame (s : McpStdio) : IO (Result String (Pair McpStdio String)) :=
  stdio_frame_loop s.child s.buf

#[partial]
def stdio_frame_loop (c : Child) (buf : String) : IO (Result String (Pair McpStdio String)) := do {
  match framing_read FramingMode.newline_delimited buf {
    FrameRead.need_more => do {
      let l <- Proc.read_line c;
      stdio_frame_on_line c buf l
    },
    FrameRead.frame body rest =>
      let s2 : McpStdio := { child := c, buf := rest } in
      return (Result.ok (Pair.pair s2 body)),
    FrameRead.bad_header reason => return (Result.err reason),
  }
}

#[partial]
def stdio_frame_on_line (c : Child) (buf : String) (l : Result String (Option String)) : IO (Result String (Pair McpStdio String)) :=
  match l {
    Result.err e => return (Result.err e),
    Result.ok o => stdio_frame_on_option c buf o,
  }

#[partial]
def stdio_frame_on_option (c : Child) (buf : String) (o : Option String) : IO (Result String (Pair McpStdio String)) :=
  match o {
    Option.none => return (Result.err "connection closed mid-message"),
    Option.some line => stdio_frame_loop c (String.concat (String.concat buf line) "\n"),
  }

/// Send a request and read frames until its response arrives.
///
/// This is the transport-level half of request/response matching, and
/// the one place the client is allowed to DISCARD input: a line that
/// does not parse as JSON is skipped, not fatal -- a server may write a
/// banner or a stray log line to stdout and the next real frame is still
/// the answer (agent-skills.md Phase 4's own survival requirement). A
/// frame whose id does not match the request is NOT skipped: this client
/// sends one request at a time, so a mismatched id means the peer is
/// confused about the conversation, and silently waiting past it would
/// turn a protocol break into a hang.
///
/// Every error exit below KILLS AND REAPS the child before returning
/// (see the module doc's failure-is-teardown contract): the send failure,
/// the read failure, and the id mismatch. The one non-error exit that
/// can lose the child -- clean `Stdio.close` -- is the caller's.
///
/// Ids are compared as rendered JSON (`Json.to_string`) rather than
/// structurally: the id this client sent is a node IT built, and the id
/// in the response is whatever the server spelled -- identical text is
/// the specification's own match rule, and text comparison cannot
/// mis-parse a number the structural walk might.
pub def Stdio.request (s : McpStdio) (id : Json) (body : String) : IO (Result String (Pair McpStdio String)) := do {
  let w <- Stdio.send s body;
  match w {
    Result.err e => stdio_send_err s e,
    Result.ok s2 => stdio_response_loop s2 (Json.to_string id),
  }
}

/// The send failed (EPIPE, most likely): the peer is gone, so tear the
/// child down before handing the error back.
def stdio_send_err (s : McpStdio) (e : String) : IO (Result String (Pair McpStdio String)) := do {
  let _dead <- Stdio.dispose s;
  return (Result.err e)
}

/// Read frames until one parses as a response carrying `want`. A failed
/// read is dispose-then-error, same contract as the send above.
#[partial]
#[terminating]
def stdio_response_loop (s : McpStdio) (want : String) : IO (Result String (Pair McpStdio String)) := do {
  let fr <- Stdio.read_frame s;
  match fr {
    Result.err e => stdio_read_err s e,
    Result.ok _ => stdio_response_step want fr,
  }
}

/// The read failed (EOF mid-message, broken pipe, or a frame past
/// `Proc.read_line`'s line bound): the child is in an unknown state, so
/// kill and reap it before reporting.
def stdio_read_err (s : McpStdio) (e : String) : IO (Result String (Pair McpStdio String)) := do {
  let _dead <- Stdio.dispose s;
  return (Result.err e)
}

/// One frame's verdict: the answer, or keep looking. The transport in
/// the verdict's payload is the frame reader's UPDATED one -- the `s`
/// this step was handed has been consumed by the read.
#[terminating]
def stdio_response_step (want : String) (fr : Result String (Pair McpStdio String)) : IO (Result String (Pair McpStdio String)) :=
  match fr {
    Result.err e => return (Result.err e),
    Result.ok p => stdio_response_pair want p,
  }

#[terminating]
def stdio_response_pair (want : String) (p : Pair McpStdio String) : IO (Result String (Pair McpStdio String)) :=
  match p {
    Pair.pair s2 body => stdio_response_body s2 want body,
  }

/// A frame body: parse it, look for the id. Unparseable frames are the
/// skippable ones -- banners and stray log lines that reached stdout.
#[terminating]
def stdio_response_body (s : McpStdio) (want : String) (body : String) : IO (Result String (Pair McpStdio String)) :=
  match Json.parse body {
    Result.err _pe => stdio_response_loop s want,
    Result.ok j => stdio_response_json s want body j,
  }

#[terminating]
def stdio_response_json (s : McpStdio) (want : String) (body : String) (j : Json) : IO (Result String (Pair McpStdio String)) :=
  match Json.get_object j {
    Result.err _e => stdio_response_loop s want,
    Result.ok obj => stdio_response_obj s want body obj,
  }

#[terminating]
def stdio_response_obj (s : McpStdio) (want : String) (body : String) (obj : BTreeMap String Json) : IO (Result String (Pair McpStdio String)) :=
  match Json.object_get "id" obj {
    Option.none => stdio_response_loop s want,
    Option.some idj =>
      if String.beq (Json.to_string idj) want
      then return (Result.ok (Pair.pair s body))
      else stdio_response_mismatch s,
  }

/// A frame arrived with the WRONG id: the peer is confused about the
/// conversation, and waiting past it would turn a protocol break into a
/// hang -- so error out, tearing the child down first (same contract as
/// every other error exit from `Stdio.request`).
def stdio_response_mismatch (s : McpStdio) : IO (Result String (Pair McpStdio String)) := do {
  let _dead <- Stdio.dispose s;
  return (Result.err "response id does not match the request")
}

/// One line of the server's stderr -- its log stream, NOT part of the
/// frame stream. `Option.none` is end of stream; the `Result.err` case is
/// a transport problem, both `Proc.read_stderr_line`'s own contract.
pub def Stdio.read_log (s : McpStdio) : IO (Result String (Option String)) :=
  Proc.read_stderr_line s.child

/// Clean teardown: `Proc.wait` closes the pipes, reaps the child, and
/// frees the slot. For a server that will not exit on its own, use
/// `Stdio.dispose` -- SIGKILL and reap in one call.
pub def Stdio.close (s : McpStdio) : IO I64 :=
  Proc.wait s.child

/// Forceful teardown: SIGKILL, then reap -- `Proc.kill` is the whole
/// thing, one call that kills, reaps, and frees the slot. Idempotent by
/// `Proc.kill`'s own contract, so a disposer that runs twice is safe.
/// No exit status is reported: a killed child's status is the signal
/// death the reap already absorbed, so this returns `Unit` where it
/// once returned a second wait's -1.
pub def Stdio.dispose (s : McpStdio) : IO Unit :=
  Proc.kill s.child
