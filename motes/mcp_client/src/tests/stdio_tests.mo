/// MCP stdio transport tests, against real `sh` peers.
///
/// The transport's job is pipes, not protocol: what can break here is
/// framing (a line in and a line out must be one frame), survival (a
/// peer's stray stdout line must be skipped, not fatal), id matching (a
/// wrong id is a protocol break, not something to wait past), EOF
/// (half a message is not a message), and the stderr separation that is
/// the whole reason the piped natives exist. Each of those needs a real
/// child process to misbehave, so each test spawns one.
///
/// The LSP server mote is NOT usable as a test peer: it speaks
/// Content-Length framing (this client speaks newline-delimited) and has
/// no standalone entry point -- `sh` one-liners stand in, the same
/// `motes/moose` tests spawn real listeners rather than mocking sockets.
///
/// Every peer starts with `read _;` so it cannot exit before the client
/// writes: a peer that exits first turns the client's write into EPIPE
/// and the test into a race.
use json::json {Json}
use mcp_client::stdio {
  McpStdio, Stdio.close, Stdio.dispose, Stdio.read_frame, Stdio.read_log, Stdio.request,
  Stdio.send, Stdio.start,
}

// --- Helpers ---

/// A frame read's verdict: `want` came out of the frame stream.
def ms_frame_is (fr : Result String (Pair McpStdio String)) (want : String) : Bool :=
  match fr {
    Result.err _e => false,
    Result.ok p =>
      match p {
        Pair.pair _s body => String.beq body want,
      },
  }

/// A request's verdict: the id-matched response body, exactly.
def ms_request_is (rr : Result String (Pair McpStdio String)) (want : String) : Bool :=
  match rr {
    Result.err _e => false,
    Result.ok p =>
      match p {
        Pair.pair _s body => String.beq body want,
      },
  }

/// An operation's verdict: the named error, not a success.
def ms_err_is (r : Result String (Pair McpStdio String)) (want : String) : Bool :=
  match r {
    Result.err e => String.beq e want,
    Result.ok _p => false,
  }

/// A log read's verdict: `want` came out of the stderr stream.
def ms_log_is (l : Result String (Option String)) (want : String) : Bool :=
  match l {
    Result.err _e => false,
    Result.ok o =>
      match o {
        Option.none => false,
        Option.some s => String.beq s want,
      },
  }

/// The id this suite's requests count from.
def ms_id : Json :=
  Json.make_num_int 5

/// The `tools/list` request this suite sends, framed by `Stdio.send`.
def ms_list_body : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"tools/list\",\"params\":{}}"

/// The matching response body a peer echoes back.
def ms_list_response : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":5,\"result\":{\"tools\":[]}}"

// --- Framing ---

/// `cat` is the honest roundtrip: one frame out, the same frame in, and
/// the child exits cleanly under the transport's own teardown.
#[test]
def test_stdio_cat_roundtrips_one_frame : IO Bool := do {
  let started <- Stdio.start "cat" [];
  match started {
    Result.err _e => return false,
    Result.ok s0 => do {
      let sent <- Stdio.send s0 "{\"a\":1}";
      match sent {
        Result.err _e => return false,
        Result.ok s1 => do {
          let fr <- Stdio.read_frame s1;
          let code <- Stdio.close s1;
          return (Bool.and (ms_frame_is fr "{\"a\":1}") (I64.beq code 0))
        }
      }
    }
  }
}

/// A frame without its newline is a truncated message: `printf half`
/// (no newline) must read as end of stream mid-message, not "half".
#[test]
def test_stdio_eof_mid_message_is_an_error : IO Bool := do {
  let started <- Stdio.start "sh" ["-c", "printf half"];
  match started {
    Result.err _e => return false,
    Result.ok s0 => do {
      let fr <- Stdio.read_frame s0;
      let code <- Stdio.close s0;
      return (Bool.and (ms_err_is fr "connection closed mid-message") (I64.beq code 0))
    }
  }
}

// --- Request/response survival ---

/// A peer that writes a non-JSON banner line to stdout before its real
/// response is the survival requirement: the banner is SKIPPED and the
/// id-matched frame still comes back -- a server's stray log line is not
/// a dead conversation.
#[test]
def test_stdio_request_skips_a_malformed_line : IO Bool := do {
  let started <- Stdio.start "sh" ["-c", "read _; echo banner-not-json; echo '{\"jsonrpc\":\"2.0\",\"id\":5,\"result\":{\"tools\":[]}}'"];
  match started {
    Result.err _e => return false,
    Result.ok s0 => do {
      let rr <- Stdio.request s0 ms_id ms_list_body;
      let code <- Stdio.close s0;
      return (Bool.and (ms_request_is rr ms_list_response) (I64.beq code 0))
    }
  }
}

/// A response carrying the WRONG id is not skipped and not answered:
/// this client sends one request at a time, so a mismatch means the peer
/// is confused about the conversation, and waiting past it would turn a
/// protocol break into a hang.
#[test]
def test_stdio_request_rejects_a_mismatched_id : IO Bool := do {
  let started <- Stdio.start "sh" ["-c", "read _; echo '{\"jsonrpc\":\"2.0\",\"id\":99,\"result\":{}}'"];
  match started {
    Result.err _e => return false,
    Result.ok s0 => do {
      let rr <- Stdio.request s0 ms_id ms_list_body;
      let code <- Stdio.close s0;
      return (Bool.and (ms_err_is rr "response id does not match the request") (I64.beq code 0))
    }
  }
}

/// The frame stream is stdout only: a peer's stderr log line comes out
/// of `Stdio.read_log` and never appears in a response frame. The
/// request goes FIRST -- a log read on a pipe whose writer is still
/// waiting for the request would block forever, which is the deadlock
/// shape the ordering rule exists to keep out of every caller.
#[test]
def test_stdio_stderr_stays_out_of_the_frame_stream : IO Bool := do {
  let started <- Stdio.start "sh" ["-c", "read _; echo log-line >&2; echo '{\"jsonrpc\":\"2.0\",\"id\":5,\"result\":{}}'"];
  match started {
    Result.err _e => return false,
    Result.ok s0 => do {
      let rr <- Stdio.request s0 ms_id ms_list_body;
      let lg <- Stdio.read_log s0;
      let code <- Stdio.close s0;
      return (Bool.and (ms_log_is lg "log-line")
        (Bool.and (ms_request_is rr "{\"jsonrpc\":\"2.0\",\"id\":5,\"result\":{}}") (I64.beq code 0)))
    }
  }
}

// --- Lifecycle ---

/// A spawn that cannot happen is the caller's `Result.err`, not a
/// native failure.
#[test]
def test_stdio_start_of_a_missing_command_is_an_error : IO Bool := do {
  let started <- Stdio.start "monad_no_such_command_exists" [];
  match started {
    Result.err _e => return true,
    Result.ok _s => return false,
  }
}

/// `Stdio.close` is `Proc.wait` underneath: the child's own exit status.
#[test]
def test_stdio_close_reports_the_exit_status : IO Bool := do {
  let started <- Stdio.start "sh" ["-c", "exit 3"];
  match started {
    Result.err _e => return false,
    Result.ok s0 => do {
      let code <- Stdio.close s0;
      return (I64.beq code 3)
    }
  }
}

/// `Stdio.dispose` is one call that kills AND reaps, and idempotent:
/// the second dispose kills an already-freed slot, which `Proc.kill`'s
/// own contract says is not an error -- a disposer that runs twice is
/// safe. `Unit` because the reap happens inside the call; there is no
/// second wait whose -1 this could report.
#[test]
def test_stdio_dispose_is_idempotent : IO Bool := do {
  let started <- Stdio.start "sh" ["-c", "sleep 30"];
  match started {
    Result.err _e => return false,
    Result.ok s0 => do {
      Stdio.dispose s0;
      Stdio.dispose s0;
      return true
    }
  }
}
