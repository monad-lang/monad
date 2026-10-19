/// `Loop.retry_send`'s policy and loop -- the UI-repair pass's retry
/// seam: `retries` total attempts, the sleep as a seam, each retry
/// announced through `emit`, and 4xx-status errors (except 429) NOT
/// worth a resend. The scripted senders count their attempts in a tap
/// file (read-modify-write -- the same no-`IORef` discipline as the
/// dumb loop's cursor), and the sleep is `silent_sleep`, so nothing
/// here waits.
use std::test {Test.write_fixture, Test.read_fixture_or}
use init::transformers {ResultT}
use shuttle::loop {Loop.retry_send}
use shuttle::message {Message, Turn, Usage}
use shuttle::message_types {Role, Content, StopReason}
use shuttle::agent {silent_sleep}
use std::process {process_id}

def pid : String := I64.to_string process_id

def tap_path : String :=
    String.concat "/tmp/shuttle_retry_tap_" (String.concat pid ".txt")

def emit_path : String :=
    String.concat "/tmp/shuttle_retry_emit_" (String.concat pid ".txt")

def read_file_opt (path : String) : IO String :=
    Test.read_fixture_or (Path.path path) ""

def write_text_opt (path : String) (text : String) : IO Unit :=
    do { let _w <- Test.write_fixture (Path.path path) text; return unit }

/// Append one mark: read, concat, write (no truncate-to-append native).
#[partial]
def tap_mark_in (path : String) : IO Unit := do {
    let t <- read_file_opt path;
    let _ <- write_text_opt path (String.concat t "-");
    IO.pure unit
}

def ok_turn : Turn :=
    let message : Message := { role := Role.assistant, content := [Content.text "recovered"] } in
    let usage : Usage := { input_tokens := 1, output_tokens := 1, cached_tokens := 0 } in
    { message := message, usage := usage, stop := StopReason.end_turn }

/// A sender that fails on the first attempt and succeeds on the second
/// (the tap's dash count is its attempt memory).
#[partial]
def fails_once (u : Unit) : ResultT String IO Turn := ResultT.mk (do {
    let _ <- tap_mark_in tap_path;
    let t <- read_file_opt tap_path;
    if String.length t > 1
    then return (Result.ok ok_turn)
    else return (Result.err "openai: HTTP 503: busy")
})

/// A sender that ALWAYS fails with the given error text; marks every attempt.
#[partial]
def always_fail (e : String) (u : Unit) : ResultT String IO Turn := ResultT.mk (do {
    let _ <- tap_mark_in tap_path;
    return (Result.err e)
})

def collect_emit (s : String) : IO Unit :=
    write_text_opt emit_path s

/// One retry run over one error text: the tap's final marks.
#[partial]
def run_and_marks (e : String) (retries : I64) : IO (Pair Bool I64) := do {
    let _ <- write_text_opt tap_path "";
    let r <- ResultT.run (Loop.retry_send (always_fail e) silent_sleep retries 1 0 collect_emit);
    let t <- read_file_opt tap_path;
    let ok : Bool := match r { Result.ok _ => true, Result.err _ => false };
    return (Pair.pair ok (String.length t))
}

#[test]
def test_retry_send_exhausts_attempts : IO Bool := do {
    let p <- run_and_marks "openai: HTTP 503: busy" 3;
    return (match p { Pair.pair ok marks => Bool.not ok && marks == 3 })
}

#[test]
def test_retry_send_recovers_on_second_attempt : IO Bool := do {
    let _ <- write_text_opt tap_path "";
    let r <- ResultT.run (Loop.retry_send fails_once silent_sleep 3 1 0 collect_emit);
    let t <- read_file_opt tap_path;
    return (match r { Result.ok _ => t == "--", Result.err _ => false })
}

#[test]
def test_retry_send_single_attempt_is_no_retry : IO Bool := do {
    let p <- run_and_marks "openai: HTTP 503: busy" 1;
    return (match p { Pair.pair ok marks => Bool.not ok && marks == 1 })
}

#[test]
def test_retry_send_skips_4xx_except_429 : IO Bool := do {
    let p422 <- run_and_marks "openai: HTTP 422: bad request" 3;
    let p429 <- run_and_marks "openai: HTTP 429: rate limited" 3;
    return Bool.and
        (match p422 { Pair.pair ok marks => Bool.not ok && marks == 1 })
        (match p429 { Pair.pair ok marks => Bool.not ok && marks == 3 })
}

#[test]
def test_retry_announces_through_emit : IO Bool := do {
    let p <- run_and_marks "openai: HTTP 503: busy" 2;
    let t <- read_file_opt emit_path;
    return (match p { Pair.pair ok _ => Bool.not ok && String.contains t "retrying (2/2)" })
}