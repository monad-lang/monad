use shuttle::tools::shell {shell_run}
use shuttle::tools::shell_args {ShellArgs}
use shuttle::message_types {Content}
use init::transformers {ResultT}

/// One round trip: build args, serialize, run the tool, unwrap the
/// `ResultT`. Every test goes through this so each exercises the real
/// entry point (deserialize -> spawn -> stream -> report) rather than an
/// internal stage.
def shell_command_result (cmd : String) : IO (Result String Content) :=
    let args : ShellArgs := { command := cmd } in
    ResultT.run (shell_run "s1" (ShellArgs.serialize_json args))

/// `want_err` is the expected `is_error`; `needle` must appear in the
/// output text. Checking only `is_error` on the error cases would pass a
/// tool that reported an error with EMPTY output, which is exactly the
/// regression the merged-streams contract exists to prevent.
def content_check (c : Content) (want_err : Bool) (needle : String) : Bool :=
    match c {
        Content.tool_result _ text is_error => is_error == want_err && String.contains text needle,
        _ => false,
    }

#[test]
def test_shell_echo_is_ok_and_captured : IO Bool := do {
    let r <- shell_command_result "echo hello-from-shell";
    return (match r {
        Result.ok c => content_check c false "hello-from-shell",
        Result.err _ => false,
    })
}

#[test]
def test_shell_nonzero_exit_is_error : IO Bool := do {
    let r <- shell_command_result "echo boom; exit 3";
    return (match r {
        Result.ok c => content_check c true "boom",
        Result.err _ => false,
    })
}

#[test]
def test_shell_stderr_is_merged : IO Bool := do {
    let r <- shell_command_result "echo to-stderr 1>&2";
    return (match r {
        Result.ok c => content_check c false "to-stderr",
        Result.err _ => false,
    })
}

#[test]
def test_shell_missing_command_reports_error : IO Bool := do {
    let r <- shell_command_result "nosuchcmdxyz";
    return (match r {
        Result.ok c => content_check c true "not found",
        Result.err _ => false,
    })
}

/// `yes` writes lines forever, so this can only end one way: the line cap
/// fires, the child is SIGKILLed, and the result is an ERROR carrying the
/// truncation marker -- never a clean ok, and never a hang.
#[test]
def test_shell_infinite_output_is_truncated_and_killed : IO Bool := do {
    let r <- shell_command_result "yes";
    return (match r {
        Result.ok c => content_check c true "[output truncated after ",
        Result.err _ => false,
    })
}
