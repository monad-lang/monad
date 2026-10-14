/// Tests for `std/src/process.mo`.
///
/// A separate file because `process.mo` is re-exported by `std/src/lib.mo`
/// and therefore seeded ambiently into every module closure, which makes
/// a `#[test]` inside it undiscoverable -- see that file's note. Same
/// reason `path_tests.mo` and `sha256_tests.mo` are separate.
///
/// Same mote, so `Proc.first_quote` stays package-private and is still
/// reachable here -- no API had to be widened to test it.

use lib::process {}

// ─── Tests: shell_quote ───

#[test]
def test_shell_quote_wraps_in_single_quotes : Bool :=
    String.beq (Proc.shell_quote "abc") "'abc'"

#[test]
def test_shell_quote_keeps_a_space_in_one_word : Bool :=
    String.beq (Proc.shell_quote "a b") "'a b'"

#[test]
def test_shell_quote_empty_is_an_empty_word : Bool :=
    String.beq (Proc.shell_quote "") "''"

/// The whole point: an embedded quote closes, escapes, and reopens.
#[test]
def test_shell_quote_escapes_an_embedded_quote : Bool :=
    String.beq (Proc.shell_quote "it's") "'it'\\''s'"

#[test]
def test_shell_quote_escapes_every_quote : Bool :=
    String.beq (Proc.shell_quote "'a'") "''\\''a'\\'''"

#[test]
def test_shell_quote_leaves_a_dollar_sign_alone : Bool :=
    String.beq (Proc.shell_quote "$HOME") "'$HOME'"

#[test]
def test_first_quote_finds_nothing_in_a_plain_word : Bool :=
    match Proc.first_quote "abc" {
        Option.none => true,
        Option.some _ => false
    }

#[test]
def test_first_quote_finds_the_first_of_two : Bool :=
    match Proc.first_quote "ab'c'd" {
        Option.some i => i == 2,
        Option.none => false
    }

// ─── Tests: capture ───

#[test]
def test_capture_returns_status_and_stdout : IO Bool := do {
    let r <- Proc.capture "echo" ["hi"];
    match r { Pair.pair code out => return (code == 0 && String.beq out "hi\n") }
}

/// Exit status and stderr in one assertion, because both are things
/// `exec_cmd` alone cannot give a caller.
#[test]
def test_capture_merges_stderr_and_keeps_the_exit_status : IO Bool := do {
    let r <- Proc.capture "sh" ["-c", "echo e >&2; exit 3"];
    match r { Pair.pair code out => return (code == 3 && String.beq out "e\n") }
}

/// The injection test. `$HOME` must arrive at `echo` as four literal
/// characters; if `Proc.shell_quote` is ever dropped from the argv
/// construction, the shell expands it here and this fails.
#[test]
def test_capture_does_not_expand_a_dollar_sign : IO Bool := do {
    let r <- Proc.capture "echo" ["$HOME"];
    match r { Pair.pair _code out => return (String.beq out "$HOME\n") }
}

/// A word with a quote in it survives the round trip through `sh -c`.
#[test]
def test_capture_passes_an_embedded_quote_through : IO Bool := do {
    let r <- Proc.capture "echo" ["it's"];
    match r { Pair.pair _code out => return (String.beq out "it's\n") }
}

/// A command that does not exist is a nonzero status and a message, not a
/// crash and not an empty string.
#[test]
def test_capture_of_a_missing_command_is_nonzero : IO Bool := do {
    let r <- Proc.capture "monad_no_such_command_exists" [];
    match r { Pair.pair code _out => return (Bool.not (code == 0)) }
}

// ─── Tests: spawn ──────────────────────────────────────────────────────────
//
// The piped-subprocess natives. These spawn real children (`echo`, `cat`,
// `sh`) rather than mocking the pipe, so each one exercises the actual
// fork/exec path on whichever backend runs it. Read assertions route
// through the `pr_*` helpers below for the same reason toolkit's framing
// tests use `fr_*`: one match per helper, so no `#[test]` def nests two
// differently-typed matches -- the recorded self-hosted codegen hazard --
// and a prefixed name that cannot collide with another mote's test
// helpers in the shared whole-program scope.

/// The payload says `expected` -- `Result.ok (Option.some expected)`.
def pr_some_is (o : Option String) (expected : String) : Bool :=
    match o {
        Option.some s => String.beq s expected,
        Option.none => false
    }

def pr_line_is (l : Result String (Option String)) (expected : String) : Bool :=
    match l {
        Result.ok o => pr_some_is o expected,
        Result.err _ => false
    }

/// End of stream: `Result.ok Option.none`, which is a clean end and not
/// an error -- the distinction a protocol loop's termination hangs on.
def pr_none_is (o : Option String) : Bool :=
    match o {
        Option.none => true,
        Option.some _s => false
    }

def pr_is_eof (l : Result String (Option String)) : Bool :=
    match l {
        Result.ok o => pr_none_is o,
        Result.err _ => false
    }

/// A write reports the byte count it accepted.
def pr_wrote (w : Result String U64) (expected : U64) : Bool :=
    match w {
        Result.ok n => U64.beq n expected,
        Result.err _ => false
    }

/// The whole read loop in miniature: one line, then end of stream, then a
/// clean exit. Everything a newline-framed protocol peer does, in order.
#[test]
def test_spawn_echo_reads_a_line_then_eof_then_waits_zero : IO Bool := do {
    let r <- Proc.spawn "echo" ["hi"];
    match r {
        Result.err _ => return false,
        Result.ok c => do {
            let l1 <- Proc.read_line c;
            let l2 <- Proc.read_line c;
            let code <- Proc.wait c;
            return (pr_line_is l1 "hi" && pr_is_eof l2 && code == 0)
        }
    }
}

/// `cat` is the honest roundtrip: what we wrote must come back, and the
/// byte count must be the string's length. `wait` closing stdin first is
/// what lets the child exit at all, so this also pins that ordering.
#[test]
def test_spawn_cat_roundtrips_a_written_line : IO Bool := do {
    let r <- Proc.spawn "cat" [];
    match r {
        Result.err _ => return false,
        Result.ok c => do {
            let w <- Proc.write c "hello\n";
            let l <- Proc.read_line c;
            let code <- Proc.wait c;
            return (pr_wrote w 6u64 && pr_line_is l "hello" && code == 0)
        }
    }
}

/// A server's stderr is its log stream, not its protocol stream: "err"
/// must come out of `read_stderr_line` while "out" stays on stdout. If
/// the pipes were merged (as `capture` merges them) this fails -- which
/// is exactly why `capture` cannot back an MCP client.
#[test]
def test_spawn_keeps_stderr_out_of_the_protocol_stream : IO Bool := do {
    let r <- Proc.spawn "sh" ["-c", "echo err >&2; echo out"];
    match r {
        Result.err _ => return false,
        Result.ok c => do {
            let e <- Proc.read_stderr_line c;
            let l <- Proc.read_line c;
            let code <- Proc.wait c;
            return (pr_line_is e "err" && pr_line_is l "out" && code == 0)
        }
    }
}

/// `exec_cmd`'s status convention, reached through the piped path: the
/// child's own exit status, not a signal death.
#[test]
def test_spawn_wait_reports_the_exit_status : IO Bool := do {
    let r <- Proc.spawn "sh" ["-c", "exit 3"];
    match r {
        Result.err _ => return false,
        Result.ok c => do {
            let code <- Proc.wait c;
            return (code == 3)
        }
    }
}

/// `kill` is the whole teardown: it SIGKILLs, reaps, and frees the
/// slot. A `wait` AFTER `kill` therefore does not see a child at all
/// -- its -1 is the freed-slot answer, not a signal-death report (the
/// signal death was already reaped inside `kill` itself). This pins
/// exactly that residual `wait`, because a disposer that calls both is
/// the order old callers used and must keep working.
#[test]
def test_spawn_wait_after_kill_reports_a_freed_slot : IO Bool := do {
    let r <- Proc.spawn "sh" ["-c", "sleep 30"];
    match r {
        Result.err _ => return false,
        Result.ok c => do {
            Proc.kill c;
            let code <- Proc.wait c;
            return (code == (0 - 1))
        }
    }
}

/// A frame without its newline is a truncated message, not a message:
/// `printf abc` (no newline) must read as end of stream, not "abc". Both
/// backends agree on discarding, and this is the pin that keeps them
/// agreeing.
#[test]
def test_spawn_discards_a_partial_line_at_eof : IO Bool := do {
    let r <- Proc.spawn "sh" ["-c", "printf abc"];
    match r {
        Result.err _ => return false,
        Result.ok c => do {
            let l <- Proc.read_line c;
            let code <- Proc.wait c;
            return (pr_is_eof l && code == 0)
        }
    }
}

/// A spawn that cannot happen is `Result.err` with the OS message, not a
/// native failure -- the caller composes it like every other error.
#[test]
def test_spawn_of_a_missing_command_is_an_error : IO Bool := do {
    let r <- Proc.spawn "monad_no_such_command_exists" [];
    match r {
        Result.err _ => return true,
        Result.ok c => do {
            let _code <- Proc.wait c;
            return false
        }
    }
}
