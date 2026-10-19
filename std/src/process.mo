// IO is ambient (init/io.mo, always a loaded root) -- no `use` needed.

use lib::io {}
use lib::stream {StreamError, StreamError.is_not_found}
open IO {current_time_nano, read_file}

#[native "exec_cmd"]
pub def exec_cmd (cmd : String) (args : List String) : IO I64

#[native "process_id"]
pub def process_id : I64

// ── Piped subprocesses (agent-skills.md Phase 4 / Design 6) ────────────
//
// `exec_cmd` and `Proc.capture` (below) wait for the child and return
// only what it already wrote; a PROTOCOL peer -- an MCP server on
// stdio -- needs the opposite: write its stdin while it runs, read its
// stdout line by line, keep stderr separate, and be able to kill it.
// That needs child state to OUTLIVE a single call, which no
// composition of `exec_cmd` can hold, so unlike `Proc.capture` these
// ARE natives -- the one place in this file the "deliberately not a
// native" rule below gives way, for the reason that rule states: the
// wiring cost buys a capability nothing else here can express.
//
// Four natives, not six: the former read/read-stderr and wait/kill
// twins are merged behind I64 flags -- `proc_read`'s second argument
// picks the stream, `proc_wait`'s picks plain reap vs
// SIGKILL-then-reap. The natives return `RawIO _`, the raw payload
// layer; the `IO.mk` wrap happens HERE, in the pub wrappers -- the
// same split `IO.pure`/`RawIO.pure` use, so the Rust and C sides stay
// raw payload producers while every user-facing operation is `IO _`.
// The wrappers are the public API; the natives are `priv` so no other
// module can reach past them.
//
// `Child` is opaque the way `FdStream` is (std/src/stream.mo): the
// constructor exists so the checker can see a type; the runtime value
// is a registry handle, never a constructor. Nothing may pattern-match,
// compare or print one. It is `pub` because `motes/mcp_client`
// (a separate mote) holds children.
//
// stdout and stderr stay SEPARATE pipes here on purpose. `Proc.
// capture` merges them, which is right for toolchain probes (see its
// own doc) and wrong for a protocol stream: a server's log line on
// stderr must not land inside the JSON-RPC framing. `read_stderr_line`
// exists so a caller can drain those logs without touching the frame
// stream.

pub type Child {
  child
}

/// `proc_read`'s stream flag: 0 = stdout. Named so the wrappers read
/// as intent rather than as a magic number, and dotted so the
/// whole-program bare-name table does not gain a `stdout`.
priv def Proc.stdout_flag : I64 := 0

/// `proc_read`'s stream flag: 1 = stderr.
priv def Proc.stderr_flag : I64 := 1

/// `proc_wait`'s kill flag: 0 = plain reap.
priv def Proc.reap_flag : I64 := 0

/// `proc_wait`'s kill flag: 1 = SIGKILL first, then reap.
priv def Proc.kill_flag : I64 := 1

/// Fork+exec `cmd args` with all three standard streams piped.
/// Payload is `Result.err` (with the OS message) rather than a native
/// failure when the child could not be spawned -- a caller composes
/// the error through `ResultT` like every other failure here.
#[native "proc_spawn"]
priv def proc_spawn (cmd : String) (args : List String) : RawIO (Result String Child)

/// Write `s` to the child's stdin and flush. Payload is `Result.err`
/// when the child is gone (a dead peer's EPIPE surfaces here -- that
/// is the signal to stop talking to it), `Result.ok` with the byte
/// count otherwise.
#[native "proc_write"]
priv def proc_write (c : Child) (s : String) : RawIO (Result String U64)

/// One line of the child's chosen stream (`stream`: 0 = stdout, 1 =
/// stderr) WITHOUT its trailing newline (any `\r` stays -- toolkit's
/// framing trims it, keeping one definition of "line" per concern).
/// Payload's `Option.none` is end of stream; a final line truncated by
/// EOF is DISCARDED rather than half-delivered, because a JSON-RPC
/// frame without its newline is a truncated message, not a message.
/// A line is BOUNDED: content beyond 1048576 bytes (one mebibyte) is
/// `Result.err` -- a peer that withholds its newline must fail the
/// read rather than grow it without limit. Both backends carry the
/// same number; the caller should treat the peer as broken.
#[native "proc_read"]
priv def proc_read (c : Child) (stream : I64) : RawIO (Result String (Option String))

/// Close the pipes, reap the child, and free its slot, returning the
/// exit status -- or -1 if it died on a signal, `exec_cmd`'s own
/// convention. With `kill` set, SIGKILL first, so one call is the whole
/// "kill, then reap" teardown. Killing an already-exited child is not
/// an error either way -- a disposer must be idempotent. The handle
/// dies with the child: nothing may use it after `proc_wait`.
#[native "proc_wait"]
priv def proc_wait (c : Child) (kill : I64) : RawIO I64

/// Fork+exec `cmd args` with all three standard streams piped.
/// `Result.err` (with the OS message) rather than a native failure
/// when the child could not be spawned -- a caller composes the error
/// through `ResultT` like every other failure here.
pub def Proc.spawn (cmd : String) (args : List String) : IO (Result String Child) :=
    IO.mk (proc_spawn cmd args)

/// Write `s` to the child's stdin and flush. `Result.err` when the
/// child is gone (a dead peer's EPIPE surfaces here -- that is the
/// signal to stop talking to it), `Result.ok` with the byte count
/// otherwise.
pub def Proc.write (c : Child) (s : String) : IO (Result String U64) :=
    IO.mk (proc_write c s)

/// One line of the child's stdout WITHOUT its trailing newline (any
/// `\r` stays -- toolkit's framing trims it, keeping one definition of
/// "line" per concern). `Option.none` is end of stream; a final line
/// truncated by EOF is DISCARDED rather than half-delivered, because
/// a JSON-RPC frame without its newline is a truncated message, not a
/// message. A line whose content exceeds one mebibyte is `Result.err`
/// (see `proc_read`'s own contract for the bound).
pub def Proc.read_line (c : Child) : IO (Result String (Option String)) :=
    IO.mk (proc_read c Proc.stdout_flag)

/// `Proc.read_line`'s contract, over the child's stderr -- the log
/// stream a server writes while its protocol stream stays clean.
pub def Proc.read_stderr_line (c : Child) : IO (Result String (Option String)) :=
    IO.mk (proc_read c Proc.stderr_flag)

/// Close the pipes, reap the child, and return its exit status -- or
/// -1 if it died on a signal, `exec_cmd`'s own convention. The handle
/// dies with the child: nothing may use it after `wait`.
pub def Proc.wait (c : Child) : IO I64 :=
    IO.mk (proc_wait c Proc.reap_flag)

/// SIGKILL the child, then reap it and free its slot -- one call is the
/// whole teardown, so no caller needs a `wait` after `kill`. Killing
/// an already-exited child is not an error (a disposer must be
/// idempotent); a `wait` AFTER `kill` returns -1 because the slot is
/// already freed, not because the kill failed to reap.
pub def Proc.kill (c : Child) : IO Unit :=
    IO.mk (RawIO.bind (proc_wait c Proc.kill_flag) (fn _ => RawIO.pure Unit.unit))

// ── Capturing a command's output ────────────────────────────────────────
// `exec_cmd` above hands back an exit status and nothing else:
// `monad_exec_cmd` (runtime/src/runtime.c) is fork + execvp + waitpid
// returning `WEXITSTATUS`, with no pipe and no `dup2`. Reading what a tool
// PRINTED therefore needs a detour, and `Proc.capture` is the one place
// that detour lives -- `clang -dumpmachine`, `llc --version` and
// `git rev-parse` all want it, and a second hand-rolled copy is how the
// old `link_ir` build-commit probe drifted (see llvm/src/link.mo's
// `build_commit_define` for that story).
//
// Deliberately NOT a new native. A native costs six wiring places --
// core_native.rs's dispatch arm AND its PURE_NATIVES allowlist,
// lower_core_ir.rs, natives.mo's `native_runtime_fn_name` AND its
// `runtime_declarations`, and runtime.c -- and then has to be kept in step
// across both runtimes forever. Everything below is ordinary Monad over
// primitives that already exist on both.

/// The byte `'` (0x27). Named because it is load-bearing twice below: it
/// is what `Proc.shell_quote` has to escape, and the fact that it is
/// BELOW 0x80 is what makes slicing at its index UTF-8-safe.
def Proc.quote_byte : U8 := 39u8

/// Index of the first `'` in `s`, or `none`.
///
/// Byte-exact, via `String.to_list`. That is not fussiness: `String.slice`
/// and `String.drop` are byte-oriented and silently return `""` when an
/// offset lands mid-character (see the UTF-8 note in
/// lang/src/parser/combinators.mo, which was written after exactly that
/// bug truncated everything after an em dash). Scanning the byte list
/// gives an exact index, and slicing AT that index is safe for the one
/// reason that matters: `0x27` is below `0x80`, so it can never be a
/// continuation byte, and a quote's index is therefore always a character
/// boundary.
def Proc.first_quote (s : String) : Option I64 :=
    Proc.first_quote_go (String.to_list s) 0

#[partial]
def Proc.first_quote_go (bytes : List U8) (i : I64) : Option I64 :=
    match bytes {
        List.empty => Option.none,
        List.cons b rest =>
            if U8.beq b Proc.quote_byte
            then Option.some i
            else Proc.first_quote_go rest (i + 1)
    }

/// Replace every `'` with `'\''` -- close the quote, emit an escaped
/// quote, reopen it. Splits AT each quote rather than walking byte by
/// byte, for the boundary reason in `Proc.first_quote`.
#[partial]
def Proc.escape_quotes (s : String) : String :=
    match Proc.first_quote s {
        Option.none => s,
        Option.some i =>
            // `String.slice`'s third argument is a LENGTH, not an end
            // index -- so this is "the i bytes before the quote".
            String.concat (String.slice s 0 i)
                (String.concat "'\\''" (Proc.escape_quotes (String.drop (i + 1) s)))
    }

/// Quote `s` so that a POSIX shell reads it as one literal word.
///
/// Single quotes, because they are the only POSIX quoting that is FULLY
/// literal: no parameter expansion, no command substitution, no backslash
/// escapes, no globbing. So a quoted argument cannot be reinterpreted by
/// the shell whatever it contains -- which is what makes it safe to pass a
/// path, a git URL or a ref through `sh -c` at all.
///
/// This is the control, not a convention. Every interpolated component of
/// a `sh -c` script must go through it, and
/// `test_capture_does_not_expand_a_dollar_sign` (in
/// `std/src/process_tests.mo`) is what fails if one stops doing so: it
/// asserts that `$HOME` reaches `echo` as four literal characters.
pub def Proc.shell_quote (s : String) : String :=
    String.concat "'" (String.concat (Proc.escape_quotes s) "'")

/// `cmd arg arg ...`, every word quoted.
#[partial]
def Proc.quoted_argv (cmd : String) (args : List String) : String :=
    String.concat (Proc.shell_quote cmd) (Proc.quoted_args args)

#[partial]
def Proc.quoted_args (args : List String) : String :=
    match args {
        List.empty => "",
        List.cons a rest =>
            String.concat " " (String.concat (Proc.shell_quote a) (Proc.quoted_args rest))
    }

/// Where the redirect lands. Pid AND nanosecond, because a fixed `/tmp`
/// name collides across concurrent runs and this corpus is swept sharded
/// (scripts/check-monad-tests.sh runs MONAD_SWEEP_JOBS processes at once).
///
/// Uniqueness is not GUARANTEED -- two captures in the same nanosecond on
/// the same pid would share a path. Each call does a fork and an exec, so
/// that cannot happen in practice; saying so is better than implying a
/// guarantee this cannot make.
def Proc.scratch_path : IO String := do {
    let nanos <- current_time_nano;
    return ("/tmp/monad_capture_" ++ I64.to_string process_id ++ "_" ++ I64.to_string nanos)
}

/// Read the redirect file, then remove it. Missing (`not_found`) means
/// `sh` never got far enough to create it, which is not an error here:
/// the caller still gets the exit status, with empty output.
///
/// Any OTHER read failure must not pass for empty output, and
/// `Proc.capture`'s type has no error channel of its own, so it is
/// folded into the existing one: the reason replaces the output and a
/// zero exit status becomes 1 (`Proc.capture_read`).
///
/// `rm` rather than a native, because there is no removal native and this
/// is already the established spelling (lang/src/codegen/test/
/// e2e_harness.mo and four slow_tests files all do `exec_cmd "rm"`).
def Proc.read_then_remove (path : String) : IO (Result StreamError String) := do {
    let out <- read_file (Path.path path);
    let _removed <- exec_cmd "rm" ["-f", path];
    return out
}

/// The exit status and output of a capture whose redirect file read as `r`.
def Proc.capture_read (code : I64) (r : Result StreamError String) : Pair I64 String :=
    match r {
        Result.ok out => Pair.pair code out,
        Result.err e =>
            if StreamError.is_not_found e
            then Pair.pair code ""
            else Pair.pair (if code == 0 then 1 else code) ("capture: reading the output failed: " ++ e.message)
    }

/// Run `cmd args` and return its exit status together with everything it
/// wrote, stdout and stderr MERGED.
///
/// Merged on purpose. The callers are toolchain probes and failing
/// external tools, and which stream carries the interesting text is not
/// something they should have to know: `clang -dumpmachine` prints the
/// triple on stdout, `llc --version` splits its target list across both
/// depending on version, and a failed `mlir-opt` pass pipeline puts its
/// ENTIRE signal on stderr (see plans/bootstrapping/mlir-codegen.md, which
/// records that as a hard blocker). One string, one exit code.
#[partial]
pub def Proc.capture (cmd : String) (args : List String) : IO (Pair I64 String) := do {
    let tmp <- Proc.scratch_path;
    let script : String :=
        Proc.quoted_argv cmd args ++ " > " ++ Proc.shell_quote tmp ++ " 2>&1";
    let code <- exec_cmd "sh" ["-c", script];
    let out <- Proc.read_then_remove tmp;
    return (Proc.capture_read code out)
}

// Tests live in `std/src/process_tests.mo`, not here, and that is forced
// rather than stylistic: this module is one of the three `std/src/lib.mo`
// re-exports (`path`, `io`, `process`), which the module loader seeds
// ambiently into every closure. A `#[test]` in one of them is never
// attributed to a TARGET module, so `monad test std/src/process.mo`
// answers "No tests found" and the `monad test std` directory sweep skips
// it silently -- verified by putting a trivial `def test_probe : Bool :=
// true` in this file and watching both ignore it. That is why
// `path_tests.mo`, `map_tests.mo` and `sha256_tests.mo` are separate files
// too.
