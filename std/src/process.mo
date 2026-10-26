// IO is ambient (init/io.mo, always a loaded root) -- no `use` needed.

use lib::io {}
use lib::stream {
  FdStream, FdStream.read_line_bounded, PartialLinePolicy, Stream, StreamError,
  StreamError.is_not_found, stream_result,
}
use lib::bytebuf {ByteBuf.free, ByteBuf.of_string}
open IO {current_time_nano, read_file}

#[native "exec_cmd"]
priv def exec_cmd_raw (cmd : String) (args : List String) : RawIO I64

pub def exec_cmd (cmd : String) (args : List String) : IO I64 :=
  IO.mk (exec_cmd_raw cmd args)

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
// Three natives, plus a view: `proc_spawn`, `proc_wait`, and
// `proc_stream_fd`, which hands out an `FdStream` view of one of the
// child's three pipes and lets `std/src/stream.mo` do the work -- a
// write is `Stream.write`, a line is the shared `stream_read_line`
// reader, and both report the `StreamError` every other stream
// reports. `proc_wait`'s flag
// picks plain reap vs SIGKILL-then-reap. The natives return `RawIO _`,
// the raw payload layer; the `IO.mk` wrap happens HERE, in the pub
// wrappers -- the same split `IO.pure`/`RawIO.pure` use, so the Rust
// and C sides stay raw payload producers while every user-facing
// operation is `IO _`. The wrappers are the public API; the natives
// are `priv` so no other module can reach past them.
//
// `proc_stream_fd` is `priv` and never handed out: a view derived
// before `proc_wait` names a pipe that call closes, so compiled it is
// a stale -- possibly recycled -- descriptor. Every `Proc.*` wrapper
// derives a view on the one call that uses it.
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

/// `proc_stream_fd`'s flag: 0 = the child's stdin (the parent's write
/// end). Named so the wrappers read as intent rather than as a magic
/// number, and dotted so the whole-program bare-name table does not
/// gain a `stdin`.
priv def Proc.stdin_flag : I64 := 0

/// `proc_stream_fd`'s flag: 1 = the child's stdout (the read end).
priv def Proc.stdout_flag : I64 := 1

/// `proc_stream_fd`'s flag: 2 = the child's stderr (the read end).
priv def Proc.stderr_flag : I64 := 2

/// The longest line the piped readers accept, in bytes: one mebibyte.
/// A peer that withholds its newline must fail the read rather than
/// grow it without limit.
priv def Proc.max_line : I64 := 1048576

/// `proc_wait`'s kill flag: 0 = plain reap.
priv def Proc.reap_flag : I64 := 0

/// `proc_wait`'s kill flag: 1 = SIGKILL first, then reap.
priv def Proc.kill_flag : I64 := 1

/// Fork+exec `cmd args` with all three standard streams piped.
/// Payload is `Result.err (Pair.pair <kind code> <message>)` rather
/// than a native failure when the child could not be spawned;
/// `Proc.spawn` decodes it to `StreamError`.
#[native "proc_spawn"]
priv def proc_spawn (cmd : String) (args : List String) : RawIO (Result (Pair I64 String) Child)

/// An `FdStream` view of one of the child's pipes.
///
/// `priv` on purpose, and never handed to a caller: after `proc_wait`
/// the pipes are closed, so a compiled view is a stale -- possibly
/// recycled -- descriptor. Each wrapper below derives a view for the
/// one call that uses it. Never `Stream.close` a view: compiled, that
/// would close the child's pipe.
#[native "proc_stream_fd"]
priv def proc_stream_fd (c : Child) (which : I64) : RawIO FdStream

/// Close the pipes, reap the child, and free its slot, returning the
/// exit status -- or -1 if it died on a signal, `exec_cmd`'s own
/// convention. With `kill` set, SIGKILL first, so one call is the whole
/// "kill, then reap" teardown. Killing an already-exited child is not
/// an error either way -- a disposer must be idempotent. The handle
/// dies with the child: nothing may use it after `proc_wait`.
#[native "proc_wait"]
priv def proc_wait (c : Child) (kill : I64) : RawIO I64

/// Fork+exec `cmd args` with all three standard streams piped.
/// `Result.err` when the child could not be spawned -- a missing
/// command is `not_found`, like every other absent thing.
pub def Proc.spawn (cmd : String) (args : List String) : IO (Result StreamError Child) := do {
    let r <- IO.mk (proc_spawn cmd args);
    return (stream_result r)
}

/// Write `s` to the child's stdin and flush. `Result.err` when the
/// child is gone (a dead peer's EPIPE arrives as `broken_pipe` -- that
/// is the signal to stop talking to it), `Result.ok` with the byte
/// count otherwise.
pub def Proc.write (c : Child) (s : String) : IO (Result StreamError I64) := do {
    // Annotated: the self-hosted checker does not infer `FdStream` through
    // `IO.mk` here, so the `Stream FdStream` instance would not be found.
    let view : FdStream <- IO.mk (proc_stream_fd c Proc.stdin_flag);
    let buf <- ByteBuf.of_string s;
    let r <- Stream.write view buf;
    let _ <- ByteBuf.free buf;
    return r
}

/// One line of the child's stdout WITHOUT its trailing newline (any
/// `\r` stays -- toolkit's framing trims it, keeping one definition of
/// "line" per concern). `Option.none` is end of stream; a final line
/// truncated by EOF is DISCARDED rather than half-delivered, because
/// a JSON-RPC frame without its newline is a truncated message, not a
/// message. A line whose content exceeds `Proc.max_line` (one
/// mebibyte) is `invalid_input` -- a peer that withholds its newline
/// must fail the read rather than grow it without limit. Treat such a
/// peer as broken.
pub def Proc.read_line (c : Child) : IO (Result StreamError (Option String)) := do {
    let view : FdStream <- IO.mk (proc_stream_fd c Proc.stdout_flag);
    FdStream.read_line_bounded view Proc.max_line PartialLinePolicy.discard
}

/// `Proc.read_line`'s contract, over the child's stderr -- the log
/// stream a server writes while its protocol stream stays clean.
pub def Proc.read_stderr_line (c : Child) : IO (Result StreamError (Option String)) := do {
    let view : FdStream <- IO.mk (proc_stream_fd c Proc.stderr_flag);
    FdStream.read_line_bounded view Proc.max_line PartialLinePolicy.discard
}

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
