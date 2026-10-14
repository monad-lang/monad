/// `shell` -- the first tool on the Phase 4 piped-subprocess surface.
/// Unlike `search.mo`'s `Proc.capture` (fork, run to completion, read one
/// buffer), this streams the child's output line by line over `Proc.spawn`
/// /`Proc.read_line`, so it can enforce a LINE-COUNT cap and kill a command
/// that floods the pipe -- `Proc.capture`'s redirect-to-file detour would
/// let a runaway `yes` fill /tmp instead.
///
/// stderr is merged into the output by spawning `sh -c "exec 2>&1;
/// <command>"` -- the redirect runs FIRST, on the shell itself, so the
/// child's stderr target is the stdout pipe before the command executes
/// and the command INHERITS the merge. That is the right contract for a
/// tool whose consumer is an agent: which stream a diagnostic lands on is
/// not something the caller should have to know -- `Proc.capture`'s own
/// rationale, applied here too.
///
/// The naive alternative -- appending `2>&1` AFTER the command text --
/// is WRONG, and `test_shell_stderr_is_merged` is the test that fails if
/// anyone "simplifies" back to it: shell redirections apply left to right,
/// so `echo x 1>&2 2>&1` points stdout at the child's stderr pipe (a
/// stream this tool never reads) and then stderr at that same pipe --
/// the line vanishes from the tool's output entirely.
///
/// NO wall-clock timeout is possible on this surface: `Proc.read_line`
/// BLOCKS on an empty pipe, and nothing in the current native set can
/// interrupt it. A command that runs forever WITHOUT printing (e.g.
/// `sleep infinity`) hangs the tool until the process that hosts it goes
/// away. The line-count cap bounds only the OUTPUT, not the runtime. A
/// timeout needs a pollable read or a timer signal, both new natives --
/// deliberately out of scope for Phase 4.
///
/// Every stage below is its own top-level def with at most one monadic
/// bind: a `let x <- ...` inside a do-block in a match arm is a shape the
/// self-hosted parser/checker mishandles (see `motes/mcp_client/src/
/// server.mo`, which was restructured the same way), so each stage ends by
/// calling the next one in pure position.
use init::transformers {ResultT}
use shuttle::message_types {Content}
use shuttle::tools::shell_args {ShellArgs}
use json::json {Json}
use std::process {Child, Proc.spawn, Proc.read_line, Proc.kill, Proc.wait}

def tool_err (id : String) (msg : String) : Content := Content.tool_result id msg true
def tool_ok (id : String) (msg : String) : Content := Content.tool_result id msg false

/// The output cap, in lines. A constant rather than a parameter: the cap
/// exists to protect the HARNESS (an unbounded tool result is an unbounded
/// prompt), not to serve the model, so the model does not get a vote.
def shell_max_lines : I64 := 200

/// The truncation marker's tail, named so the test can assert on the same
/// spelling without re-deriving the whole message.
def shell_truncated_marker : String := "[output truncated after "

pub def shell_run (id : String) (j : Json) : ResultT String IO Content :=
    match ShellArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                let c <- shell_spawn id args.command;
                return (Result.ok c)
            }),
    }

/// Spawn `sh -c "exec 2>&1; <command>"` and enter the read loop. The
/// redirect is a PREFIX on the command string, not a suffix -- see the
/// module doc for why. The command text is NOT quoted: unlike every other
/// tool here, `command` IS shell script by contract.
def shell_spawn (id : String) (command : String) : IO Content := do {
    let spawned <- Proc.spawn "sh" ["-c", "exec 2>&1; " ++ command];
    match spawned {
        Result.err e => return (tool_err id ("shell: could not spawn sh: " ++ e)),
        Result.ok child => shell_read id child 0 "",
    }
}

/// Read one line and dispatch. `count` is lines read SO FAR; the cap check
/// happens once the line is in hand, so a command whose output is exactly
/// `shell_max_lines` lines runs to completion. (`I64.lt` + `Bool.not`
/// rather than `>=`: the host lowering pass's infix table has no `>=`
/// entry, a constraint every cross-runtime file here inherits.)
#[partial]
def shell_read (id : String) (c : Child) (count : I64) (acc : String) : IO Content := do {
    let ln <- Proc.read_line c;
    match ln {
        Result.err e => return (tool_err id ("shell: read failed: " ++ e)),
        Result.ok opt => shell_got_line id c count acc opt,
    }
}

/// EOF ends the loop (wait for the exit status); a line under the cap
/// accumulates and reads on; a line AT the cap truncates.
#[partial]
def shell_got_line (id : String) (c : Child) (count : I64) (acc : String) (opt : Option String) : IO Content :=
    match opt {
        Option.none => shell_eof id c acc,
        Option.some s =>
            if Bool.not (I64.lt count shell_max_lines)
            then shell_truncate id c acc
            else shell_read id c (count + 1) (acc ++ s ++ "\n"),
    }

/// Clean end of stream: the child exited on its own, so `is_error` is
/// exactly its exit status.
def shell_eof (id : String) (c : Child) (acc : String) : IO Content := do {
    let code <- Proc.wait c;
    return (if code == 0 then tool_ok id acc else tool_err id acc)
}

/// The cap fired: SIGKILL the child, reap it, and report an ERROR -- the
/// command did not finish, and the agent must not read truncated output
/// as a completed result. `Proc.kill` alone is the whole teardown -- it
/// kills, reaps, and frees the slot -- so there is no `wait` after it,
/// and the marker text carries the reason instead of an exit code.
def shell_truncate (id : String) (c : Child) (acc : String) : IO Content := do {
    let _killed <- Proc.kill c;
    return (tool_err id (acc ++ shell_truncated_marker ++ I64.to_string shell_max_lines ++ " lines; command killed]\n"))
}
