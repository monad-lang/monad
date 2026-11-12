// Phase 4's end-to-end gate: the REAL binary, driven by a committed
// keystroke fixture, against a real file.
//
// WHY THIS EXISTS DESPITE `save_tests.mo`: that file drives the pure
// `update` and runs its commands itself, so it proves the write's own
// behaviour but nothing about the LOOP. The loop is where a piped session
// can silently lose the last keystroke's IO -- its EOF path folds one
// final batch (`motes/tui/src/tui.mo`'s `after_produce` -> `final_frame`),
// and a save issued by the LAST key only reaches disk if that fold runs
// `Cmd.perform`. This test is that assertion, end to end.
//
// THE FIXTURE IS A COMMITTED FILE, not an inline `printf`: `ESCAPE`
// followed by any key decodes as `Alt+key` (`motes/tui/src/input.mo`'s
// `escape_next`), so a fixture written from a shell string is a fixture
// whose meaning depends on quoting. The committed bytes are the contract.
//
// GATED, NOT ALWAYS-ON: the fixture drives a built `ply`, and building
// one costs a full compile (minutes). `PLY_E2E_BIN` names a binary to
// test; unset, the test SKIPs-passing and says so, the way
// `motes/weaver/test/pty_tests.mo` gates its pty suite. CI and a manual
// `scripts`-style run set the variable.

use std::io {IO.println}
use std::process {exec_cmd}
use std::stream {StreamError}

/// The binary under test: `PLY_E2E_BIN`, or `""` when unset.
def e2e_bin : IO String := do {
    let v <- IO.get_env "PLY_E2E_BIN";
    return (match v {
        Option.some b => b,
        Option.none => ""
    })
}

/// The committed keystroke fixture: `x d Space w Space q` -- normal mode
/// throughout, no ESC anywhere (see the file header). Resolved from the
/// repository root, which is `monad test`'s own cwd (the eval suite states
/// the same convention).
def e2e_keys_path : String := "motes/ply/src/tests/fixtures/edit_save.keys"

/// The keystroke fixture for the `:` line: `x d : w Enter` -- delete a line,
/// then save through the command line. Its bytes are the contract, as ever
/// (the file above's header says why): `:` is an ordinary character key, so
/// no ESC is involved.
def e2e_colon_keys_path : String := "motes/ply/src/tests/fixtures/edit_colon_save.keys"

/// The scratch file the run edits. Under `target-monad` (gitignored) so a
/// crashed run leaves nothing in the source tree.
def e2e_target_path : String := "target-monad/ply-e2e/edit.txt"

/// A second scratch file, for the `:` run -- the two gates must not share a
/// path, or a failure in one would look like a pass in the other.
def e2e_colon_target_path : String := "target-monad/ply-e2e/edit_colon.txt"

/// The text the fixture starts from: three lines, so the word delete has
/// something to remove and the remainder is more than a newline.
def e2e_before : String := "alpha\nbeta\ngamma\n"

/// What the fixture's `x d` leaves: line 0 gone, the rest intact. Derived
/// by hand from the command's rule (`x` selects line 0's content, `d`
/// deletes exactly that span) -- never by running it.
def e2e_after : String := "\nbeta\ngamma\n"

/// Write the starting file, read it back, and fail loudly if the fixture
/// could not be laid down -- a missing input would otherwise make the
/// "nothing changed" comparison pass for the wrong reason.
def e2e_prepare : IO (Result String String) := do {
    let _ <- exec_cmd "mkdir" ["-p", "target-monad/ply-e2e"];
    let r <- IO.write_file (Path.path e2e_target_path) e2e_before;
    match r {
        Result.err e => return (Result.err (String.concat "could not write the fixture: " e.message)),
        Result.ok _ => return (Result.ok e2e_target_path)
    }
}

/// The run: `sh -c '<bin> <file> < <keys>'`, so the keystrokes arrive on
/// stdin and EOF follows. `exec_cmd` inherits this process's stdio, so the
/// editor's terminal writes land in the test log (harmless -- nothing here
/// reads it; the FILE is the assertion).
pub def e2e_run (bin : String) (target : String) : IO I64 :=
    exec_cmd "sh" ["-c", String.concat_all [bin, " ", target, " < ", e2e_keys_path]]

/// The same run against a named keystroke fixture. A separate def rather
/// than a third parameter on `e2e_run`, so the original gate's signature (and
/// its log line) is untouched.
pub def e2e_run_keys (bin : String) (target : String) (keys : String) : IO I64 :=
    exec_cmd "sh" ["-c", String.concat_all [bin, " ", target, " < ", keys]]

/// Run the binary and compare the file. `e2e_*` helper defs each hold ONE
/// match or one do-block (never both): a do-block inside a match arm is a
/// recorded checker shape, and these steps are cheap to name.
def e2e_check (bin : String) : IO Bool := do {
    let prepared <- e2e_prepare;
    match prepared {
        Result.err why => e2e_prepare_failed why,
        Result.ok target => e2e_after_prepare bin target
    }
}

/// A fixture that could not be laid down would make "nothing changed" pass
/// for the wrong reason, so it is a loud failure.
def e2e_prepare_failed (why : String) : IO Bool := do {
    IO.println (String.concat "FAIL " why);
    return false
}

def e2e_after_prepare (bin : String) (target : String) : IO Bool := do {
    let rc <- e2e_run bin target;
    let back <- IO.read_file (Path.path target);
    let text_ok <- text_is back e2e_after;
    report_e2e rc text_ok
}

/// The verdict line: the exit code and the read-back, one Bool each.
def report_e2e (rc : I64) (text_ok : Bool) : IO Bool := do {
    let ok := I64.beq rc 0 && text_ok;
    IO.println (String.concat (if ok then "PASS " else "FAIL ")
        "ply e2e: edit and save through the built binary");
    return ok
}

/// The read-back comparison. A read failure is a miss, with the OS message
/// in the log rather than swallowed.
def text_is (r : Result StreamError String) (expected : String) : IO Bool :=
    match r {
        Result.ok text => IO.pure (String.beq text expected),
        Result.err e => read_back_failed e
    }

def read_back_failed (e : StreamError) : IO Bool := do {
    IO.println (String.concat "FAIL read-back: " e.message);
    return false
}

#[test]
def test_edit_save_e2e : IO Bool := do {
    let bin <- e2e_bin;
    if String.is_empty bin
    then do {
        IO.println "SKIP ply e2e: set PLY_E2E_BIN=$(monad build motes/ply --output ...) to run it";
        return true
    }
    else e2e_check bin
}

/// THE `:` GATE: a piped session types `:w` and the file really changes on
/// disk. This is the Phase 5 gate's end-to-end half -- the pure tests prove
/// the LINE reaches the `write` command, and this proves the whole path,
/// through the real terminal loop, actually writes.
///
/// The script is `x d` (delete line 0) then `: w Enter`, so the text on disk
/// is the deletion's AND the write's: a `:` line that typed but never ran
/// leaves the file untouched, and one that ran the wrong command leaves a
/// different text.
#[test]
def test_colon_write_e2e : IO Bool := do {
    let bin <- e2e_bin;
    if String.is_empty bin
    then do {
        IO.println "SKIP ply e2e (colon): set PLY_E2E_BIN to run it";
        return true
    }
    else e2e_colon_check bin
}

def e2e_colon_check (bin : String) : IO Bool := do {
    let prep <- e2e_colon_prepare;
    match prep {
        Result.err why => e2e_prepare_failed why,
        Result.ok target => e2e_colon_after bin target
    }
}

/// Lay down a SECOND fixture file (the `:` gate's own), so the two runs
/// never share a path.
def e2e_colon_prepare : IO (Result String String) := do {
    let _ <- exec_cmd "mkdir" ["-p", "target-monad/ply-e2e"];
    let r <- IO.write_file (Path.path e2e_colon_target_path) e2e_before;
    match r {
        Result.err e => return (Result.err (String.concat "could not write the fixture: " e.message)),
        Result.ok _ => return (Result.ok e2e_colon_target_path)
    }
}

def e2e_colon_after (bin : String) (target : String) : IO Bool := do {
    let rc <- e2e_run_keys bin target e2e_colon_keys_path;
    let back <- IO.read_file (Path.path target);
    let text_ok <- text_is back e2e_after;
    let ok := I64.beq rc 0 && text_ok;
    IO.println (String.concat (if ok then "PASS " else "FAIL ")
        "ply e2e: `:w` through the built binary");
    return ok
}
