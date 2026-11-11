// Phase 4's save gate, at the pure boundary plus a real file: the update
// issues a `Cmd.perform`, the test runs that action exactly as `tui`'s
// loop does, folds the message it answers back in, and reads the file off
// disk. No terminal anywhere -- the loop's own behaviour (that the EOF
// path folds a final `perform`, so a piped `Space w` really writes) is the
// e2e fixture's job, not this file's.
//
// THE FILE IS REAL, under /tmp, the way `std/src/io_file_tests.mo` does
// it: a save that only ever touches a rope proves nothing about the
// write.
//
// SHAPE: each `#[test]` is a do-block whose last step calls a helper def,
// and every helper def's whole body is a `match` whose arms are do-blocks
// (`tui.mo`'s `step_cmd` shape). A do-block nested inside a do-block
// inside a match arm is the recorded checker trap (AGENTS.md's "let x <-
// inside a do-block inside a match arm"), so the arms never nest one.
//
// No record patterns inside `#[test]` defs: every read goes through an
// `sv_*` accessor, per the recorded two-host inference hazard this mote's
// Phase 1 tests learned.

use lib::model {Document, Document.of_text, Document.with_path, Document.dirty,
    EditorState, EditorState.init, EditorState.active_doc, EditorState.pending_of,
    EditorMsg}
use lib::commands {update}
use tui::types {Key}
use tui::tui {Cmd}
use std::list {List.length}
use std::process {exec_cmd, process_id}
use std::stream {StreamError}
use lib::instances {}

// ── Fixtures ─────────────────────────────────────────────────────────────

/// A /tmp path unique to this process, so concurrent test binaries (and a
/// rerun after a crash) never collide.
def sv_path (name : String) : String :=
    "/tmp/monad_ply_save_tests_" ++ I64.to_string process_id ++ "_" ++ name

def sv_write_file (path : String) (text : String) : IO (Result StreamError Unit) :=
    IO.write_file (Path.path path) text

def sv_read (path : String) : IO (Result StreamError String) :=
    IO.read_file (Path.path path)

/// The read-back comparison, in one place so every round-trip test pins
/// the same thing: the bytes on disk ARE the expected text. A path that
/// does not exist is a `Result.err`, which is not the expected text.
def sv_read_is (r : Result StreamError String) (expected : String) : Bool :=
    match r {
        Result.ok text => String.beq text expected,
        Result.err _ => false
    }

/// A state over the file at `path`, built the way `main.mo` opens one:
/// read the text, then attach the path.
def sv_open (path : String) : IO (Option EditorState) := do {
    let r <- sv_read path;
    let text_opt <- sv_text_or_none r;
    return (sv_state_of text_opt path)
}

/// The read's text, or `none` when it failed.
def sv_text_or_none (r : Result StreamError String) : IO (Option String) :=
    match r {
        Result.ok text => IO.pure (Option.some text),
        Result.err _ => IO.pure Option.none
    }

/// The opened state: a document over `text` with `path` attached.
def sv_state_of (text : Option String) (path : String) : Option EditorState :=
    match text {
        Option.none => Option.none,
        Option.some t =>
            let doc : Document := Document.with_path (Document.of_text t) path in
            let st : EditorState := EditorState.init doc 24 80 in
            Option.some st
    }

/// A SCRATCH state: `text` with no path at all, so `Space w` has nowhere
/// to write. `Document.of_text` leaves `path` as `Option.none` -- this is
/// the shape `main.mo` builds when it is run with no argument.
def sv_scratch (text : String) : EditorState :=
    EditorState.init (Document.of_text text) 24 80

/// A state over `text` whose path names a file that need not exist -- the
/// document a save is handed when the target directory is missing.
def sv_with_path (path : String) (text : String) : EditorState :=
    EditorState.init (Document.with_path (Document.of_text text) path) 24 80

// ── Driving the update ───────────────────────────────────────────────────

def sv_key (c : String) : Key := Key.char c

/// One key's message, bound with its type spelled out (`EditorMsg.key` in
/// argument position is not a "use" the Rust host's unused-import
/// analysis can see).
def sv_msg (k : Key) : EditorMsg := EditorMsg.key k

/// Fold a keystroke script through the update, KEEPING THE LAST command.
/// A chord's prefix keys answer `Cmd.none`, so the command key's own
/// answer is the script's -- which is all `sv_commit` needs.
#[terminating]
def sv_type_go (st : EditorState) (keys : List Key) (last : Cmd EditorMsg) : Pair EditorState (Cmd EditorMsg) :=
    match keys {
        List.empty => Pair.pair st last,
        List.cons k rest => sv_type_step st k rest
    }

#[terminating]
def sv_type_step (st : EditorState) (k : Key) (rest : List Key) : Pair EditorState (Cmd EditorMsg) :=
    match update st (sv_msg k) {
        Pair.pair st2 cmd => sv_type_go st2 rest cmd
    }

def sv_type (st : EditorState) (keys : List Key) : Pair EditorState (Cmd EditorMsg) :=
    sv_type_go st keys Cmd.none

/// The state after a script -- the command dropped, for the steps whose
/// command cannot be IO (a motion, an insert).
def sv_step (st : EditorState) (keys : List Key) : EditorState :=
    match sv_type st keys {
        Pair.pair after _ => after
    }

/// The state half of a script's answer.
def sv_pair_state (pair : Pair EditorState (Cmd EditorMsg)) : EditorState :=
    match pair {
        Pair.pair st _ => st
    }

/// The command half of a script's answer.
def sv_pair_cmd (pair : Pair EditorState (Cmd EditorMsg)) : Cmd EditorMsg :=
    match pair {
        Pair.pair _ cmd => cmd
    }

/// Run a command's IO -- if it has any -- and fold the message it answers
/// straight back into the state: the fold `tui`'s `step_cmd` performs.
def sv_commit (pair : Pair EditorState (Cmd EditorMsg)) : IO EditorState :=
    match pair {
        Pair.pair st cmd => sv_commit_cmd st cmd
    }

def sv_commit_cmd (st : EditorState) (cmd : Cmd EditorMsg) : IO EditorState :=
    match cmd {
        Cmd.perform action => sv_perform st action,
        _ => IO.pure st
    }

def sv_perform (st : EditorState) (action : Unit -> IO EditorMsg) : IO EditorState := do {
    let msg <- action unit;
    return (sv_fold_msg st msg)
}

def sv_fold_msg (st : EditorState) (msg : EditorMsg) : EditorState :=
    match update st msg {
        Pair.pair st2 _ => st2
    }

def sv_is_perform (cmd : Cmd EditorMsg) : Bool :=
    match cmd {
        Cmd.perform _ => true,
        _ => false
    }

def sv_is_quit (cmd : Cmd EditorMsg) : Bool :=
    match cmd {
        Cmd.quit => true,
        _ => false
    }

// ── State accessors, one read each ───────────────────────────────────────

def sv_status (st : EditorState) : String :=
    match st { { status, .. } => status }

def sv_dirty (st : EditorState) : Bool :=
    match EditorState.active_doc st {
        Option.some doc => Document.dirty doc,
        Option.none => false
    }

/// The pending chord's length (a matched command clears it).
def sv_pending_len (st : EditorState) : I64 :=
    List.length (EditorState.pending_of st)

// ── The gate: write ──────────────────────────────────────────────────────

/// `w d Space w`: select the first word ("alpha"), delete it, save. The
/// file on disk holds "beta\ngamma\n" and the buffer is no longer dirty:
/// both halves, because a save that wrote the file without marking it
/// saved (or the reverse) would pass either assertion alone.
///
/// THE EDIT IS A WORD DELETE, NOT A LINE ONE, on purpose: deleting line 0
/// leaves "beta\ngamma\n", whose first byte is the newline the delete
/// kept -- and a `Rope.to_string` over a buffer that STARTS with a
/// newline is the exact shape that produced a leading newline in the
/// first manual run. Saving text that starts with ordinary bytes is what
/// this test pins.
///
/// The edit is chosen so that BOTH the delete and the write have to have
/// happened: the deletion's text is on disk, and the saved flag is clear.
/// (Deleting into a NEWLINE instead would not distinguish "the write ran"
/// from "nothing was written" -- see the file header.)
#[test]
def test_space_w_writes_the_buffer : IO Bool := do {
    let path := sv_path "write";
    let _ <- sv_write_file path "alpha\nbeta\ngamma\n";
    let opened <- sv_open path;
    let ok <- sv_write_case path opened;
    let _ <- exec_cmd "rm" ["-f", path];
    return ok
}

def sv_write_case (path : String) (opened : Option EditorState) : IO Bool :=
    match opened {
        Option.none => IO.pure false,
        Option.some st => sv_write_at path st
    }

def sv_write_at (path : String) (st : EditorState) : IO Bool := do {
    let pair := sv_type st [sv_key "w", sv_key "d", sv_key " ", sv_key "w"];
    let saved <- sv_commit pair;
    let back <- sv_read path;
    let wrote := sv_is_perform (sv_pair_cmd pair);
    let clean := Bool.not (sv_dirty saved);
    let text := sv_read_is back "beta\ngamma\n";
    return (wrote && clean && text)
}

/// The buffer WAS dirty before the save, and the save is what cleared it:
/// the previous test's second assertion pinned from the other side, so a
/// document that never went dirty (a delete that silently did nothing)
/// cannot pass it.
#[test]
def test_edit_dirties_then_save_clears : IO Bool := do {
    let path := sv_path "dirty";
    let _ <- sv_write_file path "alpha\nbeta\ngamma\n";
    let opened <- sv_open path;
    let ok <- sv_dirty_cycle opened;
    let _ <- exec_cmd "rm" ["-f", path];
    return ok
}

def sv_dirty_cycle (opened : Option EditorState) : IO Bool :=
    match opened {
        Option.none => IO.pure false,
        Option.some st => sv_dirty_cycle_at st
    }

def sv_dirty_cycle_at (st : EditorState) : IO Bool := do {
    let before := sv_dirty st;
    let edited := sv_step st [sv_key "x", sv_key "d"];
    let dirty_now := sv_dirty edited;
    let saved <- sv_commit (sv_type edited [sv_key " ", sv_key "w"]);
    return (Bool.not before && dirty_now && Bool.not (sv_dirty saved))
}

/// A save REPORTS the path it wrote and clears the chord's pending prefix
/// -- the status line is the only place the user learns a save happened,
/// so it is asserted rather than assumed.
#[test]
def test_save_reports_the_path : IO Bool := do {
    let path := sv_path "report";
    let _ <- sv_write_file path "x\n";
    let opened <- sv_open path;
    let ok <- sv_report_case opened;
    let _ <- exec_cmd "rm" ["-f", path];
    return ok
}

def sv_report_case (opened : Option EditorState) : IO Bool :=
    match opened {
        Option.none => IO.pure false,
        Option.some st => sv_report_at st
    }

def sv_report_at (st : EditorState) : IO Bool := do {
    let pair := sv_type st [sv_key " ", sv_key "w"];
    let cleared := I64.beq (sv_pending_len (sv_pair_state pair)) 0;
    let saved <- sv_commit pair;
    return (cleared && String.starts_with "wrote " (sv_status saved))
}

/// A scratch buffer has no path, so `Space w` refuses in the PURE half:
/// no command is issued and the status line says why.
#[test]
def test_write_refuses_without_a_path : Bool :=
    match sv_type (sv_scratch "x") [sv_key " ", sv_key "w"] {
        Pair.pair refused cmd =>
            Bool.not (sv_is_perform cmd)
                && String.beq (sv_status refused) "no path to write"
    }

// ── The gate: quit ───────────────────────────────────────────────────────

/// `Space q` on a clean buffer quits.
#[test]
def test_quit_when_clean_quits : Bool :=
    match sv_type (sv_scratch "x") [sv_key " ", sv_key "q"] {
        Pair.pair _ cmd => sv_is_quit cmd
    }

/// `Space q` with unsaved changes REFUSES: no quit, and the status names
/// the way out. The insert is what makes the buffer dirty.
#[test]
def test_quit_refuses_when_dirty : Bool :=
    let after := sv_step (sv_scratch "x") [sv_key "i", sv_key "y", Key.escape] in
    match sv_type after [sv_key " ", sv_key "q"] {
        Pair.pair refused cmd =>
            Bool.not (sv_is_quit cmd)
                && String.beq (sv_status refused) "unsaved changes; Space Q quits without saving"
    }

/// `Space Q` quits anyway -- the discard.
#[test]
def test_quit_bang_discards : Bool :=
    let after := sv_step (sv_scratch "x") [sv_key "i", sv_key "y", Key.escape] in
    match sv_type after [sv_key " ", sv_key "Q"] {
        Pair.pair _ cmd => sv_is_quit cmd
    }

/// The pair that makes the refusal a dirty-buffer rule rather than a
/// never-quit bug: a buffer whose changes were SAVED is clean, so plain
/// `q` quits -- and the saved text is on disk.
#[test]
def test_quit_after_a_save_quits : IO Bool := do {
    let path := sv_path "saved_quit";
    let _ <- sv_write_file path "x\n";
    let opened <- sv_open path;
    let ok <- sv_saved_quit_case path opened;
    let _ <- exec_cmd "rm" ["-f", path];
    return ok
}

def sv_saved_quit_case (path : String) (opened : Option EditorState) : IO Bool :=
    match opened {
        Option.none => IO.pure false,
        Option.some st => sv_saved_quit_at path st
    }

def sv_saved_quit_at (path : String) (st : EditorState) : IO Bool := do {
    let edited := sv_step st [sv_key "i", sv_key "y", Key.escape];
    let saved <- sv_commit (sv_type edited [sv_key " ", sv_key "w"]);
    let quit_pair := sv_type saved [sv_key " ", sv_key "q"];
    let back <- sv_read path;
    return (sv_is_quit (sv_pair_cmd quit_pair) && sv_read_is back "yx\n")
}

/// A FAILED write reports the OS message and leaves the buffer dirty, so
/// `q` still refuses and no text is lost to a save that did not happen.
/// The path's parent directory does not exist, which is the honest way to
/// make one write fail without touching permissions.
#[test]
def test_failed_write_keeps_the_buffer_dirty : IO Bool :=
    sv_failed_write (sv_with_path (sv_path "no_such_dir/child") "alpha")

def sv_failed_write (st : EditorState) : IO Bool := do {
    let edited := sv_step st [sv_key "i", sv_key "y", Key.escape];
    let after <- sv_commit (sv_type edited [sv_key " ", sv_key "w"]);
    let quit_pair := sv_type after [sv_key " ", sv_key "q"];
    return (sv_dirty after
        && Bool.not (sv_is_quit (sv_pair_cmd quit_pair))
        && String.starts_with "write failed" (sv_status after))
}
