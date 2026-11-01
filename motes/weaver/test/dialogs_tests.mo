// mty / weaver / dialogs -- the permission dialog (deny with a note, arrow
// selection + Enter), and the plan-review revise path. Ported from
// pty_repro_dialogs.py (retired).
//
// The edit fixture is GENERATED in the run root: the checked-in
// turns_edit.json has no `new_content`, so the Python driver wrote its own.
use mty::spawn {Mty, Output}
use mty::check {Check.report}
use weaver::mty_support {
    run_gated, with_root, spawn, not_found, found_at_row
}
use std::io {IO.println}
use std::test {Test.write_fixture, Test.read_fixture_or}
use std::path {Path}
use std::process {exec_cmd}

def saw_alt (o : Output) : Bool := Output.contains o "\u{1b}[?1049h"

/// A phrase visible on the rendered grid. The cell diff omits a space that
/// was already blank, so a spaced phrase is not contiguous in the raw stream.
def visible (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

// ── Generated fixtures ────────────────────────────────────────────────────

def edit_head : String := r#"[{"message": {"role": "assistant", "content": [{"type": "tool_use", "id": "c1", "name": "edit", "input": {"path": ""#

def edit_tail : String := r#"", "new_content": "hello world", "expected_content": "hi"}}]}, "usage": {"input_tokens": 1, "output_tokens": 10, "cached_tokens": 0}, "stop": "tool_use_stop"}, {"message": {"role": "assistant", "content": [{"type": "text", "text": "wrote it"}]}, "usage": {"input_tokens": 2, "output_tokens": 10, "cached_tokens": 0}, "stop": "end_turn"}]"#

def plan_json : String := r#"[{"message": {"role": "assistant", "content": [{"type": "text", "text": "PLAN: do the thing"}]}, "usage": {"input_tokens": 1, "output_tokens": 10, "cached_tokens": 0}, "stop": "end_turn"}]"#

def plan_config : String := String.concat (r#"mode = "plan""#) "\n"

def write_text (path : String) (text : String) : IO Unit := do {
    let _ <- Test.write_fixture (Path.path path) text;
    return unit
}

def read_text (path : String) : IO String :=
    Test.read_fixture_or (Path.path path) ""

def note_of (root : String) : String := String.concat root "/note.txt"

def edit_fixture (root : String) : IO String := do {
    let path := String.concat root "/turns_edit.json";
    let _ <- write_text path (String.concat edit_head (String.concat (note_of root) edit_tail));
    return path
}

def plan_fixture (root : String) : IO String := do {
    let path := String.concat root "/turns_plan.json";
    let _ <- write_text path plan_json;
    return path
}

def write_plan_config (root : String) : IO Unit := do {
    let dir := String.concat root "/.weaver";
    let _ <- exec_cmd "mkdir" (List.cons "-p" (List.cons dir List.empty));
    write_text (String.concat dir "/config.toml") plan_config
}

def spawn_dialogs (bin : String) (root : String) (fixture : String) : IO (Result String Mty) :=
    spawn bin "mock" 24 80 root (Option.some fixture) List.empty

// ── 1. Deny with a note ────────────────────────────────────────────────────

def deny_go (m : Mty) (root : String) : IO Bool := do {
    let note := note_of root;
    let up <- Mty.wait_until m saw_alt 6000;
    Mty.send_text m "go\n";
    let dlg <- Mty.wait_until m (fn (o : Output) =>
        visible o "Permission required") 6000;
    let o1 <- Mty.output m;
    let a <- Check.report "permission dialog appears with its options"
        (dlg && visible o1 "Approve once" && visible o1 "Deny");
    let b <- Check.report "the dialog names the file it will write"
        (String.contains (Output.stripped o1) note);
    Mty.send_text m "e";
    Mty.pump m 150;
    Mty.send_text m "please keep it";
    Mty.pump m 150;
    Mty.send_text m "\r";
    Mty.pump m 150;
    Mty.send_text m "n";
    let denied <- Mty.wait_until m (fn (o : Output) =>
        visible o "denied: please keep it") 6000;
    let c <- Check.report "a denied pick carries the note to the model" denied;
    let file <- read_text note;
    let d <- Check.report "the denied edit did not run" (file == "hi");
    let wrote <- Mty.wait_until m (fn (o : Output) =>
        visible o "wrote it") 6000;
    let e <- Check.report "the turn continues after a denial" wrote;
    let o2 <- Mty.output m;
    let gone <- Check.report "the dialog is gone after the denial"
        (Bool.and (not_found o2 "Permission required") (not_found o2 "Approve once"));
    Mty.finish m;
    return (up && a && b && c && d && e && gone)
}

def deny_run (bin : String) (root : String) : IO Bool := do {
    let _ <- write_text (note_of root) "hi";
    let fixture <- edit_fixture root;
    let r <- spawn_dialogs bin root fixture;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL mty dialogs spawn: " e); return false },
        Result.ok m => deny_go m root
    }
}

// ── 2. Arrow selection approves ───────────────────────────────────────────

def approve_go (m : Mty) (root : String) : IO Bool := do {
    let note := note_of root;
    let up <- Mty.wait_until m saw_alt 6000;
    Mty.send_text m "go\n";
    let dlg <- Mty.wait_until m (fn (o : Output) =>
        visible o "Permission required") 6000;
    Mty.send_text m "\u{1b}[A";
    Mty.pump m 150;
    Mty.send_text m "\u{1b}[A";
    Mty.pump m 150;
    Mty.send_text m "\r";
    let wrote <- Mty.wait_until m (fn (o : Output) =>
        visible o "wrote it") 6000;
    let file <- read_text note;
    let a <- Check.report "arrow selection + Enter approves the edit"
        (wrote && file == "hello world");
    let o <- Mty.output m;
    let gone <- Check.report "the dialog is gone after the approval"
        (Bool.and (not_found o "Permission required") (not_found o "Approve once"));
    Mty.finish m;
    return (up && dlg && a && gone)
}

def approve_run (bin : String) (root : String) : IO Bool := do {
    let _ <- write_text (note_of root) "hi";
    let fixture <- edit_fixture root;
    let r <- spawn_dialogs bin root fixture;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL mty dialogs spawn: " e); return false },
        Result.ok m => approve_go m root
    }
}

// ── 3. Plan review: revise fills the input box ────────────────────────────

def plan_go (m : Mty) : IO Bool := do {
    let up <- Mty.wait_until m saw_alt 6000;
    Mty.send_text m "go\n";
    // A clean plan-mode turn opens the review dialog by itself now; no /plan.
    let ready <- Mty.wait_until m (fn (o : Output) =>
        visible o "Plan ready") 12000;
    let o1 <- Mty.output m;
    let plan_seen := visible o1 "PLAN: do the thing";
    let a <- Check.report "the plan dialog shows the plan"
        (ready && plan_seen && visible o1 "Approve and execute");
    Mty.send_text m "e";
    Mty.pump m 150;
    Mty.send_text m "fix the tests too";
    Mty.pump m 150;
    Mty.send_text m "\r";
    Mty.pump m 150;
    Mty.send_text m "r";
    let revised <- Mty.wait_until m (fn (o : Output) =>
        Bool.and (not_found o "Plan ready")
            (found_at_row o "fix the tests too" 21)) 5000;
    let o2 <- Mty.output m;
    let b <- Check.report "revise with a note fills the input box"
        (visible o2 "fix the tests too");
    let c <- Check.report "the plan dialog is gone after revise" (not_found o2 "Plan ready");
    let d <- Check.report "the note sits on the input row"
        (found_at_row o2 "fix the tests too" 21);
    Mty.send_text m "!";
    let responsive <- Mty.wait_until m (fn (o : Output) =>
        found_at_row o "fix the tests too!" 21) 3000;
    let e <- Check.report "the app is responsive after revise" (revised && responsive);
    Mty.finish m;
    return (up && plan_seen && a && b && c && d && e)
}

def plan_run (bin : String) (root : String) : IO Bool := do {
    let _ <- write_plan_config root;
    let fixture <- plan_fixture root;
    let r <- spawn_dialogs bin root fixture;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL mty dialogs spawn: " e); return false },
        Result.ok m => plan_go m
    }
}

#[test]
def test_dialog_deny_with_note : IO Bool :=
    run_gated "mty weaver dialogs" test_dialog_deny_body

def test_dialog_deny_body (bin : String) : IO Bool :=
    with_root "dialogs_deny" (fn (root : String) => deny_run bin root)

#[test]
def test_dialog_arrow_approves : IO Bool :=
    run_gated "mty weaver dialogs" test_dialog_approve_body

def test_dialog_approve_body (bin : String) : IO Bool :=
    with_root "dialogs_approve" (fn (root : String) => approve_run bin root)

#[test]
def test_dialog_plan_revise : IO Bool :=
    run_gated "mty weaver dialogs" test_dialog_plan_body

def test_dialog_plan_body (bin : String) : IO Bool :=
    with_root "dialogs_plan" (fn (root : String) => plan_run bin root)
