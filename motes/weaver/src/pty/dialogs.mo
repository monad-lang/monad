// weaver / pty / dialogs -- the permission dialog (deny with a note, arrow
// selection + Enter), the plan-review revise path, and typed values in the
// settings dialog, and a dialog that must survive a long stay open. Ported
// from pty_repro_dialogs.py (retired).
//
// The edit fixture is GENERATED in the run root: the checked-in
// turns_edit.json has no `new_content`, so the Python driver wrote its own.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {
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

def spawn_dialogs (bin : String) (root : String) (fixture : String) : IO (Result String Pty) :=
    spawn bin "mock" 24 80 root (Option.some fixture) List.empty

// ── 1. Deny with a note ────────────────────────────────────────────────────

def deny_go (m : Pty) (root : String) : IO Bool := do {
    let note := note_of root;
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "go\n";
    let dlg <- Pty.wait_until m (fn (o : Output) =>
        visible o "Permission required") 6000;
    let o1 <- Pty.output m;
    let a <- Check.report "permission dialog appears with its options"
        (dlg && visible o1 "Approve once" && visible o1 "Deny");
    let b <- Check.report "the dialog names the file it will write"
        (String.contains (Output.stripped o1) note);
    Pty.send_text m "e";
    Pty.pump m 150;
    Pty.send_text m "please keep it";
    Pty.pump m 150;
    Pty.send_text m "\r";
    Pty.pump m 150;
    Pty.send_text m "n";
    let denied <- Pty.wait_until m (fn (o : Output) =>
        visible o "denied: please keep it") 6000;
    let c <- Check.report "a denied pick carries the note to the model" denied;
    let file <- read_text note;
    let d <- Check.report "the denied edit did not run" (file == "hi");
    let wrote <- Pty.wait_until m (fn (o : Output) =>
        visible o "wrote it") 6000;
    let e <- Check.report "the turn continues after a denial" wrote;
    let o2 <- Pty.output m;
    let gone <- Check.report "the dialog is gone after the denial"
        (Bool.and (not_found o2 "Permission required") (not_found o2 "Approve once"));
    Pty.finish m;
    return (up && a && b && c && d && e && gone)
}

def deny_run (bin : String) (root : String) : IO Bool := do {
    let _ <- write_text (note_of root) "hi";
    let fixture <- edit_fixture root;
    let r <- spawn_dialogs bin root fixture;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty dialogs spawn: " e); return false },
        Result.ok m => deny_go m root
    }
}

// ── 2. Arrow selection approves ───────────────────────────────────────────

def approve_go (m : Pty) (root : String) : IO Bool := do {
    let note := note_of root;
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "go\n";
    let dlg <- Pty.wait_until m (fn (o : Output) =>
        visible o "Permission required") 6000;
    Pty.send_text m "\u{1b}[A";
    Pty.pump m 150;
    Pty.send_text m "\u{1b}[A";
    Pty.pump m 150;
    Pty.send_text m "\r";
    let wrote <- Pty.wait_until m (fn (o : Output) =>
        visible o "wrote it") 6000;
    let file <- read_text note;
    let a <- Check.report "arrow selection + Enter approves the edit"
        (wrote && file == "hello world");
    let o <- Pty.output m;
    let gone <- Check.report "the dialog is gone after the approval"
        (Bool.and (not_found o "Permission required") (not_found o "Approve once"));
    Pty.finish m;
    return (up && dlg && a && gone)
}

def approve_run (bin : String) (root : String) : IO Bool := do {
    let _ <- write_text (note_of root) "hi";
    let fixture <- edit_fixture root;
    let r <- spawn_dialogs bin root fixture;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty dialogs spawn: " e); return false },
        Result.ok m => approve_go m root
    }
}

// ── 3. Plan review: revise fills the input box ────────────────────────────

def plan_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "go\n";
    // A clean plan-mode turn opens the review dialog by itself now; no /plan.
    let ready <- Pty.wait_until m (fn (o : Output) =>
        visible o "Plan ready") 12000;
    let o1 <- Pty.output m;
    let plan_seen := visible o1 "PLAN: do the thing";
    let a <- Check.report "the plan dialog shows the plan"
        (ready && plan_seen && visible o1 "Approve and execute");
    Pty.send_text m "e";
    Pty.pump m 150;
    Pty.send_text m "fix the tests too";
    Pty.pump m 150;
    Pty.send_text m "\r";
    Pty.pump m 150;
    Pty.send_text m "r";
    let revised <- Pty.wait_until m (fn (o : Output) =>
        Bool.and (not_found o "Plan ready")
            (found_at_row o "fix the tests too" 21)) 5000;
    let o2 <- Pty.output m;
    let b <- Check.report "revise with a note fills the input box"
        (visible o2 "fix the tests too");
    let c <- Check.report "the plan dialog is gone after revise" (not_found o2 "Plan ready");
    let d <- Check.report "the note sits on the input row"
        (found_at_row o2 "fix the tests too" 21);
    Pty.send_text m "!";
    let responsive <- Pty.wait_until m (fn (o : Output) =>
        found_at_row o "fix the tests too!" 21) 3000;
    let e <- Check.report "the app is responsive after revise" (revised && responsive);
    Pty.finish m;
    return (up && plan_seen && a && b && c && d && e)
}

def plan_run (bin : String) (root : String) : IO Bool := do {
    let _ <- write_plan_config root;
    let fixture <- plan_fixture root;
    let r <- spawn_dialogs bin root fixture;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty dialogs spawn: " e); return false },
        Result.ok m => plan_go m
    }
}

// ── 4. Settings: typed values, and the dialog stays open ─────────────────

def clear_screen_seq : String := "\u{1b}[2J"

def settings_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "/settings\r";
    let dlg <- Pty.wait_until m (fn (o : Output) => visible o "Output budget") 6000;
    Pty.send_text m "\u{1b}[B";
    Pty.pump m 150;
    Pty.send_text m "\u{1b}[B";
    Pty.pump m 150;
    Pty.send_text m "\r";
    Pty.pump m 150;
    Pty.send_text m "\u{15}5000";
    Pty.pump m 150;
    Pty.send_text m "\r";
    let applied <- Pty.wait_until m (fn (o : Output) =>
        visible o "max_tokens: 5000") 6000;
    let o1 <- Pty.output m;
    let a <- Check.report "a typed value applies and the dialog stays open"
        (dlg && applied && visible o1 "Output budget: 5000" && visible o1 "Save to project");
    Pty.send_text m "\r";
    Pty.pump m 150;
    Pty.send_text m "\u{15}abc";
    Pty.pump m 150;
    Pty.send_text m "\r";
    let rejected <- Pty.wait_until m (fn (o : Output) =>
        visible o "max_tokens must be a number") 6000;
    let o2 <- Pty.output m;
    let b <- Check.report "a rejected value shows its error in the dialog"
        (rejected && visible o2 "Output budget: 5000");
    let mark : I64 := String.length o2.raw;
    Pty.send_text m "\u{1b}[B";
    Pty.pump m 150;
    Pty.send_text m "\u{1b}[<65;10;10M";
    Pty.pump m 150;
    Pty.send_text m "\u{1b}[A";
    Pty.pump m 300;
    let o3 <- Pty.output m;
    let c <- Check.report "moving and scrolling repaint without clearing the screen"
        (Bool.not (String.contains (Output.since o3 mark) clear_screen_seq));
    Pty.send_text m "\u{1b}";
    let closed <- Pty.wait_until m (fn (o : Output) => not_found o "Save to project") 6000;
    let d <- Check.report "Esc closes the settings dialog" closed;
    Pty.finish m;
    return (up && a && b && c && d)
}

def settings_run (bin : String) (root : String) : IO Bool := do {
    let fixture <- plan_fixture root;
    let r <- spawn_dialogs bin root fixture;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty dialogs spawn: " e); return false },
        Result.ok m => settings_go m
    }
}

// ── 5. A dialog open for long keeps its stack flat ───────────────────────

// The modal loop once recursed through IO binds, one native frame chain
// per poll or byte, and a permission dialog left open overnight died with
// SIGSEGV on its fiber's stack. Under a 2 MiB stack the recursive loop
// overflowed inside this burst; the single-self-call loop, compiled to a
// back-edge, keeps answering.
def dialog_keys : I64 := 3000

#[partial]
def dialog_burst (m : Pty) (sent : I64) (down : Bool) : IO I64 := do {
    let o <- Pty.output m;
    if Bool.or o.eof (Bool.not (sent < dialog_keys)) then IO.pure sent
    else do {
        Pty.send_text m (if down then "j" else "k");
        Pty.pump m 4;
        dialog_burst m (sent + 1) (Bool.not down)
    }
}

def soak_dialog_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "/settings\r";
    let dlg <- Pty.wait_until m (fn (o : Output) => visible o "Output budget") 6000;
    let sent <- dialog_burst m 0 true;
    Pty.pump m 300;
    let o1 <- Pty.output m;
    IO.println (String.concat "INFO keys sent: " (I64.to_string sent));
    let a <- Check.report "3000 keys in an open dialog without a segfault (stack 2 MiB)"
        (dlg && sent == dialog_keys && Bool.not o1.eof);
    Pty.send_text m "\u{1b}";
    let closed <- Pty.wait_until m (fn (o : Output) => not_found o "Save to project") 6000;
    let b <- Check.report "Esc still closes the dialog after the burst" closed;
    Pty.finish m;
    return (up && a && b)
}

def soak_dialog_run (bin : String) (root : String) : IO Bool := do {
    let fixture <- plan_fixture root;
    let env : List (Pair String (Option String)) := [Pair.pair "MONAD_STACK_BYTES" (Option.some "2097152")];
    let r <- spawn bin "mock" 24 80 root (Option.some fixture) env;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty dialogs spawn: " e); return false },
        Result.ok m => soak_dialog_go m
    }
}

pub def run_dialog_deny_with_note : IO Bool :=
    run_gated "pty weaver dialogs" test_dialog_deny_body

def test_dialog_deny_body (bin : String) : IO Bool :=
    with_root "dialogs_deny" (fn (root : String) => deny_run bin root)

pub def run_dialog_arrow_approves : IO Bool :=
    run_gated "pty weaver dialogs" test_dialog_approve_body

def test_dialog_approve_body (bin : String) : IO Bool :=
    with_root "dialogs_approve" (fn (root : String) => approve_run bin root)

pub def run_dialog_plan_revise : IO Bool :=
    run_gated "pty weaver dialogs" test_dialog_plan_body

def test_dialog_plan_body (bin : String) : IO Bool :=
    with_root "dialogs_plan" (fn (root : String) => plan_run bin root)

pub def run_dialog_settings_edit : IO Bool :=
    run_gated "pty weaver dialogs" test_dialog_settings_body

def test_dialog_settings_body (bin : String) : IO Bool :=
    with_root "dialogs_settings" (fn (root : String) => settings_run bin root)

pub def run_dialog_open_long_keeps_the_stack_flat : IO Bool :=
    run_gated "pty weaver dialogs" test_dialog_soak_body

def test_dialog_soak_body (bin : String) : IO Bool :=
    with_root "dialogs_soak" (fn (root : String) => soak_dialog_run bin root)
