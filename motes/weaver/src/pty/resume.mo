// weaver / pty / resume -- the `/resume` picker lists the current session with
// its marker and descriptions, Esc leaves the app responsive, choosing a row
// restores that transcript, and ten sessions page with Older/Newer rows.
// Ported from pty_repro_resume.py (retired).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {
    run_gated, with_root, spawn_args, report_screen, found_at_row, pos_row, quit_cleanly,
}
use weaver::pty_fixtures {
    LineSpec, write_generated_session, pad2, write_history_session, history_len,
    history_first_text, session_dir,
}
use std::io {IO.println}
use std::path {Path}

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

/// A SELECTED option row: the `> ` marker sits on the row the label is
/// drawn on (`> 2. Alpha work`). Dialogs number their options and the
/// number moves with the page, so match the marker and the label, never
/// the whole rendered row.
def selected_row_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.none => false,
        Option.some p => row_has o (pos_row p) "> ",
    }

def grid_lacks (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.none => true,
        Option.some _ => false
    }

def row_has (o : Output) (r : I64) (needle : String) : Bool :=
    String.contains (Output.row_text o r) needle

def placeholder_seen (o : Output) : Bool :=
    grid_has o "type a message"

def synth (root : String) (id : String) (name : String) (description : String)
    (updated : I64) (marker : String) : IO Bool :=
    write_generated_session (String.concat root "/sessions") id
        (Option.some name) (Option.some description) updated 1
        (LineSpec.fixed marker)

def synth_pair (root : String) : IO Bool := do {
    let a <- synth root "s-alpha" "Alpha work" "the first task" 1000 "ALPHA-TRANSCRIPT";
    let b <- synth root "s-beta" "Beta work" "the second task" 2000 "BETA-TRANSCRIPT";
    return (Bool.and a b)
}

#[partial]
def synth_ten_go (root : String) (i : I64) (acc : Bool) : IO Bool := do {
    if Bool.not (I64.lt i 10) then IO.pure acc
    else do {
        let n := pad2 i;
        let ok <- synth root (String.concat "s-" n) (String.concat "session " n)
            (String.concat "desc " n) (100 + i * 10) (String.concat "MARK-" n);
        synth_ten_go root (i + 1) (Bool.and acc ok)
    }
}

def synth_ten (root : String) : IO Bool :=
    synth_ten_go root 0 true

def resume_args (id : String) : List String :=
    List.cons "--resume" (List.cons id List.empty)

def open_picker (m : Pty) : IO Bool := do {
    Pty.send_text m "/resume";
    Pty.send_text m "\r";
    Pty.wait_until m (fn (o : Output) => grid_has o "Resume a session") 4000
}

def picker_checks (m : Pty) : IO Bool := do {
    let ready <- Pty.wait_until m placeholder_seen 6000;
    let opened <- open_picker m;
    let a <- Check.report "the picker dialog opens" opened;
    let beta <- Pty.wait_until m (fn (o : Output) => grid_has o "Beta work") 3000;
    let b <- Check.report "the current session is listed" (Bool.and ready beta);
    let marked <- Pty.wait_until m (fn (o : Output) => grid_has o "(current)") 3000;
    let c <- Check.report "the current session is marked" marked;
    let alpha <- Pty.wait_until m (fn (o : Output) => grid_has o "Alpha work") 3000;
    let d <- Check.report "another session is listed" alpha;
    let descs <- Pty.wait_until m (fn (o : Output) =>
        Bool.and (grid_has o "the first task") (grid_has o "the second task")) 3000;
    let e <- Check.report "descriptions are shown" descs;
    Pty.send_text m "\u{1b}";
    let closed <- Pty.wait_until m (fn (o : Output) => grid_lacks o "Resume a session") 3000;
    let f <- Check.report "the dialog is gone after Esc" closed;
    Pty.send_text m "!";
    let responsive <- Pty.wait_until m (fn (o : Output) => row_has o 21 "!") 3000;
    let g <- Check.report "the app is responsive after Esc" responsive;
    Pty.finish m;
    return (Bool.and a (Bool.and b (Bool.and c (Bool.and d (Bool.and e (Bool.and f g))))))
}

def choose_checks (m : Pty) : IO Bool := do {
    let ready <- Pty.wait_until m placeholder_seen 6000;
    let opened <- open_picker m;
    let a <- Check.report "the picker dialog opens" opened;
    Pty.send_text m "\u{1b}[B";
    let moved <- Pty.wait_until m (fn (o : Output) => selected_row_has o "Alpha work") 3000;
    let b <- Check.report "ArrowDown selects the other session" moved;
    Pty.send_text m "\r";
    let loaded <- Pty.wait_until m (fn (o : Output) => grid_has o "ALPHA-TRANSCRIPT") 6000;
    let c <- Check.report "the chosen session's transcript is restored" loaded;
    let closed <- Pty.wait_until m (fn (o : Output) => grid_lacks o "Resume a session") 3000;
    let d <- report_screen m "the picker closed after choosing" closed;
    Pty.finish m;
    return (Bool.and ready (Bool.and a (Bool.and b (Bool.and c d))))
}

def pager_checks (m : Pty) : IO Bool := do {
    let ready <- Pty.wait_until m placeholder_seen 6000;
    let opened <- open_picker m;
    let a <- Check.report "the picker dialog opens" opened;
    let p1 <- Pty.wait_until m (fn (o : Output) => grid_has o "session 02") 4000;
    let b <- Check.report "the first page shows the newest sessions" p1;
    let o1 <- Pty.output m;
    let c <- Check.report "the first page hides the oldest sessions"
        (Bool.and (grid_lacks o1 "session 00") (grid_lacks o1 "session 01"));
    let d <- Check.report "the first page offers an older page" (grid_has o1 "Older sessions");
    Pty.send_text m (String.repeat "\u{1b}[B" 8);
    let on_older <- Pty.wait_until m (fn (o : Output) => selected_row_has o "Older sessions") 4000;
    let e <- Check.report "the selection reaches Older sessions" on_older;
    Pty.send_text m "\r";
    let p2 <- Pty.wait_until m (fn (o : Output) =>
        Bool.and (grid_has o "session 00") (grid_has o "session 01")) 4000;
    let f <- Check.report "the older page shows the oldest sessions" p2;
    let o2 <- Pty.output m;
    let g <- Check.report "the older page offers a newer page" (grid_has o2 "Newer sessions");
    let h <- Check.report "the older page hides the newest sessions" (grid_lacks o2 "session 02");
    Pty.send_text m "\u{1b}";
    let closed <- Pty.wait_until m (fn (o : Output) => grid_lacks o "Resume a session") 3000;
    let i <- Check.report "the paged dialog closes" closed;
    Pty.finish m;
    return (Bool.and ready (Bool.and a (Bool.and b (Bool.and c (Bool.and d (Bool.and e (Bool.and f (Bool.and g (Bool.and h i)))))))))
}

def spawn_resume (bin : String) (root : String) (id : String) : IO (Result String Pty) :=
    spawn_args bin "mock" (resume_args id) 24 80 root Option.none List.empty

def resume_picker_run (bin : String) (root : String) : IO Bool := do {
    let ok <- synth_pair root;
    if Bool.not ok then do {
        IO.println "FAIL pty resume: could not synthesize the sessions";
        return false
    } else do {
        let r <- spawn_resume bin root "s-beta";
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty resume spawn: " e); return false },
            Result.ok m => picker_checks m
        }
    }
}

def resume_choose_run (bin : String) (root : String) : IO Bool := do {
    let ok <- synth_pair root;
    if Bool.not ok then do {
        IO.println "FAIL pty resume: could not synthesize the sessions";
        return false
    } else do {
        let r <- spawn_resume bin root "s-beta";
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty resume spawn: " e); return false },
            Result.ok m => choose_checks m
        }
    }
}

def resume_pager_run (bin : String) (root : String) : IO Bool := do {
    let ok <- synth_ten root;
    if Bool.not ok then do {
        IO.println "FAIL pty resume: could not synthesize the sessions";
        return false
    } else do {
        let r <- spawn_resume bin root "s-09";
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty resume spawn: " e); return false },
            Result.ok m => pager_checks m
        }
    }
}

pub def run_resume_picker_lists_current_and_esc : IO Bool :=
    run_gated "pty weaver resume picker" test_resume_picker_body

def test_resume_picker_body (bin : String) : IO Bool :=
    with_root "resume_picker" (fn (root : String) => resume_picker_run bin root)

pub def run_resume_choose_loads_transcript : IO Bool :=
    run_gated "pty weaver resume choose" test_resume_choose_body

def test_resume_choose_body (bin : String) : IO Bool :=
    with_root "resume_choose" (fn (root : String) => resume_choose_run bin root)

pub def run_resume_pager : IO Bool :=
    run_gated "pty weaver resume pager" test_resume_pager_body

def test_resume_pager_body (bin : String) : IO Bool :=
    with_root "resume_pager" (fn (root : String) => resume_pager_run bin root)

// ── the session name at the top ────────────────────────────────────────

def name_checks (m : Pty) : IO Bool := do {
    let ready <- Pty.wait_until m placeholder_seen 6000;
    Pty.send_text m "/name pty-check\r";
    let shown <- Pty.wait_until m (fn (o : Output) => found_at_row o "pty-check" 0) 4000;
    let a <- report_screen m "/name puts the name in the frame's top edge" (Bool.and ready shown);
    Pty.finish m;
    return a
}

def name_run (bin : String) (root : String) : IO Bool := do {
    let r <- spawn_args bin "mock" List.empty 24 80 root Option.none List.empty;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty name spawn: " e); return false },
        Result.ok m => name_checks m
    }
}

pub def run_name_shows_in_the_frame : IO Bool :=
    run_gated "pty weaver session name" (fn (bin : String) =>
        with_root "name" (fn (root : String) => name_run bin root))

// ── the resume-time fold (Phase 16b, A2) ───────────────────────────────
//
// A session whose MODEL HISTORY is large must land FOLDED: the first
// resumed turn pays one system digest, not every block `history_base` ..
// `history_next` (`Store.load_history_seq` concatenates them all). The
// digest is committed through `Store.record_compacted`, so the loaded
// history shrinks AND the base moves; the startup note names it.
//
// The transcript is 3 lines but the history is 60 messages of ~4 KB each
// (~240 KB, ~60k estimated tokens), far past the default tail budget for a
// 128k window (~20k), so the fold fires deterministically.

def fold_env : List (Pair String (Option String)) :=
    [Pair.pair "SHUTTLE_MOCK_TURNS" (Option.none)]

def fold_session_count (root : String) : IO I64 :=
    history_len (session_dir (String.concat root "/sessions") "s-long")

def fold_first_text (root : String) : IO String :=
    history_first_text (session_dir (String.concat root "/sessions") "s-long")

def fold_go (m : Pty) (root : String) : IO Bool := do {
    let ready <- Pty.wait_until m placeholder_seen 6000;
    let a <- Check.report "the app is up on the resumed session" ready;
    // The fold note names the digest and the history directory.
    let noted <- Pty.wait_until m (fn (o : Output) => grid_has o "context folded") 6000;
    let b <- report_screen m "the startup note names the folded digest" noted;
    let dir_ok <- Pty.wait_until m (fn (o : Output) => grid_has o "/history") 6000;
    let c <- Check.report "the note names the history directory" dir_ok;
    // The loaded history is bounded: strictly fewer messages than the 60
    // written, and the head is the SYSTEM digest the fold built.
    let n <- fold_session_count root;
    let bounded := Bool.and (I64.gt n 0) (I64.lt n 60);
    let d <- Check.report "the resumed history is folded down" bounded;
    let head <- fold_first_text root;
    let e <- Check.report "the head of the folded history is the digest"
        (String.contains head "folded at resume");
    let _ <- quit_cleanly m 3000;
    Pty.finish m;
    return (Bool.and a (Bool.and b (Bool.and c (Bool.and d e))))
}

def fold_run (bin : String) (root : String) : IO Bool := do {
    let ok <- write_history_session (String.concat root "/sessions") "s-long" 6 10 4000;
    if Bool.not ok then do {
        IO.println "FAIL pty resume: could not synthesize the long-history session";
        return false
    } else do {
        let r <- spawn_resume bin root "s-long";
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty resume fold spawn: " e); return false },
            Result.ok m => fold_go m root
        }
    }
}

pub def run_resume_folds_the_history : IO Bool :=
    run_gated "pty weaver resume fold" test_resume_fold_body

def test_resume_fold_body (bin : String) : IO Bool :=
    with_root "resume_fold" (fn (root : String) => fold_run bin root)
