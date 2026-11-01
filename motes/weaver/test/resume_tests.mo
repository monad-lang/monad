// mty / weaver / resume -- the `/resume` picker lists the current session with
// its marker and descriptions, Esc leaves the app responsive, choosing a row
// restores that transcript, and ten sessions page with Older/Newer rows.
// Ported from pty_repro_resume.py (retired).
use mty::spawn {Mty, Output}
use mty::check {Check.report}
use weaver::mty_support {run_gated, with_root, spawn_args}
use weaver::mty_fixtures {LineSpec, write_generated_session, pad2}
use std::io {IO.println}

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
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

def open_picker (m : Mty) : IO Bool := do {
    Mty.send_text m "/resume";
    Mty.send_text m "\r";
    Mty.wait_until m (fn (o : Output) => grid_has o "Resume a session") 4000
}

def picker_checks (m : Mty) : IO Bool := do {
    let ready <- Mty.wait_until m placeholder_seen 6000;
    let opened <- open_picker m;
    let a <- Check.report "the picker dialog opens" opened;
    let beta <- Mty.wait_until m (fn (o : Output) => grid_has o "Beta work") 3000;
    let b <- Check.report "the current session is listed" (Bool.and ready beta);
    let marked <- Mty.wait_until m (fn (o : Output) => grid_has o "(current)") 3000;
    let c <- Check.report "the current session is marked" marked;
    let alpha <- Mty.wait_until m (fn (o : Output) => grid_has o "Alpha work") 3000;
    let d <- Check.report "another session is listed" alpha;
    let descs <- Mty.wait_until m (fn (o : Output) =>
        Bool.and (grid_has o "the first task") (grid_has o "the second task")) 3000;
    let e <- Check.report "descriptions are shown" descs;
    Mty.send_text m "\u{1b}";
    let closed <- Mty.wait_until m (fn (o : Output) => grid_lacks o "Resume a session") 3000;
    let f <- Check.report "the dialog is gone after Esc" closed;
    Mty.send_text m "!";
    let responsive <- Mty.wait_until m (fn (o : Output) => row_has o 21 "!") 3000;
    let g <- Check.report "the app is responsive after Esc" responsive;
    Mty.finish m;
    return (Bool.and a (Bool.and b (Bool.and c (Bool.and d (Bool.and e (Bool.and f g))))))
}

def choose_checks (m : Mty) : IO Bool := do {
    let ready <- Mty.wait_until m placeholder_seen 6000;
    let opened <- open_picker m;
    let a <- Check.report "the picker dialog opens" opened;
    Mty.send_text m "\u{1b}[B";
    let moved <- Mty.wait_until m (fn (o : Output) => grid_has o "> Alpha work") 3000;
    let b <- Check.report "ArrowDown selects the other session" moved;
    Mty.send_text m "\r";
    let loaded <- Mty.wait_until m (fn (o : Output) => grid_has o "ALPHA-TRANSCRIPT") 6000;
    let c <- Check.report "the chosen session's transcript is restored" loaded;
    let closed <- Mty.wait_until m (fn (o : Output) => grid_lacks o "Resume a session") 3000;
    let d <- Check.report "the picker closed after choosing" closed;
    Mty.finish m;
    return (Bool.and ready (Bool.and a (Bool.and b (Bool.and c d))))
}

def pager_checks (m : Mty) : IO Bool := do {
    let ready <- Mty.wait_until m placeholder_seen 6000;
    let opened <- open_picker m;
    let a <- Check.report "the picker dialog opens" opened;
    let p1 <- Mty.wait_until m (fn (o : Output) => grid_has o "session 02") 4000;
    let b <- Check.report "the first page shows the newest sessions" p1;
    let o1 <- Mty.output m;
    let c <- Check.report "the first page hides the oldest sessions"
        (Bool.and (grid_lacks o1 "session 00") (grid_lacks o1 "session 01"));
    let d <- Check.report "the first page offers an older page" (grid_has o1 "Older sessions");
    Mty.send_text m (String.repeat "\u{1b}[B" 8);
    let on_older <- Mty.wait_until m (fn (o : Output) => grid_has o "> Older sessions") 4000;
    let e <- Check.report "the selection reaches Older sessions" on_older;
    Mty.send_text m "\r";
    let p2 <- Mty.wait_until m (fn (o : Output) =>
        Bool.and (grid_has o "session 00") (grid_has o "session 01")) 4000;
    let f <- Check.report "the older page shows the oldest sessions" p2;
    let o2 <- Mty.output m;
    let g <- Check.report "the older page offers a newer page" (grid_has o2 "Newer sessions");
    let h <- Check.report "the older page hides the newest sessions" (grid_lacks o2 "session 02");
    Mty.send_text m "\u{1b}";
    let closed <- Mty.wait_until m (fn (o : Output) => grid_lacks o "Resume a session") 3000;
    let i <- Check.report "the paged dialog closes" closed;
    Mty.finish m;
    return (Bool.and ready (Bool.and a (Bool.and b (Bool.and c (Bool.and d (Bool.and e (Bool.and f (Bool.and g (Bool.and h i)))))))))
}

def spawn_resume (bin : String) (root : String) (id : String) : IO (Result String Mty) :=
    spawn_args bin "mock" (resume_args id) 24 80 root Option.none List.empty

def resume_picker_run (bin : String) (root : String) : IO Bool := do {
    let ok <- synth_pair root;
    if Bool.not ok then do {
        IO.println "FAIL mty resume: could not synthesize the sessions";
        return false
    } else do {
        let r <- spawn_resume bin root "s-beta";
        match r {
            Result.err e => do { IO.println (String.concat "FAIL mty resume spawn: " e); return false },
            Result.ok m => picker_checks m
        }
    }
}

def resume_choose_run (bin : String) (root : String) : IO Bool := do {
    let ok <- synth_pair root;
    if Bool.not ok then do {
        IO.println "FAIL mty resume: could not synthesize the sessions";
        return false
    } else do {
        let r <- spawn_resume bin root "s-beta";
        match r {
            Result.err e => do { IO.println (String.concat "FAIL mty resume spawn: " e); return false },
            Result.ok m => choose_checks m
        }
    }
}

def resume_pager_run (bin : String) (root : String) : IO Bool := do {
    let ok <- synth_ten root;
    if Bool.not ok then do {
        IO.println "FAIL mty resume: could not synthesize the sessions";
        return false
    } else do {
        let r <- spawn_resume bin root "s-09";
        match r {
            Result.err e => do { IO.println (String.concat "FAIL mty resume spawn: " e); return false },
            Result.ok m => pager_checks m
        }
    }
}

#[test]
def test_resume_picker_lists_current_and_esc : IO Bool :=
    run_gated "mty weaver resume picker" test_resume_picker_body

def test_resume_picker_body (bin : String) : IO Bool :=
    with_root "resume_picker" (fn (root : String) => resume_picker_run bin root)

#[test]
def test_resume_choose_loads_transcript : IO Bool :=
    run_gated "mty weaver resume choose" test_resume_choose_body

def test_resume_choose_body (bin : String) : IO Bool :=
    with_root "resume_choose" (fn (root : String) => resume_choose_run bin root)

#[test]
def test_resume_pager : IO Bool :=
    run_gated "mty weaver resume pager" test_resume_pager_body

def test_resume_pager_body (bin : String) : IO Bool :=
    with_root "resume_pager" (fn (root : String) => resume_pager_run bin root)
