// mty / weaver / bigplan -- a generated 2000-line plan paints promptly and is
// bottom-pinned, Home reaches its first line, `/plan` opens the review dialog,
// a 10 KB bracketed paste into the revise note completes, and Esc closes.
// Ported from pty_repro_bigplan.py (retired).
use mty::spawn {Mty, Output}
use mty::check {Check.report}
use weaver::mty_support {
    run_gated, with_root, spawn_args, send_paste, write_mode_config, count_occurrences
}
use weaver::mty_fixtures {
    write_text_script, plan_text, newest_session, session_dir, wait_store_text
}
use std::io {IO.println, IO.current_time_nano}

def tight_has (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def placeholder_seen (o : Output) : Bool :=
    grid_has o "type a message"

def ms_since (start : I64) : IO I64 := do {
    let now <- IO.current_time_nano;
    return ((now - start) / 1000000)
}

def timed_report (label : String) (start : I64) (ok : Bool) : IO Bool := do {
    let ms <- ms_since start;
    Check.report (String.concat label (String.concat " (" (String.concat (I64.to_string ms) " ms)"))) ok
}

def bigplan_go (m : Mty) (sessions : String) : IO Bool := do {
    let ready <- Mty.wait_until m placeholder_seen 8000;
    let t0 <- IO.current_time_nano;
    Mty.send_text m "go\n";
    // A clean plan-mode turn opens the review dialog by itself. Close it so
    // the transcript checks run against the panel; `/plan` reopens it below.
    let auto <- Mty.wait_until m (fn (o : Output) => tight_has o "Planready") 20000;
    let a0 <- timed_report "the plan dialog opens by itself" t0 auto;
    Mty.send_text m "\u{1b}";
    let _ <- Mty.wait_until m (fn (o : Output) => tight_has o "plannotapproved") 10000;
    // The GRID, not the stream: an unchanged screen sends no new bytes.
    let tail <- Mty.wait_until m (fn (o : Output) => grid_has o "PLAN-LINE-1999") 20000;
    let a <- timed_report "a large plan paints promptly" t0 tail;
    let id_opt <- newest_session sessions;
    let stored <- match id_opt {
        Option.none => IO.pure false,
        Option.some id => wait_store_text (session_dir sessions id) "PLAN-LINE-0000" 10000
    };
    let b <- Check.report "the plan is persisted before paging" stored;
    let t1 <- IO.current_time_nano;
    Mty.send_text m "\u{1b}[H";
    let first <- Mty.wait_until m (fn (o : Output) => grid_has o "PLAN-LINE-0000") 8000;
    let c <- timed_report "Home reaches the plan's first line" t1 first;
    Mty.send_text m "\u{1b}[F";
    let t2 <- IO.current_time_nano;
    Mty.send_text m "/plan\r";
    let ready_dialog <- Mty.wait_until m (fn (o : Output) => I64.lt 1 (count_occurrences (Output.tight o) "Planready")) 10000;
    let d <- timed_report "the plan dialog opens promptly" t2 ready_dialog;
    Mty.send_text m "e";
    let editing <- Mty.wait_until m (fn (o : Output) => grid_has o "note:") 3000;
    let t3 <- IO.current_time_nano;
    send_paste m (String.repeat "note-" 2048);
    let pasted <- Mty.wait_until m (fn (o : Output) => tight_has o "note-note-") 15000;
    let e <- timed_report "a large note paste completes" t3 pasted;
    Mty.send_text m "\u{1b}";
    // The second "plan not approved": the first was the auto dialog's.
    let closed <- Mty.wait_until m (fn (o : Output) => I64.lt 1 (count_occurrences (Output.tight o) "plannotapproved")) 8000;
    let f <- Check.report "Esc still closes the dialog after a paste" closed;
    Mty.finish m;
    return (Bool.and (Bool.and ready a0) (Bool.and a (Bool.and b (Bool.and c (Bool.and d (Bool.and editing (Bool.and e f)))))))
}

def bigplan_run (bin : String) (root : String) : IO Bool := do {
    write_mode_config root "plan";
    let turns := String.concat root "/turns_bigplan.json";
    let wrote <- write_text_script turns [plan_text 2000];
    if Bool.not wrote then do {
        IO.println "FAIL mty bigplan: could not write the turn script";
        return false
    } else do {
        let sessions := String.concat root "/sessions";
        let r <- spawn_args bin "mock" List.empty 24 80 root (Option.some turns) List.empty;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL mty bigplan spawn: " e); return false },
            Result.ok m => bigplan_go m sessions
        }
    }
}

#[test]
def test_bigplan_paint_home_dialog_paste : IO Bool :=
    run_gated "mty weaver bigplan" test_bigplan_body

def test_bigplan_body (bin : String) : IO Bool :=
    with_root "bigplan" (fn (root : String) => bigplan_run bin root)
