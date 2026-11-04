// weaver / pty / async -- the live-turn behaviors: redraws mid-turn, the
// thinking row, mid-turn keys, the completion repaint, no re-emission, one
// mid-turn Ctrl-C only hints, two quit promptly, Esc stops the turn, and the
// approval overlay owns stdin. Ported from
// pty_repro_async.py (retired).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use pty::ansi {Ansi.tight}
use weaver::pty_support {
    run_gated, with_root, fixture_path, spawn, count_occurrences, quit_cleanly
}
use std::io {IO.println}

def saw_alt (o : Output) : Bool := Output.contains o "\u{1b}[?1049h"

def tight_has (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def delay_env : List (Pair String (Option String)) :=
    [Pair.pair "SHUTTLE_MOCK_DELAY_MS" (Option.some "2500")]

def spawn_async (bin : String) (root : String) (fixture : String) : IO (Result String Pty) := do {
    let turns <- fixture_path fixture;
    spawn bin "mock" 20 80 root (Option.some turns) delay_env
}

def thinking_visible (o : Output) : Bool :=
    Bool.and (tight_has o "thinking") (Bool.and (tight_has o "↑") (tight_has o "↓"))

// ── 1. Redraws, live row, mid-turn keys, completion, no re-emission ──────

def s1_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "hello\n";
    let thinking <- Pty.wait_until m thinking_visible 5000;
    let a <- Check.report "S1 live thinking row visible mid-turn" thinking;
    let o1 <- Pty.output m;
    let mark1 := String.length o1.raw;
    Pty.pump m 600;
    let o2 <- Pty.output m;
    let redraw := String.contains (Output.since o2 mark1) "\u{1b}[";
    let b <- Check.report "S1 UI redraws while a turn runs" redraw;
    Pty.send_text m "queued";
    let queued <- Pty.wait_until m (fn (o : Output) => tight_has o "queued") 3000;
    let c <- Check.report "S2 mid-turn keys land in the input box" queued;
    let o3 <- Pty.output m;
    let mark2 := String.length o3.raw;
    let reply <- Pty.wait_until m (fn (o : Output) => tight_has o "replyslow:the") 8000;
    Pty.pump m 300;
    let o4 <- Pty.output m;
    let burst := I64.gt (String.length (Output.since o4 mark2)) 3000;
    let d <- Check.report "S2 assistant text lands in transcript" reply;
    let e <- Check.report "S3 completion forced a blank repaint" burst;
    let mark3 := String.length o4.raw;
    let _ <- Pty.wait_quiet m 500 1500;
    let o5 <- Pty.output m;
    let since := Ansi.tight (Output.since o5 mark3);
    let f <- Check.report "S3 no re-emission after the completion"
        (Bool.and (I64.beq (count_occurrences since "replyslow") 0)
            (Bool.and (I64.beq (count_occurrences since "thinking") 0)
                (I64.beq (count_occurrences since "[thinking]") 0)));
    let restored <- quit_cleanly m 3000;
    let g <- Check.report "S3 double Ctrl+C still exits cleanly" restored;
    Pty.finish m;
    return (up && a && b && c && d && e && f && g)
}

def s1_run (bin : String) (root : String) : IO Bool := do {
    let r <- spawn_async bin root "turns_slow.json";
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty async spawn: " e); return false },
        Result.ok m => s1_go m
    }
}

// ── 2. One mid-turn Ctrl-C only hints ─────────────────────────────────────

def s2_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "hi\n";
    let thinking <- Pty.wait_until m thinking_visible 5000;
    Pty.send_text m "\u{3}";
    let reply <- Pty.wait_until m (fn (o : Output) => tight_has o "replyslow:the") 8000;
    let a <- Check.report "S4 mid-turn Ctrl-C does not interrupt the turn" (thinking && reply);
    let restored <- quit_cleanly m 3000;
    let b <- Check.report "S4 clean exit after the turn" restored;
    Pty.finish m;
    return (up && a && b)
}

def s2_run (bin : String) (root : String) : IO Bool := do {
    let r <- spawn_async bin root "turns_slow.json";
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty async spawn: " e); return false },
        Result.ok m => s2_go m
    }
}

// ── 3. Two mid-turn Ctrl-C presses quit promptly ──────────────────────────

def s3_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "hi\n";
    let thinking <- Pty.wait_until m thinking_visible 5000;
    Pty.send_text m "\u{3}";
    Pty.pump m 150;
    Pty.send_text m "\u{3}";
    let restored <- Pty.wait_until m (fn (o : Output) => Output.contains o "\u{1b}[?1049l") 2000;
    let o <- Pty.output m;
    let preempted := Bool.not (tight_has o "replyslow:the");
    let a <- Check.report "S4 double mid-turn Ctrl-C restores the terminal" restored;
    let b <- Check.report "S4 the quit preempted the slow turn" preempted;
    Pty.finish m;
    return (up && thinking && a && b)
}

def s3_run (bin : String) (root : String) : IO Bool := do {
    let r <- spawn_async bin root "turns_slow.json";
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty async spawn: " e); return false },
        Result.ok m => s3_go m
    }
}

// ── 4. Esc stops the running turn ─────────────────────────────────────────

def s4_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "hi\n";
    let thinking <- Pty.wait_until m thinking_visible 5000;
    Pty.send_text m "\u{1b}";
    let stopping <- Pty.wait_until m (fn (o : Output) => grid_has o "stopping") 3000;
    let a <- Check.report "S6 Esc shows the stopping row" stopping;
    let stopped <- Pty.wait_until m (fn (o : Output) => tight_has o "[stopped]") 8000;
    let b <- Check.report "S6 the stopped turn ends with [stopped]" stopped;
    let o <- Pty.output m;
    let c <- Check.report "S6 stop still persists the streamed reply"
        (tight_has o "replyslow:the");
    let restored <- quit_cleanly m 3000;
    let d <- Check.report "S6 clean exit after the stop" restored;
    Pty.finish m;
    return (up && thinking && a && b && c && d)
}

def s4_run (bin : String) (root : String) : IO Bool := do {
    let r <- spawn_async bin root "turns_slow.json";
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty async spawn: " e); return false },
        Result.ok m => s4_go m
    }
}

// ── 5. The overlay stays stdin's first reader ─────────────────────────────

def s5_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 6000;
    Pty.send_text m "xxx";
    Pty.send_text m "hello\n";
    let first <- Pty.wait_until m (fn (o : Output) => tight_has o "Permissionrequired") 8000;
    Pty.send_text m "y";
    let second <- Pty.wait_until m (fn (o : Output) =>
        I64.gt (count_occurrences (Output.tight o) "Permissionrequired") 1) 8000;
    let a <- Check.report "S5 the overlay consumed the y (the second prompt appears)" second;
    Pty.send_text m "y";
    let _ <- Pty.wait_quiet m 500 3000;
    let restored <- quit_cleanly m 3000;
    let b <- Check.report "S5 clean exit after both prompts" restored;
    Pty.finish m;
    return (up && first && a && b)
}

def s5_run (bin : String) (root : String) : IO Bool := do {
    let r <- spawn_async bin root "turns_two_reads.json";
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty async spawn: " e); return false },
        Result.ok m => s5_go m
    }
}

// ── Entries ───────────────────────────────────────────────────────────────

pub def run_async_live_turn_and_completion : IO Bool :=
    run_gated "pty weaver async" test_async_s1_body

def test_async_s1_body (bin : String) : IO Bool :=
    with_root "async_live" (fn (root : String) => s1_run bin root)

pub def run_async_one_ctrl_c_mid_turn : IO Bool :=
    run_gated "pty weaver async" test_async_s2_body

def test_async_s2_body (bin : String) : IO Bool :=
    with_root "async_one_c" (fn (root : String) => s2_run bin root)

pub def run_async_double_ctrl_c_mid_turn : IO Bool :=
    run_gated "pty weaver async" test_async_s3_body

def test_async_s3_body (bin : String) : IO Bool :=
    with_root "async_two_c" (fn (root : String) => s3_run bin root)

pub def run_async_esc_stops_turn : IO Bool :=
    run_gated "pty weaver async" test_async_s4_body

def test_async_s4_body (bin : String) : IO Bool :=
    with_root "async_stop" (fn (root : String) => s4_run bin root)

pub def run_async_overlay_owns_stdin : IO Bool :=
    run_gated "pty weaver async" test_async_s5_body

def test_async_s5_body (bin : String) : IO Bool :=
    with_root "async_overlay" (fn (root : String) => s5_run bin root)
