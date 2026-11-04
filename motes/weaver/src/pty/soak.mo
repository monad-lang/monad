// weaver / pty / soak -- a long run must not grow the native stack. Every
// frame of the tui loop is a do-bind chain; the IO do-bind fusion compiles
// it direct-style, so the self-recursive frame loop is a tco back-edge and
// a 2 MiB stack stays enough for the 3000-key burst (one step per key).
// Before the fusion `monad_io_bind` called each continuation inside its own
// C frame and a recursive frame loop died with SIGSEGV in a long session --
// the reason the temporary `IO.iterate` native existed; see
// plans/bootstrapping/heapless-loops.md.
// Ported from pty_repro_soak.py (retired).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, fixture_path, spawn, rss_kb}
use std::io {IO.println}

def soak_keys : I64 := 3000

def saw_alt (o : Output) : Bool := Output.contains o "\u{1b}[?1049h"

/// One key per frame, paced so the reader does not coalesce them into one
/// batch: the point is the NUMBER of loop iterations. Stops early at EOF
/// (the child died).
#[partial]
def burst (m : Pty) (sent : I64) : IO I64 := do {
    let o <- Pty.output m;
    if Bool.or o.eof (Bool.not (sent < soak_keys)) then IO.pure sent
    else do {
        Pty.send_text m "x";
        Pty.pump m 4;
        burst m (sent + 1)
    }
}

def soak_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 8000;
    let a <- Check.report "the initial frame renders" up;
    let sent <- burst m 0;
    let o1 <- Pty.output m;
    let b <- Check.report "3000 frames without a segfault (stack 2 MiB)"
        (Bool.and (sent == soak_keys) (Bool.not o1.eof));
    // Ctrl+U clears the long input: one more frame, still answered.
    Pty.send_text m "\u{15}";
    Pty.pump m 300;
    let o2 <- Pty.output m;
    let c <- Check.report "answers a key after the burst" (Bool.not o2.eof);
    let rss <- rss_kb (Pty.child_pid m);
    IO.println (String.concat "INFO VmRSS after the burst: " (String.concat (I64.to_string rss) " kB"));
    Pty.send_text m "\u{3}";
    Pty.pump m 400;
    Pty.send_text m "\u{3}";
    let restored <- Pty.wait_until m (fn (o : Output) => Output.contains o "\u{1b}[?1049l") 3000;
    let d <- Check.report "the double Ctrl+C exits through the restore path" restored;
    let _ <- Pty.wait_until m (fn (o : Output) => o.eof) 6000;
    let reaped <- Pty.reap m;
    let e <- Check.report "the process exited" (I64.gt reaped 0);
    Pty.finish m;
    return (a && b && c && d && e)
}

def soak_run (bin : String) (root : String) : IO Bool := do {
    let turns <- fixture_path "turns_select.json";
    let env : List (Pair String (Option String)) :=
        List.cons (Pair.pair "MONAD_STACK_BYTES" (Option.some "2097152"))
        (List.cons (Pair.pair "WEAVER_LOG_DIR" (Option.some (String.concat root "/debug"))) List.empty);
    let r <- spawn bin "mock" 24 80 root (Option.some turns) env;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty soak spawn: " e); return false },
        Result.ok m => soak_go m
    }
}

pub def run_soak_long_run_keeps_the_stack_flat : IO Bool :=
    run_gated "pty weaver soak" test_soak_body

def test_soak_body (bin : String) : IO Bool :=
    with_root "soak" (fn (root : String) => soak_run bin root)

// A pending turn redraws the spinner ten times a second. Before the IO
// do-bind fusion every redraw's bind frame stayed alive (and the model and
// screen each pointed at): ~1 MB per redraw, 600 MB a minute at 50x200. The
// plain recursive frame loop must hold RSS flat while the turn waits.
def pending_bound_kb : I64 := 20000

def pending_go (m : Pty) : IO Bool := do {
    let up <- Pty.wait_until m saw_alt 8000;
    let a <- Check.report "the initial frame renders" up;
    Pty.send_text m "hello\r";
    Pty.pump m 3000;
    let before <- rss_kb (Pty.child_pid m);
    Pty.pump m 20000;
    let after <- rss_kb (Pty.child_pid m);
    IO.println (String.concat "INFO VmRSS over 20 s of a pending turn: " (String.concat (I64.to_string before)
        (String.concat " -> " (String.concat (I64.to_string after) " kB"))));
    let b <- Check.report "RSS stays flat while a turn is pending" (I64.lt (after - before) pending_bound_kb);
    Pty.send_text m "\u{3}";
    Pty.pump m 400;
    Pty.send_text m "\u{3}";
    let _ <- Pty.wait_until m (fn (o : Output) => o.eof) 6000;
    let _ <- Pty.reap m;
    Pty.finish m;
    return (a && b)
}

def pending_run (bin : String) (root : String) : IO Bool := do {
    let turns <- fixture_path "turns_slow.json";
    let env : List (Pair String (Option String)) :=
        [Pair.pair "SHUTTLE_MOCK_DELAY_MS" (Option.some "60000"),
            Pair.pair "WEAVER_LOG_DIR" (Option.some (String.concat root "/debug"))];
    let r <- spawn bin "mock" 50 200 root (Option.some turns) env;
    match r {
        Result.err e => do { IO.println (String.concat "FAIL pty pending spawn: " e); return false },
        Result.ok m => pending_go m
    }
}

pub def run_soak_pending_turn_keeps_rss_flat : IO Bool :=
    run_gated "pty weaver pending-turn rss" (fn (bin : String) => with_root "pending" (fn (root : String) => pending_run bin root))
