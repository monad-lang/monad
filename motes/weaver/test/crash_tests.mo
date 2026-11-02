// mty / weaver / crash -- a SIGKILLed run leaves no exit marker; the next run
// warns about the previous crash and logs crash_detected; a clean /quit writes
// the exit marker. Ported from pty_repro_crash.py (retired).
use mty::spawn {Mty, Output}
use mty::check {Check.report}
use weaver::mty_support {
    run_gated, with_root, fixture_path, spawn_args, wait_file_contains, read_text
}
use std::io {IO.println}

def has_stripped (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def crash_go (bin : String) (root : String) (turns : String) : IO Bool := do {
    let log_dir := String.concat root "/logs";
    let run1 := String.concat log_dir "/run1.log";
    let run2 := String.concat log_dir "/run2.log";
    let env1 : List (Pair String (Option String)) :=
        List.cons (Pair.pair "WEAVER_LOG_DIR" (Option.some log_dir))
        (List.cons (Pair.pair "WEAVER_DEBUG_LOG" (Option.some run1)) List.empty);
    let r1 <- spawn_args bin "mock" List.empty 24 80 root (Option.some turns) env1;
    match r1 {
        Result.err e => do { IO.println (String.concat "FAIL mty crash spawn 1: " e); return false },
        Result.ok m1 => do {
            let started <- wait_file_contains run1 "ev=process_start" 6000;
            let a <- Check.report "the first run starts and logs" started;
            Mty.terminate m1;
            let _ <- Mty.reap m1;
            Mty.close m1;
            let text1 <- read_text run1;
            let b <- Check.report "the killed run has no exit marker"
                (Bool.not (String.contains text1 "ev=process_exit"));
            let env2 : List (Pair String (Option String)) :=
                List.cons (Pair.pair "WEAVER_LOG_DIR" (Option.some log_dir))
                (List.cons (Pair.pair "WEAVER_DEBUG_LOG" (Option.some run2)) List.empty);
            let r2 <- spawn_args bin "mock" List.empty 24 80 root (Option.some turns) env2;
            match r2 {
                Result.err e => do { IO.println (String.concat "FAIL mty crash spawn 2: " e); return false },
                Result.ok m2 => do {
                    let warned <- Mty.wait_until m2
                        (fn (o : Output) => has_stripped o "previoussessionendedunexpectedly") 6000;
                    let c <- Check.report "the restart warns about the previous crash" warned;
                    let logged <- wait_file_contains run2 "ev=crash_detected" 6000;
                    let d <- Check.report "the restart logs crash_detected" logged;
                    Mty.send_text m2 "/quit\r";
                    let exited <- wait_file_contains run2 "ev=process_exit" 6000;
                    let e <- Check.report "a clean exit writes process_exit" exited;
                    Mty.finish m2;
                    return (Bool.and a (Bool.and b (Bool.and c (Bool.and d e))))
                }
            }
        }
    }
}

def crash_run (bin : String) (root : String) : IO Bool := do {
    let turns <- fixture_path "turns_select.json";
    crash_go bin root turns
}

#[test]
def test_crash_detect_and_clean_exit : IO Bool :=
    run_gated "mty weaver crash" test_crash_body

def test_crash_body (bin : String) : IO Bool :=
    with_root "crash" (fn (root : String) => crash_run bin root)
