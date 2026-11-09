// weaver / pty / plans -- a plan-mode turn's plan lands in the plan repo, and
// a FRESH weaver run (not --resume) finds it with /plans, shows it, and loads
// it into the new session.
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use weaver::pty_support {run_gated, with_root, spawn_args, write_mode_config}
use weaver::pty_fixtures {write_text_script, newest_session, session_dir, store_user_texts}
use std::io {IO.println, IO.current_time}
use std::process {Proc.capture}
use std::list {List.any}
use std::concurrent::combine {sleepIO}

def tight_has (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def placeholder_seen (o : Output) : Bool :=
    grid_has o "type a message"

def plan_body : String := "# Stored plan check\n\nPLAN-STEP-ONE: carry this across sessions"

/// The plan file is on disk once a grep under the plan repo finds it.
#[partial]
def wait_plan_file (plans : String) (deadline : I64) : IO Bool := do {
    let r <- Proc.capture "grep" ["-rl", "PLAN-STEP-ONE", plans];
    let found : Bool := match r { Pair.pair code _ => code == 0 };
    if found then IO.pure true
    else do {
        let now <- IO.current_time;
        if I64.gt now deadline then IO.pure false
        else do { sleepIO 50; wait_plan_file plans deadline }
    }
}

def capture_go (m : Pty) (root : String) : IO Bool := do {
    let ready <- Pty.wait_until m placeholder_seen 8000;
    Pty.send_text m "go\n";
    let auto <- Pty.wait_until m (fn (o : Output) => tight_has o "Planready") 20000;
    Pty.send_text m "\u{1b}";
    let _ <- Pty.wait_until m (fn (o : Output) => tight_has o "plannotapproved") 10000;
    let start <- IO.current_time;
    let stored <- wait_plan_file (String.concat root "/plans") (start + 10000);
    Pty.finish m;
    let a <- Check.report "a plan-mode turn's plan lands in the plan repo" (ready && auto && stored);
    return a
}

def load_go (m : Pty) (root : String) : IO Bool := do {
    let ready <- Pty.wait_until m placeholder_seen 8000;
    Pty.send_text m "/plans\r";
    let listed <- Pty.wait_until m (fn (o : Output) => tight_has o "Storedplancheck") 10000;
    let a <- Check.report "a fresh run lists the stored plan" (ready && listed);
    Pty.send_text m "\r";
    let shown <- Pty.wait_until m (fn (o : Output) => grid_has o "PLAN-STEP-ONE") 10000;
    let b <- Check.report "opening it shows the plan" shown;
    Pty.send_text m "l";
    let loaded <- Pty.wait_until m (fn (o : Output) => tight_has o "loadedplan") 10000;
    let c <- Check.report "loading it says so" loaded;
    let sessions : String := String.concat root "/sessions";
    let id <- newest_session sessions;
    let texts <- user_texts_of sessions id;
    let d <- Check.report "the plan reaches the new session's history"
        (List.any (fn (t : String) => String.contains t "Stored plan (") texts);
    Pty.finish m;
    return (a && b && c && d)
}

def user_texts_of (sessions : String) (id : Option String) : IO (List String) :=
    match id {
        Option.none => IO.pure List.empty,
        Option.some i => store_user_texts (session_dir sessions i)
    }

def plans_run (bin : String) (root : String) : IO Bool := do {
    write_mode_config root "plan";
    let turns := String.concat root "/turns_plans.json";
    let wrote <- write_text_script turns [plan_body, "noted"];
    if Bool.not wrote then do {
        IO.println "FAIL pty plans: could not write the turn script";
        return false
    } else do {
        let first <- spawn_args bin "mock" List.empty 24 80 root (Option.some turns) List.empty;
        match first {
            Result.err e => do { IO.println (String.concat "FAIL pty plans spawn: " e); return false },
            Result.ok m => plans_second bin root turns m
        }
    }
}

def plans_second (bin : String) (root : String) (turns : String) (m : Pty) : IO Bool := do {
    let a <- capture_go m root;
    write_mode_config root "manual";
    let second <- spawn_args bin "mock" List.empty 24 80 root (Option.some turns) List.empty;
    match second {
        Result.err e => do { IO.println (String.concat "FAIL pty plans respawn: " e); return false },
        Result.ok m2 => do {
            let b <- load_go m2 root;
            return (a && b)
        }
    }
}

pub def run_plans_survive_a_fresh_run : IO Bool :=
    run_gated "pty weaver plans" test_plans_body

def test_plans_body (bin : String) : IO Bool :=
    with_root "plans" (fn (root : String) => plans_run bin root)
