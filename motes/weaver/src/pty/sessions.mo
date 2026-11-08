// weaver / pty / sessions -- persistence and resume: a turn is written to the
// session store, `--resume` restores it, Home pages older lines from disk, a
// bracketed paste is one user block, `--no-color` emits no palette codes, and
// an 18 MB session stays on disk (startup RSS bounded, idle flat).
// Ported from pty_repro_sessions.py (retired).
use pty::spawn {Pty, Output}
use pty::check {Check.report}
use pty::ansi {Ansi.has_color}
use weaver::pty_support {
    run_gated, with_root, spawn_args, status_turns, send_paste, quit_cleanly,
    rss_kb, count_occurrences
}
use weaver::pty_fixtures {
    LineSpec, write_text_script, write_generated_session, session_dir,
    newest_session, newest_new, session_ids, store_lines, store_user_texts,
    store_has_text, wait_store_text, history_block_exists
}
use weaver::store {TLine}
use std::io {IO.println}
use std::path {Path, Path.to_string}
use std::list {List.any, List.length}

def tight_has (o : Output) (needle : String) : Bool :=
    String.contains (Output.tight o) needle

def grid_has (o : Output) (needle : String) : Bool :=
    match Output.find o needle {
        Option.some _ => true,
        Option.none => false
    }

def placeholder_seen (o : Output) : Bool :=
    grid_has o "type a message"

def user_line (l : TLine) (text : String) : Bool :=
    Bool.and l.user (l.text == text)

#[partial]
def has_user_line (ls : List TLine) (text : String) : Bool :=
    match ls {
        List.empty => false,
        List.cons l rest => Bool.or (user_line l text) (has_user_line rest text)
    }

#[partial]
def user_lines (ls : List TLine) (acc : List String) : List String :=
    match ls {
        List.empty => List.reverse acc,
        List.cons l rest =>
            if l.user
            then user_lines rest (List.cons l.text acc)
            else user_lines rest acc
    }

def reply_one (o : Output) : Bool :=
    Bool.and (grid_has o "persisted-reply") (status_turns o 1)

def sessions_spawn (bin : String) (root : String) (extra : List String)
    (fixture : Option String) : IO (Result String Pty) :=
    spawn_args bin "mock" extra 24 100 root fixture List.empty

def persist_checks (m : Pty) (sessions : String) (before : List String) : IO Bool := do {
    let ready <- Pty.wait_until m placeholder_seen 6000;
    Pty.send_text m "hi\r";
    let replied <- Pty.wait_until m reply_one 10000;
    let a <- Check.report "the reply renders and the turn completes"
        (Bool.and ready replied);
    let id_opt <- newest_new sessions before;
    match id_opt {
        Option.none => do {
            let b <- Check.report "a new session directory appears" false;
            Pty.finish m;
            return (Bool.and a b)
        },
        Option.some id => do {
            let dir := session_dir sessions id;
            let stored <- wait_store_text dir "persisted-reply" 5000;
            let _ <- quit_cleanly m 4000;
            Pty.finish m;
            let lines <- store_lines dir;
            let users <- store_user_texts dir;
            let hist <- history_block_exists dir 1;
            let b <- Check.report "the turn is persisted to the session store" stored;
            let assistant <- store_has_text dir "persisted-reply";
            let c <- Check.report "the transcript has the assistant reply" assistant;
            let d <- Check.report "the transcript has the user line" (has_user_line lines "hi");
            let e <- Check.report "the history holds the user message"
                (List.any (fn (s : String) => s == "hi") users);
            let f <- Check.report "the history block file exists" hist;
            return (Bool.and a (Bool.and b (Bool.and c (Bool.and d (Bool.and e f)))))
        }
    }
}

def persist_run (bin : String) (root : String) : IO Bool := do {
    let sessions := String.concat root "/sessions";
    let turns := String.concat root "/turns1.json";
    let wrote <- write_text_script turns ["persisted-reply"];
    if Bool.not wrote then do {
        IO.println "FAIL pty sessions: could not write the turn script";
        return false
    } else do {
        let before <- session_ids sessions;
        let r <- sessions_spawn bin root List.empty (Option.some turns);
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty sessions spawn: " e); return false },
            Result.ok m => do {
                let ok <- persist_checks m sessions before;
                if Bool.not ok then do { return false }
                else do {
                    let id_opt <- newest_session sessions;
                    match id_opt {
                        Option.none => do {
                            let g <- Check.report "a session id is available for resume" false;
                            return g
                        },
                        Option.some id => do {
                            let args := List.cons "--resume" (List.cons id List.empty);
                            let r2 <- sessions_spawn bin root args Option.none;
                            match r2 {
                                Result.err e => do {
                                    IO.println (String.concat "FAIL pty sessions resume spawn: " e);
                                    return false
                                },
                                Result.ok m2 => do {
                                    let restored <- Pty.wait_until m2
                                        (fn (o : Output) => grid_has o "persisted-reply") 8000;
                                    let g <- Check.report "--resume restores the transcript" restored;
                                    // Up recalls the resumed session's prompt: the
                                    // placeholder gives way to one more "hi".
                                    let o0 <- Pty.output m2;
                                    let before : I64 := count_occurrences (Output.text o0) "hi";
                                    Pty.send_text m2 "\u{1b}[A";
                                    let recalled <- Pty.wait_until m2 (fn (o : Output) =>
                                        Bool.and (Bool.not (grid_has o "type a message"))
                                            (I64.lt before (count_occurrences (Output.text o) "hi"))) 3000;
                                    let h <- Check.report "Up recalls the resumed session's prompt" recalled;
                                    Pty.finish m2;
                                    return (g && h)
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

pub def run_sessions_persist_then_resume : IO Bool :=
    run_gated "pty weaver sessions persist" test_sessions_persist_body

def test_sessions_persist_body (bin : String) : IO Bool :=
    with_root "sessions_persist" (fn (root : String) => persist_run bin root)

// ── S3: Home pages older lines from disk ────────────────────────────────

def paging_run (bin : String) (root : String) : IO Bool := do {
    let sessions := String.concat root "/sessions";
    let ok <- write_generated_session sessions "s-manual" Option.none Option.none 1000 1200 (LineSpec.indexed "EARLIEST-LINE-" "" 4);
    if Bool.not ok then do {
        IO.println "FAIL pty sessions: could not synthesize the session";
        return false
    } else do {
        let path := Path.to_string (session_dir sessions "s-manual");
        let args := List.cons "--resume" (List.cons path List.empty);
        let r <- sessions_spawn bin root args Option.none;
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty sessions spawn: " e); return false },
            Result.ok m => do {
                let ready <- Pty.wait_until m placeholder_seen 8000;
                Pty.send_text m "\u{1b}[H";
                let first <- Pty.wait_until m (fn (o : Output) => grid_has o "EARLIEST-LINE-0000") 8000;
                let a <- Check.report "Home pages older lines from disk" (Bool.and ready first);
                Pty.finish m;
                return a
            }
        }
    }
}

pub def run_sessions_home_pages_from_disk : IO Bool :=
    run_gated "pty weaver sessions home" test_sessions_home_body

def test_sessions_home_body (bin : String) : IO Bool :=
    with_root "sessions_home" (fn (root : String) => paging_run bin root)

// ── S4: a bracketed paste is one user block ─────────────────────────────

def first_is (xs : List String) (want : String) : Bool :=
    Bool.and (I64.beq (List.length xs) 1)
        (match List.get 0 xs { Option.some s => s == want, Option.none => false })

def paste_run (bin : String) (root : String) : IO Bool := do {
    let sessions := String.concat root "/sessions";
    let turns := String.concat root "/turns_paste.json";
    let wrote <- write_text_script turns ["persisted-reply"];
    if Bool.not wrote then do {
        IO.println "FAIL pty sessions: could not write the turn script";
        return false
    } else do {
        let r <- sessions_spawn bin root List.empty (Option.some turns);
        match r {
            Result.err e => do { IO.println (String.concat "FAIL pty sessions spawn: " e); return false },
            Result.ok m => do {
                let ready <- Pty.wait_until m placeholder_seen 6000;
                send_paste m "alpha\nbeta";
                let typed <- Pty.wait_until m (fn (o : Output) => grid_has o "alpha") 4000;
                Pty.send_text m "\r";
                let replied <- Pty.wait_until m reply_one 10000;
                let a <- Check.report "the pasted text submits as one turn"
                    (Bool.and (Bool.and ready typed) replied);
                let id_opt <- newest_session sessions;
                match id_opt {
                    Option.none => do {
                        let b <- Check.report "the pasted turn is persisted" false;
                        Pty.finish m;
                        return (Bool.and a b)
                    },
                    Option.some id => do {
                        let dir := session_dir sessions id;
                        let stored <- wait_store_text dir "alpha" 5000;
                        let _ <- quit_cleanly m 4000;
                        Pty.finish m;
                        let users <- store_user_texts dir;
                        let lines <- store_lines dir;
                        let ulines := user_lines lines List.empty;
                        let b <- Check.report "the pasted turn is persisted" stored;
                        let c <- Check.report "one user message holds the whole paste"
                            (first_is users "alpha\nbeta");
                        let d <- Check.report "the transcript splits it into two user lines"
                            (Bool.and (I64.beq (List.length ulines) 2)
                                (match List.get 0 ulines { Option.some s => s == "alpha", Option.none => false }));
                        return (Bool.and a (Bool.and b (Bool.and c d)))
                    }
                }
            }
        }
    }
}

pub def run_sessions_bracketed_paste_is_one_block : IO Bool :=
    run_gated "pty weaver sessions paste" test_sessions_paste_body

def test_sessions_paste_body (bin : String) : IO Bool :=
    with_root "sessions_paste" (fn (root : String) => paste_run bin root)

// ── S5: --no-color emits no palette codes ───────────────────────────────

def color_run (bin : String) (root : String) (extra : List String) : IO (Option Bool) := do {
    let turns := String.concat root "/turns_color.json";
    let r <- sessions_spawn bin root extra (Option.some turns);
    match r {
        Result.err e => do {
            IO.println (String.concat "FAIL pty sessions color spawn: " e);
            IO.pure Option.none
        },
        Result.ok m => do {
            let ready <- Pty.wait_until m placeholder_seen 6000;
            Pty.send_text m "go\n";
            let seen <- Pty.wait_until m (fn (o : Output) => tight_has o "colored") 8000;
            let o <- Pty.output m;
            let colored := Bool.and ready (Bool.and seen (Ansi.has_color o.raw));
            Pty.finish m;
            IO.pure (Option.some colored)
        }
    }
}

def no_color_run (bin : String) (root : String) : IO Bool := do {
    let turns := String.concat root "/turns_color.json";
    let wrote <- write_text_script turns ["colored"];
    if Bool.not wrote then do {
        IO.println "FAIL pty sessions: could not write the turn script";
        return false
    } else do {
        let a_opt <- color_run bin root List.empty;
        let b_opt <- color_run bin root (List.cons "--no-color" List.empty);
        match a_opt {
            Option.none => IO.pure false,
            Option.some colored => match b_opt {
                Option.none => IO.pure false,
                Option.some plain => do {
                    let a <- Check.report "the default run emits palette codes" colored;
                    let b <- Check.report "--no-color emits no palette codes" (Bool.not plain);
                    return (Bool.and a b)
                }
            }
        }
    }
}

pub def run_sessions_no_color : IO Bool :=
    run_gated "pty weaver sessions color" test_sessions_color_body

def test_sessions_color_body (bin : String) : IO Bool :=
    with_root "sessions_color" (fn (root : String) => no_color_run bin root)

// ── S6: an 18 MB session stays on disk ──────────────────────────────────

/// 20 000 lines of 900 z's plus a zero-padded index. With `cols = 100` the
/// 900 z's fill exactly nine rows, so `-19999` is contiguous on the tenth.
def rss_huge_spec : LineSpec :=
    LineSpec.indexed (String.concat (String.repeat "z" 900) "-") "" 5

def rss_spawn (bin : String) (root : String) (id : String) : IO (Option Pty) := do {
    let args := List.cons "--resume" (List.cons id List.empty);
    let r <- sessions_spawn bin root args Option.none;
    match r {
        Result.err e => do {
            IO.println (String.concat "FAIL pty sessions rss spawn: " e);
            IO.pure Option.none
        },
        Result.ok m => IO.pure (Option.some m)
    }
}

/// The control: a one-line session, resumed and measured once it is idle.
def rss_baseline (bin : String) (root : String) (sessions : String) : IO I64 := do {
    let ok <- write_generated_session sessions "s-small" Option.none Option.none
        1000 1 (LineSpec.fixed "hello");
    if Bool.not ok then do {
        IO.println "FAIL pty sessions rss: could not synthesize the baseline session";
        return 0 - 1
    } else do {
        let m_opt <- rss_spawn bin root "s-small";
        match m_opt {
            Option.none => do { return 0 - 1 },
            Option.some m => do {
                let ready <- Pty.wait_until m placeholder_seen 15000;
                let _ <- Check.report "the baseline session paints" ready;
                let _ <- Pty.wait_quiet m 300 3000;
                if Bool.not ready then do {
                    Pty.finish m;
                    return 0 - 1
                } else do {
                    let rss <- rss_kb (Pty.child_pid m);
                    Pty.finish m;
                    return rss
                }
            }
        }
    }
}

def rss_huge (bin : String) (root : String) (sessions : String)
    (base : I64) : IO Bool :=
    if I64.lt base 1 then do {
        let _ <- Check.report "the baseline RSS is readable" false;
        return false
    } else rss_huge_body bin root sessions base

def rss_huge_body (bin : String) (root : String) (sessions : String)
    (base : I64) : IO Bool := do {
    let ok <- write_generated_session sessions "s-huge" Option.none Option.none
        2000 20000 rss_huge_spec;
    if Bool.not ok then do {
        IO.println "FAIL pty sessions rss: could not synthesize the huge session";
        return false
    } else do {
        let m_opt <- rss_spawn bin root "s-huge";
        match m_opt {
            Option.none => do { return false },
            Option.some m => do {
                let ready <- Pty.wait_until m placeholder_seen 15000;
                let painted <- Pty.wait_until m
                    (fn (o : Output) => grid_has o "-19999") 60000;
                let r1 <- rss_kb (Pty.child_pid m);
                let _ <- Pty.wait_quiet m 1000 5000;
                let r2 <- rss_kb (Pty.child_pid m);
                let a <- Check.report "the huge session's tail paints"
                    (Bool.and ready painted);
                let b <- Check.report "startup RSS stays within 10 MB of the baseline"
                    (Bool.and (I64.gt r1 0) (I64.lt r1 (base + 10240)));
                let c <- Check.report "idle RSS growth stays under 20 MB"
                    (Bool.and (I64.gt r2 0) (I64.lt (r2 - r1) 20000));
                IO.println (String.concat "rss base=" (String.concat (I64.to_string base)
                    (String.concat "KB huge=" (String.concat (I64.to_string r1)
                        (String.concat "KB idle=" (String.concat (I64.to_string r2) "KB"))))));
                Pty.finish m;
                return (Bool.and a (Bool.and b c))
            }
        }
    }
}

def rss_run (bin : String) (root : String) : IO Bool := do {
    let sessions := String.concat root "/sessions";
    let base <- rss_baseline bin root sessions;
    rss_huge bin root sessions base
}

pub def run_sessions_big_session_rss : IO Bool :=
    run_gated "pty weaver sessions rss" test_sessions_rss_body

def test_sessions_rss_body (bin : String) : IO Bool :=
    with_root "sessions_rss" (fn (root : String) => rss_run bin root)
