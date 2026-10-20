/// IO tests for the session store. Every root is a fresh, pid-qualified
/// /tmp directory -- never $HOME, and safe under the concurrent sweep.
use weaver::store {
    StoreState, TranscriptPage, TLine, TLine.plain, TLine.user_line,
    Store.new_session, Store.import_session, Store.append_transcript,
    Store.read_page, Store.record_turn, Store.load_session, Store.latest_session,
    Store.ensure_root, Store.startup_transcript, Store.tail_lines, Store.child,
    Store.append_chunk, Store.read_live, Store.discard_live, Store.append_history_note, Store.update_meta,
}
use shuttle::session {Session, Session.messages_to_json}
use shuttle::provider {ProviderConfig, mock}
use shuttle::message {Message, Usage}
use shuttle::message_types {text, user, assistant}
use std::path {Path, Path.of, Path.to_string}
use std::process {process_id, exec_cmd}
use std::list {List.length}
use std::io {IO.write_file}
use std::concurrent::combine {sleepIO}
use json::json {Json}

#[partial]
def lines_go (i : I64) (n : I64) : List TLine :=
    if n < i then List.empty
    else List.cons (TLine.plain (String.concat "l" (I64.to_string i))) (lines_go (i + 1) n)

def lines_from (n : I64) : List TLine := lines_go 1 n

#[partial]
def texts (ls : List TLine) : List String :=
    match ls {
        List.empty => List.empty,
        List.cons l rest => List.cons l.text (texts rest),
    }

def test_cfg : ProviderConfig :=
    { base_url := "http://localhost:11434", model := "m", api_key_env := "K", max_tokens := 8, wire := Wire.mock }

def test_usage : Usage := { input_tokens := 1, output_tokens := 2, cached_tokens := 3 }

def test_session : Session :=
    { config := test_cfg, system_prompt := "s", tools := List.empty, history := List.empty, turns := 0, spent := test_usage }

def user_msg (text : String) : Message :=
    { role := Role.user, content := [Content.text text] }

def assistant_msg (text : String) : Message :=
    { role := Role.assistant, content := [Content.text text] }

def root_for (name : String) : Path :=
    match Path.of (String.concat "/tmp/weaver_store_" (String.concat (I64.to_string process_id) (String.concat "_" name))) {
        Result.err _ => Path.path "/tmp/weaver_store_fallback",
        Result.ok p => p,
    }

def clean (p : Path) : IO Unit := do {
    let _ <- exec_cmd "rm" ["-rf", Path.to_string p];
    return unit
}

def with_history (s : Session) (ms : List Message) : Session :=
    let s2 : Session := { s with history := ms } in
    s2

// ── creation, append, paging, startup ─────────────────────────────────

#[test]
def test_new_session_append_and_page : IO Bool := do {
    let root : Path := root_for "append";
    clean root;
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok st => check_append st,
    }
}

def check_append (st : StoreState) : IO Bool := do {
    let a <- Store.append_transcript st.dir 0 (lines_from 300);
    let p <- Store.read_page st.dir 254 6;
    match a {
        Result.err _ => IO.pure false,
        Result.ok _ => check_page p,
    }
}

def check_page (p : Result String TranscriptPage) : IO Bool :=
    match p {
        Result.err _ => IO.pure false,
        Result.ok pg => IO.pure (pg.start == 254 && texts pg.lines == ["l255", "l256", "l257", "l258", "l259", "l260"]),
    }

#[test]
def test_startup_loads_the_tail : IO Bool := do {
    let root : Path := root_for "startup";
    clean root;
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok st => check_startup st,
    }
}

def check_startup (st : StoreState) : IO Bool := do {
    let _ <- Store.append_transcript st.dir 0 (lines_from 600);
    let t <- Store.startup_transcript st.dir;
    let total : I64 := t.total;
    let start : I64 := t.tail_start;
    let n : I64 := List.length t.tail;
    return (total == 600 && start == 88 && n == Store.tail_lines)
}

#[test]
def test_out_of_sync_append_is_an_error : IO Bool := do {
    let root : Path := root_for "sync";
    clean root;
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok st => check_sync st,
    }
}

def check_sync (st : StoreState) : IO Bool := do {
    let a <- Store.append_transcript st.dir 5 [TLine.plain "x"];
    match a {
        Result.err e => IO.pure (String.contains e "out of sync"),
        Result.ok _ => IO.pure false,
    }
}

#[test]
def test_index_rebuilds_after_removal : IO Bool := do {
    let root : Path := root_for "rebuild";
    clean root;
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok st => check_rebuild st,
    }
}

def check_rebuild (st : StoreState) : IO Bool := do {
    let _ <- Store.append_transcript st.dir 0 (lines_from 300);
    let ip : Path := Store.child (Store.child st.dir "transcript") "index.json";
    let _ <- exec_cmd "rm" ["-f", Path.to_string ip];
    let p <- Store.read_page st.dir 0 3;
    match p {
        Result.err _ => IO.pure false,
        Result.ok pg => IO.pure (pg.start == 0 && texts pg.lines == ["l1", "l2", "l3"]),
    }
}

// ── history ───────────────────────────────────────────────────────────

#[test]
def test_history_roundtrip_across_turns : IO Bool := do {
    let root : Path := root_for "history";
    clean root;
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok st => check_history st,
    }
}

def check_history (st : StoreState) : IO Bool := do {
    let d1 : List Message := [user_msg "hi", assistant_msg "hello"];
    let r1 <- Store.record_turn st test_session d1 0 [TLine.user_line "hi", TLine.plain "hello"];
    let d2 : List Message := [user_msg "again", assistant_msg "yes"];
    let r2 <- Store.record_turn st test_session d2 2 [TLine.user_line "again", TLine.plain "yes"];
    let loaded <- Store.load_session st.dir;
    match r1 {
        Result.err _ => IO.pure false,
        Result.ok _ => match r2 {
            Result.err _ => IO.pure false,
            Result.ok _ => check_loaded loaded,
        },
    }
}

def check_loaded (r : Result String Session) : IO Bool :=
    match r {
        Result.err _ => IO.pure false,
        Result.ok s =>
            let n : I64 := List.length s.history in
            IO.pure (n == 4),
    }

// ── the commit point: history_next ────────────────────────────────────

def write_orphan (st : StoreState) : IO Unit := do {
    let p : Path := Store.child (Store.child st.dir "history") "000000000002.json";
    let _ <- IO.write_file p (Json.to_string (Session.messages_to_json [user_msg "orphan"]));
    return unit
}

def orphan_finish (st : StoreState) : IO Bool := do {
    write_orphan st;
    let loaded <- Store.load_session st.dir;
    match loaded {
        Result.err _ => IO.pure false,
        Result.ok s => IO.pure (List.length s.history == 2),
    }
}

def orphan_step (st : StoreState) : IO Bool := do {
    let r <- Store.record_turn st test_session [user_msg "hi", assistant_msg "hello"] 0 [TLine.user_line "hi", TLine.plain "hello"];
    match r {
        Result.err _ => IO.pure false,
        Result.ok _ => orphan_finish st,
    }
}

/// An uncommitted block (written, but `history_next` never advanced) is
/// ignored -- otherwise the next turn overwrites it and resurrects its
/// messages in the meantime.
#[test]
def test_history_loads_only_the_committed_prefix : IO Bool := do {
    let root : Path := root_for "orphan";
    clean root;
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok st => orphan_step st,
    }
}

def gap_finish (st : StoreState) : IO Bool := do {
    let p : Path := Store.child (Store.child st.dir "history") "000000000001.json";
    let _ <- exec_cmd "rm" ["-f", Path.to_string p];
    let loaded <- Store.load_session st.dir;
    match loaded {
        Result.err _ => IO.pure false,
        Result.ok s => IO.pure (List.length s.history == 0),
    }
}

def gap_second (st : StoreState) : IO Bool := do {
    let r <- Store.record_turn st test_session [user_msg "c", assistant_msg "d"] 2 [TLine.plain "c", TLine.plain "d"];
    match r {
        Result.err _ => IO.pure false,
        Result.ok _ => gap_finish st,
    }
}

def gap_first (st : StoreState) : IO Bool := do {
    let r <- Store.record_turn st test_session [user_msg "a", assistant_msg "b"] 0 [TLine.plain "a", TLine.plain "b"];
    match r {
        Result.err _ => IO.pure false,
        Result.ok _ => gap_second st,
    }
}

/// A hole in the committed prefix would pair a tool result with the
/// wrong call, so the load stops there rather than skipping the block.
#[test]
def test_history_stops_at_a_missing_block : IO Bool := do {
    let root : Path := root_for "gap";
    clean root;
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok st => gap_first st,
    }
}

#[test]
def test_import_session_keeps_history : IO Bool := do {
    let root : Path := root_for "import";
    clean root;
    let hist : List Message := [user_msg "one", assistant_msg "two"];
    let s : Session := with_history test_session hist;
    let r <- Store.import_session root s;
    match r {
        Result.err _ => IO.pure false,
        Result.ok st => check_import st,
    }
}

def check_import (st : StoreState) : IO Bool := do {
    let loaded <- Store.load_session st.dir;
    match loaded {
        Result.err _ => IO.pure false,
        Result.ok s => IO.pure (List.length s.history == 2),
    }
}

// ── sessions listing and degradation ──────────────────────────────────

def check_latest (root : Path) : IO Bool := do {
    let l <- Store.latest_session root;
    return (match l { Option.some _ => true, Option.none => false })
}

#[test]
def test_latest_session_is_some : IO Bool := do {
    let root : Path := root_for "latest";
    clean root;
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok _ => check_latest root,
    }
}

def latest_order_read (root : Path) (st1 : StoreState) : IO Bool := do {
    let l <- Store.latest_session root;
    match l {
        Option.some id => IO.pure (id == st1.id),
        Option.none => IO.pure false,
    }
}

def latest_order_finish (root : Path) (st1 : StoreState) : IO Bool := do {
    let _ <- sleepIO 5;
    let u <- Store.update_meta st1.dir test_session;
    match u {
        Result.err _ => IO.pure false,
        Result.ok _ => latest_order_read root st1,
    }
}

def latest_order_second (root : Path) (st1 : StoreState) : IO Bool := do {
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok _ => latest_order_finish root st1,
    }
}

/// The newest session is the greatest `updated`, not the first or last
/// directory name encountered.
#[test]
def test_latest_session_is_the_most_recently_updated : IO Bool := do {
    let root : Path := root_for "latest_order";
    clean root;
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok st1 => latest_order_second root st1,
    }
}

def check_unwritable (p : Path) : IO Bool := do {
    let ok <- Store.ensure_root p;
    return (Bool.not ok)
}

#[test]
def test_unwritable_root_is_rejected : IO Bool :=
    match Path.of "/dev/null/weaver" {
        Result.err _ => IO.pure true,
        Result.ok p => check_unwritable p,
    }

// ── live streamed output ──────────────────────────────────────────────

#[test]
def test_chunks_append_and_discard : IO Bool := do {
    let root : Path := root_for "chunks";
    clean root;
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok st => check_chunks st,
    }
}

def check_chunks (st : StoreState) : IO Bool := do {
    let _ <- Store.append_chunk st "hel";
    let _ <- Store.append_chunk st "lo";
    let first <- Store.read_live st;
    let _ <- Store.discard_live st;
    let after <- Store.read_live st;
    let text_ok : Bool := match first { Option.some t => t == "hello", Option.none => false };
    let gone_ok : Bool := match after { Option.none => true, Option.some _ => false };
    return (text_ok && gone_ok)
}

/// A standalone note (a plan approval's revision note) is committed as a
/// history block and advances `history_next`, so `/resume` keeps it.
#[test]
def test_history_note_is_committed : IO Bool := do {
    let root : Path := root_for "note";
    clean root;
    let r <- Store.new_session root test_session;
    match r {
        Result.err _ => IO.pure false,
        Result.ok st => check_note st,
    }
}

def check_note (st : StoreState) : IO Bool := do {
    let w <- Store.append_history_note st test_session "look at the plan";
    match w {
        Result.err _ => IO.pure false,
        Result.ok _ => do {
            let loaded <- Store.load_session st.dir;
            match loaded {
                Result.err _ => IO.pure false,
                Result.ok s => IO.pure (List.length s.history == 1),
            }
        }
    }
}
