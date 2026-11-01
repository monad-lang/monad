// weaver / mty_fixtures -- turn scripts and synthetic session stores for the
// pty drivers under `motes/weaver/test/`.
//
// Two jobs:
//
//   * build the mock wire's turn JSON (the same shape
//     `motes/shuttle/src/wire/mock.mo` parses), including scripts that carry
//     an absolute path or a generated plan;
//   * synthesize a session store with weaver's OWN encoders
//     (`Store.encode_block/index/meta`), so the fixtures cannot drift from the
//     reader. The 18 MB session is written one 256-line block at a time and
//     never materializes its lines.
//
// Store readers here are the test-side assertions: transcript lines, history
// user texts, and the history block file.

use json::json {Json}
use std::concurrent::combine {sleepIO}
use std::io {IO.current_time, IO.file_exists}
use std::list {List.any, List.intercalate}
use std::path {Path, Path.join, Path.to_string}
use std::process {exec_cmd}
use std::test {Test.write_fixture}
use shuttle::message {Message, Usage}
use shuttle::message_types {Role, Content}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::session {Session}
use weaver::store {
    Store.block_lines, Store.encode_block, Store.encode_index, Store.encode_meta,
    Store.list_sessions, Store.load_session, Store.pad12, Store.read_index,
    Store.read_page, Store.session_dir,
    StoreIndex, StoreIndexBlock, StoreMeta, SessionInfo, TLine, TLine.plain
}

// ── Mock wire turn scripts ───────────────────────────────────────────────

def text_content (text : String) : Json :=
    Json.make_object_pairs
        [Pair.pair "type" (Json.make_str "text"),
         Pair.pair "text" (Json.make_str text)]

def tool_content (id : String) (name : String) (input : Json) : Json :=
    Json.make_object_pairs
        [Pair.pair "type" (Json.make_str "tool_use"),
         Pair.pair "id" (Json.make_str id),
         Pair.pair "name" (Json.make_str name),
         Pair.pair "input" input]

def usage_json : Json :=
    Json.make_object_pairs
        [Pair.pair "input_tokens" (Json.make_num_int 1),
         Pair.pair "output_tokens" (Json.make_num_int 10),
         Pair.pair "cached_tokens" (Json.make_num_int 0)]

/// One scripted turn: assistant message, usage, stop reason.
pub def turn_json (content : Json) (stop : String) : Json :=
    Json.make_object_pairs
        [Pair.pair "message"
            (Json.make_object_pairs
                [Pair.pair "role" (Json.make_str "assistant"),
                 Pair.pair "content" (Json.make_array [content])]),
         Pair.pair "usage" usage_json,
         Pair.pair "stop" (Json.make_str stop)]

pub def text_turn_json (text : String) : Json :=
    turn_json (text_content text) "end_turn"

pub def tool_use_turn_json (id : String) (name : String) (input : Json) : Json :=
    turn_json (tool_content id name input) "tool_use_stop"

pub def write_turns (path : String) (turns : List Json) : IO Bool :=
    Test.write_fixture (Path.path path) (Json.to_string (Json.make_array turns))

pub def write_text_script (path : String) (texts : List String) : IO Bool :=
    write_turns path (List.map (fn (t : String) => text_turn_json t) texts)

/// Turn 0: a `read` of a real note file (so the approval overlay and the tool
/// result are real). Turn 1: the final text.
pub def write_base_script (path : String) (note_path : String) : IO Bool :=
    let input : Json := Json.make_object_pairs [Pair.pair "path" (Json.make_str note_path)] in
    write_turns path
        [tool_use_turn_json "b1" "read" input,
         text_turn_json "done reading"]

/// Turn 0 starts a detached process; turn 1 reports.
pub def write_process_script (path : String) (command : String) : IO Bool :=
    let input : Json :=
        Json.make_object_pairs
            [Pair.pair "command" (Json.make_str command),
             Pair.pair "cwd" (Json.make_str "")] in
    write_turns path
        [tool_use_turn_json "p1" "start_process" input,
         text_turn_json "started it"]

// ── Generated text ───────────────────────────────────────────────────────

pub def pad4 (n : I64) : String :=
    let s := I64.to_string n in
    let zeros : I64 := 4 - String.length s in
    String.concat (String.repeat "0" (if I64.lt zeros 0 then 0 else zeros)) s

pub def pad2 (n : I64) : String :=
    let s := I64.to_string n in
    let zeros : I64 := 2 - String.length s in
    String.concat (String.repeat "0" (if I64.lt zeros 0 then 0 else zeros)) s

#[partial]
def plan_lines_go (i : I64) (n : I64) (acc : List String) : List String :=
    if Bool.not (I64.lt i n) then List.reverse acc
    else
        let line := String.concat "PLAN-LINE-" (String.concat (pad4 i)
            " inspect the module and propose the next step in detail") in
        plan_lines_go (i + 1) n (List.cons line acc)

/// The bigplan fixture: `n` numbered plan lines, ~70 bytes each.
pub def plan_text (n : I64) : String :=
    List.intercalate "\n" (plan_lines_go 0 n List.empty)

// ── Synthetic session stores ─────────────────────────────────────────────

def test_cfg : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY",
      api_key := Option.none, max_tokens := 8, wire := Wire.mock, thinking := false }

def test_usage : Usage := { input_tokens := 0, output_tokens := 0, cached_tokens := 0 }

def test_session (turns : I64) : Session :=
    { config := test_cfg, system_prompt := "s", tools := List.empty,
      history := List.empty, turns := turns, spent := test_usage }

pub def session_dir (sessions : String) (id : String) : Path :=
    Store.session_dir (Path.path sessions) id

def transcript_dir (dir : Path) : Path := Path.join dir (Path.path "transcript")

def history_dir (dir : Path) : Path := Path.join dir (Path.path "history")

def block_path (dir : Path) (seq : I64) : Path :=
    Path.join (transcript_dir dir)
        (Path.path (String.concat (Store.pad12 seq) ".json"))

pub def history_block_exists (dir : Path) (seq : I64) : IO Bool :=
    IO.file_exists
        (Path.join (history_dir dir) (Path.path (String.concat (Store.pad12 seq) ".json")))

/// How a synthesized session's lines are made: a constant text, or a prefix,
/// zero-padded counter and suffix. A value (not a function) keeps the store
/// writer free of closures.
pub type LineSpec {
    fixed (text : String),
    indexed (prefix : String) (suffix : String) (pad : I64)
}

#[partial]
def pad_go (zeros : I64) (acc : String) : String :=
    if I64.lt zeros 1 then acc else pad_go (zeros - 1) (String.concat "0" acc)

pub def pad_n (pad : I64) (i : I64) : String :=
    let s := I64.to_string i in
    let zeros : I64 := pad - String.length s in
    String.concat (pad_go zeros "") s

pub def LineSpec.text (spec : LineSpec) (i : I64) : String :=
    match spec {
        fixed text => text,
        indexed prefix suffix pad =>
            let num := if I64.lt pad 1 then I64.to_string i else pad_n pad i in
            String.concat prefix (String.concat num suffix)
    }

#[partial]
def make_lines (spec : LineSpec) (i : I64) (to : I64) (acc : List TLine) : List TLine :=
    if Bool.not (I64.lt i to) then List.reverse acc
    else make_lines spec (i + 1) to (List.cons (TLine.plain (LineSpec.text spec i)) acc)

struct BlockState {
    ok : Bool,
    next_seq : I64,
    blocks : List StoreIndexBlock
}

/// Write blocks of `Store.block_lines` until `count`, updating the index
/// metadata as it goes. One block's lines exist at a time.
#[partial]
def write_blocks_go (dir : Path) (spec : LineSpec) (start : I64) (count : I64)
                    (seq : I64) (st : BlockState) : IO BlockState := do {
    if Bool.not (I64.lt start count) then IO.pure st
    else do {
        let room := count - start;
        let n := if I64.lt room Store.block_lines then room else Store.block_lines;
        let lines := make_lines spec start (start + n) List.empty;
        let block := Store.encode_block seq start lines;
        let ok1 <- Test.write_fixture (block_path dir seq) (Json.to_string block);
        let meta_b : StoreIndexBlock := { seq := seq, start := start, count := n };
        let st2 : BlockState := {
            ok := Bool.and st.ok ok1,
            next_seq := seq + 1,
            blocks := List.cons meta_b st.blocks
        };
        write_blocks_go dir spec (start + n) count (seq + 1) st2
    }
}

/// A session with `count` plain assistant lines made by `spec`.
/// `updated` orders it in the picker; `name`/`description` fill the row.
pub def write_generated_session (sessions : String) (id : String)
                                (name : Option String) (description : Option String)
                                (updated : I64) (count : I64)
                                (spec : LineSpec) : IO Bool := do {
    let dir := session_dir sessions id;
    let tdir := transcript_dir dir;
    let hdir := history_dir dir;
    let _ <- exec_cmd "mkdir"
        (List.cons "-p" (List.cons (Path.to_string dir)
        (List.cons (Path.to_string tdir) (List.cons (Path.to_string hdir) List.empty))));
    let st0 : BlockState := { ok := true, next_seq := 1, blocks := List.empty };
    let st <- write_blocks_go dir spec 0 count 1 st0;
    let idx : StoreIndex := {
        total := count,
        next_seq := st.next_seq,
        blocks := List.reverse st.blocks
    };
    let ok1 <- Test.write_fixture
        (Path.join tdir (Path.path "index.json"))
        (Json.to_string (Store.encode_index idx));
    let meta : StoreMeta := {
        session := test_session 0,
        created := updated,
        updated := updated,
        history_next := 1,
        history_base := 1,
        plan := Option.none,
        name := name,
        description := description
    };
    let ok2 <- Test.write_fixture
        (Path.join dir (Path.path "meta.json"))
        (Json.to_string (Store.encode_meta meta));
    return (Bool.and (Bool.and st.ok ok1) ok2)
}

// ── Store readers used as assertions ─────────────────────────────────────

pub def store_lines (dir : Path) : IO (List TLine) := do {
    let idx_r <- Store.read_index dir;
    match idx_r {
        Result.err _ => IO.pure List.empty,
        Result.ok idx => do {
            let page_r <- Store.read_page dir 0 idx.total;
            match page_r {
                Result.err _ => IO.pure List.empty,
                Result.ok page => IO.pure page.lines
            }
        }
    }
}

#[partial]
def lines_have (ls : List TLine) (needle : String) : Bool :=
    match ls {
        List.empty => false,
        List.cons l rest =>
            String.contains l.text needle || lines_have rest needle
    }

pub def store_has_text (dir : Path) (needle : String) : IO Bool := do {
    let ls <- store_lines dir;
    return (lines_have ls needle)
}

pub def wait_store_text (dir : Path) (needle : String) (deadline_ms : I64) : IO Bool := do {
    let start <- IO.current_time;
    wait_store_go dir needle (start + deadline_ms)
}

#[partial]
def wait_store_go (dir : Path) (needle : String) (deadline : I64) : IO Bool := do {
    let there <- store_has_text dir needle;
    if there then IO.pure true
    else do {
        let now <- IO.current_time;
        if I64.gt now deadline then IO.pure false
        else do { sleepIO 50; wait_store_go dir needle deadline }
    }
}

def content_text (c : Content) : List String :=
    match c {
        Content.text s => List.cons s List.empty,
        _ => List.empty
    }

#[partial]
def content_texts (cs : List Content) : List String :=
    match cs {
        List.empty => List.empty,
        List.cons c rest => List.append (content_text c) (content_texts rest)
    }

def user_texts_of (m : Message) : List String :=
    match m.role {
        Role.user => content_texts m.content,
        _ => List.empty
    }

#[partial]
def user_texts (ms : List Message) : List String :=
    match ms {
        List.empty => List.empty,
        List.cons m rest => List.append (user_texts_of m) (user_texts rest)
    }

/// Every `role: user` message's text content, in order.
pub def store_user_texts (dir : Path) : IO (List String) := do {
    let r <- Store.load_session dir;
    match r {
        Result.err _ => IO.pure List.empty,
        Result.ok s => IO.pure (user_texts s.history)
    }
}

pub def session_ids (sessions : String) : IO (List String) := do {
    let infos <- Store.list_sessions (Path.path sessions);
    return (List.map (fn (i : SessionInfo) => i.id) infos)
}

/// The picker's first row: the newest-`updated` session.
pub def newest_session (sessions : String) : IO (Option String) := do {
    let infos <- Store.list_sessions (Path.path sessions);
    match infos {
        List.empty => IO.pure Option.none,
        List.cons i _ => IO.pure (Option.some i.id)
    }
}

#[partial]
def first_new (infos : List SessionInfo) (before : List String) : Option String :=
    match infos {
        List.empty => Option.none,
        List.cons i rest =>
            if List.any (fn (b : String) => b == i.id) before
            then first_new rest before
            else Option.some i.id
    }

/// The id that appeared since `before` (a pre-spawn `session_ids` snapshot).
pub def newest_new (sessions : String) (before : List String) : IO (Option String) := do {
    let infos <- Store.list_sessions (Path.path sessions);
    return (first_new infos before)
}
