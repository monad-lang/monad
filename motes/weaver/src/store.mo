/// Weaver's session store -- durable transcripts and per-turn model
/// history under `~/.weaver/sessions`.
///
/// `IO.write_file` truncates and there is no append, so each block is a
/// fresh, never-reused file (truncating-create IS append). `index.json`
/// and `meta.json` are small caches rewritten atomically (temp + `mv`);
/// the block files are the source of truth and a stale index rebuilds.
use json::json {
    Json, Json.parse, Json.to_string, Json.make_object, Json.make_array,
    Json.make_str, Json.make_num_int, Json.get_object, Json.get_array,
    Json.get_str, Json.get_num, Json.get_num_i64, Json.object_get,
}
use std::io {IO.read_file, IO.write_file, IO.file_exists, IO.is_dir, IO.list_dir, IO.get_env}
use std::path {Path, Path.of, Path.to_string, Path.join, Path.with_suffix, Path.parent}
use std::process {exec_cmd, process_id}
use std::bench {Bench.now}
use std::map {BTreeMap}
use std::list {List.length}
use shuttle::session {Session, Session.messages_to_json, Session.messages_of_json}
use shuttle::message {Message}

// ── the in-memory view ────────────────────────────────────────────────
// Absolute line coordinates: `total` counts every line ever appended;
// `tail` is the last `tail_lines`; `page` is at most one older page.

pub struct TranscriptPage {
    start : I64,
    lines : List String,
}

pub struct Transcript {
    total : I64,
    tail_start : I64,
    tail : List String,
    page : Option TranscriptPage,
    page_error : Option String,
}

/// The sessions root, the session directory, and its bare name (for
/// display, `/resume` and allocating a sibling session on `/clear`).
pub struct StoreState {
    root : Path,
    dir : Path,
    id : String,
}

pub struct StoreIndexBlock {
    seq : I64,
    start : I64,
    count : I64,
}

pub struct StoreIndex {
    total : I64,
    next_seq : I64,
    blocks : List StoreIndexBlock,
}

pub struct StoreMeta {
    session : Session,
    created : I64,
    updated : I64,
    history_next : I64,
}

pub def Store.tail_lines : I64 := 512
pub def Store.page_lines : I64 := 512
pub def Store.block_lines : I64 := 256

// ── small list helpers (model.mo has its own; store sits below it) ─────

#[partial]
def list_len (xs : List String) : I64 :=
    match xs {
        List.empty => 0,
        List.cons _ rest => 1 + list_len rest,
    }

#[partial]
def take_n (n : I64) (xs : List String) : List String :=
    if n < 1 then List.empty
    else match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (take_n (n - 1) rest),
    }

#[partial]
def drop_n (n : I64) (xs : List String) : List String :=
    if n < 1 then xs
    else match xs {
        List.empty => xs,
        List.cons _ rest => drop_n (n - 1) rest,
    }

#[partial]
def take_last (n : I64) (xs : List String) : List String :=
    drop_n (list_len xs - n) xs

#[terminating]
def blanks (n : I64) : List String :=
    if n < 1 then List.empty else List.cons "" (blanks (n - 1))

#[terminating]
def pad_left (s : String) (width : I64) : String :=
    let need : I64 := width - String.length s in
    if need < 1 then s else String.concat (String.repeat "0" need) s

pub def Store.clamp (x : I64) (lo : I64) (hi : I64) : I64 :=
    if x < lo then lo else if hi < x then hi else x

def max_i (a : I64) (b : I64) : I64 := if a < b then b else a

def min_i (a : I64) (b : I64) : I64 := if a < b then a else b

// ── the pure Transcript model ─────────────────────────────────────────

pub def Transcript.empty : Transcript :=
    let t : Transcript := { total := 0, tail_start := 0, tail := List.empty, page := Option.none, page_error := Option.none } in
    t

/// The separator row a new block opens with after the first one.
pub def Transcript.next_block (t : Transcript) (lines : List String) : List String :=
    if t.total > 0 then List.cons "" lines else lines

pub def Transcript.append (t : Transcript) (lines : List String) : Transcript :=
    let total2 : I64 := t.total + list_len lines in
    let tail2 : List String := take_last Store.tail_lines (List.append t.tail lines) in
    let t2 : Transcript := { t with total := total2, tail_start := total2 - list_len tail2, tail := tail2 } in
    t2

pub def Transcript.with_page (t : Transcript) (p : TranscriptPage) : Transcript :=
    let t2 : Transcript := { t with page := Option.some p, page_error := Option.none } in
    t2

def page_start (t : Transcript) : I64 :=
    match t.page {
        Option.some p => p.start,
        Option.none => t.tail_start,
    }

def page_end (t : Transcript) : I64 :=
    match t.page {
        Option.some p => p.start + list_len p.lines,
        Option.none => t.tail_start,
    }

def placeholders (a : I64) (b : I64) : List String :=
    if Bool.not (a < b) then List.empty else blanks (b - a)

/// The requested absolute range, assembled from the loaded page and tail;
/// indices neither covers become `""` placeholders. O(tail + count).
pub def Transcript.slice (t : Transcript) (start : I64) (count : I64) : List String :=
    let s : I64 := Store.clamp start 0 t.total in
    let e : I64 := Store.clamp (start + count) 0 t.total in
    if Bool.not (s < e) then List.empty
    else slice_parts t s e

def slice_parts (t : Transcript) (s : I64) (e : I64) : List String :=
    let ps : I64 := page_start t in
    let pe : I64 := page_end t in
    let head : List String := placeholders s (min_i e ps) in
    let body : List String := page_slice t (max_i s ps) (min_i e pe) in
    let mid : List String := placeholders (max_i s pe) (min_i e t.tail_start) in
    let tail : List String := tail_slice t (max_i s t.tail_start) e in
    List.append head (List.append body (List.append mid tail))

def page_slice (t : Transcript) (a : I64) (b : I64) : List String :=
    match t.page {
        Option.none => List.empty,
        Option.some p =>
            if Bool.not (a < b) then List.empty
            else take_n (b - a) (drop_n (a - p.start) p.lines),
    }

def tail_slice (t : Transcript) (a : I64) (b : I64) : List String :=
    if Bool.not (a < b) then List.empty
    else take_n (b - a) (drop_n (a - t.tail_start) t.tail)

// ── JSON codecs ───────────────────────────────────────────────────────

def obj_field (obj : BTreeMap String Json) (name : String) : Result String Json :=
    match Json.object_get name obj {
        Option.some j => Result.ok j,
        Option.none => Result.err (String.concat "store: missing field: " name),
    }

def num_of (j : Json) : Result String I64 :=
    Json.get_num_i64 (Json.get_num j)

def field_i64 (obj : BTreeMap String Json) (name : String) : Result String I64 :=
    match obj_field obj name {
        Result.err e => Result.err e,
        Result.ok j => num_of j,
    }

pub def Store.pad12 (n : I64) : String :=
    pad_left (I64.to_string n) 12

pub def Store.encode_block (seq : I64) (start : I64) (lines : List String) : Json :=
    let body : BTreeMap String Json :=
        Map.insert "version" (Json.make_num_int 1)
        (Map.insert "seq" (Json.make_num_int seq)
        (Map.insert "start" (Json.make_num_int start)
        (Map.insert "count" (Json.make_num_int (list_len lines))
        (Map.insert "lines" (Json.make_array (List.map Json.make_str lines)) BTreeMap.empty)))) in
    Json.make_object body

#[partial]
def decode_lines (js : List Json) : Result String (List String) :=
    match js {
        List.empty => Result.ok List.empty,
        List.cons j rest => decode_lines_head j rest,
    }

#[terminating]
def decode_lines_head (j : Json) (rest : List Json) : Result String (List String) :=
    match Json.get_str j {
        Result.err e => Result.err e,
        Result.ok s => decode_lines_tail s rest,
    }

#[terminating]
def decode_lines_tail (s : String) (rest : List Json) : Result String (List String) :=
    match decode_lines rest {
        Result.err e => Result.err e,
        Result.ok ss => Result.ok (List.cons s ss),
    }

pub def Store.decode_block (j : Json) : Result String (Pair StoreIndexBlock (List String)) :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj => decode_block_seq obj,
    }

def decode_block_seq (obj : BTreeMap String Json) : Result String (Pair StoreIndexBlock (List String)) :=
    match field_i64 obj "seq" {
        Result.err e => Result.err e,
        Result.ok seq => decode_block_start obj seq,
    }

def decode_block_start (obj : BTreeMap String Json) (seq : I64) : Result String (Pair StoreIndexBlock (List String)) :=
    match field_i64 obj "start" {
        Result.err e => Result.err e,
        Result.ok start => decode_block_lines obj seq start,
    }

def decode_block_lines (obj : BTreeMap String Json) (seq : I64) (start : I64) : Result String (Pair StoreIndexBlock (List String)) :=
    match obj_field obj "lines" {
        Result.err e => Result.err e,
        Result.ok lj => decode_block_array seq start lj,
    }

def decode_block_array (seq : I64) (start : I64) (lj : Json) : Result String (Pair StoreIndexBlock (List String)) :=
    match Json.get_array lj {
        Result.err e => Result.err e,
        Result.ok js => decode_block_finish seq start js,
    }

def decode_block_finish (seq : I64) (start : I64) (js : List Json) : Result String (Pair StoreIndexBlock (List String)) :=
    match decode_lines js {
        Result.err e => Result.err e,
        Result.ok ls => Result.ok (Pair.pair (mk_index_block seq start (list_len ls)) ls),
    }

def mk_index_block (seq : I64) (start : I64) (count : I64) : StoreIndexBlock :=
    let b : StoreIndexBlock := { seq := seq, start := start, count := count } in
    b

pub def Store.empty_index : StoreIndex :=
    let i : StoreIndex := { total := 0, next_seq := 1, blocks := List.empty } in
    i

def encode_index_block (b : StoreIndexBlock) : Json :=
    let body : BTreeMap String Json :=
        Map.insert "seq" (Json.make_num_int b.seq)
        (Map.insert "start" (Json.make_num_int b.start)
        (Map.insert "count" (Json.make_num_int b.count) BTreeMap.empty)) in
    Json.make_object body

pub def Store.encode_index (i : StoreIndex) : Json :=
    let body : BTreeMap String Json :=
        Map.insert "version" (Json.make_num_int 1)
        (Map.insert "total" (Json.make_num_int i.total)
        (Map.insert "next_seq" (Json.make_num_int i.next_seq)
        (Map.insert "blocks" (Json.make_array (List.map encode_index_block i.blocks)) BTreeMap.empty))) in
    Json.make_object body

#[partial]
def decode_index_blocks (js : List Json) : Result String (List StoreIndexBlock) :=
    match js {
        List.empty => Result.ok List.empty,
        List.cons j rest => decode_index_blocks_head j rest,
    }

#[terminating]
def decode_index_blocks_head (j : Json) (rest : List Json) : Result String (List StoreIndexBlock) :=
    match decode_index_block j {
        Result.err e => Result.err e,
        Result.ok b => decode_index_blocks_tail b rest,
    }

#[terminating]
def decode_index_blocks_tail (b : StoreIndexBlock) (rest : List Json) : Result String (List StoreIndexBlock) :=
    match decode_index_blocks rest {
        Result.err e => Result.err e,
        Result.ok bs => Result.ok (List.cons b bs),
    }

def decode_index_block (j : Json) : Result String StoreIndexBlock :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj => decode_index_block_seq obj,
    }

def decode_index_block_seq (obj : BTreeMap String Json) : Result String StoreIndexBlock :=
    match field_i64 obj "seq" {
        Result.err e => Result.err e,
        Result.ok seq => decode_index_block_start obj seq,
    }

def decode_index_block_start (obj : BTreeMap String Json) (seq : I64) : Result String StoreIndexBlock :=
    match field_i64 obj "start" {
        Result.err e => Result.err e,
        Result.ok start => decode_index_block_count obj seq start,
    }

def decode_index_block_count (obj : BTreeMap String Json) (seq : I64) (start : I64) : Result String StoreIndexBlock :=
    match field_i64 obj "count" {
        Result.err e => Result.err e,
        Result.ok count => Result.ok (mk_index_block seq start count),
    }

pub def Store.decode_index (j : Json) : Result String StoreIndex :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj => decode_index_total obj,
    }

def decode_index_total (obj : BTreeMap String Json) : Result String StoreIndex :=
    match field_i64 obj "total" {
        Result.err e => Result.err e,
        Result.ok total => decode_index_next obj total,
    }

def decode_index_next (obj : BTreeMap String Json) (total : I64) : Result String StoreIndex :=
    match field_i64 obj "next_seq" {
        Result.err e => Result.err e,
        Result.ok next_seq => decode_index_array obj total next_seq,
    }

def decode_index_array (obj : BTreeMap String Json) (total : I64) (next_seq : I64) : Result String StoreIndex :=
    match obj_field obj "blocks" {
        Result.err e => Result.err e,
        Result.ok j => decode_index_array_of total next_seq j,
    }

def decode_index_array_of (total : I64) (next_seq : I64) (j : Json) : Result String StoreIndex :=
    match Json.get_array j {
        Result.err e => Result.err e,
        Result.ok js => decode_index_finish total next_seq js,
    }

def decode_index_finish (total : I64) (next_seq : I64) (js : List Json) : Result String StoreIndex :=
    match decode_index_blocks js {
        Result.err e => Result.err e,
        Result.ok bs =>
            let i : StoreIndex := { total := total, next_seq := next_seq, blocks := bs } in
            Result.ok i,
    }

pub def Store.encode_meta (m : StoreMeta) : Json :=
    let inner : Session := m.session in
    let bare : Session := { inner with history := List.empty } in
    let body : BTreeMap String Json :=
        Map.insert "version" (Json.make_num_int 1)
        (Map.insert "created" (Json.make_num_int m.created)
        (Map.insert "updated" (Json.make_num_int m.updated)
        (Map.insert "history_next" (Json.make_num_int m.history_next)
        (Map.insert "session" (Session.serialize_json bare) BTreeMap.empty)))) in
    Json.make_object body

pub def Store.decode_meta (j : Json) : Result String StoreMeta :=
    match Json.get_object j {
        Result.err e => Result.err e,
        Result.ok obj => decode_meta_created obj,
    }

def decode_meta_created (obj : BTreeMap String Json) : Result String StoreMeta :=
    match field_i64 obj "created" {
        Result.err e => Result.err e,
        Result.ok created => decode_meta_updated obj created,
    }

def decode_meta_updated (obj : BTreeMap String Json) (created : I64) : Result String StoreMeta :=
    match field_i64 obj "updated" {
        Result.err e => Result.err e,
        Result.ok updated => decode_meta_next obj created updated,
    }

def decode_meta_next (obj : BTreeMap String Json) (created : I64) (updated : I64) : Result String StoreMeta :=
    match field_i64 obj "history_next" {
        Result.err e => Result.err e,
        Result.ok next => decode_meta_session obj created updated next,
    }

def decode_meta_session (obj : BTreeMap String Json) (created : I64) (updated : I64) (next : I64) : Result String StoreMeta :=
    match obj_field obj "session" {
        Result.err e => Result.err e,
        Result.ok sj => decode_meta_finish sj created updated next,
    }

def decode_meta_finish (sj : Json) (created : I64) (updated : I64) (next : I64) : Result String StoreMeta :=
    match Session.deserialize_json sj {
        Result.err e => Result.err e,
        Result.ok s =>
            let m : StoreMeta := { session := s, created := created, updated := updated, history_next := next } in
            Result.ok m,
    }

// ── paths ─────────────────────────────────────────────────────────────

/// `WEAVER_SESSION_ROOT` wins, then `$HOME/.weaver/sessions`; both are
/// validated paths, and an empty value is the same as unset.
pub def Store.root_of (override : Option String) (home : Option String) : Option Path :=
    match non_empty override {
        Option.some o => path_or_none o,
        Option.none => match non_empty home {
            Option.none => Option.none,
            Option.some h => home_root h,
        },
    }

def non_empty (o : Option String) : Option String :=
    match o {
        Option.none => Option.none,
        Option.some s => if String.is_empty s then Option.none else Option.some s,
    }

def path_or_none (s : String) : Option Path :=
    match Path.of s {
        Result.err _ => Option.none,
        Result.ok p => Option.some p,
    }

def home_root (h : String) : Option Path :=
    match Path.of h {
        Result.err _ => Option.none,
        Result.ok hp => home_sub hp,
    }

def home_sub (hp : Path) : Option Path :=
    match Path.of ".weaver/sessions" {
        Result.err _ => Option.none,
        Result.ok sub => Option.some (Path.join hp sub),
    }

pub def Store.session_dir (root : Path) (id : String) : Path :=
    Path.join root (Path.path id)

pub def Store.child (dir : Path) (name : String) : Path :=
    Path.join dir (Path.path name)

/// The last path component; for a session directory that is its id.
pub def Store.base_name (p : Path) : String :=
    let parent : String := Path.parent p in
    let s : String := Path.to_string p in
    if String.is_empty parent then s
    else String.drop (String.length parent + 1) s

/// Split a line block into `block_lines` chunks (none for empty input).
#[partial]
pub def Store.chunks (lines : List String) : List (List String) :=
    match lines {
        List.empty => List.empty,
        List.cons _ _ => List.cons (take_n Store.block_lines lines) (chunks_rest (drop_n Store.block_lines lines)),
    }

#[partial]
def chunks_rest (lines : List String) : List (List String) :=
    Store.chunks lines

// ── IO: root and sessions ─────────────────────────────────────────────

pub def Store.sessions_root : IO (Option Path) := do {
    let o <- IO.get_env "WEAVER_SESSION_ROOT";
    let h <- IO.get_env "HOME";
    return (Store.root_of o h)
}

def mkdir_p (p : Path) : IO Unit := do {
    let _ <- exec_cmd "mkdir" ["-p", Path.to_string p];
    return unit
}

/// `IO.write_file` cannot report failure compiled (it returns Unit), so a
/// write is trusted only after a read-back.
def write_verified (p : Path) (text : String) : IO Bool := do {
    IO.write_file p text;
    let back <- IO.read_file p;
    return (back == text)
}

/// Data first, cache second: `mv` makes the replacement atomic.
def write_atomic (p : Path) (text : String) : IO Bool := do {
    let tmp : Path := Path.with_suffix p ".tmp";
    let ok <- write_verified tmp text;
    if Bool.not ok then IO.pure false
    else do {
        let rc <- exec_cmd "mv" ["-f", Path.to_string tmp, Path.to_string p];
        return (rc == 0)
    }
}

pub def Store.ensure_root (root : Path) : IO Bool := do {
    mkdir_p root;
    let there <- IO.is_dir root;
    if Bool.not there then IO.pure false
    else do {
        let probe : Path := Store.child root ".probe";
        let ok <- write_verified probe "ok";
        let _ <- exec_cmd "rm" ["-f", Path.to_string probe];
        return ok
    }
}

#[terminating]
def free_id (root : Path) (base : String) (n : I64) : IO String := do {
    let id : String := if n < 1 then base else String.concat base (String.concat "-" (I64.to_string (n + 1)));
    let taken <- IO.is_dir (Store.session_dir root id);
    if Bool.not taken then IO.pure id else free_id root base (n + 1)
}

def transcript_dir (dir : Path) : Path := Store.child dir "transcript"

def history_dir (dir : Path) : Path := Store.child dir "history"

def index_path (dir : Path) : Path := Store.child (transcript_dir dir) "index.json"

def meta_path (dir : Path) : Path := Store.child dir "meta.json"

def block_path (dir : Path) (seq : I64) : Path :=
    Store.child (transcript_dir dir) (String.concat (Store.pad12 seq) ".json")

def history_path (dir : Path) (seq : I64) : Path :=
    Store.child (history_dir dir) (String.concat (Store.pad12 seq) ".json")

def meta_of (s : Session) (created : I64) (updated : I64) (next : I64) : StoreMeta :=
    let m : StoreMeta := { session := s, created := created, updated := updated, history_next := next } in
    m

def state_of (root : Path) (dir : Path) (id : String) : StoreState :=
    let st : StoreState := { root := root, dir := dir, id := id } in
    st

def write_meta_at (dir : Path) (m : StoreMeta) : IO Bool :=
    write_atomic (meta_path dir) (Json.to_string (Store.encode_meta m))

pub def Store.read_meta (dir : Path) : IO (Result String StoreMeta) := do {
    let p : Path := meta_path dir;
    let there <- IO.file_exists p;
    if Bool.not there then IO.pure (Result.err "session meta is missing")
    else do {
        let text <- IO.read_file p;
        return (meta_from_text text)
    }
}

def meta_from_text (text : String) : Result String StoreMeta :=
    match Json.parse text {
        Result.err _ => Result.err "session meta is not valid JSON",
        Result.ok j => Store.decode_meta j,
    }

pub def Store.new_session (root : Path) (s : Session) : IO (Result String StoreState) := do {
    let ok <- Store.ensure_root root;
    if Bool.not ok then IO.pure (Result.err "session root is not writable")
    else do {
        let base : String := String.concat "s-" (I64.to_string process_id);
        let id <- free_id root base 0;
        let dir : Path := Store.session_dir root id;
        mkdir_p (transcript_dir dir);
        mkdir_p (history_dir dir);
        let _ <- exec_cmd "chmod" ["700", Path.to_string dir];
        let now <- Bench.now;
        let mok <- write_meta_at dir (meta_of s now now 1);
        let iok <- write_atomic (index_path dir) (Json.to_string (Store.encode_index Store.empty_index));
        if Bool.and mok iok
        then IO.pure (Result.ok (state_of root dir id))
        else IO.pure (Result.err "could not initialise the session")
    }
}

/// A shuttle JSON checkpoint becomes a new session directory whose first
/// history block is the loaded transcript.
pub def Store.import_session (root : Path) (s : Session) : IO (Result String StoreState) := do {
    let r <- Store.new_session root s;
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok st => import_into st s,
    }
}

def import_into (st : StoreState) (s : Session) : IO (Result String StoreState) := do {
    let p : Path := history_path st.dir 1;
    let ok <- write_verified p (Json.to_string (Session.messages_to_json s.history));
    if Bool.not ok then IO.pure (Result.err "could not write imported history")
    else do {
        let now <- Bench.now;
        let mok <- write_meta_at st.dir (meta_of s now now 2);
        if mok then IO.pure (Result.ok st) else IO.pure (Result.err "could not write the session meta")
    }
}

// ── IO: transcript index ──────────────────────────────────────────────

def is_block_name (name : String) : Bool :=
    Bool.and (String.ends_with name ".json") (Bool.not (name == "index.json"))

#[partial]
def count_blocks (names : List String) : I64 :=
    match names {
        List.empty => 0,
        List.cons n rest => if is_block_name n then 1 + count_blocks rest else count_blocks rest,
    }

def index_from_text (text : String) : Option StoreIndex :=
    match Json.parse text {
        Result.err _ => Option.none,
        Result.ok j => match Store.decode_index j {
            Result.err _ => Option.none,
            Result.ok i => Option.some i,
        },
    }

#[partial]
def reverse_blocks (bs : List StoreIndexBlock) (acc : List StoreIndexBlock) : List StoreIndexBlock :=
    match bs {
        List.empty => acc,
        List.cons b rest => reverse_blocks rest (List.cons b acc),
    }

/// Walk the sorted block names, accepting a contiguous run whose `seq`
/// and `start` agree; the first torn/missing block ends the run.
#[partial]
def rebuild_go (dir : Path) (names : List String) (seq : I64) (at : I64) (acc : List StoreIndexBlock) : IO StoreIndex :=
    match names {
        List.empty => IO.pure (rebuilt at seq acc),
        List.cons n rest =>
            if Bool.not (is_block_name n) then rebuild_go dir rest seq at acc
            else do {
                let p : Path := Store.child (transcript_dir dir) n;
                let text <- IO.read_file p;
                match Json.parse text {
                    Result.err _ => IO.pure (rebuilt at seq acc),
                    Result.ok j => match Store.decode_block j {
                        Result.err _ => IO.pure (rebuilt at seq acc),
                        Result.ok pr => match pr {
                            Pair.pair b lines =>
                                if Bool.and (b.seq == seq) (b.start == at)
                                then rebuild_go dir rest (seq + 1) (at + b.count) (List.cons b acc)
                                else IO.pure (rebuilt at seq acc),
                        },
                    },
                }
            },
    }

def rebuilt (total : I64) (next_seq : I64) (acc : List StoreIndexBlock) : StoreIndex :=
    let blocks : List StoreIndexBlock := reverse_blocks acc List.empty in
    let i : StoreIndex := { total := total, next_seq := next_seq, blocks := blocks } in
    i

def rebuild_index (dir : Path) : IO StoreIndex := do {
    let names <- IO.list_dir (transcript_dir dir);
    let idx <- rebuild_go dir names 1 0 List.empty;
    let _ <- write_atomic (index_path dir) (Json.to_string (Store.encode_index idx));
    return idx
}

/// The cached index when it parses; rebuilds from the block files when it
/// does not. Callers compare block counts themselves (`checked_index`).
pub def Store.read_index (dir : Path) : IO (Result String StoreIndex) := do {
    let p : Path := index_path dir;
    let there <- IO.file_exists p;
    if Bool.not there then rebuild_ok dir
    else do {
        let text <- IO.read_file p;
        match index_from_text text {
            Option.some idx => IO.pure (Result.ok idx),
            Option.none => rebuild_ok dir,
        }
    }
}

def rebuild_ok (dir : Path) : IO (Result String StoreIndex) := do {
    let idx <- rebuild_index dir;
    return (Result.ok idx)
}

/// The index with its block count verified against the directory; used at
/// startup and before page reads, where a stale cache would show wrong
/// lines. O(entries in the transcript dir), not O(bytes).
pub def Store.checked_index (dir : Path) : IO (Result String StoreIndex) := do {
    let idx_r <- Store.read_index dir;
    match idx_r {
        Result.err e => IO.pure (Result.err e),
        Result.ok idx => check_index dir idx,
    }
}

def check_index (dir : Path) (idx : StoreIndex) : IO (Result String StoreIndex) := do {
    let names <- IO.list_dir (transcript_dir dir);
    if count_blocks names == (idx.next_seq - 1)
    then IO.pure (Result.ok idx)
    else rebuild_ok dir
}

// ── IO: appending and reading ─────────────────────────────────────────

#[partial]
def write_chunks (dir : Path) (seq : I64) (at : I64) (chunks : List (List String)) : IO (Result String (List StoreIndexBlock)) :=
    match chunks {
        List.empty => IO.pure (Result.ok List.empty),
        List.cons c rest => do {
            let p : Path := block_path dir seq;
            let ok <- write_verified p (Json.to_string (Store.encode_block seq at c));
            if Bool.not ok then IO.pure (Result.err (String.concat "could not write " (Path.to_string p)))
            else do {
                let r <- write_chunks dir (seq + 1) (at + list_len c) rest;
                match r {
                    Result.err e => IO.pure (Result.err e),
                    Result.ok bs => IO.pure (Result.ok (List.cons (mk_index_block seq at (list_len c)) bs)),
                }
            }
        },
    }

pub def Store.append_transcript (dir : Path) (start : I64) (lines : List String) : IO (Result String Unit) := do {
    let idx_r <- Store.read_index dir;
    match idx_r {
        Result.err e => IO.pure (Result.err e),
        Result.ok idx =>
            if idx.total == start
            then do {
                let r <- write_chunks dir idx.next_seq idx.total (Store.chunks lines);
                match r {
                    Result.err e => IO.pure (Result.err e),
                    Result.ok added => finish_append dir idx added lines,
                }
            }
            else IO.pure (Result.err "transcript log out of sync"),
    }
}

def next_index (idx : StoreIndex) (added : List StoreIndexBlock) (lines : List String) : StoreIndex :=
    let idx2 : StoreIndex := { idx with total := idx.total + list_len lines, next_seq := idx.next_seq + List.length added, blocks := List.append idx.blocks added } in
    idx2

def finish_append (dir : Path) (idx : StoreIndex) (added : List StoreIndexBlock) (lines : List String) : IO (Result String Unit) := do {
    let idx2 : StoreIndex := next_index idx added lines;
    let ok <- write_atomic (index_path dir) (Json.to_string (Store.encode_index idx2));
    if ok then IO.pure (Result.ok unit) else IO.pure (Result.err "could not write the transcript index")
}

#[partial]
def wanted_blocks (bs : List StoreIndexBlock) (s : I64) (e : I64) : List StoreIndexBlock :=
    match bs {
        List.empty => List.empty,
        List.cons b rest =>
            if Bool.and (b.start < e) ((b.start + b.count) > s)
            then List.cons b (wanted_blocks rest s e)
            else wanted_blocks rest s e,
    }

#[partial]
def read_wanted (dir : Path) (bs : List StoreIndexBlock) (s : I64) (e : I64) (acc : List String) : IO (Result String (List String)) :=
    match bs {
        List.empty => IO.pure (Result.ok acc),
        List.cons b rest => do {
            let text <- IO.read_file (block_path dir b.seq);
            match Store.decode_block_of_text text {
                Result.err e0 => IO.pure (Result.err e0),
                Result.ok pr => match pr {
                    Pair.pair meta lines =>
                        let bs0 : I64 := max_i s meta.start in
                        let be0 : I64 := min_i e (meta.start + meta.count) in
                        let part : List String :=
                            if be0 - bs0 > 0 then take_n (be0 - bs0) (drop_n (bs0 - meta.start) lines) else List.empty in
                        read_wanted dir rest s e (List.append acc part),
                },
            }
        },
    }

pub def Store.read_page (dir : Path) (start : I64) (count : I64) : IO (Result String TranscriptPage) := do {
    let idx_r <- Store.checked_index dir;
    match idx_r {
        Result.err e => IO.pure (Result.err e),
        Result.ok idx => read_page_idx dir idx start count,
    }
}

def read_page_idx (dir : Path) (idx : StoreIndex) (start : I64) (count : I64) : IO (Result String TranscriptPage) := do {
    let total : I64 := idx.total;
    let s : I64 := Store.clamp start 0 total;
    let e : I64 := Store.clamp (start + count) 0 total;
    if Bool.not (s < e)
    then IO.pure (Result.ok (mk_page s List.empty))
    else do {
        let r <- read_wanted dir (wanted_blocks idx.blocks s e) s e List.empty;
        match r {
            Result.err e0 => IO.pure (Result.err e0),
            Result.ok lines => IO.pure (Result.ok (mk_page s lines)),
        }
    }
}

def mk_page (start : I64) (lines : List String) : TranscriptPage :=
    let p : TranscriptPage := { start := start, lines := lines } in
    p

def transcript_of (total : I64) (start : I64) (lines : List String) : Transcript :=
    let t : Transcript := { total := total, tail_start := start, tail := lines, page := Option.none, page_error := Option.none } in
    t

/// The tail a fresh model starts with: the last `tail_lines` lines.
pub def Store.startup_transcript (dir : Path) : IO Transcript := do {
    let idx_r <- Store.checked_index dir;
    match idx_r {
        Result.err _ => IO.pure Transcript.empty,
        Result.ok idx => startup_of dir idx,
    }
}

def startup_of (dir : Path) (idx : StoreIndex) : IO Transcript := do {
    let total : I64 := idx.total;
    let n : I64 := min_i total Store.tail_lines;
    let s : I64 := max_i 0 (total - n);
    let page_r <- Store.read_page dir s n;
    match page_r {
        Result.err _ => IO.pure Transcript.empty,
        Result.ok p => IO.pure (transcript_of total s p.lines),
    }
}

// ── IO: history and metadata ──────────────────────────────────────────

#[partial]
def load_history_names (hdir : Path) (names : List String) (acc : List Message) : IO (Result String (List Message)) :=
    match names {
        List.empty => IO.pure (Result.ok acc),
        List.cons n rest =>
            if Bool.not (String.ends_with n ".json") then load_history_names hdir rest acc
            else do {
                let text <- IO.read_file (Store.child hdir n);
                match messages_from_text text {
                    Result.err _ => IO.pure (Result.ok acc),
                    Result.ok ms => load_history_names hdir rest (List.append acc ms),
                }
            },
    }

def messages_from_text (text : String) : Result String (List Message) :=
    match Json.parse text {
        Result.err _ => Result.err "history block is not valid JSON",
        Result.ok j => Session.messages_of_json j,
    }

def session_with_history (s : Session) (ms : List Message) : Session :=
    let s2 : Session := { s with history := ms } in
    s2

pub def Store.load_session (dir : Path) : IO (Result String Session) := do {
    let meta_r <- Store.read_meta dir;
    match meta_r {
        Result.err e => IO.pure (Result.err e),
        Result.ok m => load_session_meta dir m,
    }
}

def load_session_meta (dir : Path) (m : StoreMeta) : IO (Result String Session) := do {
    let names <- IO.list_dir (history_dir dir);
    let hist_r <- load_history_names (history_dir dir) names List.empty;
    match hist_r {
        Result.err e => IO.pure (Result.err e),
        Result.ok ms => IO.pure (Result.ok (session_with_history m.session ms)),
    }
}

def meta_updated (m : StoreMeta) (s : Session) (now : I64) : StoreMeta :=
    let m2 : StoreMeta := { m with session := s, updated := now } in
    m2

pub def Store.update_meta (dir : Path) (s : Session) : IO (Result String Unit) := do {
    let meta_r <- Store.read_meta dir;
    match meta_r {
        Result.err e => IO.pure (Result.err e),
        Result.ok m => update_meta_of dir m s,
    }
}

def update_meta_of (dir : Path) (m : StoreMeta) (s : Session) : IO (Result String Unit) := do {
    let now <- Bench.now;
    let m2 : StoreMeta := meta_updated m s now;
    let ok <- write_meta_at dir m2;
    if ok then IO.pure (Result.ok unit) else IO.pure (Result.err "could not write the session meta")
}

/// One successful turn: transcript blocks, then the history delta, then
/// the meta cache (the block files are the truth).
pub def Store.record_turn (st : StoreState) (s : Session) (delta : List Message) (tstart : I64) (tlines : List String) : IO (Result String Unit) := do {
    let ar <- Store.append_transcript st.dir tstart tlines;
    match ar {
        Result.err e => IO.pure (Result.err e),
        Result.ok _ => Store.record_history st s delta,
    }
}

/// The history half alone -- dumb mode has no transcript blocks.
pub def Store.record_history (st : StoreState) (s : Session) (delta : List Message) : IO (Result String Unit) :=
    if list_msg_len delta < 1
    then Store.update_meta st.dir s
    else do {
        let meta_r <- Store.read_meta st.dir;
        match meta_r {
            Result.err e => IO.pure (Result.err e),
            Result.ok m => record_turn_meta st s delta m,
        }
    }

def meta_next (m : StoreMeta) (s : Session) (now : I64) (next : I64) : StoreMeta :=
    let m2 : StoreMeta := { m with session := s, updated := now, history_next := next } in
    m2

def record_turn_meta (st : StoreState) (s : Session) (delta : List Message) (m : StoreMeta) : IO (Result String Unit) := do {
    let p : Path := history_path st.dir m.history_next;
    let ok <- write_verified p (Json.to_string (Session.messages_to_json delta));
    if Bool.not ok then IO.pure (Result.err "could not write the history block")
    else do {
        let now <- Bench.now;
        let m2 : StoreMeta := meta_next m s now (m.history_next + 1);
        let wok <- write_meta_at st.dir m2;
        if wok then IO.pure (Result.ok unit) else IO.pure (Result.err "could not write the session meta")
    }
}

pub def Store.record_output (st : StoreState) (s : Session) (lines : List String) (tstart : I64) : IO (Result String Unit) := do {
    let ar <- Store.append_transcript st.dir tstart lines;
    match ar {
        Result.err e => IO.pure (Result.err e),
        Result.ok _ => Store.update_meta st.dir s,
    }
}

#[partial]
def list_msg_len (ms : List Message) : I64 :=
    match ms {
        List.empty => 0,
        List.cons _ rest => 1 + list_msg_len rest,
    }

// ── IO: latest session ────────────────────────────────────────────────

#[partial]
def latest_go (root : Path) (names : List String) (best : Option String) (best_t : I64) : IO (Option String) :=
    match names {
        List.empty => IO.pure best,
        List.cons n rest => do {
            let dir : Path := Store.session_dir root n;
            let isd <- IO.is_dir dir;
            if Bool.not isd then latest_go root rest best best_t
            else do {
                let meta_r <- Store.read_meta dir;
                match meta_r {
                    Result.err _ => latest_go root rest best best_t,
                    Result.ok m =>
                        if m.updated > best_t
                        then latest_go root rest (Option.some n) m.updated
                        else latest_go root rest best best_t,
                }
            }
        },
    }

/// The session with the greatest `meta.updated` (the `/resume` default).
pub def Store.latest_session (root : Path) : IO (Option String) := do {
    let names <- IO.list_dir root;
    latest_go root names Option.none 0
}

/// Decode a block straight from its file text (used by page reads).
pub def Store.decode_block_of_text (text : String) : Result String (Pair StoreIndexBlock (List String)) :=
    match Json.parse text {
        Result.err _ => Result.err "transcript block is not valid JSON",
        Result.ok j => Store.decode_block j,
    }
