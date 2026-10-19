/// Pure tests for the session store: absolute transcript coordinates,
/// paging slices, JSON codecs and path resolution. No IO.
use weaver::store {
    Transcript, TranscriptPage, StoreIndex, StoreIndexBlock, StoreMeta,
    Transcript.empty, Transcript.append, Transcript.next_block, Transcript.slice,
    Transcript.with_page,
    Store.encode_block, Store.decode_block, Store.encode_index, Store.decode_index,
    Store.encode_meta, Store.decode_meta, Store.pad12, Store.chunks, Store.root_of,
    Store.tail_lines,
}
use shuttle::session {Session}
use shuttle::provider {ProviderConfig, mock}
use shuttle::message {Usage}
use json::json {Json.parse, Json.to_string}
use std::path {Path.to_string}
use std::list {List.length}

#[partial]
def lines_go (i : I64) (n : I64) : List String :=
    if n < i then List.empty
    else List.cons (String.concat "l" (I64.to_string i)) (lines_go (i + 1) n)

def lines_from (n : I64) : List String := lines_go 1 n

def pair_of (pr : Pair StoreIndexBlock (List String)) : StoreIndexBlock :=
    match pr { Pair.pair b _ => b }

def lines_of (pr : Pair StoreIndexBlock (List String)) : List String :=
    match pr { Pair.pair _ ls => ls }

// ── coordinates ───────────────────────────────────────────────────────

#[test]
def test_append_tracks_total_and_tail : Bool :=
    let t : Transcript := Transcript.append Transcript.empty ["a", "b"] in
    t.total == 2 && t.tail_start == 0 && List.length t.tail == 2

#[test]
def test_next_block_inserts_a_separator_after_the_first : Bool :=
    let t : Transcript := Transcript.append Transcript.empty ["a"] in
    let blk : List String := Transcript.next_block t ["b"] in
    List.length blk == 2 && (match blk { List.cons x _ => x == "", _ => false })

#[test]
def test_empty_transcript_has_no_separator : Bool :=
    Transcript.next_block Transcript.empty ["a"] == ["a"]

#[test]
def test_tail_trims_at_tail_lines : Bool :=
    let n : I64 := Store.tail_lines + 100 in
    let t : Transcript := Transcript.append Transcript.empty (lines_from n) in
    List.length t.tail == Store.tail_lines && t.tail_start == 100 && t.total == n

#[test]
def test_slice_reads_the_tail : Bool :=
    let t : Transcript := Transcript.append Transcript.empty ["a", "b", "c"] in
    Transcript.slice t 0 3 == ["a", "b", "c"] && Transcript.slice t 1 1 == ["b"]

#[test]
def test_page_covers_lines_above_the_tail : Bool :=
    let t0 : Transcript := Transcript.append Transcript.empty (lines_from 600) in
    let p : TranscriptPage := { start := 0, lines := lines_from 88 } in
    let t : Transcript := Transcript.with_page t0 p in
    Transcript.slice t 0 2 == ["l1", "l2"] && Transcript.slice t 86 3 == ["l87", "l88", "l89"]

#[test]
def test_uncovered_indices_are_placeholders : Bool :=
    let t : Transcript := Transcript.append Transcript.empty (lines_from 600) in
    Transcript.slice t 0 2 == ["", ""] && Transcript.slice t 86 4 == ["", "", "l89", "l90"]

#[test]
def test_slice_clamps_outside_the_transcript : Bool :=
    let t : Transcript := Transcript.append Transcript.empty ["a"] in
    Transcript.slice t 0 50 == ["a"] && Transcript.slice t 5 2 == List.empty

// ── codecs ────────────────────────────────────────────────────────────

#[test]
def test_block_json_roundtrip : Bool :=
    match Json.parse (Json.to_string (Store.encode_block 3 120 ["x", "y"])) {
        Result.err _ => false,
        Result.ok j => match Store.decode_block j {
            Result.err _ => false,
            Result.ok pr =>
                let b : StoreIndexBlock := pair_of pr in
                b.seq == 3 && b.start == 120 && b.count == 2 && lines_of pr == ["x", "y"],
        },
    }

#[test]
def test_index_json_roundtrip : Bool :=
    let b : StoreIndexBlock := { seq := 1, start := 0, count := 4 } in
    let i : StoreIndex := { total := 4, next_seq := 2, blocks := [b] } in
    match Json.parse (Json.to_string (Store.encode_index i)) {
        Result.err _ => false,
        Result.ok j => match Store.decode_index j {
            Result.err _ => false,
            Result.ok i2 => i2.total == 4 && i2.next_seq == 2 && List.length i2.blocks == 1,
        },
    }

def test_cfg : ProviderConfig :=
    { base_url := "http://localhost:11434", model := "m", api_key_env := "K", max_tokens := 8, wire := Wire.mock }

def test_usage : Usage := { input_tokens := 1, output_tokens := 2, cached_tokens := 3 }

def test_session : Session :=
    { config := test_cfg, system_prompt := "s", tools := List.empty, history := List.empty, turns := 2, spent := test_usage }

#[test]
def test_meta_json_roundtrip : Bool :=
    let m : StoreMeta := { session := test_session, created := 10, updated := 20, history_next := 3 } in
    let j := Store.encode_meta m in
    match Json.parse (Json.to_string j) {
        Result.err _ => false,
        Result.ok j2 => match Store.decode_meta j2 {
            Result.err _ => false,
            Result.ok m => m.created == 10 && m.updated == 20 && m.history_next == 3 && m.session.turns == 2 && List.length m.session.history == 0,
        },
    }

// ── names and paths ───────────────────────────────────────────────────

#[test]
def test_pad12 : Bool :=
    Store.pad12 7 == "000000000007" && Store.pad12 123456789012 == "123456789012"

#[test]
def test_chunks_split_at_block_lines : Bool :=
    let cs : List (List String) := Store.chunks (lines_from 300) in
    List.length cs == 2 && List.length (match cs { List.cons a _ => a, _ => List.empty }) == 256

#[test]
def test_chunks_of_empty_is_empty : Bool :=
    List.length (Store.chunks List.empty) == 0

#[test]
def test_root_override_wins : Bool :=
    match Store.root_of (Option.some "/tmp/override") (Option.some "/home/u") {
        Option.some p => Path.to_string p == "/tmp/override",
        Option.none => false,
    }

#[test]
def test_root_falls_back_to_home : Bool :=
    match Store.root_of Option.none (Option.some "/home/u") {
        Option.some p => Path.to_string p == "/home/u/.weaver/sessions",
        Option.none => false,
    }

#[test]
def test_root_none_without_home : Bool :=
    match Store.root_of Option.none Option.none {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_empty_override_is_unset : Bool :=
    match Store.root_of (Option.some "") (Option.some "/home/u") {
        Option.some p => Path.to_string p == "/home/u/.weaver/sessions",
        Option.none => false,
    }
