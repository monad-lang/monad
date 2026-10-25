/// Pure tests for the session store: absolute transcript coordinates,
/// paging slices, JSON codecs (including the v1 -> v2 line migration) and
/// path resolution. No IO.
use weaver::store {
    TLine, TLine.plain, TLine.user_line,
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
def plain_go (i : I64) (n : I64) : List TLine :=
    if n < i then List.empty
    else List.cons (TLine.plain (String.concat "l" (I64.to_string i))) (plain_go (i + 1) n)

def plain_from (n : I64) : List TLine := plain_go 1 n

def plain_lines (ss : List String) : List TLine :=
    match ss {
        List.empty => List.empty,
        List.cons s rest => List.cons (TLine.plain s) (plain_lines rest),
    }

#[partial]
def texts (ls : List TLine) : List String :=
    match ls {
        List.empty => List.empty,
        List.cons l rest => List.cons l.text (texts rest),
    }

def pair_of (pr : Pair StoreIndexBlock (List TLine)) : StoreIndexBlock :=
    match pr { Pair.pair b _ => b }

def lines_of (pr : Pair StoreIndexBlock (List TLine)) : List TLine :=
    match pr { Pair.pair _ ls => ls }

#[partial]
def nth_line (ls : List TLine) (i : I64) : TLine :=
    match ls {
        List.empty => TLine.plain "",
        List.cons l rest => if i < 1 then l else nth_line rest (i - 1),
    }

// ── coordinates ───────────────────────────────────────────────────────

#[test]
def test_append_tracks_total_and_tail : Bool :=
    let t : Transcript := Transcript.append Transcript.empty (plain_lines ["a", "b"]) in
    t.total == 2 && t.tail_start == 0 && List.length t.tail == 2

#[test]
def test_next_block_inserts_a_separator_after_the_first : Bool :=
    let t : Transcript := Transcript.append Transcript.empty (plain_lines ["a"]) in
    let blk : List TLine := Transcript.next_block t (plain_lines ["b"]) in
    List.length blk == 2 && (match blk { List.cons x _ => x.text == "", _ => false })

#[test]
def test_empty_transcript_has_no_separator : Bool :=
    texts (Transcript.next_block Transcript.empty (plain_lines ["a"])) == ["a"]

#[test]
def test_tail_trims_at_tail_lines : Bool :=
    let n : I64 := Store.tail_lines + 100 in
    let t : Transcript := Transcript.append Transcript.empty (plain_from n) in
    List.length t.tail == Store.tail_lines && t.tail_start == 100 && t.total == n

#[test]
def test_slice_reads_the_tail : Bool :=
    let t : Transcript := Transcript.append Transcript.empty (plain_lines ["a", "b", "c"]) in
    texts (Transcript.slice t 0 3) == ["a", "b", "c"] && texts (Transcript.slice t 1 1) == ["b"]

#[test]
def test_page_covers_lines_above_the_tail : Bool :=
    let t0 : Transcript := Transcript.append Transcript.empty (plain_from 600) in
    let p : TranscriptPage := { start := 0, lines := plain_from 88 } in
    let t : Transcript := Transcript.with_page t0 p in
    texts (Transcript.slice t 0 2) == ["l1", "l2"] && texts (Transcript.slice t 86 3) == ["l87", "l88", "l89"]

#[test]
def test_uncovered_indices_are_placeholders : Bool :=
    let t : Transcript := Transcript.append Transcript.empty (plain_from 600) in
    texts (Transcript.slice t 0 2) == ["", ""] && texts (Transcript.slice t 86 4) == ["", "", "l89", "l90"]

#[test]
def test_slice_clamps_outside_the_transcript : Bool :=
    let t : Transcript := Transcript.append Transcript.empty (plain_lines ["a"]) in
    texts (Transcript.slice t 0 50) == ["a"] && List.length (Transcript.slice t 5 2) == 0

// ── codecs ────────────────────────────────────────────────────────────

#[test]
def test_block_json_roundtrip : Bool :=
    let ls : List TLine := [TLine.user_line "x", TLine.plain "y"] in
    match Json.parse (Json.to_string (Store.encode_block 3 120 ls)) {
        Result.err _ => false,
        Result.ok j => match Store.decode_block j {
            Result.err _ => false,
            Result.ok pr =>
                let b : StoreIndexBlock := pair_of pr in
                let decoded : List TLine := lines_of pr in
                let first : TLine := nth_line decoded 0 in
                let second : TLine := nth_line decoded 1 in
                b.seq == 3 && b.start == 120 && b.count == 2
                    && texts decoded == ["x", "y"]
                    && first.user == true
                    && second.user == false,
        },
    }

/// Version-1 blocks stored plain strings; the prefixes migrate on read.
#[test]
def test_v1_block_lines_migrate : Bool :=
    let text : String := "{\"version\":1,\"seq\":1,\"start\":0,\"count\":2,\"lines\":[\"you: hi\",\"assistant: there\"]}" in
    match Json.parse text {
        Result.err _ => false,
        Result.ok j => match Store.decode_block j {
            Result.err _ => false,
            Result.ok pr =>
                let decoded : List TLine := lines_of pr in
                let first : TLine := nth_line decoded 0 in
                let second : TLine := nth_line decoded 1 in
                texts decoded == ["hi", "there"]
                    && first.user == true
                    && second.user == false,
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
    { base_url := "http://localhost:11434", model := "m", api_key_env := "K", max_tokens := 8, wire := Wire.mock, thinking := false }

def test_usage : Usage := { input_tokens := 1, output_tokens := 2, cached_tokens := 3 }

def test_session : Session :=
    { config := test_cfg, system_prompt := "s", tools := List.empty, history := List.empty, turns := 2, spent := test_usage }

#[test]
def test_meta_json_roundtrip : Bool :=
    let m : StoreMeta := { session := test_session, created := 10, updated := 20, history_next := 3, history_base := 1, plan := Option.none } in
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
    let cs : List (List TLine) := Store.chunks (plain_from 300) in
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

/// The plan is part of the meta: an encoded plan decodes back exactly,
/// and an absent key (an older session) decodes as none.
#[test]
def test_meta_plan_roundtrip : Bool :=
    let m : StoreMeta := { session := test_session, created := 10, updated := 20, history_next := 3, history_base := 1, plan := Option.some "PLAN: 1) read" } in
    match Store.decode_meta (Store.encode_meta m) {
        Result.err _ => false,
        Result.ok m2 =>
            match m2.plan {
                Option.some p => String.beq p "PLAN: 1) read",
                Option.none => false,
            },
    }
