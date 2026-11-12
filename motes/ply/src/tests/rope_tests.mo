// Phase 1's rope gate: round-trip, chunking, replace-oracle, line index.
//
// EVERY EXPECTATION IS AN OFFSET OR A CHUNK COUNT COUNTED BY HAND where a
// fixture's shape decides it (the toolkit test suite's discipline), and
// the two properties that could silently break -- a leaf boundary landing
// inside a multi-byte character, and `replace` disagreeing with a flat
// String doing the same edits -- are pinned by comparing against
// hand-computed oracles, not against the rope's own arithmetic.
//
// Field reads inside `#[test]` defs go through the typed accessors below
// (`rp_*`), never inline, per this repo's recorded `#[test]` +
// struct-field codegen hazard. The `rp_` prefix is collision-avoiding:
// whole-program scope is shared with every other mote's tests.

use std::io {IO.current_time}
use init::shared {Shared}
use lib::types {Rope}
use lib::rope {Rope.bytes, Rope.of_string, Rope.to_string, Rope.slice, Rope.split_at,
    Rope.replace, Rope.line_start, Rope.newlines, Rope.leaf_count,
    Rope.needs_balance, Rope.balance, Rope.concat, Rope.char_start}

// --- Accessors: one read, one binding, each used once ---

/// The rope's byte count.
def rp_bytes (r : Rope) : I64 := Rope.bytes r

/// The rope's newline count.
def rp_newlines (r : Rope) : I64 := Rope.newlines r

/// The rope's leaf count -- the chunking witness. A single leaf means
/// `Rope.of_string` never chunked; more means it did, and the round-trip
/// tests below are what prove the chunking did not lose a byte.
def rp_leaves (r : Rope) : I64 := Rope.leaf_count r

/// `n` copies of `s` in a row -- the generated-input builder. The 1 MiB
/// fixture and the chunk-scale fixtures come from here; no IO, so the
/// suite runs on both hosts and in the interpreter.
#[terminating]
def rp_repeat (s : String) (n : I64) : String :=
    if I64.beq n 0 then "" else String.concat s (rp_repeat s (n - 1))

// ── Round-trip: the whole gate's backbone ────────────────────────────────

#[test]
def test_roundtrip_ascii : Bool :=
    String.beq (Rope.to_string (Rope.of_string "hello, ply!")) "hello, ply!"

/// The empty string is a rope with no bytes and no newlines, and
/// round-trips through the empty leaf.
#[test]
def test_roundtrip_empty : Bool :=
    let r : Rope := Rope.of_string "" in
    String.beq (Rope.to_string r) "" && I64.beq (rp_bytes r) 0

/// Multi-byte text round-trips byte-for-byte: `é` (2 bytes), `—` (3),
/// `🧵` (4, astral). The astral case is the one that separates "counts
/// characters" from "counts bytes" implementations.
#[test]
def test_roundtrip_multibyte : Bool :=
    let text : String := "café — 🧵 end" in
    String.beq (Rope.to_string (Rope.of_string text)) text

#[test]
def test_bytes_counts_bytes_not_characters : Bool :=
    // "café" is c(1) a(1) f(1) é(2) = 5 bytes, 4 characters; "🧵" is 4
    // bytes, 1 character, 2 UTF-16 units. The BYTE count is the one the
    // rope stores.
    I64.beq (rp_bytes (Rope.of_string "café")) 5
        && I64.beq (rp_bytes (Rope.of_string "🧵")) 4

/// The 1 MiB gate case: a generated input over the chunk target, brought
/// back through `to_string` and compared to its source. Interpreted this
/// is the suite's slow test; it is the one that catches a chunker that
/// drops or duplicates a boundary byte a thousand leaves in.
#[test]
def test_roundtrip_one_mib : Bool :=
    let big : String := rp_repeat "0123456789abcdef" 65536 in
    let r : Rope := Rope.of_string big in
    I64.beq (rp_bytes r) 1048576 && String.beq (Rope.to_string r) big

// ── Chunking: the UTF-8-splits-never rule ────────────────────────────────

/// CHUNKING IS LINEAR IN THE TEXT, not quadratic.
///
/// `Rope.of_string`'s chunker scans each chunk for a newline to cut on, and
/// it used to probe every byte with `String.get`, whose compiled general
/// path calls `monad_string_length` -- a full `strlen` -- per call. One
/// chunk therefore cost O(chunk x strlen(whole tail)), so the whole
/// conversion was O(n^2): measured on the built binary, a 638 KB file spent
/// 14.5 s inside `Rope.of_string`, which was the ENTIRE cost of opening it.
///
/// The assertion is a RATIO, not a wall-clock bound -- a millisecond
/// threshold would be flaky on a loaded machine. Two sizes 8x apart should
/// cost about 8x if linear and about 64x if quadratic; the bound is 32, so
/// only a real complexity change trips it.
#[test]
def test_of_string_is_linear_not_quadratic : IO Bool := do {
    let _ <- rp_warm;
    let small : String := rp_block 8000;
    let large : String := rp_block 64000;
    let t1 <- IO.current_time;
    let one : Rope := Rope.of_string small;
    let t2 <- IO.current_time;
    let big : Rope := Rope.of_string large;
    let t3 <- IO.current_time;
    let correct : Bool :=
        Bool.and (I64.beq (rp_bytes one) 8000) (I64.beq (rp_bytes big) 64000);
    let grew : Bool := rp_linear_enough (rp_elapsed t1 t2) (rp_elapsed t2 t3);
    return (Bool.and correct grew)
}

/// The elapsed milliseconds between two `IO.current_time` readings, floored
/// at 1 so the ratio below stays meaningful for a sub-millisecond
/// measurement -- a floor can only make the assertion STRICTER.
///
/// A separate def, not an inline `let ... := if ... in` in the test body: a
/// pure `let ... in` inside a do-block is a recorded self-hosted load
/// failure when the block also has `let ... <-` binds.
def rp_elapsed (a : I64) (b : I64) : I64 :=
    let d : I64 := b - a in
    if d < 1 then 1 else d

/// Is `big` under 32x `small`? Two sizes 8x apart cost ~8x when linear and
/// ~64x when quadratic, so 32 separates them with room for noise either way.
def rp_linear_enough (small_ms : I64) (big_ms : I64) : Bool :=
    big_ms < small_ms * 32

/// One warm-up conversion, so the first timed call does not pay for
/// anything allocated lazily on the way.
def rp_warm : IO Unit := do {
    let _r : Rope := Rope.of_string (rp_block 500);
    return unit
}

/// `n` bytes of newline-free ASCII. No newline means the chunker takes its
/// plain-boundary path every time, which is the shape that scanned
/// furthest. Built right-nested so the fixture itself is not the quadratic
/// part of the measurement.
#[terminating]
def rp_block (n : I64) : String :=
    if Bool.not (0 < n) then "" else String.concat "x" (rp_block (n - 1))

/// A string over the chunk target is more than one leaf; under it, one.
/// This is the precondition the multi-byte round-trips below only mean
/// anything against: a chunked rope COULD have split a character, a
/// single-leaf rope never had the chance.
#[test]
def test_over_target_chunks : Bool :=
    let big : String := rp_repeat "ab" 800 in
    Bool.not (I64.beq (rp_leaves (Rope.of_string big)) 1)

#[test]
def test_under_target_is_one_leaf : Bool :=
    let small : String := rp_repeat "ab" 100 in
    I64.beq (rp_leaves (Rope.of_string small)) 1

/// THE UTF-8 PIN: 700 `é` (2 bytes each) is 1400 bytes, so the chunker
/// must cut -- and every cut is at a character start, so the round trip
/// still equals the source. A chunker cutting at the byte target alone
/// lands mid-`é` and this comparison sees replacement characters, not a
/// match.
#[test]
def test_chunking_never_splits_multibyte : Bool :=
    let big : String := rp_repeat "é" 700 in
    let r : Rope := Rope.of_string big in
    Bool.not (I64.beq (rp_leaves r) 1) && String.beq (Rope.to_string r) big

/// The astral case on its own: 400 `🧵` (4 bytes each) is 1600 bytes.
#[test]
def test_chunking_never_splits_astral : Bool :=
    let big : String := rp_repeat "🧵" 400 in
    let r : Rope := Rope.of_string big in
    Bool.not (I64.beq (rp_leaves r) 1) && String.beq (Rope.to_string r) big

/// Newline-preferred chunking: 200 ten-byte lines is 2200 bytes, so it
/// chunks, and the newline count survives the tree exactly (a cached
/// total that drifts from the leaves shows up here first).
#[test]
def test_newline_count_over_a_chunked_tree : Bool :=
    let big : String := rp_repeat "abcdefghij\n" 200 in
    let r : Rope := Rope.of_string big in
    Bool.not (I64.beq (rp_leaves r) 1) && I64.beq (rp_newlines r) 200

// ── slice ────────────────────────────────────────────────────────────────

#[test]
def test_slice_mid : Bool := String.beq (Rope.slice (Rope.of_string "abcdefgh") 2 3) "cde"

/// A slice crossing a chunk boundary -- the case a flat-leaf
/// implementation cannot get wrong and a tree can.
#[test]
def test_slice_across_leaves : Bool :=
    let big : String := rp_repeat "xy" 700 in
    let r : Rope := Rope.of_string big in
    // byte 1024 is the first boundary's neighbourhood; slice a window
    // that straddles it either way
    String.beq (Rope.slice r 1020 8) "xyxyxyxy"

#[test]
def test_slice_empty : Bool := String.beq (Rope.slice (Rope.of_string "abc") 1 0) ""

// ── split_at ─────────────────────────────────────────────────────────────

#[test]
def test_split_interior : Bool :=
    match Rope.split_at (Rope.of_string "abcdef") 3 {
        Pair.pair a b => String.beq (Rope.to_string a) "abc" && String.beq (Rope.to_string b) "def"
    }

#[test]
def test_split_at_zero : Bool :=
    match Rope.split_at (Rope.of_string "abc") 0 {
        Pair.pair a b => String.beq (Rope.to_string a) "" && String.beq (Rope.to_string b) "abc"
    }

#[test]
def test_split_at_end : Bool :=
    match Rope.split_at (Rope.of_string "abc") 3 {
        Pair.pair a b => String.beq (Rope.to_string a) "abc" && String.beq (Rope.to_string b) ""
    }

/// A split at a chunk boundary inside a big rope: both halves reassemble
/// into the source -- the persistence property the edit path depends on.
#[test]
def test_split_chunked : Bool :=
    let big : String := rp_repeat "ab" 800 in
    let r : Rope := Rope.of_string big in
    match Rope.split_at r 1000 {
        Pair.pair a b => String.beq (String.concat (Rope.to_string a) (Rope.to_string b)) big
    }

// ── replace: the flat-String oracle ──────────────────────────────────────

/// The oracle itself: replace on a flat String, to compare the rope
/// against. Hand-rolled with slice/concat because that is all the
/// prelude gives; the point is that it is OBVIOUSLY right, not fast.
def rp_flat_replace (s : String) (start : I64) (stop : I64) (text : String) : String :=
    String.concat (String.slice s 0 start) (String.concat text (String.drop stop s))

#[test]
def test_replace_replaces : Bool :=
    let r : Rope := Rope.of_string "hello world" in
    String.beq (Rope.to_string (Rope.replace r 6 11 "ply")) "hello ply"

#[test]
def test_replace_insert : Bool :=
    // stop == start is an insert
    String.beq (Rope.to_string (Rope.replace (Rope.of_string "ab") 1 1 "XY")) "aXYb"

#[test]
def test_replace_delete : Bool :=
    // text == "" is a delete
    String.beq (Rope.to_string (Rope.replace (Rope.of_string "abcdef") 2 5 "")) "abf"

/// THE ORACLE PIN: a scripted sequence of replaces, rope against flat
/// String, one edit at a time. The flat side is the sequence a plain
/// `String` editor would produce; the rope must agree at every step,
/// including the multi-byte step.
#[test]
def test_replace_agrees_with_flat_oracle : Bool :=
    let shared : Shared (List (Pair (Pair I64 I64) String)) := Shared.of
        [Pair.pair (Pair.pair 0 0) "The ", Pair.pair (Pair.pair 8 13) "rope",
            Pair.pair (Pair.pair 4 9) "a chunked", Pair.pair (Pair.pair 19 19) "!"] in
    let flat : String := rp_oracle_fold (Shared.get shared) "text is bytes" in
    let roped : String := rp_rope_fold (Shared.get shared) "text is bytes" in
    String.beq roped flat

/// One edit: the flat side.
def rp_oracle_step (acc : String) (e : Pair (Pair I64 I64) String) : String :=
    match e {
        Pair.pair span t =>
            match span {
                Pair.pair a b => rp_flat_replace acc a b t
            }
    }

/// One edit: the rope side.
def rp_rope_step (acc : String) (e : Pair (Pair I64 I64) String) : String :=
    match e {
        Pair.pair span t =>
            match span {
                Pair.pair a b => Rope.to_string (Rope.replace (Rope.of_string acc) a b t)
            }
    }

#[terminating]
def rp_oracle_fold (edits : List (Pair (Pair I64 I64) String)) (acc : String) : String :=
    match edits {
        List.empty => acc,
        List.cons e rest => rp_oracle_fold rest (rp_oracle_step acc e)
    }

#[terminating]
def rp_rope_fold (edits : List (Pair (Pair I64 I64) String)) (acc : String) : String :=
    match edits {
        List.empty => acc,
        List.cons e rest => rp_rope_fold rest (rp_rope_step acc e)
    }

/// Replace on a CHUNKED rope agrees with the oracle too -- the tree walk,
/// not just the single-leaf case.
#[test]
def test_replace_chunked_agrees : Bool :=
    let big : String := rp_repeat "abcdefgh" 200 in
    let roped : String := Rope.to_string (Rope.replace (Rope.of_string big) 900 1200 "XY") in
    String.beq roped (rp_flat_replace big 900 1200 "XY")

/// A replace inside multi-byte text: offsets on character boundaries
/// (5 = after "caf", the `é` start... "café" -- é starts at byte 3) stay
/// whole. Hand-checked: "café au lait" -- replace bytes [3,5) ("é ")
/// with "é, " keeps the bytes valid.
#[test]
def test_replace_multibyte_boundaries : Bool :=
    let s : String := "café au lait" in
    String.beq (Rope.to_string (Rope.replace (Rope.of_string s) 5 8 "XY")) (rp_flat_replace s 5 8 "XY")

// ── line_start: the newline-scan oracle ──────────────────────────────────

#[test]
def test_line_start_small : Bool :=
    let r : Rope := Rope.of_string "ab\ncd\nef" in
    I64.beq (Rope.line_start r 0) 0 && I64.beq (Rope.line_start r 1) 3
        && I64.beq (Rope.line_start r 2) 6

/// The newline-scan oracle: find the line start by walking a flat string
/// counting `\n`s, and compare `line_start`'s descent against it for a
/// chunked, many-line rope. Line 250 of 500 three-byte lines ("xy\n"
/// repeated): byte 750 is its start.
#[test]
def test_line_start_agrees_with_scan : Bool :=
    let big : String := rp_repeat "xy\n" 500 in
    let r : Rope := Rope.of_string big in
    I64.beq (Rope.line_start r 250) (rp_scan_line big 250)

/// The hand-rolled scan: offset of the byte after the nth `\n`.
#[terminating]
def rp_scan_line (s : String) (n : I64) : I64 :=
    rp_scan_go (String.to_list s) 0 0 n

#[terminating]
def rp_scan_go (bs : List U8) (i : I64) (seen : I64) (n : I64) : I64 :=
    match bs {
        List.cons b rest =>
            if U8.beq b 10u8 && I64.beq seen (n - 1)
            then i + 1
            else if U8.beq b 10u8
            then rp_scan_go rest (i + 1) (seen + 1) n
            else rp_scan_go rest (i + 1) seen n,
        List.empty => i
    }

/// A line past the end clamps to the last line's start, and line 0 is
/// always offset 0 -- the total-input rule (the same one
/// `toolkit::text`'s cursor scan states for client input).
#[test]
def test_line_start_clamps : Bool :=
    let r : Rope := Rope.of_string "ab\ncd" in
    I64.beq (Rope.line_start r 99) 3 && I64.beq (Rope.line_start r 0) 0

/// A leading newline: line 1 starts at 1 (the empty line 0 is just the
/// terminator). Editors disagree here; pinning it makes the view's row
/// arithmetic testable.
#[test]
def test_line_start_empty_first_line : Bool :=
    I64.beq (Rope.line_start (Rope.of_string "\nabc") 1) 1

// ── char boundaries ───────────────────────────────────────────────────────

#[test]
def test_char_start_accepts_ascii : Bool :=
    Rope.char_start (Rope.of_string "abc") 0 && Rope.char_start (Rope.of_string "abc") 1

#[test]
def test_char_start_accepts_end : Bool := Rope.char_start (Rope.of_string "abc") 3

/// A continuation byte's offset is NOT a boundary -- the UTF-8-offsets
/// rejection rule's test case ("é"'s second byte).
#[test]
def test_char_start_rejects_continuation : Bool :=
    Bool.not (Rope.char_start (Rope.of_string "café") 4)

#[test]
def test_char_start_accepts_lead : Bool :=
    Rope.char_start (Rope.of_string "café") 3

// ── balance ───────────────────────────────────────────────────────────────

/// A rope built by `of_string` is already balanced (the bottom-up merge),
/// so `needs_balance` is false and `balance` is the identity.
#[test]
def test_built_rope_is_balanced : Bool :=
    let big : String := rp_repeat "ab" 800 in
    Bool.not (Rope.needs_balance (Rope.of_string big))

/// A right-spine skew -- one leaf consed onto a rope, repeatedly -- is
/// deeper than the limit, and `balance` flattens it back under.
#[test]
def test_balance_flattens_a_skew : Bool :=
    let big : String := rp_repeat "ab" 2000 in
    let r : Rope := Rope.of_string big in
    let skewed : Rope := Rope.concat (Rope.leaf "z") r in
    let deep : Rope := Rope.concat (Rope.leaf "y") skewed in
    Bool.not (Rope.needs_balance deep) || Bool.not (Rope.needs_balance (Rope.balance deep))
