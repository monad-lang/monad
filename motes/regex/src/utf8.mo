/// Scalar ranges to UTF-8 byte-range sequences: the `Utf8Sequences`
/// algorithm of Rust's `regex-syntax`.
///
/// A scalar range splits into sequences, each a list of 1-4 byte ranges,
/// such that a byte string is the UTF-8 encoding of a scalar in the range
/// exactly when it matches one sequence. Surrogates (U+D800-U+DFFF) have no
/// UTF-8 encoding and are skipped. The automata built from these never
/// decode.
use std::list {}

def not_mask (m : I64) : I64 := I64.xor m (0 - 1)

/// The UTF-8 bytes of a scalar value, as `I64`s.
pub def encode_scalar (c : I64) : List I64 :=
    if I64.lt c 128 then [c]
    else if I64.lt c 2048 then [I64.or 192 (I64.shr c 6), I64.or 128 (I64.and c 63)]
    else if I64.lt c 65536 then
        [I64.or 224 (I64.shr c 12), I64.or 128 (I64.and (I64.shr c 6) 63), I64.or 128 (I64.and c 63)]
    else
        [I64.or 240 (I64.shr c 18), I64.or 128 (I64.and (I64.shr c 12) 63),
            I64.or 128 (I64.and (I64.shr c 6) 63), I64.or 128 (I64.and c 63)]

/// The sequences for one inclusive scalar range, in ascending order.
pub def utf8_sequences (lo : I64) (hi : I64) : List (List (Pair I64 I64)) :=
    List.reverse (seqs_go (List.cons (Pair.pair lo hi) List.empty) List.empty)

/// The sequences for every range of a class.
pub def class_utf8_sequences (rs : List (Pair I64 I64)) : List (List (Pair I64 I64)) :=
    List.flatten (List.map (fn (r : Pair I64 I64) => utf8_sequences r.first r.second) rs)

/// A worklist: each step either splits the head range (pushing the upper
/// part) or emits it as one sequence. Every split shrinks a range, and a
/// range of one scalar never splits, so the worklist drains.
#[terminating]
def seqs_go (stack : List (Pair I64 I64)) (acc : List (List (Pair I64 I64))) : List (List (Pair I64 I64)) :=
    match stack {
        List.empty => acc,
        List.cons r rest => seq_one r.first r.second rest acc,
    }

#[terminating]
def seq_one (lo : I64) (hi : I64) (rest : List (Pair I64 I64)) (acc : List (List (Pair I64 I64))) : List (List (Pair I64 I64)) :=
    if I64.lt hi lo then seqs_go rest acc
    else if I64.lt lo 57344 && I64.lt 55295 hi then
        seq_one lo 55295 (List.cons (Pair.pair 57344 hi) rest) acc
    else match length_split lo hi {
        Option.some m => seq_one lo m (List.cons (Pair.pair (m + 1) hi) rest) acc,
        Option.none =>
            if I64.lt hi 128 then seqs_go rest (List.cons (List.cons (Pair.pair lo hi) List.empty) acc)
            else seq_bits lo hi rest acc 1,
    }

/// A range straddling an encoding-length boundary splits there.
def length_split (lo : I64) (hi : I64) : Option I64 :=
    if I64.lt lo 128 && I64.lt 127 hi then Option.some 127
    else if I64.lt lo 2048 && I64.lt 2047 hi then Option.some 2047
    else if I64.lt lo 65536 && I64.lt 65535 hi then Option.some 65535
    else Option.none

/// Split until every continuation byte position spans its full 0x80-0xBF
/// range or a single value; then the range is one sequence.
#[terminating]
def seq_bits (lo : I64) (hi : I64) (rest : List (Pair I64 I64)) (acc : List (List (Pair I64 I64))) (i : I64) : List (List (Pair I64 I64)) :=
    if I64.lt 3 i then seqs_go rest (List.cons (zip_ranges (encode_scalar lo) (encode_scalar hi)) acc)
    else
        let m : I64 := I64.shl 1 (6 * i) - 1 in
        if Bool.not (I64.beq (I64.and lo (not_mask m)) (I64.and hi (not_mask m))) then
            if Bool.not (I64.beq (I64.and lo m) 0) then
                seq_one lo (I64.or lo m) (List.cons (Pair.pair (I64.or lo m + 1) hi) rest) acc
            else if Bool.not (I64.beq (I64.and hi m) m) then
                seq_one lo (I64.and hi (not_mask m) - 1) (List.cons (Pair.pair (I64.and hi (not_mask m)) hi) rest) acc
            else seq_bits lo hi rest acc (i + 1)
        else seq_bits lo hi rest acc (i + 1)

#[terminating]
def zip_ranges (a : List I64) (b : List I64) : List (Pair I64 I64) :=
    match a {
        List.empty => List.empty,
        List.cons x xs =>
            match b {
                List.empty => List.empty,
                List.cons y ys => List.cons (Pair.pair x y) (zip_ranges xs ys),
            },
    }
