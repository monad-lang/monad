/// UTF-8 sequences: every scalar of a range encodes into exactly one
/// emitted sequence, and nothing outside it (surrogates included) does.
use regex::utf8 {encode_scalar, utf8_sequences}

#[terminating]
def seq_matches (seq : List (Pair I64 I64)) (bytes : List I64) : Bool :=
    match seq {
        List.empty => List.is_empty bytes,
        List.cons r rest =>
            match bytes {
                List.empty => false,
                List.cons b more => Bool.not (I64.lt b r.first) && Bool.not (I64.lt r.second b) && seq_matches rest more,
            },
    }

#[terminating]
def count_matching (seqs : List (List (Pair I64 I64))) (bytes : List I64) (n : I64) : I64 :=
    match seqs {
        List.empty => n,
        List.cons s rest => count_matching rest bytes (if seq_matches s bytes then n + 1 else n),
    }

def samples : List I64 :=
    [0, 1, 65, 127, 128, 129, 1023, 2047, 2048, 2049, 4095, 4096, 55295, 57344, 57345, 61440,
        65535, 65536, 65537, 98304, 262143, 262144, 1048575, 1048576, 1114111]

/// Each sample inside [lo, hi] matches exactly one sequence; each outside, none.
#[terminating]
def check_range (lo : I64) (hi : I64) (xs : List I64) : Bool :=
    match xs {
        List.empty => true,
        List.cons c rest =>
            let n : I64 := count_matching (utf8_sequences lo hi) (encode_scalar c) 0 in
            let inside : Bool := Bool.not (I64.lt c lo) && Bool.not (I64.lt hi c) in
            I64.beq n (if inside then 1 else 0) && check_range lo hi rest,
    }

#[test]
def test_encode : Bool :=
    I64.beq (List.length (encode_scalar 65)) 1 && I64.beq (List.length (encode_scalar 233)) 2
        && I64.beq (List.length (encode_scalar 26085)) 3 && I64.beq (List.length (encode_scalar 128512)) 4

#[test]
def test_full_range : Bool := check_range 0 1114111 samples

#[test]
def test_partial_ranges : Bool :=
    check_range 100 3000 samples && check_range 2049 65537 samples && check_range 4096 4096 samples
        && check_range 1000 1048576 samples && check_range 129 129 samples

#[test]
def test_surrogates_have_no_sequence : Bool :=
    I64.beq (List.length (utf8_sequences 55296 57343)) 0

#[test]
def test_ascii_is_one_sequence : Bool :=
    I64.beq (List.length (utf8_sequences 0 127)) 1
