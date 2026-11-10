/// `lib::splitmix` is pure, so these run natively (no web externs).

use lib::splitmix {SplitMix64, SplitMix64.seed, SplitMix64.next, SplitMix64.below}

#[test]
def test_splitmix_first_word_for_seed_zero : Bool :=
    match SplitMix64.next (SplitMix64.seed 0u64) {
        Pair.pair _ v => U64.beq v 0xE220A8397B1DCDAFu64,
    }

#[test]
def test_splitmix_is_deterministic : Bool :=
    let a : SplitMix64 := SplitMix64.seed 12345u64 in
    let b : SplitMix64 := SplitMix64.seed 12345u64 in
    match SplitMix64.next a {
        Pair.pair _ av =>
            match SplitMix64.next b {
                Pair.pair _ bv => U64.beq av bv,
            },
    }

#[test]
def test_splitmix_different_seeds_differ : Bool :=
    let a : SplitMix64 := SplitMix64.seed 1u64 in
    let b : SplitMix64 := SplitMix64.seed 2u64 in
    match SplitMix64.next a {
        Pair.pair _ av =>
            match SplitMix64.next b {
                Pair.pair _ bv => Bool.not (U64.beq av bv),
            },
    }

#[test]
def test_splitmix_below_is_in_range : Bool :=
    let r : SplitMix64 := SplitMix64.seed 99u64 in
    match SplitMix64.below r 16 {
        Pair.pair _ v => Bool.not (I64.lt v 0) && I64.lt v 16,
    }

#[test]
def test_splitmix_below_nonpositive_is_zero : Bool :=
    match SplitMix64.below (SplitMix64.seed 1u64) 0 {
        Pair.pair _ v => I64.beq v 0,
    }

#[test]
def test_splitmix_state_advances : Bool :=
    match SplitMix64.next (SplitMix64.seed 7u64) {
        Pair.pair r2 _ =>
            match SplitMix64.next r2 {
                Pair.pair _ v2 => Bool.not (U64.beq v2 7u64),
            },
    }
