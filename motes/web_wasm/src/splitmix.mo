/// SplitMix64 (Steele/Lea/Flood): a pure, seeded 64-bit generator for
/// reproducible generation and deterministic tests. Kept in its own module
/// (no web imports) so it runs and tests natively. The shifts are division
/// by powers of two until `U64.shr` is public.

pub struct SplitMix64 {
    state : U64
}

pub def SplitMix64.seed (seed : U64) : SplitMix64 := { state := seed }

/// `z ^ (z >> shift)`, with the shift spelled as its power of two until
/// `U64.shr` is public.
def splitmix_xor_shift (z : U64) (shift_pow2 : U64) : U64 :=
    U64.xor z (U64.div z shift_pow2)

/// The next word and the advanced state. SplitMix64's mix is
/// `z ^= z >> k; z *= c` at (k, c) = (30, C1), (27, C2), then
/// `z ^ (z >> 31)`.
pub def SplitMix64.next (r : SplitMix64) : Pair SplitMix64 U64 :=
    let s : U64 := U64.add r.state 0x9E3779B97F4A7C15u64 in
    let z1 : U64 := splitmix_xor_shift s 1073741824u64 in
    let z2 : U64 := z1 * 0xBF58476D1CE4E5B9u64 in
    let z3 : U64 := splitmix_xor_shift z2 134217728u64 in
    let z4 : U64 := z3 * 0x94D049BB133111EBu64 in
    let out : U64 := splitmix_xor_shift z4 2147483648u64 in
    Pair.pair (SplitMix64.seed s) out

/// A value in `[0, n)`, or 0 when `n <= 0`.
pub def SplitMix64.below (r : SplitMix64) (n : I64) : Pair SplitMix64 I64 :=
    if I64.lt n 1
    then Pair.pair r 0i64
    else
        match SplitMix64.next r {
            Pair.pair r2 v => Pair.pair r2 (U64.to_i64 (U64.mod v (I64.to_u64 n))),
        }
