/// Isolated micro-benchmark for `std/map.mo`'s `HashMap.get_bucket`/
/// `set_bucket` dispatch cost specifically — decoupled from `HashMap`'s
/// hashing/insert/lookup logic (unlike `bench/scope_lookup.mo`, whose
/// `hash build`/`hash lookup` numbers mix dispatch cost together with
/// allocation (each `set_bucket` call rebuilds a fresh 16-field
/// `Buckets16` regardless of dispatch depth) and hashing cost). Built
/// specifically to answer "does flattening the 16-way `if`/`else`
/// dispatch chain into two ≤8-deep tiers (`get_bucket_lo`/`hi`,
/// `set_bucket_lo`/`hi`) actually help" — per this project's own
/// established rule (see `AGENTS.md`'s BTreeMap-regression writeup):
/// measure, don't assume Big-O/chain-depth reasoning translates to a
/// real wall-clock win in this interpreter.
///
/// Drives a high call VOLUME (`n` in the tens of thousands) of pure
/// `get_bucket`/`set_bucket` calls, cycling `idx` 0..15 so every tier
/// (lo/hi) and every position within each tier gets equal exposure —
/// isolating per-call dispatch cost from the one-time overhead of a
/// smaller test.
use std.map {}
use std.bench {now, report, since}
use std.list {length}

#[terminating]
def set_loop (i : I64) (n : I64) (idx : U64) (b : Bucket16 (Bucket16 (List (Pair I64 I64)))) : Bucket16 (Bucket16 (List (Pair I64 I64))) :=
    if I64.beq i n then b
    else
        let next_idx : U64 := U64.mod (U64.add idx 1u64) 256u64 in
        set_loop (i + 1) n next_idx (HashMap.set_bucket b idx (List.cons (Pair.pair i i) List.empty))

#[terminating]
def get_loop (i : I64) (n : I64) (idx : U64) (b : Bucket16 (Bucket16 (List (Pair I64 I64)))) (acc : I64) : I64 :=
    if I64.beq i n then acc
    else
        let next_idx : U64 := U64.mod (U64.add idx 1u64) 256u64 in
        let bucket : List (Pair I64 I64) := HashMap.get_bucket b idx in
        get_loop (i + 1) n next_idx b (acc + List.length bucket)

def run_bench (n : I64) (label : String) : IO Bool := do {
    let empty : Bucket16 (Bucket16 (List (Pair I64 I64))) := HashMap.empty_buckets;
    let set_start : I64 <- Bench.now;
    let b := set_loop 0 n 0u64 empty;
    let set_elapsed : I64 <- Bench.since set_start;
    Bench.report (String.concat "set_bucket " label) set_elapsed;
    let get_start : I64 <- Bench.now;
    let total := get_loop 0 n 0u64 b 0;
    let get_elapsed : I64 <- Bench.since get_start;
    Bench.report (String.concat "get_bucket " label) get_elapsed;
    // `total` just needs to be deterministic and non-degenerate (proof
    // the loop actually ran and touched real bucket content), not a
    // specific value -- every bucket holds exactly one 1-element list
    // by the time `get_loop` reads it back (cycling `idx` overwrites
    // each bucket's slot every 16 calls), so `total` == the number of
    // buckets actually read (== n once n >= 16, since every idx 0..15
    // is visited before any repeats).
    return (I64.gt total 0)
}

#[test]
def bench_bucket_dispatch_50k : IO Bool := run_bench 50000 "n=50000"

#[test]
def bench_bucket_dispatch_200k : IO Bool := run_bench 200000 "n=200000"
