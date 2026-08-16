/// Benchmark: `List`+linear-scan vs `std/map.mo`'s `BTreeMap` (AVL
/// tree) vs its `HashMap` (fixed 16-bucket chaining hash table), at
/// sizes approximating `lang/scope.mo`'s real `ScopeData.def_refs`
/// usage.
///
/// Exists to answer, with real numbers instead of assumption, whether
/// `scope.mo`'s O(n) linear-scan name lookup (`find_def_in_list` and
/// friends, over `ScopeData.def_refs`/`.inductives`/etc., all `List`)
/// is worth replacing with a `Map`. `AGENTS.md` documents a directly
/// relevant prior experiment: swapping `List`+linear-scan for
/// `BTreeMap` in `lang/module.mo`'s dependency-set tracking caused a
/// **25x regression** (2.1s -> 53s), because the self-hosted
/// interpreter's per-call/allocation overhead dominates at the
/// collection sizes actually reached — both `Map` implementations
/// benchmarked here are real, allocation-heavy structures (`BTreeMap`
/// rebuilds nodes through AVL rebalancing on every insert; `HashMap`
/// rebuilds a whole 16-entry bucket array `Buckets16` plus its target
/// bucket's chain on every insert — see `std/map.mo`'s
/// `HashMap.set_bucket`), not a cheap O(1) mutable hash table the way
/// a native `HashMap` would be. This benchmark measures both the
/// *build* cost (matching `scope_data_add_def`'s repeated-cons / a
/// repeated-`Map.insert` pattern) and the *lookup* cost (matching
/// `find_def_in_list` / `Map.lookup`) separately, at a few sizes
/// bracketing a real merged prelude+init `ScopeData` (several hundred
/// entries — init/ alone has ~388 top-level `def`s + ~33
/// `type`/`struct` decls, each contributing more entries for their own
/// constructors).
///
/// `use std.map {}` (empty import) deliberately matches
/// `std/map_tests.mo`'s own documented workaround: explicitly naming
/// any of `std.map`'s `Map`-class-instance exports exposes a
/// pre-existing latent instance/dictionary-resolution bug — everything
/// below remains available regardless via the same always-on mechanism
/// that lets any top-level type/def resolve without being explicitly
/// `use`d.
use std.map {}
use std.bench {now, report}

// --- List: build via repeated cons (matches `scope_data_add_def`'s
// real access pattern), lookup via linear scan (matches
// `find_def_in_list`). ---

#[partial]
def list_build (i : I64) (n : I64) (acc : List (Pair I64 I64)) : List (Pair I64 I64) :=
    if I64.beq i n then acc
    else list_build (i + 1) n (List.cons (Pair.pair i i) acc)

#[partial]
def list_lookup (target : I64) (xs : List (Pair I64 I64)) : Option I64 :=
    match xs {
        List.empty => Option.none,
        List.cons p rest =>
            match p {
                Pair.pair k v =>
                    if I64.beq k target then Option.some v else list_lookup target rest
            }
    }

#[partial]
def list_lookup_range (i : I64) (n : I64) (xs : List (Pair I64 I64)) (hits : I64) : I64 :=
    if I64.beq i n then hits
    else
        match list_lookup i xs {
            Option.some _ => list_lookup_range (i + 1) n xs (hits + 1),
            Option.none => list_lookup_range (i + 1) n xs hits
        }

// --- BTreeMap: build via repeated `Map.insert`, lookup via `Map.lookup`. ---

#[partial]
def map_build (i : I64) (n : I64) (acc : BTreeMap I64 I64) : BTreeMap I64 I64 :=
    if I64.beq i n then acc
    else map_build (i + 1) n (Map.insert i i acc)

#[partial]
def map_lookup_range (i : I64) (n : I64) (m : BTreeMap I64 I64) (hits : I64) : I64 :=
    if I64.beq i n then hits
    else
        match Map.lookup i m {
            Option.some _ => map_lookup_range (i + 1) n m (hits + 1),
            Option.none => map_lookup_range (i + 1) n m hits
        }

// --- HashMap: `std/map.mo` also has a real HashMap (fixed 16-bucket
// chaining hash table, `[Hashable K, BOrd K]` — `I64` already has a
// `Hashable` instance, `init/number.mo`), implementing the same `Map`
// class as `BTreeMap` — build via repeated `Map.insert`, lookup via
// `Map.lookup`, identical shape to the `BTreeMap` benchmark above, just
// a different concrete instance (driven by the `HashMap I64 I64` type
// annotation on `empty`). ---

#[partial]
def hashmap_build (i : I64) (n : I64) (acc : HashMap I64 I64) : HashMap I64 I64 :=
    if I64.beq i n then acc
    else hashmap_build (i + 1) n (Map.insert i i acc)

#[partial]
def hashmap_lookup_range (i : I64) (n : I64) (m : HashMap I64 I64) (hits : I64) : I64 :=
    if I64.beq i n then hits
    else
        match Map.lookup i m {
            Option.some _ => hashmap_lookup_range (i + 1) n m (hits + 1),
            Option.none => hashmap_lookup_range (i + 1) n m hits
        }

// --- Benchmarks: build N entries, then look up all N of them once
// (a full-range pass, not just repeatedly hitting the same key) ---

def run_list_bench (n : I64) (label : String) : Bool :=
    let empty : List (Pair I64 I64) := List.empty in
    let build_start := Bench.now in
    let xs := list_build 0 n empty in
    let build_elapsed := I64.sub Bench.now build_start in
    let logged_build := Bench.report (String.concat "list build  " label) build_elapsed in
    let lookup_start := Bench.now in
    let hits := list_lookup_range 0 n xs 0 in
    let lookup_elapsed := I64.sub Bench.now lookup_start in
    let logged_lookup := Bench.report (String.concat "list lookup " label) lookup_elapsed in
    I64.beq hits n

def run_map_bench (n : I64) (label : String) : Bool :=
    let empty : BTreeMap I64 I64 := Map.empty in
    let build_start := Bench.now in
    let m := map_build 0 n empty in
    let build_elapsed := I64.sub Bench.now build_start in
    let logged_build := Bench.report (String.concat "btree build " label) build_elapsed in
    let lookup_start := Bench.now in
    let hits := map_lookup_range 0 n m 0 in
    let lookup_elapsed := I64.sub Bench.now lookup_start in
    let logged_lookup := Bench.report (String.concat "btree lookup " label) lookup_elapsed in
    I64.beq hits n

def run_hashmap_bench (n : I64) (label : String) : Bool :=
    let empty : HashMap I64 I64 := Map.empty in
    let build_start := Bench.now in
    let m := hashmap_build 0 n empty in
    let build_elapsed := I64.sub Bench.now build_start in
    let logged_build := Bench.report (String.concat "hash  build " label) build_elapsed in
    let lookup_start := Bench.now in
    let hits := hashmap_lookup_range 0 n m 0 in
    let lookup_elapsed := I64.sub Bench.now lookup_start in
    let logged_lookup := Bench.report (String.concat "hash  lookup " label) lookup_elapsed in
    I64.beq hits n

// Sizes kept modest: even a few hundred levels of self-hosted-interpreted
// recursion (`list_build`/`map_build`/`*_lookup_range` are all "obviously"
// tail-recursive by shape, but this interpreter apparently does not TCO
// them) reliably stack-overflows well below `scope.mo`'s real several-
// hundred-entry sizes — n=1000 overflowed even under `cargo run -- test`'s
// own 64MB-stack test-worker threads. That in itself is real, relevant
// data: it confirms per-call native-stack cost is high enough that even
// "just build a scope of realistic size" is already expensive/risky in
// this interpreter, regardless of which data structure is used.
#[test]
def bench_list_50 : Bool := run_list_bench 50 "n=50"

#[test]
def bench_map_50 : Bool := run_map_bench 50 "n=50"

#[test]
def bench_hashmap_50 : Bool := run_hashmap_bench 50 "n=50"

#[test]
def bench_list_100 : Bool := run_list_bench 100 "n=100"

#[test]
def bench_map_100 : Bool := run_map_bench 100 "n=100"

#[test]
def bench_hashmap_100 : Bool := run_hashmap_bench 100 "n=100"

#[test]
def bench_list_200 : Bool := run_list_bench 200 "n=200"

#[test]
def bench_map_200 : Bool := run_map_bench 200 "n=200"

#[test]
def bench_hashmap_200 : Bool := run_hashmap_bench 200 "n=200"
