/// The regex mote's Phase 0 perf spike (plans/library-ideas/regex.md):
/// the costs its Pike VM is built on, measured before the engine exists.
///
/// - haystack setup: `String.to_list` over 1 MB and a walk of the list (the
///   compiled `String.get` pays a `strlen` per non-zero index, and
///   `Array.from_list` fills with copying `Array.set`s -- O(n^2) -- so a
///   search walks a `List U8` cursor instead);
/// - `Array.from_list` at 64, 1024 and 4096 elements (the quadratic, measured);
/// - `Array.get_or` throughput;
/// - `Array.set` (copy-on-write) at 16, 32 and 64 elements;
/// - one Pike-VM-shaped dedup step (insert m/2 states, test m) for a flat
///   `Array I64` word bitset versus a sorted-list merge-dedup.
///
/// Gated on MONAD_BENCH=1 (`view_bench.mo`'s rule): the sweep runs every
/// test under `bench/`, and an assertion-free measurement should not.
///
/// ```text
/// MONAD_BENCH=1 monad test bench/src/regex_spike.mo
/// ```
use std::bench {Bench.now}
use std::array {Array}
use std::list {}
open IO {get_env, println}

def bench_enabled : IO Bool := do {
    let v <- get_env "MONAD_BENCH";
    return (match v { Option.some _ => true, Option.none => false })
}

def report (label : String) (elapsed_ms : I64) (ops : I64) : IO Unit :=
    println (String.concat_list [label, ": ", I64.to_string elapsed_ms, " ms, ",
        I64.to_string (I64.div (I64.mul elapsed_ms 1000000) ops), " ns/op"])

/// `s` doubled `k` times: `String.repeat` is a linear chain of concats, so
/// a 1 MB input built with it is quadratic.
#[terminating]
def doubled (s : String) (k : I64) : String :=
    if I64.lt 0 k then doubled (String.concat s s) (k - 1) else s

// ─── Array reads ───

#[terminating]
def sum_list (xs : List U8) (acc : I64) : I64 :=
    match xs {
        List.empty => acc,
        List.cons b rest => sum_list rest (acc + U8.to_i64 b),
    }

#[terminating]
def sum_array (a : Array I64) (i : I64) (n : I64) (acc : I64) : I64 :=
    if I64.lt i n then sum_array a (i + 1) n (acc + Array.get_or a (I64.and i 63) 0)
    else acc

#[terminating]
def iota (i : I64) (n : I64) (acc : List I64) : List I64 :=
    if I64.lt i n then iota (i + 1) n (List.cons i acc) else acc

def time_from_list (n : I64) : IO Unit := do {
    let xs := iota 0 n List.empty;
    let t0 <- Bench.now;
    let a : Array I64 := Array.from_list xs;
    let t1 <- Bench.now;
    report (String.concat_list ["Array.from_list n=", I64.to_string n, " (", I64.to_string (Array.length a), ")"]) (t1 - t0) n
}

// ─── Array.set ───

#[terminating]
def set_loop (a : Array I64) (len : I64) (i : I64) (n : I64) : Array I64 :=
    if I64.lt i n then set_loop (Array.set a (I64.rem i len) i) len (i + 1) n
    else a

// ─── Thread-set candidates ───

/// A pseudo-random state id in [0, m): an LCG, so both candidates see the
/// same sequence.
def lcg (x : I64) : I64 := I64.and (x * 6364136223846793005 + 1442695040888963407) 9223372036854775807

def bit_test (words : Array I64) (pc : I64) : Bool :=
    let w : I64 := Array.get_or words (I64.shr pc 6) 0 in
    Bool.not (I64.beq (I64.and w (I64.shl 1 (I64.and pc 63))) 0)

def bit_insert (words : Array I64) (pc : I64) : Array I64 :=
    let wi : I64 := I64.shr pc 6 in
    let w : I64 := Array.get_or words wi 0 in
    Array.set words wi (I64.or w (I64.shl 1 (I64.and pc 63)))

/// One step: insert each of `k` pseudo-random pcs unless already present.
#[terminating]
def bit_step (words : Array I64) (m : I64) (seed : I64) (k : I64) (hits : I64) : I64 :=
    if I64.lt 0 k then
        let s : I64 := lcg seed in
        let pc : I64 := I64.rem s m in
        if bit_test words pc then bit_step words m s (k - 1) (hits + 1)
        else bit_step (bit_insert words pc) m s (k - 1) hits
    else hits

#[terminating]
def bit_steps (m : I64) (steps : I64) (acc : I64) : I64 :=
    if I64.lt 0 steps then
        bit_steps m (steps - 1) (acc + bit_step (Array.new (I64.div (m + 63) 64) 0) m steps (I64.div m 2) 0)
    else acc

/// Sorted insert: the list a closure would keep, and whether `pc` was
/// already in it (the list comes back unchanged then).
#[terminating]
def sorted_insert (xs : List I64) (pc : I64) : Pair (List I64) Bool :=
    match xs {
        List.empty => Pair.pair [pc] false,
        List.cons x rest =>
            if I64.beq x pc then Pair.pair (List.cons x rest) true
            else if I64.lt pc x then Pair.pair (List.cons pc (List.cons x rest)) false
            else match sorted_insert rest pc {
                Pair.pair r hit => Pair.pair (List.cons x r) hit,
            },
    }

#[terminating]
def list_step (xs : List I64) (m : I64) (seed : I64) (k : I64) (hits : I64) : I64 :=
    if I64.lt 0 k then
        let s : I64 := lcg seed in
        match sorted_insert xs (I64.rem s m) {
            Pair.pair ys hit => list_step ys m s (k - 1) (if hit then hits + 1 else hits),
        }
    else hits

#[terminating]
def list_steps (m : I64) (steps : I64) (acc : I64) : I64 :=
    if I64.lt 0 steps then list_steps m (steps - 1) (acc + list_step List.empty m steps (I64.div m 2) 0)
    else acc

def time_sets (m : I64) (steps : I64) : IO Unit := do {
    let ops : I64 := steps * I64.div m 2;
    let t0 <- Bench.now;
    let h1 := bit_steps m steps 0;
    let t1 <- Bench.now;
    report (String.concat_list ["bitset  m=", I64.to_string m, " hits=", I64.to_string h1]) (t1 - t0) ops;
    let t2 <- Bench.now;
    let h2 := list_steps m steps 0;
    let t3 <- Bench.now;
    report (String.concat_list ["sorted  m=", I64.to_string m, " hits=", I64.to_string h2]) (t3 - t2) ops
}

def time_set_len (len : I64) : IO Unit := do {
    let n : I64 := 1000000;
    let t0 <- Bench.now;
    let a := set_loop (Array.new len 0) len 0 n;
    let t1 <- Bench.now;
    report (String.concat_list ["Array.set len=", I64.to_string len, " (", I64.to_string (Array.get_or a 0 0), ")"]) (t1 - t0) n
}

#[test]
def bench_regex_spike : IO Bool := do {
    let on <- bench_enabled;
    if Bool.not on then return true
    else do {
        let mb : String := doubled "abcdefghijklmnopqrstuvwxyz012345" 15;
        let n : I64 := String.length mb;
        let t0 <- Bench.now;
        let hay : List U8 := String.to_list mb;
        let s := sum_list hay 0;
        let t1 <- Bench.now;
        report (String.concat "to_list+walk 1MB sum=" (I64.to_string s)) (t1 - t0) n;
        let small : Array I64 := Array.new 64 3;
        let t2 <- Bench.now;
        let s2 := sum_array small 0 n 0;
        let t3 <- Bench.now;
        report (String.concat "Array.get_or x1M sum=" (I64.to_string s2)) (t3 - t2) n;
        time_from_list 64;
        time_from_list 1024;
        time_from_list 4096;
        time_set_len 16;
        time_set_len 32;
        time_set_len 64;
        time_sets 64 4000;
        time_sets 256 1000;
        time_sets 1024 250;
        time_sets 4096 60;
        return true
    }
}
