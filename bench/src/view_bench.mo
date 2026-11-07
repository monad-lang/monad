/// `Cell` vs `Ref`: the view-types Phase 3 "show the win" probe.
///
/// `Cell` is a LINEAR handle over one `Copy` payload (`init/src/view.mo`):
/// no lock, no atomic, and (in the fused do-bind) no `Pair`/closure
/// allocation. `Ref` is the shared, atomic cell (`std/src/ref.mo`) and is the
/// right comparison: both do one load/store per operation, but only `Ref`
/// pays the atomic. The probe is a manual measurement (run by hand, not every
/// commit) and prints ns/op for a get/set loop through each.
///
/// Both loops are the shape codegen fuses (`try_compile_view_bind_db` /
/// the IO do-bind path): bind the accessor, consume the result immediately.
/// That is what makes the comparison meaningful -- the boxed `Cell` path
/// allocates a `Pair` and would measure the wrong thing.
///
/// Timing uses `Bench.now` (milliseconds) with 10M iterations, so one
/// millisecond of resolution is ~0.1 ns/op. (A `current_time_nano` reference
/// here compiled to an unwrapped native call; `Bench.now` is the portable
/// shape.)
///
/// Gated on MONAD_BENCH=1, like the affine probes: `scripts/check-monad-tests.sh`
/// sweeps every test under `bench/`, and a 20M-iteration measurement with no
/// assertion should not run on every commit.
use std::bench {Bench.now}
open IO {get_env, println}
use init::view {Cell}
use std::ref {Ref}

/// One get/set round-trip per iteration, threaded through the same handle.
/// `Cell.get` returns the handle, so the recursion keeps the linear value.
#[terminating]
def cell_loop (i : I64) (n : I64) (c : Cell I64) : IO (Cell I64) :=
    if I64.beq i n then return c
    else do {
        let p <- Cell.get c;
        match p {
            Pair.pair v c2 => do {
                let c3 <- Cell.set c2 (I64.add v 1);
                cell_loop (i + 1) n c3
            },
        }
    }

#[terminating]
def ref_loop (i : I64) (n : I64) (r : Ref I64) : IO Unit :=
    if I64.beq i n then return unit
    else do {
        let v <- Ref.get r;
        let _ <- Ref.set r (I64.add v 1);
        ref_loop (i + 1) n r
    }

def ns_per_op (label : String) (elapsed_ms : I64) (n : I64) : IO Bool := do {
    let per := I64.div (I64.mul elapsed_ms 1000000) n;
    println (String.concat label (String.concat ": " (String.concat (I64.to_string per) " ns/op")));
    return true
}

def bench_enabled : IO Bool := do {
    let v <- get_env "MONAD_BENCH";
    return (match v { Option.some _ => true, Option.none => false })
}

#[test]
def bench_cell_against_ref : IO Bool := do {
    let on <- bench_enabled;
    if Bool.not on then return true
    else do {
        let n : I64 := 10000000;
        let c0 <- Cell.new 0;
        let t0 <- Bench.now;
        let c1 <- cell_loop 0 n c0;
        let t1 <- Bench.now;
        let _ <- Cell.free c1;
        let _ok <- ns_per_op "cell get+set" (I64.sub t1 t0) n;

        let r <- Ref.new 0;
        let t2 <- Bench.now;
        let _ <- ref_loop 0 n r;
        let t3 <- Bench.now;
        let ok <- ns_per_op "ref get+set" (I64.sub t3 t2) n;
        return ok
    }
}
