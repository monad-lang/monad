/// Evaluator micro-benchmarks: time `lang::core_eval.eval` alone, with the
/// parse/typecheck/elaborate/lower setup amortized out.
///
/// The workloads are lowered through `Eval.lower_file_for_bench` (the same
/// elaborate/validate/lower recipe `monad eval` and /try run), then `eval`
/// is called `iters` times, each with a FRESH `GlobalCache` -- the evaluator
/// equivalent of the Rust criterion bench's `iter_batched` setup.
///
/// Run from the repository root:
///   MONAD_BENCH=1 <built>/monad test bench/src/core_eval_bench.mo
///
/// Gated on MONAD_BENCH=1 (`view_bench.mo`'s rule): `scripts/check-monad-tests.sh`
/// sweeps every test under `bench/`, so an ungated run must return true
/// without touching the filesystem.
///
/// Record before/after numbers in this doc comment, not in a result file:
/// none are committed anywhere in this repo.
///
/// **Result (2026-11-14, minima of four interleaved runs, this host).**
/// Evaluator, the four changes kept (outcome type + de-CPS, unlimited
/// fuel/depth fast path, Array-backed global cache, env frames):
///
///   arith_native        6500 -> 2047 ms  (-69%)
///   list_build_match     675 ->  185 ms  (-73%)
///   closures            2741 ->  972 ms  (-65%)
///   struct_fields        893 ->  291 ms  (-67%)
///   native_mix          1287 ->  789 ms  (-39%)
///   globals_wide       17394 -> 6045 ms  (-65%)
///   lowering            7297 -> 7614 ms  (unchanged setup; noise)
///
/// A fifth change -- an id-indexed closure table for native dispatch --
/// measured **40-100x slower** (indirect calls defeat the native call
/// codegen) and was reverted. Do not retry it; if native dispatch matters,
/// measure an integer-id chain instead.
use eval::file {Eval.lower_file_for_bench}
use eval::run {EvalBenchProgram}
use lang::core_eval {basic_native_table, eval}
use lang::core_value {
    Env, global_cache_fuel, global_cache_new, global_cache_new_fueled, global_table_len,
}
use lang::typecheck::meta_eval {show_value_debug}
use std::bench {Bench.now, Bench.since}
use std::list {List.intercalate}
use std::path {Path}
use std::process {exec_cmd}
use std::test {Test.write_fixture}
open IO {get_env, println}

// ─── Harness ───────────────────────────────────────────────────────────

def fixture_dir : String := "target-monad/eval-bench"

/// The sweep runs every `#[test]` under `bench/`, so the real work is
/// opt-in and the ungated test is a no-op success.
def bench_enabled : IO Bool := do {
    let value <- get_env "MONAD_BENCH";
    return (match value {
        Option.some _ => true,
        Option.none => false,
    })
}

/// `-1` means unlimited everywhere else; here it is a step budget large
/// enough to leave the counter readable after a full workload.
def node_budget : I64 := 1000000000

/// Write the workload and lower its `main` without evaluating it. Called
/// only after the MONAD_BENCH gate.
def lower_workload (name : String) (source : String) : IO (Result String EvalBenchProgram) := do {
    let _ <- exec_cmd "mkdir" ["-p", fixture_dir];
    let path : String := String.concat fixture_dir (String.concat "/" (String.concat name ".mo"));
    let _written <- Test.write_fixture (Path.path path) source;
    Eval.lower_file_for_bench path "main" false
}

def eval_once (program : EvalBenchProgram) (len : I64) : Option String :=
    match eval program.ir Env.env_nil program.globals basic_native_table
        (global_cache_new len) {
        Pair.pair r _cache =>
            match r {
                Result.ok v => Option.some (show_value_debug v),
                Result.err _e => Option.none,
            },
    }

/// Evaluate `iters` times with a fresh cache each time; returns how many
/// runs completed, so a silently failing benchmark fails the assertion.
#[partial]
def run_iterations (program : EvalBenchProgram) (len : I64) (iters : I64)
    (done : I64) : I64 :=
    if I64.beq iters 0
    then done
    else
        match eval program.ir Env.env_nil program.globals basic_native_table
            (global_cache_new len) {
            Pair.pair r _cache =>
                match r {
                    Result.ok _v => run_iterations program len (I64.sub iters 1) (I64.add done 1),
                    Result.err _e => done,
                },
        }

/// One evaluation on a counted fuel budget: the nodes that ran are the
/// steps the cache's fuel counter consumed. This is the `ns/node` guard.
def count_nodes (program : EvalBenchProgram) (len : I64) : I64 :=
    match eval program.ir Env.env_nil program.globals basic_native_table
        (global_cache_new_fueled len node_budget (-1)) {
        Pair.pair r cache =>
            match r {
                Result.ok _v => I64.sub node_budget (global_cache_fuel cache),
                Result.err _e => 0,
            },
    }

def report_line (name : String) (iters : I64) (ms : I64) (nodes : I64) : IO Unit := do {
    let total_ns : I64 := I64.mul ms 1000000;
    let per_iter : I64 := if I64.beq iters 0 then 0 else I64.div total_ns iters;
    // `nodes` is one evaluation's count, so normalize the per-iteration time
    // by it -- not the total, which covers every iteration.
    let per_node : I64 := if I64.beq nodes 0 then 0 else I64.div per_iter nodes;
    let line : String :=
        List.intercalate " "
            ["bench", name, "iters=", I64.to_string iters, "ms=", I64.to_string ms,
                "ns/iter=", I64.to_string per_iter, "nodes=", I64.to_string nodes,
                "ns/node=", I64.to_string per_node];
    println line
}

def fail_bench (name : String) (message : String) : IO Bool := do {
    println (String.concat "bench " (String.concat name (String.concat ": " message)));
    return false
}

def run_bench (name : String) (program : EvalBenchProgram) (iters : I64)
    (expected : String) : IO Bool := do {
    let len : I64 := global_table_len program.globals;
    // A benchmark that measures nothing is worse than one that measures the
    // wrong thing: the result is checked before any timing.
    match eval_once program len {
        Option.none => fail_bench name "evaluation failed",
        Option.some got =>
            if Bool.not (String.beq got expected)
            then fail_bench name
                (String.concat "expected " (String.concat expected (String.concat ", got " got)))
            else do {
                let _warm : I64 := run_iterations program len 2 0;
                let nodes : I64 := count_nodes program len;
                let start <- Bench.now;
                let done : I64 := run_iterations program len iters 0;
                let ms <- Bench.since start;
                report_line name iters ms nodes;
                return (I64.beq done iters && I64.gt nodes 0)
            },
    }
}

def bench_program (name : String) (source : String) (iters : I64)
    (expected : String) : IO Bool := do {
    let lowered <- lower_workload name source;
    match lowered {
        Result.err e =>
            fail_bench name (String.concat "lower failed: " e),
        Result.ok program =>
            run_bench name program iters expected,
    }
}

// ─── Workloads ─────────────────────────────────────────────────────────

/// Application/apply, locals, the integer natives and `if`-as-match.
def arith_source : String :=
    r#"#[terminating]
def loop (n : I64) (acc : I64) : I64 :=
    if n == 0
    then acc
    else loop (n - 1) (acc + n)

def main : I64 := loop 100 0
"#

/// Constructor values, match dispatch, and one env binding per field.
def list_source : String :=
    r#"#[terminating]
def build (n : I64) : List I64 :=
    if n == 0
    then List.empty
    else List.cons n (build (n - 1))

#[terminating]
def total (xs : List I64) : I64 :=
    match xs {
        List.cons h t => h + total t,
        List.empty => 0,
    }

def main : I64 := total (build 40)
"#

/// Closure capture and repeated application through `apply`.
def closures_source : String :=
    r#"def inc (x : I64) : I64 := x + 1

def compose (f : I64 -> I64) (g : I64 -> I64) : I64 -> I64 :=
    fn (x : I64) => f (g x)

#[terminating]
def apply_n (n : I64) (f : I64 -> I64) (x : I64) : I64 :=
    if n == 0
    then x
    else apply_n (n - 1) f (f x)

def main : I64 := apply_n 30 (compose inc inc) 0
"#

/// Wide records: every field read lowers to a match whose arm binds all
/// four fields, so this is the per-field env-extension cost.
def struct_source : String :=
    r#"struct Box {
    a : I64,
    b : I64,
    c : I64,
    d : I64,
}

def start : Box := { a := 1, b := 2, c := 3, d := 4 }

#[terminating]
def bump (n : I64) (p : Box) : Box :=
    if n == 0
    then p
    else
        let next : Box := { p with a := p.a + 1 } in
        bump (n - 1) next

def main : I64 :=
    let p : Box := bump 20 start in
    p.a
"#

/// The end of the 102-arm native name chain: U64/U32 ops and conversions.
def native_mix_source : String :=
    r#"#[terminating]
def loop (n : I64) (acc : I64) : I64 :=
    if n == 0
    then acc
    else
        let a : U64 := U64.add (I64.to_u64 n) 1u64 in
        let b : U32 := U32.add (I64.to_u32 n) 2u32 in
        let a2 : I64 := U64.to_i64 a in
        let b2 : I64 := U32.to_i64 b in
        loop (n - 1) (acc + a2 + b2)

def main : I64 := loop 10 0
"#

// The wide-globals workload is generated: 256 defs, all reachable (the
// `total` chain forces each one once), then a 20k-iteration loop that reads
// the highest-indexed def on every iteration. That is the O(cache index)
// signal the array-backed cache removes.
#[partial]
def globals_defs (i : I64) (n : I64) (acc : String) : String :=
    if I64.beq i n
    then acc
    else
        globals_defs (i + 1) n
            (String.concat acc
                (String.concat "def g" (String.concat (I64.to_string i)
                    (String.concat " : I64 := " (String.concat (I64.to_string i) "\n")))))

#[partial]
def globals_add (i : I64) (n : I64) (acc : String) : String :=
    if I64.beq i n
    then acc
    else globals_add (i + 1) n (String.concat acc (String.concat " + g" (I64.to_string i)))

def globals_source : String :=
    String.concat (globals_defs 0 256 "")
        (String.concat
            "\n#[terminating]\ndef loop (n : I64) (acc : I64) : I64 :=\n    if n == 0\n    then acc\n    else loop (n - 1) (acc + g255)\n\ndef main : I64 :=\n    let total : I64 := 0"
            (String.concat (globals_add 0 256 "")
                " in\n    loop 20000 total\n"))

// ─── Tests ─────────────────────────────────────────────────────────────

#[test]
def bench_arith_native : IO Bool := do {
    let on <- bench_enabled;
    if Bool.not on then return true
    else bench_program "arith_native" arith_source 2000 "5050"
}

#[test]
def bench_list_build_match : IO Bool := do {
    let on <- bench_enabled;
    if Bool.not on then return true
    else bench_program "list_build_match" list_source 500 "820"
}

#[test]
def bench_closures : IO Bool := do {
    let on <- bench_enabled;
    if Bool.not on then return true
    else bench_program "closures" closures_source 2000 "60"
}

#[test]
def bench_struct_fields : IO Bool := do {
    let on <- bench_enabled;
    if Bool.not on then return true
    else bench_program "struct_fields" struct_source 1000 "21"
}

#[test]
def bench_native_mix : IO Bool := do {
    let on <- bench_enabled;
    if Bool.not on then return true
    else bench_program "native_mix" native_mix_source 2000 "140"
}

#[test]
def bench_globals_wide : IO Bool := do {
    let on <- bench_enabled;
    if Bool.not on then return true
    else bench_program "globals_wide" globals_source 20 "5132640"
}

/// Setup cost only: parse + elaborate + validate + lower the 256-global
/// workload. This is the guard for any change to the lowering pass.
#[test]
def bench_eval_lowering : IO Bool := do {
    let on <- bench_enabled;
    if Bool.not on then return true
    else do {
        let start <- Bench.now;
        let lowered <- lower_workload "globals_wide_lowering" globals_source;
        let ms <- Bench.since start;
        match lowered {
            Result.err e => fail_bench "lowering_globals_wide" e,
            Result.ok program => do {
                let len : I64 := global_table_len program.globals;
                report_line "lowering_globals_wide" 1 ms len;
                return (I64.gt len 0)
            },
        }
    }
}
