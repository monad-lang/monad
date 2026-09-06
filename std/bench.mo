/// Benchmark utilities.

use io {IO}
use std.io {current_time, println}
open IO {current_time, println}

/// Milliseconds from an arbitrary fixed origin. Only differences between
/// two readings are meaningful.
///
/// `IO I64`, and NOT a native itself: a clock reading is a side effect,
/// so two `Bench.now`s in one expression must be free to differ, and a
/// pure `I64` invites exactly the sharing and reordering that would make
/// a measured span meaningless. The native it defers to is
/// `IO.current_time` (std/io.mo), alongside the other genuine effects.
def Bench.now : IO I64 := current_time

/// Print one timing span.
///
/// Written in Monad and typed `IO Unit`, NOT a native: as a native it
/// was a generated stub that returned `1` and dropped both arguments
/// (`emit_bench_report`, `lang/codegen/runtime.mo`), so every
/// `--verbose` timing this codebase emits printed nothing at all from a
/// COMPILED binary -- the instrumentation existed only under the Rust
/// host. Printing is IO, so the type says so, and the compiled compiler
/// reports its own stage timings like the host does.
def Bench.report (label : String) (elapsed_ms : I64) : IO Unit :=
    println (String.concat label (String.concat " " (String.concat (I64.to_string elapsed_ms) "ms")))

/// Milliseconds elapsed since `t0`.
///
/// The reading has to be bound before it can be subtracted, so the
/// old inline `(Bench.now - t0)` has no direct translation now that
/// the clock is `IO`. This is that expression, spelled once.
def Bench.since (t0 : I64) : IO I64 := do {
    let t1 : I64 <- Bench.now;
    return (t1 - t0)
}

/// Report the span since `t0` under `label` -- `Bench.report` and
/// `Bench.since` in the one combination nearly every caller wants.
def Bench.report_since (label : String) (t0 : I64) : IO Unit := do {
    let elapsed : I64 <- Bench.since t0;
    Bench.report label elapsed
}

