/// Benchmark utilities.

use io {IO}
open IO {println}

/// Milliseconds from an arbitrary fixed origin. Only differences between
/// two readings are meaningful.
#[native bench_now]
def Bench.now : I64

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
