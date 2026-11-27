/// A scalar `#[kernel]`, compiled through `mlir-opt` and linked in.
///
/// Scalar because that is what `codegen/src/kernel/scalar.mo` lowers today:
/// arithmetic, comparisons and a two-arm `if`. A `Buf` kernel (`saxpy`)
/// waits on the `memref` write path (the plan's cost items 3-5).
///
/// `monad kernels motes/kernel_example` prints the verdict; a kernel that is
/// not ready still compiles, as its ordinary body.
open IO {println}

/// `a * x + y`, clamped below at zero.
#[kernel]
def axpy_clamped (a : I64) (x : I64) (y : I64) : I64 :=
    if I64.lt (a * x + y) 0 then 0 else a * x + y

def main : IO Unit := do {
    println (I64.to_string (axpy_clamped 3 4 5));
    println (I64.to_string (axpy_clamped 2 (0 - 7) 3))
}
