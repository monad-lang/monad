func.func @saxpy(%dst: memref<16xf32> {llvm.noalias}, %a_bits: i32) attributes {loc = loc("kernels.mo":12:5)} {
  %c0 = arith.constant 0 : index loc("kernels.mo":12:5)
  %c1 = arith.constant 1 : index loc("kernels.mo":12:5)
  %c16 = arith.constant 16 : index loc("kernels.mo":12:5)
  %a = arith.bitcast %a_bits : i32 to f32 loc("kernels.mo":12:5)
  %one = arith.constant 1.0 : f32 loc("kernels.mo":12:5)
  scf.for %i = %c0 to %c16 step %c1 {
    %i64 = arith.index_cast %i : index to i64 loc("kernels.mo":12:5)
    %x = arith.sitofp %i64 : i64 to f32 loc("kernels.mo":12:5)
    %t = arith.mulf %a, %x : f32 loc("kernels.mo":12:5)
    %r = arith.addf %t, %one : f32 loc("kernels.mo":12:5)
    memref.store %r, %dst[%i] : memref<16xf32> loc("kernels.mo":12:5)
  } loc("kernels.mo":12:5)
  return loc("kernels.mo":12:5)
}
