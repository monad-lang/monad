func.func @total(%v: memref<16xf32> {llvm.noalias}) -> (f64) attributes {loc = loc("kernels.mo":12:5)} {
  %c0 = arith.constant 0 : index loc("kernels.mo":12:5)
  %c1 = arith.constant 1 : index loc("kernels.mo":12:5)
  %c16 = arith.constant 16 : index loc("kernels.mo":12:5)
  %zero = arith.constant 0.0 : f64 loc("kernels.mo":12:5)
  %acc = scf.for %i = %c0 to %c16 step %c1 iter_args(%s = %zero) -> (f64) {
    %vi = memref.load %v[%i] : memref<16xf32> loc("kernels.mo":12:5)
    %vid = arith.extf %vi : f32 to f64 loc("kernels.mo":12:5)
    %next = arith.addf %s, %vid : f64 loc("kernels.mo":12:5)
    scf.yield %next : f64 loc("kernels.mo":12:5)
  } loc("kernels.mo":12:5)
  return %acc : f64 loc("kernels.mo":12:5)
}
