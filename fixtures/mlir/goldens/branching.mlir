func.func @indicator(%n: i64) -> (f64) attributes {loc = loc("kernels.mo":12:5)} {
  %zero = arith.constant 0.0 : f64 loc("kernels.mo":12:5)
  %one = arith.constant 1.0 : f64 loc("kernels.mo":12:5)
  %n_max = arith.constant 0 : i64 loc("kernels.mo":12:5)
  %pos = arith.cmpi sgt, %n, %n_max : i64 loc("kernels.mo":12:5)
  %r = scf.if %pos -> (f64) {
    scf.yield %one : f64 loc("kernels.mo":12:5)
  } else {
    scf.yield %zero : f64 loc("kernels.mo":12:5)
  } loc("kernels.mo":12:5)
  return %r : f64 loc("kernels.mo":12:5)
}
