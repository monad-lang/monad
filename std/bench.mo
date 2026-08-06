
/// Benchmark utilities

#[native bench_now]
def Bench.now : I64

#[native bench_report]
def Bench.report (label : String) (elapsed_ms : I64) : Bool
