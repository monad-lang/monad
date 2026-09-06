/// Benchmarks for std/sha256.mo, using the std/bench.mo Bench.now/report
/// idiom (see init/string_profile.mo for the same pattern applied to
/// String natives). Sizes are calibrated to this tree-walking-successor
/// interpreter's own overhead, not to what a native SHA-256 would
/// consider "large" — every hashed byte triggers several nested calls
/// (pack/rotr/sigma/ch/maj) x64 rounds x N blocks, so don't reach for
/// NIST-scale stress inputs here.

use std.bench {now, report, since}
use std.sha256 {}

#[test]
def bench_sha256_short : IO Bool := do {
  let input := "The quick brown fox jumps over the lazy dog";
  let start : I64 <- Bench.now;
  let ignored := Sha256.hash input;
  let elapsed : I64 <- Bench.since start;
  Bench.report "sha256 44 bytes (1 block)" elapsed;
  return true
}

#[test]
def bench_sha256_medium : IO Bool := do {
  // 1000 bytes, ~16 blocks
  let input := String.repeat "0123456789" 100;
  let start : I64 <- Bench.now;
  let ignored := Sha256.hash input;
  let elapsed : I64 <- Bench.since start;
  Bench.report "sha256 1000 bytes (~16 blocks)" elapsed;
  return true
}
