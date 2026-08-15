/// Benchmarks for std/sha256.mo, using the std/bench.mo Bench.now/report
/// idiom (see init/string_profile.mo for the same pattern applied to
/// String natives). Sizes are calibrated to this tree-walking-successor
/// interpreter's own overhead, not to what a native SHA-256 would
/// consider "large" — every hashed byte triggers several nested calls
/// (pack/rotr/sigma/ch/maj) x64 rounds x N blocks, so don't reach for
/// NIST-scale stress inputs here.

use std.bench {now, report}
use std.sha256 {}

#[test]
def bench_sha256_short : Bool :=
  let input := "The quick brown fox jumps over the lazy dog" in
  let start := Bench.now in
  let ignored := Sha256.hash input in
  let elapsed := I64.sub Bench.now start in
  Bench.report "sha256 44 bytes (1 block)" elapsed

#[test]
def bench_sha256_medium : Bool :=
  let input := String.repeat "0123456789" 100 in // 1000 bytes, ~16 blocks
  let start := Bench.now in
  let ignored := Sha256.hash input in
  let elapsed := I64.sub Bench.now start in
  Bench.report "sha256 1000 bytes (~16 blocks)" elapsed
