/// Tests for `build/src/test_cache.mo`: the key, the entry's paths, and the
/// readiness rule a hit depends on.
///
/// The cache's *behaviour* (a hit runs the stored driver and reports the
/// same total) is an end-to-end property of `monad test` and is not
/// reachable from a unit test; what is pinned here is the format, because
/// every one of these paths is compiled INTO a driver binary.

use std::process {process_id}
use build::test_cache {
  Build.test_entry_bin, Build.test_entry_count, Build.test_entry_count_read,
  Build.test_entry_count_write, Build.test_entry_dir, Build.test_entry_ir,
  Build.test_entry_prepare, Build.test_entry_ready, Build.test_entry_report,
  Build.test_key, Build.test_plan,
}
use build::check {Build.cache_plan_active}

def commit_x : String := "0123456789abcdef0123456789abcdef01234567"
def sum_x : String := "sha256:00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"

def Build.tcf_root (tag : String) : String :=
    "/tmp/monad_test_cache_" ++ I64.to_string process_id ++ "_" ++ tag

#[test]
def test_key_covers_every_component : Bool :=
    let k : String := Build.test_key "fh" "cl" "cp" "x86_64-unknown-linux-gnu" in
    String.beq k (Build.test_key "fh" "cl" "cp" "x86_64-unknown-linux-gnu")
        && Bool.not (String.beq k (Build.test_key "fh2" "cl" "cp" "x86_64-unknown-linux-gnu"))
        && Bool.not (String.beq k (Build.test_key "fh" "cl2" "cp" "x86_64-unknown-linux-gnu"))
        && Bool.not (String.beq k (Build.test_key "fh" "cl" "cp2" "x86_64-unknown-linux-gnu"))
        && Bool.not (String.beq k (Build.test_key "fh" "cl" "cp" "aarch64-unknown-linux-gnu"))
        && I64.beq (String.length k) 64

/// Every path a driver's compiled-in report relies on.
#[test]
def test_entry_paths_live_under_the_key : Bool :=
    String.beq (Build.test_entry_dir "/t" "abc") "/t/abc"
        && String.beq (Build.test_entry_bin "/t" "abc") "/t/abc/bin"
        && String.beq (Build.test_entry_ir "/t" "abc") "/t/abc/bin.ll"
        && String.beq (Build.test_entry_report "/t" "abc") "/t/abc/monad_test_result.txt"
        && String.beq (Build.test_entry_count "/t" "abc") "/t/abc/count"

/// One file is not worth a key -- the same gate the check cache applies,
/// for the same reason (the key costs a compiler digest and a closure
/// walk).
#[test]
def test_one_file_is_not_cached : IO Bool := do {
    let p <- Build.test_plan ["a.mo"] "/t" "x86_64-unknown-linux-gnu" true;
    return (Bool.not (Build.cache_plan_active p))
}

/// Neither is a run that did not ask for the cache.
#[test]
def test_a_run_that_did_not_ask_is_inactive : IO Bool := do {
    let p <- Build.test_plan ["a.mo", "b.mo"] "/t" "x86_64-unknown-linux-gnu" false;
    return (Bool.not (Build.cache_plan_active p))
}

/// Ready means "a driver AND the count its report cannot supply". A
/// missing count is a miss, because a hit that cannot name the denominator
/// would report a passing file as having no tests.
#[test]
def test_readiness_needs_both_the_driver_and_the_count : IO Bool := do {
    let root : String := Build.tcf_root "ready";
    let key : String := "k1";
    let _mk <- Build.test_entry_prepare root key;
    let empty <- Build.test_entry_ready root key;
    let _w <- Build.test_entry_count_write root key 3;
    let count_only <- Build.test_entry_ready root key;
    let bin : String := Build.test_entry_bin root key;
    let _b <- Build.write_fake_bin bin;
    let both <- Build.test_entry_ready root key;
    let n <- Build.test_entry_count_read root key;
    let _rm <- exec_cmd "rm" ["-rf", root];
    return (Bool.not empty && Bool.not count_only && both && same_count n 3)
}

/// Write a stand-in for a driver: readiness is a file-existence question,
/// and linking a real one needs llc and clang.
def Build.write_fake_bin (path : String) : IO Bool := do {
    let r <- IO.write_file (Path.path path) "#!/bin/sh\nexit 0\n";
    match r {
        Result.ok _ => return true,
        Result.err _ => return false
    }
}

def same_count (n : Option I64) (want : I64) : Bool :=
    match n {
        Option.none => false,
        Option.some got => I64.beq got want
    }

/// A count leaf that is absent or not a number is `none`, never `0`: a
/// zero would read as "this file has no tests".
#[test]
def test_a_missing_or_garbage_count_is_none : IO Bool := do {
    let root : String := Build.tcf_root "garbage";
    let key : String := "k2";
    let _mk <- Build.test_entry_prepare root key;
    let absent <- Build.test_entry_count_read root key;
    let _w <- IO.write_file (Path.path (Build.test_entry_count root key)) "not a number";
    let garbage <- Build.test_entry_count_read root key;
    let _rm <- exec_cmd "rm" ["-rf", root];
    return (is_none absent && is_none garbage)
}

def is_none (o : Option I64) : Bool :=
    match o {
        Option.none => true,
        Option.some _ => false
    }
