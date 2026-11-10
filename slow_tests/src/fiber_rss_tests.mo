/// Roadmap PR 2's reproduction: allocations a fiber makes must be collected
/// once it has finished. Twenty fibers each build ~3 MB and are awaited;
/// then a little churn forces collections; VmRSS is read from /proc. With
/// the leak this test was written for (~170 MB retained) the bound fails.
///
/// Compiled backend only: the Rust host's `forkIO` is lazy and never runs a
/// fiber on its own thread, so run this with the tree compiler's `test`.
use std::concurrent::fiber {forkIO, await_fiber}
use std::io {IO.read_file}
use std::path {Path}
use parsec::number {parse_i64}

/// 1500 pieces of 2 KB each: about 3 MB.
def chunk : String := String.repeat "x" 2000

#[partial]
def pieces (n : I64) (acc : List String) : List String :=
    if I64.lt n 1 then acc else pieces (n - 1) (List.cons chunk acc)

/// Build a string on the calling thread and answer its length.
def build : IO I64 := do {
    let s : String := String.concat_list (pieces 1500 List.empty);
    IO.pure (String.length s)
}

/// Fork and await `n` fibers in turn; none of their strings is kept.
#[partial]
def fibers_at (n : I64) (acc : I64) : IO I64 :=
    if I64.lt n 1 then IO.pure acc
    else do {
        let f <- forkIO (fn (_ : Unit) => build);
        let r <- await_fiber f;
        let next : I64 := match r { Result.ok len => acc + len, Result.err _ => acc };
        fibers_at (n - 1) next
    }

/// Allocate and drop ~600 KB per step, enough to trigger collections.
#[partial]
def churn (n : I64) : IO Unit :=
    if I64.lt n 1 then IO.pure unit
    else do {
        let s : String := String.concat_list (pieces 300 List.empty);
        let _len : I64 := String.length s;
        churn (n - 1)
    }

#[partial]
def lines_at (s : String) (i : I64) (start : I64) (acc : List String) : List String :=
    if Bool.not (I64.lt i (String.length s))
    then List.reverse (List.cons (String.slice s start (String.length s - start)) acc)
    else if String.slice s i 1 == "\n"
    then lines_at s (i + 1) (i + 1) (List.cons (String.slice s start (i - start)) acc)
    else lines_at s (i + 1) start acc

def lines_of (s : String) : List String :=
    lines_at s 0 0 List.empty

#[partial]
def digit_run (s : String) (i : I64) (acc : String) : String :=
    if I64.lt i (String.length s)
    then
        let ch : String := String.slice s i 1 in
        if Bool.and (Bool.not (String.is_empty ch)) (String.contains "0123456789" ch)
        then digit_run s (i + 1) (String.concat acc ch)
        else acc
    else acc

#[partial]
def find_digits (s : String) (i : I64) : Option String :=
    if I64.lt i (String.length s)
    then
        let ch : String := String.slice s i 1 in
        if Bool.and (Bool.not (String.is_empty ch)) (String.contains "0123456789" ch)
        then Option.some (digit_run s i "")
        else find_digits s (i + 1)
    else Option.none

def rss_of_line (l : String) : I64 :=
    match find_digits l 0 {
        Option.none => 0,
        Option.some digits => match parse_i64 digits {
            Option.some n => n,
            Option.none => 0,
        },
    }

#[partial]
def rss_of (lines : List String) : I64 :=
    match lines {
        List.empty => 0,
        List.cons l rest =>
            if String.starts_with "VmRSS:" l then rss_of_line l else rss_of rest,
    }

def read_rss_kb : IO I64 := do {
    let r <- IO.read_file (Path.path "/proc/self/status");
    match r {
        Result.ok text => do {
            IO.println (String.concat "status_bytes=" (I64.to_string (String.length text)));
            IO.println (if String.contains text "VmRSS:" then "has_vmrss" else "no_vmrss");
            IO.pure (rss_of (lines_of text))
        },
        Result.err e => do {
            IO.println (String.concat "status_read_error=" e.message);
            IO.pure 0
        },
    }
}

/// The work is ~60 MB live at peak; with the leak it stayed ~170 MB after
/// the fibers ended. 250 MB leaves room for the driver and the collector's
/// free pages while still failing on the leak.
#[test]
def test_fiber_allocations_are_collected : IO Bool := do {
    let total <- fibers_at 20 0;
    let _ <- churn 30;
    let kb <- read_rss_kb;
    IO.println (String.concat "fiber_rss_kb=" (String.concat (I64.to_string kb) (String.concat " built=" (I64.to_string total))));
    return (I64.lt 0 kb && I64.lt kb 250000)
}
