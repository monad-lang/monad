/// End-to-end test for `std/watch.mo`'s four inotify natives: a compiled
/// program opens a watch, registers a directory, sees an idle timeout as an
/// EMPTY event list, writes a file and sees the event naming it.
///
/// In `slow_tests/` rather than `std/watch_tests.mo` because it compiles a
/// program through the real pipeline, links the real runtime and runs it:
/// that is the only thing that proves the natives are wired into codegen
/// (`validate_no_unwired_natives` catches a missing `natives.mo` entry, not
/// a missing `platform_posix.c` one). The decode half is `std/watch_tests.mo`,
/// which also runs under the Rust host.
///
/// `inotify` is Linux-only; on another POSIX target `Watch.new` fails with
/// `ENOSYS` and this exits 1, which is the documented contract rather than a
/// test bug (the suite runs on Linux).
use std::process {exec_cmd, process_id}
use lang::codegen::test::e2e_harness {compile_source_run_expect}

/// A unique temp directory for this process (the same shape
/// `codegen_wired_natives_e2e_tests.mo` uses).
def watch_dir : String :=
    "/tmp/monad_watch_e2e_" ++ I64.to_string process_id

#[test]
def test_watch_native_end_to_end : IO Bool :=
    let dir := watch_dir in
    let lit := "\"" ++ dir ++ "\"" in
    let source := r#"use std::list {List.length}
use std::path {Path}
use std::process {exec_cmd}
use std::stream {FdStream, Stream}
use std::watch {
  Watch.add, Watch.changes, Watch.new, Watch.next, WatchEvent, WatchEvent.closed_for_write,
  WatchEvent.created, WatchEvent.moved_to,
}

#[terminating]
def saw (evs : List WatchEvent) (name : String) : Bool :=
  match evs {
    List.cons e rest =>
      if String.beq e.name name
      then WatchEvent.created e || WatchEvent.closed_for_write e || WatchEvent.moved_to e
      else saw rest name,
    List.empty => false
  }

def after_write (w : FdStream) (dir : String) : IO I64 := do {
  let _ <- IO.write_file (Path.path (String.concat dir "/edited.txt")) "one";
  let events <- Watch.next w 2000;
  let _ <- Stream.close w;
  match events {
    Result.err _ => IO.pure 3,
    Result.ok evs => IO.pure (if saw evs "edited.txt" then 7 else 4)
  }
}

def after_add (w : FdStream) (dir : String) : IO I64 := do {
  let idle <- Watch.next w 0;
  match idle {
    Result.err _ => IO.pure 5,
    Result.ok evs =>
      if I64.beq (List.length evs) 0
      then after_write w dir
      else do {
        let _ <- Stream.close w;
        IO.pure 5
      }
  }
}

def watched (w : FdStream) (dir : String) : IO I64 := do {
  let added <- Watch.add w (Path.path dir) Watch.changes;
  match added {
    Result.err _ => IO.pure 2,
    Result.ok _ => after_add w dir
  }
}

def main (args : List String) : IO I64 := do {
  let dir := "# ++ lit ++ r#";
  let _ <- exec_cmd "rm" ["-rf", dir];
  let _ <- exec_cmd "mkdir" ["-p", dir];
  let opened <- Watch.new;
  match opened {
    Result.err _ => IO.pure 1,
    Result.ok w => watched w dir
  }
}
"# in
    do {
      let ok <- compile_source_run_expect source "watch_native" 7;
      let _ <- exec_cmd "rm" ["-rf", dir];
      IO.pure ok
    }
