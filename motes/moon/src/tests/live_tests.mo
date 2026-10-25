/// Live-reload tests: the SSE reload source, the file watcher, and the client
/// snippet.

use std::concurrent::combine {sleepIO}
use std::io {IO.write_file}
use std::path {Path}
use std::concurrent::fiber {cancel_fiber}
use std::process {process_id}
use std::ref {Ref, Ref.add_i64, Ref.get, Ref.new}
use http::body_io {Body.pull}
use http::types {Request, Request.get, Uri}
use moon::live {Live.reload, Live.script, Live.watch}

def dummy_req : Request :=
  Request.get (Uri.uri "" Option.none "" Option.none "/live" Option.none Option.none)

#[test]
def test_reload_emits_reload_event : IO Bool := do {
  let version <- Ref.new 0i64;
  let _ <- Ref.add_i64 version 1;
  let handler := Live.reload version;
  let r <- handler dummy_req;
  match r {
    Result.err _ => return false,
    Result.ok res => do {
      let chunk <- Body.pull res.body;
      match chunk {
        Option.none => return false,
        Option.some bytes =>
          return (String.starts_with "event: reload" (String.from_list bytes))
      }
    }
  }
}

/// Compiled-only: `Live.watch` forks a watcher and this test waits on the
/// `Ref` that fiber bumps. The Rust host starts fibers lazily (at
/// await/poll), so the watcher never runs and both waits exhaust their
/// retries.
#[test]
def test_watch_bumps_version : IO Bool := do {
  let name := String.concat "moon_live_watch_" (String.concat (I64.to_string process_id) ".txt");
  let path := String.concat "/tmp/" name;
  let _ <- IO.write_file (Path.path path) "one";
  let version <- Ref.new 0i64;
  let watcher <- Live.watch (Path.path path) version;
  let first <- wait_version version 1i64 40i64;
  let _ <- IO.write_file (Path.path path) "two";
  let second <- wait_version version 2i64 40i64;
  cancel_fiber watcher;
  return (Bool.and first second)
}

/// Poll `version` until it reaches `want`, or `tries` 50 ms sleeps elapse.
#[partial]
def wait_version (version : Ref I64) (want : I64) (tries : I64) : IO Bool := do {
  let v <- Ref.get version;
  if I64.gt v (I64.sub want 1i64)
  then return true
  else if I64.lt tries 1
  then return false
  else do {
    sleepIO 50;
    wait_version version want (I64.sub tries 1)
  }
}

#[test]
def test_script_is_a_script : Bool :=
  Bool.and (String.starts_with "<script>" (Live.script "/live"))
    (String.ends_with (Live.script "/live") "</script>")
