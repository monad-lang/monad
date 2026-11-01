/// Live-reload tests: the SSE reload source, the file watcher, and the client
/// snippet.

use std::concurrent::combine {sleepIO}
use std::io {IO.write_file}
use std::path {Path}
use std::concurrent::fiber {cancel_fiber}
use std::process {exec_cmd, process_id}
use std::ref {Ref, Ref.add_i64, Ref.get, Ref.new}
use std::watch {WatchEvent}
use http::body_io {Body.pull}
use http::sse {Sse.response}
use http::types {
  Body, Body.is_stream, Headers, Headers.get, Request, Request.get, Response, Response.html,
  Response.json, Uri,
}
use moon::handler_t {HandlerT, HandlerT.pure_io, HandlerT.run_io, HttpError}
use moon::live {
  Live.dev_middleware_t, Live.names_batch_matters, Live.reload, Live.script, Live.watch,
  Live.watch_files, Live.watch_tree,
}

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
/// await/poll), so the watcher never runs and the wait exhausts its retries.
///
/// The bump is the WRITE's, not the watcher's: starting a watch does not
/// report the files it already found (the old polling form's initial empty
/// digest did, which was an artifact rather than a signal).
#[test]
def test_watch_bumps_version : IO Bool := do {
  let name := String.concat "moon_live_watch_" (String.concat (I64.to_string process_id) ".txt");
  let path := String.concat "/tmp/" name;
  let _ <- IO.write_file (Path.path path) "one";
  let version <- Ref.new 0i64;
  let watcher <- Live.watch (Path.path path) version;
  sleepIO 300;
  let _ <- IO.write_file (Path.path path) "two";
  let bumped <- wait_version version 1i64 60i64;
  cancel_fiber watcher;
  IO.pure bumped
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

// ── initial reload, sanitized script, dev middleware ────────────────────

#[test]
def test_reload_initial_event_at_zero : IO Bool := do {
  let version : Ref I64 <- Ref.new 0i64;
  let handler := Live.reload version;
  let r <- handler dummy_req;
  match r {
    Result.err _ => IO.pure false,
    Result.ok res => do {
      let chunk <- Body.pull res.body;
      match chunk {
        Option.none => IO.pure false,
        Option.some bytes =>
          IO.pure (String.starts_with "event: reload" (String.from_list bytes))
      }
    }
  }
}

#[test]
def test_script_sanitizes_endpoint : Bool :=
  let s := Live.script r#"/a"b<c"# in
  Bool.and (String.contains s "/abc") (Bool.not (String.contains s "b<c"))

def dev_html_handler : HandlerT IO Response :=
  HandlerT.pure_io (Response.html 200u16 "<html><body>hi</body></html>")

#[test]
def test_dev_middleware_injects_html : IO Bool := do {
  let h := Live.dev_middleware_t "/live" dev_html_handler;
  let r <- HandlerT.run_io h dummy_req;
  match r {
    Result.err _ => IO.pure false,
    Result.ok res =>
      match res {
        { status, headers, version, body } =>
          match body {
            Body.text s =>
              IO.pure (Bool.and (String.contains s "EventSource")
                (match Headers.get "Cache-Control" headers {
                  Option.some v => String.beq v "no-store",
                  Option.none => false
                })),
            _ => IO.pure false
          }
      }
  }
}

#[test]
def test_dev_middleware_ignores_json : IO Bool := do {
  let base : HandlerT IO Response :=
    HandlerT.pure_io (Response.json 200u16 "{}");
  let h := Live.dev_middleware_t "/live" base;
  let r <- HandlerT.run_io h dummy_req;
  match r {
    Result.err _ => IO.pure false,
    Result.ok res =>
      match res.body {
        Body.text s => IO.pure (String.beq s "{}"),
        _ => IO.pure false
      }
  }
}

#[test]
def test_dev_middleware_ignores_stream : IO Bool := do {
  let base : HandlerT IO Response :=
    HandlerT.pure_io (Sse.response (fn (_ : Unit) => IO.pure Option.none));
  let h := Live.dev_middleware_t "/live" base;
  let r <- HandlerT.run_io h dummy_req;
  match r {
    Result.err _ => IO.pure false,
    Result.ok res => IO.pure (Body.is_stream res.body)
  }
}

// ── watchers ────────────────────────────────────────────────────────────

#[test]
def test_watch_files_bumps_version : IO Bool := do {
  let name := String.concat "moon_watch_files_" (String.concat (I64.to_string process_id) ".mo");
  let p1 := String.concat "/tmp/" (String.concat name "_1");
  let p2 := String.concat "/tmp/" (String.concat name "_2");
  let _ <- IO.write_file (Path.path p1) "one";
  let _ <- IO.write_file (Path.path p2) "one";
  let version : Ref I64 <- Ref.new 0i64;
  let watcher <- Live.watch_files [Path.path p1, Path.path p2] version;
  sleepIO 600;
  let _ <- IO.write_file (Path.path p1) "two";
  let bumped <- wait_version version 1i64 60i64;
  cancel_fiber watcher;
  let _ <- exec_cmd "rm" ["-f", p1, p2];
  IO.pure bumped
}

#[test]
def test_watch_tree_ignores_target : IO Bool := do {
  let nanos <- IO.current_time_nano;
  let dir := String.concat "/tmp/moon_tree_"
    (String.concat (I64.to_string process_id) (String.concat "_" (I64.to_string nanos)));
  let target_dir := String.concat dir "/target";
  let _ <- exec_cmd "mkdir" ["-p", target_dir];
  let source := String.concat dir "/a.mo";
  let target_file := String.concat target_dir "/x.mo";
  let _ <- IO.write_file (Path.path source) "one";
  let _ <- IO.write_file (Path.path target_file) "one";
  let version : Ref I64 <- Ref.new 0i64;
  let watcher <- Live.watch_tree (Path.path dir) List.empty version;
  sleepIO 700;
  let after_target <- Ref.get version;
  let _ <- IO.write_file (Path.path source) "two";
  let bumped <- wait_version version 1i64 60i64;
  cancel_fiber watcher;
  let _ <- exec_cmd "rm" ["-rf", dir];
  IO.pure (Bool.and (I64.beq after_target 0i64) bumped)
}

// ── inotify path (with the polling fallback) ────────────────────────────
//
// These rows exercise the `std::watch` path: the watcher is started before
// the change, so what bumps is the kernel queue, not a signature diff. They
// are compiled-only for the reason `test_watch_bumps_version` gives: the Rust
// host starts fibers lazily.

def live_tmp (name : String) : String :=
  String.concat "/tmp/moon_live_"
    (String.concat (I64.to_string process_id) (String.concat "_" name))

/// A file CREATED after the watch starts bumps the version: the directory's
/// watch reports the new name, which the extension filter accepts.
#[test]
def test_watch_tree_creates_file : IO Bool := do {
  let dir := live_tmp "create";
  let _ <- exec_cmd "rm" ["-rf", dir];
  let _ <- exec_cmd "mkdir" ["-p", dir];
  let version : Ref I64 <- Ref.new 0i64;
  let watcher <- Live.watch_tree (Path.path dir) List.empty version;
  sleepIO 300;
  let _ <- IO.write_file (Path.path (String.concat dir "/new.mo")) "one";
  let bumped <- wait_version version 1i64 60i64;
  cancel_fiber watcher;
  let _ <- exec_cmd "rm" ["-rf", dir];
  IO.pure bumped
}

/// An ATOMIC SAVE -- write a temporary file, rename it over the target -- is
/// the `IN_MOVED_TO` shape every editor produces. Watching the file itself
/// would lose the watch on the first save; the directory watch sees the
/// rename.
#[test]
def test_watch_tree_atomic_save : IO Bool := do {
  let dir := live_tmp "atomic";
  let _ <- exec_cmd "rm" ["-rf", dir];
  let _ <- exec_cmd "mkdir" ["-p", dir];
  let source := String.concat dir "/a.mo";
  let _ <- IO.write_file (Path.path source) "one";
  let version : Ref I64 <- Ref.new 0i64;
  let watcher <- Live.watch_tree (Path.path dir) List.empty version;
  sleepIO 300;
  let tmp := String.concat dir "/.a.mo.tmp";
  let _ <- IO.write_file (Path.path tmp) "two";
  let _ <- exec_cmd "mv" [tmp, source];
  let bumped <- wait_version version 1i64 60i64;
  cancel_fiber watcher;
  let _ <- exec_cmd "rm" ["-rf", dir];
  IO.pure bumped
}

/// A root that does not exist yet makes inotify fail, so the watcher must
/// DEGRADE to the polling signature and still report a file created later.
#[test]
def test_watch_tree_falls_back_when_inotify_fails : IO Bool := do {
  let dir := live_tmp "fallback";
  let _ <- exec_cmd "rm" ["-rf", dir];
  let version : Ref I64 <- Ref.new 0i64;
  let watcher <- Live.watch_tree (Path.path dir) List.empty version;
  sleepIO 300;
  let _ <- exec_cmd "mkdir" ["-p", dir];
  sleepIO 500;
  let _ <- IO.write_file (Path.path (String.concat dir "/late.mo")) "one";
  let bumped <- wait_version version 1i64 80i64;
  cancel_fiber watcher;
  let _ <- exec_cmd "rm" ["-rf", dir];
  IO.pure bumped
}

/// The SSE source sees a bump on its NEXT pull: with
/// `Live.reload_poll_ms` = 100 a reload reaches the browser in ~100 ms plus
/// the watch's quiet window, not the old fixed 500 ms.
#[test]
def test_reload_source_sees_bump_on_next_pull : IO Bool := do {
  let version <- Ref.new 0i64;
  let handler := Live.reload version;
  let r <- handler dummy_req;
  match r {
    Result.err _ => IO.pure false,
    Result.ok res => live_pull_after_bump res.body version
  }
}

def live_pull_after_bump (body : Body) (version : Ref I64) : IO Bool := do {
  let first <- Body.pull body;
  let _ <- Ref.add_i64 version 1;
  let second <- Body.pull body;
  let first_ok := match first {
    Option.some bytes => String.starts_with "event: reload" (String.from_list bytes),
    Option.none => false
  };
  let second_ok := match second {
    Option.some bytes => String.starts_with "event: reload" (String.from_list bytes),
    Option.none => false
  };
  IO.pure (Bool.and first_ok second_ok)
}

/// An overflow on the fd-level queue (the single-file and explicit-set
/// watchers) must bump too: events were lost, so anything could have changed.
#[test]
def test_names_batch_matters_on_overflow : Bool :=
  let e : WatchEvent := { watch := 0 - 1, mask := 0x4000, cookie := 0, name := "" } in
  let hit : WatchEvent := { watch := 3, mask := 0x2, cookie := 0, name := "a.mo" } in
  let miss : WatchEvent := { watch := 3, mask := 0x2, cookie := 0, name := "b.mo" } in
  let watched : List WatchEvent := [hit] in
  let other : List WatchEvent := [miss] in
  Bool.and (Live.names_batch_matters ["a.mo"] watched)
    (Bool.and (Live.names_batch_matters ["a.mo"] [e])
      (Bool.not (Live.names_batch_matters ["a.mo"] other)))
