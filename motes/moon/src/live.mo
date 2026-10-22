/// Live reload: an SSE endpoint fed by a file-watch fiber.
///
/// `Live.watch` polls a file's SHA-256 every 500 ms and bumps a `Ref I64`
/// version when it changes. `Live.reload` streams a `reload` event for each
/// new version and a heartbeat comment otherwise; `Live.script` is the
/// client that listens for it.
///
/// Polling, not inotify: there is no file-watcher native, and a 500 ms poll
/// is enough for a development loop.

use std::concurrent::combine {sleepIO}
use std::concurrent::fiber {Fiber, forkIO}
use std::io {IO.read_file}
use std::path {Path}
use std::ref {Ref, Ref.add_i64, Ref.get, Ref.new, Ref.set}
use std::sha256 {Sha256.hash}
use http::sse {Sse.response, SseEvent}
use http::types {Request, Response}

/// An SSE handler for an arbitrary event source.
pub def Live.events (source : Unit -> IO (Option SseEvent)) : Request -> IO (Result String Response) :=
  fn (_ : Request) => IO.pure (Result.ok (Sse.response source))

/// An SSE handler that emits `reload` when `version` advances, and a
/// heartbeat otherwise.
pub def Live.reload (version : Ref I64) : Request -> IO (Result String Response) :=
  fn (_ : Request) => do {
    let seen : Ref I64 <- Ref.new 0i64;
    return (Result.ok (Sse.response (Live.reload_source version seen)))
  }

def Live.reload_source (version : Ref I64) (seen : Ref I64) : Unit -> IO (Option SseEvent) :=
  fn (_ : Unit) => do {
    sleepIO 500;
    let v <- Ref.get version;
    let s <- Ref.get seen;
    if I64.gt v s
    then do {
      Ref.set seen v;
      let ev : SseEvent := { event := "reload", data := I64.to_string v };
      return (Option.some ev)
    }
    else do {
      let ev : SseEvent := { event := "heartbeat", data := "" };
      return (Option.some ev)
    }
  }

/// Poll `path` in a fiber; each content change bumps `version`.
pub def Live.watch (path : Path) (version : Ref I64) : IO (Fiber Unit) :=
  forkIO (fn (_ : Unit) => Live.watch_loop path version "")

#[terminating]
def Live.watch_loop (path : Path) (version : Ref I64) (last : String) : IO Unit := do {
  sleepIO 500;
  let r <- IO.read_file path;
  match r {
    Result.err _ => Live.watch_loop path version last,
    Result.ok text =>
      let h := Sha256.hash text in
      if String.beq h last
      then Live.watch_loop path version last
      else do {
        let _ <- Ref.add_i64 version 1;
        Live.watch_loop path version h
      }
  }
}

/// The client snippet: reload the page on a `reload` event.
pub def Live.script (endpoint : String) : String :=
  String.concat "<script>const s = new EventSource(\""
    (String.concat endpoint
      "\"); s.addEventListener(\"reload\", () => location.reload());</script>")
