/// Live reload: an SSE endpoint fed by a file/tree watcher, plus the
/// dev-only middleware that injects the client snippet into HTML.
///
/// `Live.watch` watches one file, `Live.watch_files` an explicit input set
/// and `Live.watch_tree` a source tree filtered to the extension set below;
/// each bumps a `Ref I64` version when something it serves changes.
/// `Live.reload` streams a `reload` event for each new version (and an
/// initial one on connect) and a heartbeat otherwise.
///
/// All three prefer inotify (`std::watch`) and keep the original polling
/// signature as the fallback, so a platform without inotify (or a watch that
/// fails mid-flight) still reloads. The tree form coalesces a save's several
/// masks into one bump, resolves full paths, and picks up directories created
/// after the watch started. See `plans/implementations/inotify-file-watching.md`.

use init::clone {Clone}
use std::concurrent::combine {sleepIO}
use std::concurrent::fiber {Fiber, forkIO}
use std::hex {Hex.encode}
use std::io {IO.is_dir, IO.list_dir, IO.read_file, IO.read_file_bytes}
use std::path {Path, Path.file_name, Path.to_string}
use std::ref {Ref, Ref.add_i64, Ref.get, Ref.new, Ref.set}
use std::sha256 {Sha256.hash, Sha256.hash_bytes}
use std::stream {FdStream, Stream, StreamError}
use std::watch {
  Watch, Watch.add, Watch.any_overflow, Watch.changes, Watch.close, Watch.default_ignored,
  Watch.drain, Watch.new, Watch.next, Watch.recursive, WatchBatch, WatchEvent,
  WatchEvent.is_dir,
}
use http::sse {Sse.response, SseEvent}
use http::types {Body, Headers, Headers.get, Headers.set, HttpVersion, Request, Response, Status.ok}
use lib::context {Ctx}
use lib::handler_t {HandlerT, HandlerT.io_bind, HandlerT.run, HttpError}

// ── SSE ─────────────────────────────────────────────────────────────────

/// An SSE handler for an arbitrary event source.
pub def Live.events (source : Unit -> IO (Option SseEvent)) : Request -> IO (Result String Response) :=
  fn (_ : Request) => IO.pure (Result.ok (Sse.response source))

/// An SSE handler that emits `reload` when `version` advances. A client
/// that connects now sees one `reload` immediately (the browser is at least
/// as fresh as the server), then one per change.
pub def Live.reload (version : Ref I64) : Request -> IO (Result String Response) :=
  fn (_ : Request) => do {
    let v <- Ref.get version;
    let seen : Ref I64 <- Ref.new (I64.sub v 1i64);
    return (Result.ok (Sse.response (Live.reload_source version seen)))
  }

/// How long one `reload_source` call waits before answering; a bump reaches
/// the browser within this plus the watch's quiet window.
///
/// A `Channel` would not help here: `Channel.take` is single-consumer, so N
/// connected tabs would each need their own subscription and the SSE layer has
/// no disconnect hook to unsubscribe them. The version `Ref` is the broadcast,
/// and polling it at this interval is how every client sees every bump.
pub def Live.reload_poll_ms : I64 := 100

def Live.reload_source (version : Ref I64) (seen : Ref I64) : Unit -> IO (Option SseEvent) :=
  fn (_ : Unit) => do {
    sleepIO Live.reload_poll_ms;
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

/// The transformer-handler form of `Live.reload`.
pub def Live.reload_t (version : Ref I64) : HandlerT IO Response :=
  HandlerT.mk (fn (_ : Ctx) => do {
    let v <- Ref.get version;
    let seen : Ref I64 <- Ref.new (I64.sub v 1i64);
    IO.pure (Result.ok (Sse.response (Live.reload_source version seen)))
  })

// ── file watchers ───────────────────────────────────────────────────────
//
// Each watcher prefers inotify (`std::watch`) and falls back to the polling
// signature below when the platform has no inotify, or when the watch fails
// later (a queue error, a directory that vanished). The polling code is kept
// deliberately: it is the degradation path, and it needs no kernel feature.
//
// `Live.watch` and `Live.watch_files` watch DIRECTORIES one level deep (the
// files' parents), so an explicit input set never drags a recursive walk
// along with it; `Live.watch_tree` is the recursive form, and the one that
// resolves full paths.

/// Watch one file: inotify on its parent directory, filtered to the file's
/// name; polling when the path has no parent (a bare file name) or inotify is
/// unavailable.
pub def Live.watch (path : Path) (version : Ref I64) : IO (Fiber Unit) :=
  match (Path.parent path) {
    Option.none => forkIO (fn (_ : Unit) => Live.watch_loop path version ""),
    Option.some dir =>
      Live.watch_names [dir] [Path.file_name path] version
        (fn (_ : Unit) => Live.watch_loop path version "")
  }

/// One inotify queue over `dirs` (each ONE level deep), bumping `version`
/// when a child whose bare name is in `names` changes. `fallback` is the
/// polling loop that runs instead when inotify cannot be set up or fails
/// later.
def Live.watch_names (dirs : List Path) (names : List String) (version : Ref I64)
    (fallback : Unit -> IO Unit) : IO (Fiber Unit) := do {
  let opened <- Watch.new;
  match opened {
    Result.err _ => forkIO (fn (_ : Unit) => fallback Unit.unit),
    Result.ok stream => Live.watch_names_queued stream dirs names version fallback
  }
}

def Live.watch_names_queued (stream : FdStream) (dirs : List Path) (names : List String)
    (version : Ref I64) (fallback : Unit -> IO Unit) : IO (Fiber Unit) := do {
  let added <- Live.watch_each stream dirs;
  match added {
    Result.err _ => Live.watch_names_failed stream fallback,
    Result.ok _ => forkIO (fn (_ : Unit) => Live.watch_names_loop stream names version fallback)
  }
}

def Live.watch_names_failed (stream : FdStream) (fallback : Unit -> IO Unit)
    : IO (Fiber Unit) := do {
  let _ <- Stream.close stream;
  forkIO (fn (_ : Unit) => fallback Unit.unit)
}

#[terminating]
def Live.watch_each (stream : FdStream) (dirs : List Path) : IO (Result StreamError Unit) :=
  match dirs {
    List.empty => IO.pure (Result.ok Unit.unit),
    List.cons dir rest => do {
      let added <- Watch.add stream dir Watch.changes;
      match added {
        Result.err e => IO.pure (Result.err e),
        Result.ok _ => Live.watch_each stream rest
      }
    }
  }

#[terminating]
def Live.watch_names_loop (stream : FdStream) (names : List String) (version : Ref I64)
    (fallback : Unit -> IO Unit) : IO Unit := do {
  let got <- Watch.next stream 1000;
  match got {
    Result.err _ => do {
      let _ <- Stream.close stream;
      fallback Unit.unit
    },
    Result.ok evs =>
      if Live.names_batch_matters names evs
      then do {
        let _ <- Ref.add_i64 version 1;
        Live.watch_names_loop stream names version fallback
      }
      else Live.watch_names_loop stream names version fallback
  }
}

/// Whether a read from the fd-level queue is worth a bump: a watched name
/// changed, or the kernel's queue overflowed (events were lost, so anything
/// could have changed -- the same rule `Live.batch_relevant` applies to the
/// tree form).
pub def Live.names_batch_matters (names : List String) (evs : List WatchEvent) : Bool :=
  Bool.or (Live.events_any_name names evs) (Watch.any_overflow evs)

#[terminating]
def Live.events_any_name (names : List String) (evs : List WatchEvent) : Bool :=
  match evs {
    List.empty => false,
    List.cons e rest =>
      if Live.mem_string e.name names
      then true
      else Live.events_any_name names rest
  }

/// Poll the file's SHA-256: the single-file fallback.
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

/// Watch an explicit input set. The parents are watched one level deep (no
/// subtree walk), so this stays cheap even for a file directly in /tmp; a
/// path with no parent, or a platform without inotify, falls back to polling
/// the same digest signature the pre-inotify watcher used.
///
/// Names are matched by BARE NAME across the watched directories, so two
/// inputs called `main.mo` in different directories bump for either: an extra
/// reload, never a missed one.
pub def Live.watch_files (paths : List Path) (version : Ref I64) : IO (Fiber Unit) :=
  match (Live.parents_of paths) {
    Option.none => Live.watch_files_poll paths version,
    Option.some dirs => Live.watch_files_watched paths dirs version
  }

def Live.watch_files_watched (paths : List Path) (dirs : List Path) (version : Ref I64)
    : IO (Fiber Unit) :=
  Live.watch_names dirs (Live.file_names paths) version
    (fn (_ : Unit) => Live.watch_files_poll_body paths version)

def Live.file_names (paths : List Path) : List String :=
  List.map (fn (p : Path) => Path.file_name p) paths

#[terminating]
def Live.parents_of (paths : List Path) : Option (List Path) :=
  match paths {
    List.empty => Option.some List.empty,
    List.cons p rest => Live.parent_of p rest
  }

#[terminating]
def Live.parent_of (p : Path) (rest : List Path) : Option (List Path) :=
  match (Path.parent p) {
    Option.none => Option.none,
    Option.some dir => Live.parents_cons dir rest
  }

#[terminating]
def Live.parents_cons (dir : Path) (rest : List Path) : Option (List Path) :=
  match (Live.parents_of rest) {
    Option.none => Option.none,
    Option.some dirs => Option.some (List.cons dir dirs)
  }

def Live.watch_files_poll (paths : List Path) (version : Ref I64) : IO (Fiber Unit) :=
  forkIO (fn (_ : Unit) => Live.watch_files_poll_body paths version)

def Live.watch_files_poll_body (paths : List Path) (version : Ref I64) : IO Unit := do {
  let initial <- Live.signature_of_files paths;
  Live.watch_files_loop paths version initial
}

#[terminating]
def Live.watch_files_loop (paths : List Path) (version : Ref I64) (last : String) : IO Unit := do {
  sleepIO 400;
  let sig <- Live.signature_of_files paths;
  if String.beq sig last
  then Live.watch_files_loop paths version last
  else do {
    let _ <- Ref.add_i64 version 1;
    Live.watch_files_loop paths version sig
  }
}

#[terminating]
def Live.signature_of_files (paths : List Path) : IO String :=
  Live.signature_of_files_go paths ""

#[terminating]
def Live.signature_of_files_go (paths : List Path) (acc : String) : IO String :=
  match paths {
    List.empty => IO.pure acc,
    List.cons p rest => do {
      let h <- Live.file_digest p;
      let line := String.concat (Path.to_string p) (String.concat ":" h);
      Live.signature_of_files_go rest (String.concat acc (String.concat line "\n"))
    }
  }

def Live.file_digest (p : Path) : IO String := do {
  let r <- IO.read_file_bytes p;
  match r {
    Result.err _ => IO.pure "missing",
    Result.ok bytes => IO.pure (Hex.encode (Sha256.hash_bytes bytes))
  }
}

/// Watch a source tree: one recursive inotify watch, with the polling
/// signature as the fallback.
pub def Live.watch_tree (root : Path) (ignored : List String)
    (version : Ref I64) : IO (Fiber Unit) := do {
  let opened <- Watch.recursive root (List.append Watch.default_ignored ignored);
  match opened {
    Result.err _ => Live.watch_tree_poll root ignored version,
    Result.ok w => forkIO (fn (_ : Unit) => Live.watch_tree_inotify w root ignored version)
  }
}

/// The inotify loop: one `Watch.drain` per second at worst, so an idle tree
/// costs one blocked `poll(2)`; a batch bumps the version once, however many
/// events it carried.
#[terminating]
def Live.watch_tree_inotify (w : Watch) (root : Path) (ignored : List String)
    (version : Ref I64) : IO Unit := do {
  let got <- Watch.drain (Shared.of w) 1000 50;
  match got {
    Result.err _ => Live.watch_tree_degrade w root ignored version,
    Result.ok batch =>
      if Live.batch_relevant batch
      then do {
        let _ <- Ref.add_i64 version 1;
        Live.watch_tree_inotify w root ignored version
      }
      else Live.watch_tree_inotify w root ignored version
  }
}

/// A watch that failed mid-flight: close it and spend the rest of the fiber
/// on the polling signature, which needs no kernel state.
def Live.watch_tree_degrade (w : Watch) (root : Path) (ignored : List String)
    (version : Ref I64) : IO Unit := do {
  let _ <- Watch.close w;
  Live.watch_tree_poll_body root ignored version
}

/// A batch matters when it touched a file the extension set serves, changed a
/// directory, or lost events (the kernel's queue overflowed: anything could
/// have changed, so reload).
def Live.batch_relevant (batch : WatchBatch) : Bool :=
  Bool.or batch.overflow (Live.events_relevant batch.events)

#[terminating]
def Live.events_relevant (pairs : List (Pair WatchEvent Path)) : Bool :=
  match pairs {
    List.empty => false,
    List.cons p rest =>
      match p {
        Pair.pair event path =>
          if Live.tree_event_relevant event path
          then true
          else Live.events_relevant rest
      }
  }

def Live.tree_event_relevant (event : WatchEvent) (path : Path) : Bool :=
  Bool.or (WatchEvent.is_dir event) (Live.watched_file (Path.file_name path))

/// The polling tree watcher: kept as the fallback, and public so a caller can
/// choose it explicitly.
pub def Live.watch_tree_poll (root : Path) (ignored : List String)
    (version : Ref I64) : IO (Fiber Unit) :=
  forkIO (fn (_ : Unit) => Live.watch_tree_poll_body root ignored version)

def Live.watch_tree_poll_body (root : Path) (ignored : List String)
    (version : Ref I64) : IO Unit := do {
  let initial <- Live.tree_signature root ignored;
  Live.watch_tree_poll_loop root ignored version initial
}

#[terminating]
def Live.watch_tree_poll_loop (root : Path) (ignored : List String)
    (version : Ref I64) (last : String) : IO Unit := do {
  sleepIO 400;
  let sig <- Live.tree_signature root ignored;
  if String.beq sig last
  then Live.watch_tree_poll_loop root ignored version last
  else do {
    let _ <- Ref.add_i64 version 1;
    Live.watch_tree_poll_loop root ignored version sig
  }
}

def Live.tree_signature (root : Path) (ignored : List String) : IO String := do {
  let entries <- IO.list_dir root;
  let files <- Live.collect_files entries ignored List.empty;
  Live.signature_of_files files
}

#[terminating]
def Live.collect_files (entries : List Path) (ignored : List String)
    (acc : List Path) : IO (List Path) :=
  match entries {
    List.empty => IO.pure (List.reverse acc),
    List.cons p rest => do {
      let is_dir <- IO.is_dir p;
      if is_dir
      then
        if Live.ignored_name (Path.file_name p) ignored
        then Live.collect_files rest ignored acc
        else do {
          let children <- IO.list_dir p;
          let acc2 <- Live.collect_files children ignored acc;
          Live.collect_files rest ignored acc2
        }
      else if Live.watched_file (Path.file_name p)
      then Live.collect_files rest ignored (List.cons p acc)
      else Live.collect_files rest ignored acc
    }
  }

/// Build outputs and VCS data are never watched.
def Live.ignored_name (name : String) (ignored : List String) : Bool :=
  if String.beq name "target"
    || String.starts_with "target-" name
    || String.beq name ".git"
    || String.beq name "node_modules"
    || String.beq name ".devenv"
  then true
  else Live.mem_string name ignored

#[terminating]
def Live.mem_string (name : String) (xs : List String) : Bool :=
  match xs {
    List.empty => false,
    List.cons x rest =>
      if String.beq name x then true else Live.mem_string name rest
  }

def Live.watched_file (name : String) : Bool :=
  let n := String.to_lowercase name in
  if Bool.or (String.ends_with n ".mo") (String.ends_with n ".html")
  then true
  else if Bool.or (String.ends_with n ".htm") (String.ends_with n ".css")
  then true
  else if Bool.or (String.ends_with n ".js") (String.ends_with n ".mjs")
  then true
  else if Bool.or (String.ends_with n ".json") (String.ends_with n ".wasm")
  then true
  else String.beq n "mote.toml"

// ── the client snippet and dev middleware ──────────────────────────────

/// The client snippet: reload the page on a `reload` event. The endpoint is
/// sanitized so a path cannot close the string or the script element.
pub def Live.script (endpoint : String) : String :=
  let safe := String.from_list (Live.js_safe (String.to_list endpoint)) in
  String.concat "<script>const s = new EventSource(\""
    (String.concat safe
      "\"); s.addEventListener(\"reload\", () => location.reload());</script>")

#[terminating]
def Live.js_safe (bytes : List U8) : List U8 :=
  match bytes {
    List.empty => List.empty,
    List.cons b rest =>
      if U8.beq b 34u8
        || U8.beq b 92u8
        || U8.beq b 60u8
        || U8.beq b 10u8
        || U8.beq b 13u8
      then Live.js_safe rest
      else List.cons b (Live.js_safe rest)
  }

/// Inject the reload script into a successful HTML response and mark it
/// `no-store`. Non-200, non-HTML and streamed bodies pass through.
pub def Live.inject (res : Response) (endpoint : String) : Response :=
  match res {
    { status, headers, version, body } =>
      Live.inject_parts status headers version body endpoint
  }

def Live.inject_parts (status : U16) (headers : Headers) (version : HttpVersion)
    (body : Body) (endpoint : String) : Response :=
  let hb : Shared Headers := Shared.of headers in
  if Bool.not (U16.beq status Status.ok)
  then { status := status, headers := Clone.clone hb, version := version, body := body }
  else
    match body {
      Body.text s =>
        match Headers.get "Content-Type" (Shared.get hb) {
          Option.some ct =>
            if String.contains (String.to_lowercase ct) "text/html"
            then
              let injected := String.concat s (Live.script endpoint) in
              let hs := Headers.set "Cache-Control" "no-store" (Shared.get hb) in
              let res2 : Response :=
                { status := status, headers := hs, version := version,
                  body := Body.text injected } in
              res2
            else
              { status := status, headers := Clone.clone hb, version := version,
                body := Body.text s },
          Option.none =>
            { status := status, headers := Clone.clone hb, version := version,
              body := Body.text s }
        },
      Body.empty =>
        { status := status, headers := Clone.clone hb, version := version, body := Body.empty },
      Body.bytes data =>
        { status := status, headers := Clone.clone hb, version := version, body := Body.bytes data },
      Body.stream next =>
        { status := status, headers := Clone.clone hb, version := version, body := Body.stream next },
      Body.form fields =>
        { status := status, headers := Clone.clone hb, version := version, body := Body.form fields }
    }

/// Old-API dev middleware.
pub def Live.dev_middleware (endpoint : String)
    (next : Request -> IO Response) : Request -> IO Response :=
  fn (req : Request) => do {
    let res <- next req;
    IO.pure (Live.inject res endpoint)
  }

/// Transformer dev middleware.
pub def Live.dev_middleware_t (endpoint : String)
    (next : HandlerT IO Response) : HandlerT IO Response :=
  HandlerT.mk (fn (ctx : Ctx) =>
    HandlerT.io_bind (HandlerT.run next ctx) (fn (r : Result HttpError Response) =>
      match r {
        Result.ok res => IO.pure (Result.ok (Live.inject res endpoint)),
        Result.err e => IO.pure (Result.err e)
      }))
