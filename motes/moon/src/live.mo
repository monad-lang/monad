/// Live reload: an SSE endpoint fed by a file/tree watcher, plus the
/// dev-only middleware that injects the client snippet into HTML.
///
/// `Live.watch` polls one file's SHA-256 every 500 ms and bumps a `Ref I64`
/// version when it changes. `Live.watch_files` and `Live.watch_tree` are the
/// dev-server forms: explicit input files, or a source tree filtered to the
/// extension set below. `Live.reload` streams a `reload` event for each new
/// version (and an initial one on connect) and a heartbeat otherwise.
///
/// Polling, not inotify: there is no file-watcher native, and a 400–500 ms
/// poll is enough for a development loop. Hashing whole files is the cost;
/// an mtime native would make the poll cheap and is the next step.

use init::borrow {Borrow, Borrow.get}
use std::concurrent::combine {sleepIO}
use std::concurrent::fiber {Fiber, forkIO}
use std::hex {Hex.encode}
use std::io {IO.is_dir, IO.list_dir, IO.read_file, IO.read_file_bytes}
use std::list {List.length}
use std::path {Path, Path.file_name, Path.to_string}
use std::ref {Ref, Ref.add_i64, Ref.get, Ref.new, Ref.set}
use std::sha256 {Sha256.hash, Sha256.hash_bytes}
use http::sse {Sse.response, SseEvent}
use http::types {Body, Headers, Headers.get, Headers.set, HttpVersion, Request, Response, Status.ok}
use lib::context {Ctx, Ctx.request}
use lib::handler_t {
  HandlerT, HandlerT.io_bind, HandlerT.run, HttpError, HttpError.make,
}

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

/// The transformer-handler form of `Live.reload`.
pub def Live.reload_t (version : Ref I64) : HandlerT IO Response :=
  HandlerT.mk (fn (ctx : Borrow Ctx) =>
    HandlerT.io_bind (Live.reload version (Borrow.get (Ctx.request (Borrow.get ctx))))
      (fn (r : Result String Response) =>
        match r {
          Result.ok res => IO.pure (Result.ok res),
          Result.err e => IO.pure (Result.err (Live.io_error e))
        }))

/// Lift the old handler's string error into `HttpError`.
def Live.io_error (e : String) : HttpError :=
  HttpError.make 500u16 e

// ── file watchers ───────────────────────────────────────────────────────

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

/// Poll an explicit input set. The dev script knows exactly what it
/// consumes, so this is the cheap form.
pub def Live.watch_files (paths : List Path) (version : Ref I64) : IO (Fiber Unit) := do {
  let initial <- Live.signature_of_files paths;
  forkIO (fn (_ : Unit) => Live.watch_files_loop paths version initial)
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

/// Poll a source tree. Only the extension set in `Live.watched_file` is
/// hashed; `ignored` names (and `target`, `target-*`) are skipped.
pub def Live.watch_tree (root : Path) (ignored : List String)
    (version : Ref I64) : IO (Fiber Unit) := do {
  let initial <- Live.tree_signature root ignored;
  forkIO (fn (_ : Unit) => Live.watch_tree_loop root ignored version initial)
}

#[terminating]
def Live.watch_tree_loop (root : Path) (ignored : List String)
    (version : Ref I64) (last : String) : IO Unit := do {
  sleepIO 400;
  let sig <- Live.tree_signature root ignored;
  if String.beq sig last
  then Live.watch_tree_loop root ignored version last
  else do {
    let _ <- Ref.add_i64 version 1;
    Live.watch_tree_loop root ignored version sig
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
  let hb : Borrow Headers := Borrow.of headers in
  if Bool.not (U16.beq status Status.ok)
  then { status := status, headers := Borrow.get hb, version := version, body := body }
  else
    match body {
      Body.text s =>
        match Headers.get "Content-Type" (Borrow.get hb) {
          Option.some ct =>
            if String.contains (String.to_lowercase ct) "text/html"
            then
              let injected := String.concat s (Live.script endpoint) in
              let hs := Headers.set "Cache-Control" "no-store" (Borrow.get hb) in
              let res2 : Response :=
                { status := status, headers := hs, version := version,
                  body := Body.text injected } in
              res2
            else
              { status := status, headers := Borrow.get hb, version := version,
                body := Body.text s },
          Option.none =>
            { status := status, headers := Borrow.get hb, version := version,
              body := Body.text s }
        },
      Body.empty =>
        { status := status, headers := Borrow.get hb, version := version, body := Body.empty },
      Body.bytes data =>
        { status := status, headers := Borrow.get hb, version := version, body := Body.bytes data },
      Body.stream next =>
        { status := status, headers := Borrow.get hb, version := version, body := Body.stream next },
      Body.form fields =>
        { status := status, headers := Borrow.get hb, version := version, body := Body.form fields }
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
  HandlerT.mk (fn (ctx : Borrow Ctx) =>
    HandlerT.io_bind (HandlerT.run next ctx) (fn (r : Result HttpError Response) =>
      match r {
        Result.ok res => IO.pure (Result.ok (Live.inject res endpoint)),
        Result.err e => IO.pure (Result.err e)
      }))
