/// Live-reload tests: the SSE reload source, the file watcher, and the client
/// snippet.

use std::concurrent::combine {sleepIO}
use std::io {IO.write_file}
use std::path {Path}
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

#[test]
def test_watch_bumps_version : IO Bool := do {
  let name := String.concat "moon_live_watch_" (String.concat (I64.to_string process_id) ".txt");
  let path := String.concat "/tmp/" name;
  let _ <- IO.write_file (Path.path path) "one";
  let version <- Ref.new 0i64;
  let _ <- Live.watch (Path.path path) version;
  sleepIO 700;
  let v <- Ref.get version;
  return (I64.gt v 0)
}

#[test]
def test_script_is_a_script : Bool :=
  Bool.and (String.starts_with "<script>" (Live.script "/live"))
    (String.ends_with (Live.script "/live") "</script>")
