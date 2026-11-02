/// Tests for `std/src/watch.mo`: the pure decoder and predicates, then the
/// tree form against real directories under /tmp.
///
/// A separate file for the reason `stream_tests.mo` gives. The wire format is
/// pinned with hand-built `inotify_event` records (no filesystem), the tree
/// rows use real ones, and `slow_tests/src/watch_e2e_tests.mo` adds a compiled
/// end-to-end program through the real pipeline.
use init::shared {Shared.get, of}
use std::io {IO.write_file}
use std::list {List.length}
use std::path {Path}
use std::process {exec_cmd, process_id}
use std::stream {StreamError}
use std::watch {
  Watch, Watch.any_overflow, Watch.close, Watch.decode, Watch.default_ignored,
  Watch.drain, Watch.event_path, Watch.ignore_dir, Watch.recursive,
  WatchBatch, WatchEvent, WatchEvent.closed_for_write, WatchEvent.created,
  WatchEvent.deleted,
  WatchEvent.has, WatchEvent.ignored, WatchEvent.is_dir, WatchEvent.moved_from,
  WatchEvent.moved_to, WatchEvent.overflowed, WatchEvent.removed_self,
}

// ── building the wire form ───────────────────────────────────────────────
//
// `inotify_event`: watch descriptor (i32 LE), mask (u32 LE), cookie (u32
// LE), name length INCLUDING the NUL padding (u32 LE), then the padded
// name. `len` makes the record a multiple of 16.

#[terminating]
def wt_two_pow (k : I64) : I64 :=
  if I64.lt k 1 then 1 else 2 * wt_two_pow (k - 1)

/// Byte `k` of `n`, little-endian order.
def wt_byte (n : I64) (k : I64) : U8 :=
  U32.to_u8 (I64.to_u32 (I64.div n (wt_two_pow (I64.mul 8 k))))

def wt_u32 (n : I64) : List U8 :=
  [wt_byte n 0, wt_byte n 1, wt_byte n 2, wt_byte n 3]

#[terminating]
def wt_zeros (n : I64) : List U8 :=
  if I64.lt n 1 then List.empty else List.cons 0u8 (wt_zeros (n - 1))

/// The padded name length for a name of `n` bytes (`n + 1` NUL, rounded up
/// to 16).
def wt_pad_len (n : I64) : I64 :=
  let raw := n + 1 in
  I64.mul 16 (I64.div (raw + 15) 16)

def wt_event (watch : I64) (mask : I64) (cookie : I64) (name : String) : List U8 :=
  let name_len := List.length (String.to_list name) in
  let padded := wt_pad_len name_len in
  let pad := I64.sub padded name_len in
  let header := List.append (wt_u32 watch)
    (List.append (wt_u32 mask) (List.append (wt_u32 cookie) (wt_u32 padded))) in
  List.append header
    (List.append (String.to_list name) (wt_zeros pad))

/// A header claiming a 32-byte name with only two bytes behind it: the
/// incomplete tail the decoder must drop.
def wt_truncated_tail (watch : I64) (mask : I64) : List U8 :=
  List.append (wt_u32 watch)
    (List.append (wt_u32 mask)
      (List.append (wt_u32 0) (List.append (wt_u32 32) (String.to_list "ab"))))

// ── reading a decoded event ──────────────────────────────────────────────

def wt_first_name (evs : List WatchEvent) : String :=
  match evs {
    List.cons e _ => e.name,
    List.empty => "<none>"
  }

def wt_first_watch (evs : List WatchEvent) : I64 :=
  match evs {
    List.cons e _ => e.watch,
    List.empty => 0 - 1
  }

def wt_first_mask (evs : List WatchEvent) : I64 :=
  match evs {
    List.cons e _ => e.mask,
    List.empty => 0 - 1
  }

def wt_first_cookie (evs : List WatchEvent) : I64 :=
  match evs {
    List.cons e _ => e.cookie,
    List.empty => 0 - 1
  }

def wt_count (evs : List WatchEvent) : I64 := List.length evs

/// Whether the FIRST event satisfies `check` (false for an empty list).
def wt_first_ok (evs : List WatchEvent) (check : WatchEvent -> Bool) : Bool :=
  match evs {
    List.cons e _ => check e,
    List.empty => false
  }

// ── the tests ────────────────────────────────────────────────────────────

#[test]
def test_watch_decode_one : Bool :=
  let evs := Watch.decode (wt_event 5 0x100 0 "a.mo") in
  let fields_ok := I64.beq (wt_first_watch evs) 5
    && I64.beq (wt_first_mask evs) 0x100
    && I64.beq (wt_first_cookie evs) 0 in
  I64.beq (wt_count evs) 1 && fields_ok && String.beq (wt_first_name evs) "a.mo"

/// A name of exactly 16 bytes gets one NUL and no padding beyond the block;
/// the next event must still start at the right offset.
#[test]
def test_watch_decode_exact_block_name : Bool :=
  let name := "0123456789abcdef" in
  let bytes := List.append (wt_event 1 0x2 0 name) (wt_event 2 0x200 0 "b") in
  let evs := Watch.decode bytes in
  I64.beq (wt_count evs) 2 && String.beq (wt_first_name evs) name

/// Two records back to back, the second about the watched directory itself
/// (a zero-length name).
#[test]
def test_watch_decode_two_and_zero_name : Bool :=
  let bytes := List.append (wt_event 1 0x2 0 "x.mo") (wt_event 1 0x400 0 "") in
  let evs := Watch.decode bytes in
  let second := match evs {
    List.cons _ rest => wt_first_name rest,
    List.empty => "<none>"
  } in
  I64.beq (wt_count evs) 2 && String.beq (wt_first_name evs) "x.mo"
    && String.beq second ""

/// An incomplete tail is dropped, not guessed at: the kernel refuses to
/// split an event into a 4 KiB read, but a short hand-built buffer can.
#[test]
def test_watch_decode_truncated_tail : Bool :=
  let bytes := List.append (wt_event 1 0x2 0 "ok") (wt_truncated_tail 1 0x2) in
  let evs := Watch.decode bytes in
  I64.beq (wt_count evs) 1 && String.beq (wt_first_name evs) "ok"

#[test]
def test_watch_decode_empty_is_empty : Bool :=
  I64.beq (wt_count (Watch.decode List.empty)) 0

// One predicate per named def: a lambda calling the accessors is the
// constrained-call-in-a-lambda shape the codegen bug lives in, and these
// tests run compiled too.

def wt_is_created_dir (e : WatchEvent) : Bool :=
  WatchEvent.created e && WatchEvent.is_dir e && Bool.not (WatchEvent.deleted e)

/// The predicates read the mask the way the mask bits name it.
#[test]
def test_watch_event_predicates : Bool :=
  wt_first_ok (Watch.decode (wt_event 1 0x40000100 0 "dir")) wt_is_created_dir

def wt_is_moved_to (e : WatchEvent) : Bool :=
  WatchEvent.moved_to e && Bool.not (WatchEvent.created e)
    && Bool.not (WatchEvent.moved_from e)

def wt_is_closed (e : WatchEvent) : Bool := WatchEvent.closed_for_write e

def wt_is_removed_self (e : WatchEvent) : Bool := WatchEvent.removed_self e

def wt_is_ignored (e : WatchEvent) : Bool :=
  WatchEvent.ignored e && Bool.not (WatchEvent.overflowed e)

/// `IN_MOVED_TO` is the atomic-save signal; `IN_CLOSE_WRITE` the plain one.
#[test]
def test_watch_event_move_and_close : Bool :=
  let moved := Watch.decode (wt_event 1 0x80 9 "new.mo") in
  let closed := Watch.decode (wt_event 1 0x8 0 "edit.mo") in
  wt_first_ok moved wt_is_moved_to && wt_first_ok closed wt_is_closed

/// A closed watch reports `IN_IGNORED`; nothing else arrives on that handle.
#[test]
def test_watch_event_ignored_is_not_overflow : Bool :=
  let dropped := Watch.decode (wt_event 1 0x8000 0 "") in
  wt_first_ok dropped wt_is_ignored

/// The watched directory going away.
#[test]
def test_watch_event_removed_self : Bool :=
  wt_first_ok (Watch.decode (wt_event 1 0x400 0 "")) wt_is_removed_self

def wt_is_self_moved_only (e : WatchEvent) : Bool :=
  WatchEvent.self_moved e && Bool.not (WatchEvent.self_deleted e)

def wt_is_self_deleted (e : WatchEvent) : Bool := WatchEvent.self_deleted e

/// `IN_MOVE_SELF` and `IN_DELETE_SELF` are different answers: a rename keeps
/// the watch (the descriptor names an inode), a deletion ends it.
#[test]
def test_watch_event_move_self_is_not_a_delete : Bool :=
  Bool.and
    (wt_first_ok (Watch.decode (wt_event 1 0x800 0 "")) wt_is_self_moved_only)
    (Bool.and
      (wt_first_ok (Watch.decode (wt_event 1 0x400 0 "")) wt_is_self_deleted)
      (Bool.not (wt_first_ok (Watch.decode (wt_event 1 0x800 0 "")) wt_is_self_deleted)))

def wt_has_modify_not_create (e : WatchEvent) : Bool :=
  WatchEvent.has e 0x2 && Bool.not (WatchEvent.has e 0x100)

/// `has` is bit membership, not equality: a combined mask answers yes to
/// each of its bits.
#[test]
def test_watch_event_has_is_membership : Bool :=
  let evs := Watch.decode (wt_event 1 0x402 0 "") in
  wt_first_ok evs wt_has_modify_not_create && wt_first_ok evs wt_is_removed_self

// ── the tree form: filesystem rows ───────────────────────────────────────
//
// Real directories under /tmp, like `stream_tests.mo`: nothing below the
// natives can be mocked. A `Watch.recursive` that fails with ENOSYS means this
// host has no inotify (the non-Linux stubs), and the row is SKIPPED there
// rather than failed.

def wt_tmp (name : String) : String :=
  "/tmp/monad_watch_tests_" ++ I64.to_string process_id ++ "_" ++ name

def wt_rm (dir : String) : IO Unit := do {
  let _ <- exec_cmd "rm" ["-rf", dir];
  IO.pure Unit.unit
}

def wt_mkdir (dir : String) : IO Unit := do {
  let _ <- exec_cmd "mkdir" ["-p", dir];
  IO.pure Unit.unit
}

def wt_write (path : String) (text : String) : IO Unit := do {
  let _ <- IO.write_file (Path.path path) text;
  IO.pure Unit.unit
}

/// `true` when the watch could not be created because this platform has no
/// inotify: the row is skipped, not failed.
def wt_unsupported (e : StreamError) : Bool :=
  String.contains e.message "not implemented"

#[terminating]
def wt_saw_path (events : List (Pair WatchEvent Path)) (target : String) : Bool :=
  match events {
    List.empty => false,
    List.cons p rest =>
      match p {
        Pair.pair _ path =>
          if String.beq (Path.to_string path) target
          then true
          else wt_saw_path rest target
      }
  }

#[terminating]
def wt_saw_dir (events : List (Pair WatchEvent Path)) (target : String) : Bool :=
  match events {
    List.empty => false,
    List.cons p rest =>
      match p {
        Pair.pair e path =>
          if Bool.and (WatchEvent.is_dir e) (String.beq (Path.to_string path) target)
          then true
          else wt_saw_dir rest target
      }
  }

/// Whether ANY event names a path under `prefix` -- the negative half of the
/// ignored-directory row.
#[terminating]
def wt_saw_under (events : List (Pair WatchEvent Path)) (prefix : String) : Bool :=
  match events {
    List.empty => false,
    List.cons p rest =>
      match p {
        Pair.pair _ path =>
          if String.starts_with prefix (Path.to_string path)
          then true
          else wt_saw_under rest prefix
      }
  }

def wt_close_false (w : Watch) (root : String) : IO Bool := do {
  Watch.close w;
  wt_rm root;
  IO.pure false
}

/// A write two directories down resolves to its full path: the walk watched
/// every directory, and `Watch.drain` resolved the bare name through the map.
#[test]
def test_watch_recursive_nested_edit : IO Bool := do {
  let root := wt_tmp "nested";
  wt_rm root;
  wt_mkdir (root ++ "/a/b");
  wt_write (root ++ "/a/b/one.mo") "one";
  let opened <- Watch.recursive (Path.path root) List.empty;
  match opened {
    Result.err e => IO.pure (wt_unsupported e),
    Result.ok w => wt_nested_edit w root
  }
}

def wt_nested_edit (w : Watch) (root : String) : IO Bool := do {
  wt_write (root ++ "/a/b/one.mo") "two";
  let r <- Watch.drain (Shared.of w) 2000 50;
  Watch.close w;
  wt_rm root;
  match r {
    Result.err _ => IO.pure false,
    Result.ok b => IO.pure (wt_saw_path b.events (root ++ "/a/b/one.mo"))
  }
}

/// A directory created AFTER the watch is watched from its creation: the
/// create event reports it, and a file written into it afterwards is seen.
#[test]
def test_watch_recursive_new_directory : IO Bool := do {
  let root := wt_tmp "newdir";
  wt_rm root;
  wt_mkdir root;
  let opened <- Watch.recursive (Path.path root) List.empty;
  match opened {
    Result.err e => IO.pure (wt_unsupported e),
    Result.ok w => wt_new_directory w root
  }
}

def wt_new_directory (w : Watch) (root : String) : IO Bool := do {
  wt_mkdir (root ++ "/newdir");
  let first <- Watch.drain (Shared.of w) 2000 50;
  match first {
    Result.err _ => wt_close_false w root,
    Result.ok b => wt_new_directory_added w root b
  }
}

def wt_new_directory_added (w : Watch) (root : String) (b : WatchBatch) : IO Bool := do {
  let saw_dir := wt_saw_dir b.events (root ++ "/newdir");
  wt_write (root ++ "/newdir/x.mo") "x";
  let second <- Watch.drain (Shared.of w) 2000 50;
  Watch.close w;
  wt_rm root;
  match second {
    Result.err _ => IO.pure false,
    Result.ok b2 =>
      IO.pure (Bool.and saw_dir (wt_saw_path b2.events (root ++ "/newdir/x.mo")))
  }
}

/// `Watch.default_ignored` keeps `target/` out of the map: a write there is
/// silent, while the same write in a kept directory is reported.
#[test]
def test_watch_recursive_ignored_directory : IO Bool := do {
  let root := wt_tmp "ignored";
  wt_rm root;
  wt_mkdir (root ++ "/target");
  wt_mkdir (root ++ "/keep");
  let opened <- Watch.recursive (Path.path root) Watch.default_ignored;
  match opened {
    Result.err e => IO.pure (wt_unsupported e),
    Result.ok w => wt_ignored_directory w root
  }
}

def wt_ignored_directory (w : Watch) (root : String) : IO Bool := do {
  wt_write (root ++ "/target/x.mo") "x";
  wt_write (root ++ "/keep/y.mo") "y";
  let r <- Watch.drain (Shared.of w) 2000 50;
  Watch.close w;
  wt_rm root;
  match r {
    Result.err _ => IO.pure false,
    Result.ok b =>
      let evs := Shared.of b.events in
      IO.pure (Bool.and (wt_saw_path (Shared.get evs) (root ++ "/keep/y.mo"))
        (Bool.not (wt_saw_under (Shared.get evs) (root ++ "/target"))))
  }
}

// ── the tree form: pure rows ─────────────────────────────────────────────

#[test]
def test_watch_ignore_dir_names : Bool :=
  Bool.and (Watch.ignore_dir "target" Watch.default_ignored)
    (Bool.and (Watch.ignore_dir "target-nix" Watch.default_ignored)
      (Bool.and (Watch.ignore_dir ".git" Watch.default_ignored)
        (Bool.and (Bool.not (Watch.ignore_dir "src" Watch.default_ignored))
          (Bool.not (Watch.ignore_dir "keep" List.empty)))))

#[test]
def test_watch_any_overflow : Bool :=
  Bool.and (Watch.any_overflow (Watch.decode (wt_event 0 0x4000 0 "")))
    (Bool.and (Bool.not (Watch.any_overflow (Watch.decode (wt_event 1 0x2 0 "x.mo"))))
      (Bool.not (Watch.any_overflow List.empty)))

def wt_path_of_first (dirs : List (Pair I64 Path)) (root : Path) (evs : List WatchEvent) : String :=
  match evs {
    List.cons e _ => Path.to_string (Watch.event_path dirs root e),
    List.empty => "<none>"
  }

/// A child event joins to its directory; a zero-name event IS its directory;
/// an unknown descriptor falls back to the root.
#[test]
def test_watch_event_path : Bool :=
  let dirs := [Pair.pair 5 (Path.path "/root/a")] in
  let root := Path.path "/root" in
  Bool.and
    (String.beq (wt_path_of_first dirs root (Watch.decode (wt_event 5 0x2 0 "x.mo")))
      "/root/a/x.mo")
    (Bool.and
      (String.beq (wt_path_of_first dirs root (Watch.decode (wt_event 5 0x400 0 "")))
        "/root/a")
      (String.beq (wt_path_of_first dirs root (Watch.decode (wt_event 9 0x2 0 "y.mo")))
        "/root"))

/// A directory renamed WITHIN the tree keeps its inode, so
/// `inotify_add_watch` hands back the SAME descriptor for the new path; events
/// afterwards must resolve through it, not through the old name.
#[test]
def test_watch_recursive_renamed_directory : IO Bool := do {
  let root := wt_tmp "renamed";
  wt_rm root;
  wt_mkdir root;
  let opened <- Watch.recursive (Path.path root) List.empty;
  match opened {
    Result.err e => IO.pure (wt_unsupported e),
    Result.ok w => wt_renamed_directory w root
  }
}

def wt_renamed_directory (w : Watch) (root : String) : IO Bool := do {
  wt_mkdir (root ++ "/old");
  let created <- Watch.drain (Shared.of w) 2000 50;
  match created {
    Result.err _ => wt_close_false w root,
    Result.ok _ => wt_renamed_after w root
  }
}

def wt_renamed_after (w : Watch) (root : String) : IO Bool := do {
  let _ <- exec_cmd "mv" [root ++ "/old", root ++ "/new"];
  let moved <- Watch.drain (Shared.of w) 2000 50;
  match moved {
    Result.err _ => wt_close_false w root,
    Result.ok _ => wt_renamed_write w root
  }
}

def wt_renamed_write (w : Watch) (root : String) : IO Bool := do {
  wt_write (root ++ "/new/x.mo") "x";
  let r <- Watch.drain (Shared.of w) 2000 50;
  Watch.close w;
  wt_rm root;
  match r {
    Result.err _ => IO.pure false,
    Result.ok b => IO.pure (wt_saw_path b.events (root ++ "/new/x.mo"))
  }
}
