/// File-system watching over Linux's inotify, with the event decoding written
/// in Monad (`Watch.decode`) so it is unit-testable with no filesystem.
///
/// A watch IS an `FdStream` over the inotify queue: `Watch.new` creates it,
/// `Stream.close` releases it, and `Watch.add` registers one DIRECTORY. The
/// kernel reports that directory's children by bare name, and a new
/// subdirectory must be added explicitly (`WatchEvent.is_dir` marks the event
/// that announced it) -- there is no recursive watch in inotify itself. The
/// recursive walker, the coalescing and the moon live-reload swap are later
/// phases of `plans/implementations/inotify-file-watching.md`.
///
/// Watch DIRECTORIES, not files: an inotify watch is per inode, so an editor
/// that saves by writing a temporary file and renaming it over the target
/// silently kills a file watch (`WatchEvent.ignored` is what a dead watch
/// reports).
///
/// Linux-only. On any other POSIX target the four natives report `ENOSYS` and
/// `Watch.new` fails with an ordinary `StreamError`, so a caller that has a
/// polling fallback keeps working; on wasm the target gate refuses a reachable
/// call at compile time.
use lib::bytebuf {ByteBuf}
use lib::list {List.length}
use lib::path {Path}
use lib::stream {FdStream, StreamError, stream_result}

// ── the native half (runtime/src/platform_posix.c) ──────────────────────

#[native "inotify_init"]
priv def inotify_init_raw (flags : I64) : RawIO (Result (Pair I64 String) FdStream)

#[native "inotify_add_watch"]
priv def inotify_add_watch_raw (w : FdStream) (dir : String) (mask : I64)
    : RawIO (Result (Pair I64 String) I64)

#[native "inotify_rm_watch"]
priv def inotify_rm_watch_raw (w : FdStream) (watch : I64)
    : RawIO (Result (Pair I64 String) Unit)

#[native "inotify_read"]
priv def inotify_read_raw (w : FdStream) (timeout_ms : I64) (max_bytes : I64)
    : RawIO (Result (Pair I64 String) ByteBuf)

// ── the mask bits (`inotify(7)`) ─────────────────────────────────────────
//
// `Watch.add`'s mask. The change bits are what a caller waits for; the two
// "how to interpret this event" bits are `is_dir` and `only_dir`, and the
// meta bits (`ignored`, `overflow`) arrive on events rather than being
// requested.

pub def Watch.access : I64 := 0x1
pub def Watch.modify : I64 := 0x2
pub def Watch.attrib : I64 := 0x4
pub def Watch.close_write : I64 := 0x8
pub def Watch.close_nowrite : I64 := 0x10
/// `IN_OPEN`: a child was opened (named `opened` -- `Watch.new` is the
/// constructor).
pub def Watch.opened : I64 := 0x20
pub def Watch.moved_from : I64 := 0x40
pub def Watch.moved_to : I64 := 0x80
pub def Watch.create : I64 := 0x100
pub def Watch.delete : I64 := 0x200
pub def Watch.delete_self : I64 := 0x400
pub def Watch.move_self : I64 := 0x800
pub def Watch.unmount : I64 := 0x2000
pub def Watch.overflow : I64 := 0x4000
pub def Watch.ignored_bit : I64 := 0x8000
pub def Watch.only_dir : I64 := 0x1000000
pub def Watch.dont_follow : I64 := 0x2000000
pub def Watch.is_dir_bit : I64 := 0x40000000

/// The mask a general consumer asks for: creation, deletion, metadata and
/// content writes, close-for-write, renames, and the watched directory's own
/// removal (`0xFCE`).
///
/// Deliberately WITHOUT the read events (`IN_ACCESS`, `IN_OPEN`,
/// `IN_CLOSE_NOWRITE`): a dev server reads the very files it watches, so
/// asking for those makes the watcher wake on its own traffic -- the event
/// storm this API exists to avoid. The `is_dir`/`ignored`/`overflow` bits are
/// not requests either; they arrive on events as the kernel reports them.
pub def Watch.changes : I64 := 0xFCE

/// The `inotify_init1` flags `Watch.new` passes: `IN_NONBLOCK` (a drain loop
/// polls, then reads, and must never block on an empty queue) and
/// `IN_CLOEXEC` (a spawned child must not inherit the queue).
pub def Watch.init_flags : I64 := 0x800 + 0x80000

/// The largest event is 16 header bytes + a `NAME_MAX`+1 name; `inotify_read`
/// fails with `EINVAL` rather than split an event, so this buffer can never
/// truncate one, and one 4 KiB read usually carries a whole burst.
pub def Watch.read_bytes : I64 := 4096

// ── the watch ───────────────────────────────────────────────────────────

/// Create a watch. Close it with `Stream.close`.
pub def Watch.new : IO (Result StreamError FdStream) := do {
  let r <- IO.mk (inotify_init_raw Watch.init_flags);
  return (stream_result r)
}

/// Watch `dir` (one directory, not its subtree) for the events in `mask`;
/// the returned handle is what `Watch.remove` takes.
pub def Watch.add (w : FdStream) (dir : Path) (mask : I64) : IO (Result StreamError I64) := do {
  let r <- IO.mk (inotify_add_watch_raw w (Path.to_string dir) mask);
  return (stream_result r)
}

/// Stop watching a handle from `Watch.add`.
pub def Watch.remove (w : FdStream) (handle : I64) : IO (Result StreamError Unit) := do {
  let r <- IO.mk (inotify_rm_watch_raw w handle);
  return (stream_result r)
}

/// Wait up to `timeout_ms` for events (negative waits forever) and return
/// every COMPLETE event the kernel had queued -- an empty list is a timeout,
/// never an error. Call it again to drain the rest of a burst.
///
/// One reader per watch: two fibers calling this race for the same events.
pub def Watch.next (w : FdStream) (timeout_ms : I64)
    : IO (Result StreamError (List WatchEvent)) := do {
  let raw <- IO.mk (inotify_read_raw w timeout_ms Watch.read_bytes);
  Watch.next_read (stream_result raw)
}

/// The two stages of `Watch.next` after the native call, split out because a
/// do-block with binds inside a `match` arm is the shape the codegen notes
/// warn about.
def Watch.next_read (read : Result StreamError ByteBuf)
    : IO (Result StreamError (List WatchEvent)) :=
  match read {
    Result.err e => IO.pure (Result.err e),
    Result.ok buf => Watch.decode_buffer buf
  }

/// Decode one read (freeing the buffer), including the empty one a timeout
/// returns.
def Watch.decode_buffer (buf : ByteBuf) : IO (Result StreamError (List WatchEvent)) := do {
  let n := ByteBuf.length buf;
  let bytes <- ByteBuf.to_list buf n;
  let _ <- ByteBuf.free buf;
  IO.pure (Result.ok (Watch.decode bytes))
}

// ── the events ───────────────────────────────────────────────────────────

/// One `inotify_event`. `watch` is the handle `Watch.add` returned, `mask`
/// the event bits (test them with `WatchEvent.has`/the predicates), `cookie`
/// pairs a `moved_from` with its `moved_to`, and `name` is the child's bare
/// name (empty for an event about the watched directory itself).
pub struct WatchEvent {
  watch : I64,
  mask : I64,
  cookie : I64,
  name : String
}

/// A decoded event is a pure value -- `I64`s and a `Copy` `String` -- so
/// sharing one (a predicate reads two bits of the same mask) is a bit-copy,
/// not an ownership move.
pub instance Copy WatchEvent {
  def copy (e : WatchEvent) : Pair WatchEvent WatchEvent := Pair.pair e e
}

/// Whether `mask` carries `bit`.
pub def WatchEvent.has (e : WatchEvent) (bit : I64) : Bool :=
  Bool.not (U32.beq (U32.and (I64.to_u32 e.mask) (I64.to_u32 bit)) 0u32)

/// A child was created (`Watch.create`).
pub def WatchEvent.created (e : WatchEvent) : Bool := WatchEvent.has e Watch.create
/// A child's contents or metadata changed. Fires MID-WRITE -- wait for
/// `closed_for_write` before reading the file.
pub def WatchEvent.modified (e : WatchEvent) : Bool :=
  Bool.or (WatchEvent.has e Watch.modify) (WatchEvent.has e Watch.attrib)
/// A writer closed the file: its contents are complete.
pub def WatchEvent.closed_for_write (e : WatchEvent) : Bool := WatchEvent.has e Watch.close_write
/// A child was deleted (`Watch.delete`).
pub def WatchEvent.deleted (e : WatchEvent) : Bool := WatchEvent.has e Watch.delete
/// The old half of a rename; `cookie` names the pair.
pub def WatchEvent.moved_from (e : WatchEvent) : Bool := WatchEvent.has e Watch.moved_from
/// The new half of a rename -- an atomic save looks like this, not
/// `closed_for_write`.
pub def WatchEvent.moved_to (e : WatchEvent) : Bool := WatchEvent.has e Watch.moved_to
/// The watched DIRECTORY itself went away (`delete_self`/`move_self`); its
/// watch handle is dead and must be dropped.
pub def WatchEvent.removed_self (e : WatchEvent) : Bool :=
  Bool.or (WatchEvent.has e Watch.delete_self) (WatchEvent.has e Watch.move_self)
/// The event is about a directory (a new one needs its own `Watch.add`).
pub def WatchEvent.is_dir (e : WatchEvent) : Bool := WatchEvent.has e Watch.is_dir_bit
/// Events were lost: the queue overflowed, so the caller must rescan.
pub def WatchEvent.overflowed (e : WatchEvent) : Bool := WatchEvent.has e Watch.overflow
/// The kernel dropped this watch (`IN_IGNORED`: the inode is gone, or it was
/// removed). Nothing more will arrive on that handle.
pub def WatchEvent.ignored (e : WatchEvent) : Bool := WatchEvent.has e Watch.ignored_bit

// ── decoding (pure) ──────────────────────────────────────────────────────
//
// The wire form: for each event a 16-byte header -- watch descriptor (i32 LE),
// mask (u32 LE), cookie (u32 LE), name length INCLUDING its NUL padding
// (u32 LE) -- followed by `len` bytes of NUL-padded name. `len` is 16-aligned.

/// Decode a byte run of `inotify_event` records. An incomplete tail is
/// dropped: the kernel reports `EINVAL` instead of splitting an event, so
/// only a caller that passes a short hand-built buffer can see one.
#[terminating]
pub def Watch.decode (bytes : List U8) : List WatchEvent :=
  match Watch.decode_one bytes {
    Option.none => List.empty,
    Option.some p =>
      match p {
        Pair.pair ev rest => List.cons ev (Watch.decode rest)
      }
  }

def Watch.decode_one (bytes : List U8) : Option (Pair WatchEvent (List U8)) :=
  if I64.lt (List.length bytes) 16
  then Option.none
  else
    let watch := Watch.u32_at bytes 0 in
    let mask := Watch.u32_at bytes 4 in
    let cookie := Watch.u32_at bytes 8 in
    let name_len := Watch.u32_at bytes 12 in
    let total := 16 + name_len in
    if I64.lt (List.length bytes) total
    then Option.none
    else
      let name := String.from_list (Watch.name_bytes bytes 16 name_len) in
      let ev : WatchEvent := { watch := watch, mask := mask, cookie := cookie, name := name } in
      Option.some (Pair.pair ev (Watch.drop_n total bytes))

/// The little-endian u32 at byte offset `off` (0 outside the list).
def Watch.u32_at (bytes : List U8) (off : I64) : I64 :=
  let b0 := U8.to_i64 (Watch.u8_at bytes off) in
  let b1 := U8.to_i64 (Watch.u8_at bytes (off + 1)) in
  let b2 := U8.to_i64 (Watch.u8_at bytes (off + 2)) in
  let b3 := U8.to_i64 (Watch.u8_at bytes (off + 3)) in
  b0 + b1 * 256 + b2 * 65536 + b3 * 16777216

/// Byte `i`, or 0 outside the list.
def Watch.u8_at (bytes : List U8) (i : I64) : U8 :=
  match List.get i bytes {
    Option.some b => b,
    Option.none => 0u8
  }

/// The name bytes at `off`, stopping at the NUL padding or after `len` bytes.
#[terminating]
def Watch.name_bytes (bytes : List U8) (off : I64) (len : I64) : List U8 :=
  if I64.lt len 1
  then List.empty
  else
    let b := Watch.u8_at bytes off in
    if U8.beq b 0u8
    then List.empty
    else List.cons b (Watch.name_bytes bytes (off + 1) (len - 1))

/// Drop the first `n` bytes.
#[terminating]
def Watch.drop_n (n : I64) (bytes : List U8) : List U8 :=
  if I64.lt n 1
  then bytes
  else
    match bytes {
      List.empty => List.empty,
      List.cons _ rest => Watch.drop_n (n - 1) rest
    }
