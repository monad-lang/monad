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
use lib::io {IO.is_dir, IO.list_dir}
use lib::list {}
use lib::path {Path}
use lib::ref {Ref}
use lib::stream {FdStream, Stream, StreamError, stream_result}

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
    let src := Shared.of buf;
    let n := ByteBuf.length (Shared.get src);
    let bytes <- ByteBuf.to_list (Shared.get src) n;
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
/// The watched directory itself was DELETED (`IN_DELETE_SELF`): the watch is
/// finished, and `Watch.drain` drops its descriptor.
pub def WatchEvent.self_deleted (e : WatchEvent) : Bool := WatchEvent.has e Watch.delete_self
/// The watched directory itself was renamed or moved (`IN_MOVE_SELF`). The
/// watch SURVIVES -- it is bound to the inode, not the name -- so this is not a
/// close signal. A rename within the tree is followed by a `moved_to` on the
/// new parent, which is what re-resolves the path.
pub def WatchEvent.self_moved (e : WatchEvent) : Bool := WatchEvent.has e Watch.move_self
/// The watched directory itself went away, by deletion or by a move. Only
/// `self_deleted` means the watch is finished.
pub def WatchEvent.removed_self (e : WatchEvent) : Bool :=
    Bool.or (WatchEvent.self_deleted e) (WatchEvent.self_moved e)
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
    match Watch.decode_one (Shared.of bytes) {
        Option.none => List.empty,
        Option.some p =>
            match p {
                Pair.pair ev rest => List.cons ev (Watch.decode rest)
            }
    }

def Watch.decode_one (bytes : Shared (List U8)) : Option (Pair WatchEvent (List U8)) :=
    if I64.lt (List.length (Shared.get bytes)) 16
    then Option.none
    else
        let watch := Watch.u32_at bytes 0 in
        let mask := Watch.u32_at bytes 4 in
        let cookie := Watch.u32_at bytes 8 in
        let name_len := Watch.u32_at bytes 12 in
        let total := 16 + name_len in
        if I64.lt (List.length (Shared.get bytes)) total
        then Option.none
        else
            let name := String.from_list (Watch.name_bytes bytes 16 name_len) in
            let ev : WatchEvent := { watch := watch, mask := mask, cookie := cookie, name := name } in
            Option.some (Pair.pair ev (Watch.drop_n total (Shared.get bytes)))

/// The little-endian u32 at byte offset `off` (0 outside the list).
def Watch.u32_at (bytes : Shared (List U8)) (off : I64) : I64 :=
    let b0 := U8.to_i64 (Watch.u8_at (Shared.get bytes) off) in
    let b1 := U8.to_i64 (Watch.u8_at (Shared.get bytes) (off + 1)) in
    let b2 := U8.to_i64 (Watch.u8_at (Shared.get bytes) (off + 2)) in
    let b3 := U8.to_i64 (Watch.u8_at (Shared.get bytes) (off + 3)) in
    b0 + b1 * 256 + b2 * 65536 + b3 * 16777216

/// Byte `i`, or 0 outside the list.
def Watch.u8_at (bytes : List U8) (i : I64) : U8 :=
    match List.get i bytes {
        Option.some b => b,
        Option.none => 0u8
    }

/// The name bytes at `off`, stopping at the NUL padding or after `len` bytes.
#[terminating]
def Watch.name_bytes (bytes : Shared (List U8)) (off : I64) (len : I64) : List U8 :=
    if I64.lt len 1
    then List.empty
    else
        let b := Watch.u8_at (Shared.get bytes) off in
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

// ── the tree form ────────────────────────────────────────────────────────
//
// A bare inotify queue reports a watch descriptor and a child's bare name; a
// watcher of a *tree* needs the full path and needs to keep up as
// directories appear. `Watch` carries the descriptor -> directory map that
// answers both, and `Watch.drain` is the only reader.

/// A watched tree: the queue, the root it was walked from, the directory names
/// it skips, and the descriptor -> directory map. `Watch.drain` updates the map
/// as directories appear and disappear, so one value serves the watcher's whole
/// lifetime.
pub struct Watch {
    stream : FdStream,
    root : Path,
    ignored : List String,
    dirs : Ref (List (Pair I64 Path))
}

/// Directory names the walker never watches: Monad's build output (`target/`,
/// and `target-*` by `Watch.ignore_dir`) plus the VCS and dependency caches.
/// Pass `List.empty` to watch every directory.
pub def Watch.default_ignored : List String :=
    ["target", ".git", "node_modules", ".devenv"]

/// Whether the walker skips a directory named `name`: an exact entry in
/// `ignored`, or the `target-*` build-output convention.
pub def Watch.ignore_dir (name : String) (ignored : List String) : Bool :=
    if String.starts_with "target-" name then true else Watch.mem name ignored

#[terminating]
def Watch.mem (name : String) (xs : List String) : Bool :=
    match xs {
        List.empty => false,
        List.cons x rest => if String.beq name x then true else Watch.mem name rest
    }

/// Watch `root` and every non-ignored directory under it. Close the result
/// with `Watch.close`.
pub def Watch.recursive (root : Path) (ignored : List String)
    : IO (Result StreamError Watch) := do {
    let opened <- Watch.new;
    match opened {
        Result.err e => IO.pure (Result.err e),
        Result.ok stream => Watch.recursive_opened stream root ignored
    }
}

/// The walk below only READS the stream and the ignore list (`Shared.of`
/// borrows them); the values themselves are stored in the returned
/// `Watch`, so they stay owned here.
def Watch.recursive_opened (stream : FdStream) (root : Path) (ignored : List String)
    : IO (Result StreamError Watch) := do {
    let walked <- Watch.walk (Shared.of stream) root (Shared.of ignored);
    Watch.recursive_walked stream root ignored walked
}

def Watch.recursive_walked (stream : FdStream) (root : Path) (ignored : List String)
    (walked : Result StreamError (List (Pair I64 Path)))
    : IO (Result StreamError Watch) :=
    match walked {
        Result.err e => Watch.close_failed stream e,
        Result.ok dirs => Watch.recursive_dirs stream root ignored dirs
    }

def Watch.recursive_dirs (stream : FdStream) (root : Path) (ignored : List String)
    (dirs : List (Pair I64 Path)) : IO (Result StreamError Watch) := do {
    let cell <- Ref.new dirs;
    let w : Watch := { stream := stream, root := root, ignored := ignored, dirs := cell };
    IO.pure (Result.ok w)
}

/// Close a queue the walk opened before it failed, so the error path does not
/// leak the descriptor.
def Watch.close_failed (stream : FdStream) (e : StreamError)
    : IO (Result StreamError Watch) := do {
    let _ <- Stream.close stream;
    IO.pure (Result.err e)
}

/// Release the queue. Nothing may use `w` afterwards.
pub def Watch.close (w : Watch) : IO Unit := Stream.close w.stream

/// Add a watch for `dir` and every non-ignored directory under it, returning
/// the descriptor -> directory map of everything watched. `Watch.only_dir` is
/// ORed into the mask (`Watch.changes` has no bit at or above `0x1000000`, so
/// adding the two IS the OR): the walker watches directories, and a path that
/// is not one (a file root, or a directory deleted between the event and this
/// call) fails at `Watch.add` instead of half-watching a file.
#[terminating]
def Watch.walk (stream : Shared FdStream) (dir : Path) (ignored : Shared (List String))
    : IO (Result StreamError (List (Pair I64 Path))) := do {
    let added <- Watch.add (Shared.get stream) dir (Watch.changes + Watch.only_dir);
    match added {
        Result.err e => IO.pure (Result.err e),
        Result.ok handle => Watch.walk_added stream dir ignored handle
    }
}

#[terminating]
def Watch.walk_added (stream : Shared FdStream) (dir : Path) (ignored : Shared (List String)) (handle : I64)
    : IO (Result StreamError (List (Pair I64 Path))) := do {
    let entries <- IO.list_dir dir;
    Watch.walk_entries stream ignored entries (List.cons (Pair.pair handle dir) List.empty)
}

/// Walk `entries` -- already the children of a watched directory -- appending
/// every watched descendant's descriptor to `acc`.
#[terminating]
def Watch.walk_entries (stream : Shared FdStream) (ignored : Shared (List String)) (entries : List Path)
    (acc : List (Pair I64 Path)) : IO (Result StreamError (List (Pair I64 Path))) :=
    match entries {
        List.empty => IO.pure (Result.ok (List.reverse acc)),
        List.cons p rest => Watch.walk_entry stream ignored p rest acc
    }

#[terminating]
def Watch.walk_entry (stream : Shared FdStream) (ignored : Shared (List String)) (p : Path)
    (rest : List Path) (acc : List (Pair I64 Path))
    : IO (Result StreamError (List (Pair I64 Path))) := do {
    let is_dir <- IO.is_dir p;
    if is_dir
    then
        if Watch.ignore_dir (Path.file_name p) (Shared.get ignored)
        then Watch.walk_entries stream ignored rest acc
        else Watch.walk_sub stream ignored p rest acc
    else Watch.walk_entries stream ignored rest acc
}

#[terminating]
def Watch.walk_sub (stream : Shared FdStream) (ignored : Shared (List String)) (p : Path)
    (rest : List Path) (acc : List (Pair I64 Path))
    : IO (Result StreamError (List (Pair I64 Path))) := do {
    let sub <- Watch.walk stream p ignored;
    match sub {
        Result.err e => IO.pure (Result.err e),
        Result.ok more => Watch.walk_entries stream ignored rest (List.append more acc)
    }
}

/// The directory a descriptor names, if it is still watched.
#[terminating]
pub def Watch.dir_of (dirs : List (Pair I64 Path)) (handle : I64) : Option Path :=
    match dirs {
        List.empty => Option.none,
        List.cons p rest =>
            match p {
                Pair.pair w d =>
                    if I64.beq w handle then Option.some d else Watch.dir_of rest handle
            }
    }

/// An event's full path: the watched directory joined with the child's name,
/// the directory itself for a zero-length name (an event about the directory),
/// and the root when its descriptor is no longer known.
pub def Watch.event_path (dirs : List (Pair I64 Path)) (root : Path) (e : WatchEvent) : Path :=
    match Watch.dir_of dirs e.watch {
        Option.none => root,
        Option.some d => if String.beq e.name "" then d else Path.join d (Path.path e.name)
    }

/// Whether any event reports a kernel queue overflow: events were lost, so the
/// caller must rescan rather than trust the batch.
#[terminating]
pub def Watch.any_overflow (evs : List WatchEvent) : Bool :=
    match evs {
        List.empty => false,
        List.cons e rest => if WatchEvent.overflowed e then true else Watch.any_overflow rest
    }

/// One `Watch.drain` result.
pub struct WatchBatch {
    /// Every event with the path it concerns, in the order the kernel reported
    /// them. Overflow events are not here -- they set `overflow`.
    events : List (Pair WatchEvent Path),
    /// The kernel dropped events (`/proc/sys/fs/inotify/max_queued_events`):
    /// anything could have changed, so rescan the tree.
    overflow : Bool
}

/// How many reads one `Watch.drain` may do before returning. A tree under a
/// build emits events faster than a quiet window closes; the caller drains
/// again rather than the watcher starving.
pub def Watch.max_reads : I64 := 64

/// Wait up to `timeout_ms` for the first event (negative waits forever), then
/// keep reading until a `quiet_ms` window passes with nothing new, so one
/// save's several masks come back as ONE batch. Watches for newly created or
/// moved-in directories are added before returning, and descriptors the kernel
/// retired are dropped from the map.
///
/// One reader per watch: two fibers calling this race for the same events.
/// An error means the batch was DISCARDED (a native failure, or a directory the
/// walk could not enter): rescan rather than retrying, since the events are
/// already consumed off the queue.
///
/// A directory moved OUT of the tree keeps its watch (inotify binds watches to
/// inodes, not paths) and its map entry therefore names a path that no longer
/// exists; its events still arrive until `Watch.close`. Rescan when that
/// matters -- `WatchBatch.overflow` is the kernel's version of the same answer.
/// Takes the watch by `Shared`: draining only reads the handle's fields
/// (it updates the map through the `Ref` cell), so the caller keeps
/// ownership for a later `Watch.close`.
pub def Watch.drain (w : Shared Watch) (timeout_ms : I64) (quiet_ms : I64)
    : IO (Result StreamError WatchBatch) :=
    let watch : Watch := Shared.get w in
    match watch {
        { stream, root, ignored, dirs } =>
            Watch.drain_started (Shared.of stream) root (Shared.of ignored) dirs timeout_ms quiet_ms
    }

def Watch.drain_started (stream : Shared FdStream) (root : Path) (ignored : Shared (List String))
    (dirs : Ref (List (Pair I64 Path))) (timeout_ms : I64) (quiet_ms : I64)
    : IO (Result StreamError WatchBatch) := do {
    let got <- Watch.drain_events stream timeout_ms quiet_ms 0 List.empty;
    match got {
        Result.err e => IO.pure (Result.err e),
        Result.ok evs => Watch.drain_batch stream root ignored dirs (Shared.of evs)
    }
}

#[terminating]
def Watch.drain_events (stream : Shared FdStream) (timeout_ms : I64) (quiet_ms : I64)
    (reads : I64) (acc : List WatchEvent)
    : IO (Result StreamError (List WatchEvent)) := do {
    let wait := if I64.lt reads 1 then timeout_ms else quiet_ms;
    let got <- Watch.next (Shared.get stream) wait;
    match got {
        Result.err e => IO.pure (Result.err e),
        Result.ok evs => Watch.drain_events_got stream timeout_ms quiet_ms reads (Shared.of evs) acc
    }
}

#[terminating]
def Watch.drain_events_got (stream : Shared FdStream) (timeout_ms : I64) (quiet_ms : I64)
    (reads : I64) (evs : Shared (List WatchEvent)) (acc : List WatchEvent)
    : IO (Result StreamError (List WatchEvent)) :=
    if I64.beq (List.length (Shared.get evs)) 0
    then IO.pure (Result.ok (List.reverse acc))
    else if I64.gt reads Watch.max_reads
    then IO.pure (Result.ok (List.reverse (List.append (List.reverse (Shared.get evs)) acc)))
    else Watch.drain_events stream timeout_ms quiet_ms (reads + 1)
        (List.append (List.reverse (Shared.get evs)) acc)

def Watch.drain_batch (stream : Shared FdStream) (root : Path) (ignored : Shared (List String))
    (dirs : Ref (List (Pair I64 Path))) (evs : Shared (List WatchEvent))
    : IO (Result StreamError WatchBatch) := do {
    let added <- Watch.watch_new_dirs stream ignored dirs root evs;
    match added {
        Result.err e => IO.pure (Result.err e),
        Result.ok _ => Watch.drain_resolve root dirs evs
    }
}

def Watch.drain_resolve (root : Path) (dirs : Ref (List (Pair I64 Path)))
    (evs : Shared (List WatchEvent)) : IO (Result StreamError WatchBatch) := do {
    let current <- Ref.get dirs;
    let cur := Shared.of current;
    let kept := Watch.reap_dead (Shared.get cur) evs;
    let _ <- Ref.set dirs kept;
    let batch : WatchBatch :=
        { events := Watch.resolve root cur evs, overflow := Watch.any_overflow (Shared.get evs) };
    IO.pure (Result.ok batch)
}

/// A directory appearing under the tree: created empty, or moved in with its
/// own subtree.
def Watch.is_new_dir (e : WatchEvent) : Bool :=
    Bool.and (WatchEvent.is_dir e) (Bool.or (WatchEvent.created e) (WatchEvent.moved_to e))

/// Add a watch (and walk) for every directory the batch reports created or
/// moved in, so a new subdirectory is watched from its creation.
#[terminating]
def Watch.watch_new_dirs (stream : Shared FdStream) (ignored : Shared (List String))
    (dirs : Ref (List (Pair I64 Path))) (root : Path) (evs : Shared (List WatchEvent))
    : IO (Result StreamError Unit) :=
    match Shared.get evs {
        List.empty => IO.pure (Result.ok Unit.unit),
        List.cons e rest =>
            if Watch.is_new_dir e
            then Watch.watch_new_dir stream ignored dirs root e (Shared.of rest)
            else Watch.watch_new_dirs stream ignored dirs root (Shared.of rest)
    }

#[terminating]
def Watch.watch_new_dir (stream : Shared FdStream) (ignored : Shared (List String))
    (dirs : Ref (List (Pair I64 Path))) (root : Path) (e : WatchEvent) (rest : Shared (List WatchEvent))
    : IO (Result StreamError Unit) := do {
    let current <- Ref.get dirs;
    let cur := Shared.of current;
    let path := Watch.event_path (Shared.get cur) root e;
    let walked <- Watch.walk stream path ignored;
    match walked {
        Result.err err => IO.pure (Result.err err),
        Result.ok more => Watch.watch_new_dir_added stream ignored dirs root rest more (Shared.get cur)
    }
}

#[terminating]
def Watch.watch_new_dir_added (stream : Shared FdStream) (ignored : Shared (List String))
    (dirs : Ref (List (Pair I64 Path))) (root : Path) (rest : Shared (List WatchEvent))
    (more : List (Pair I64 Path)) (current : List (Pair I64 Path))
    : IO (Result StreamError Unit) := do {
    let ms := Shared.of more;
    let cs := Shared.of current;
    let _ <- Ref.set dirs (List.append (Shared.get ms) (Watch.reap_replaced (Shared.get cs) ms));
    Watch.watch_new_dirs stream ignored dirs root rest
}

/// Whether `handle` appears in `dirs`.
#[terminating]
def Watch.wd_in (dirs : List (Pair I64 Path)) (handle : I64) : Bool :=
    match dirs {
        List.empty => false,
        List.cons p rest =>
            match p {
                Pair.pair w _ => if I64.beq w handle then true else Watch.wd_in rest handle
            }
    }

/// `current` without any descriptor `fresh` supersedes. `inotify_add_watch` on
/// an inode that is already watched returns the EXISTING descriptor, so a
/// directory renamed within the tree yields the same handle under a new path:
/// the entry has to be replaced, not appended, or `Watch.dir_of` could resolve
/// events to the old name.
#[terminating]
def Watch.reap_replaced (current : List (Pair I64 Path)) (fresh : Shared (List (Pair I64 Path)))
    : List (Pair I64 Path) :=
    match current {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Pair.pair w d =>
                    let wd : I64 := w in
                    if Watch.wd_in (Shared.get fresh) wd
                    then Watch.reap_replaced rest fresh
                    else List.cons (Pair.pair wd d) (Watch.reap_replaced rest fresh)
            }
    }

/// Resolve each event's path (overflow pseudo-events are dropped; they are the
/// batch's `overflow`).
#[terminating]
def Watch.resolve (root : Path) (dirs : Shared (List (Pair I64 Path))) (evs : Shared (List WatchEvent))
    : List (Pair WatchEvent Path) :=
    match Shared.get evs {
        List.empty => List.empty,
        List.cons e rest =>
            let ev : WatchEvent := e in
            if WatchEvent.overflowed ev
            then Watch.resolve root dirs (Shared.of rest)
            else
                List.cons (Pair.pair ev (Watch.event_path (Shared.get dirs) root ev))
                    (Watch.resolve root dirs (Shared.of rest))
    }

/// Drop descriptors the kernel retired -- `IN_IGNORED`, or the directory
/// itself moved/vanished -- so the map does not grow stale and a later reused
/// descriptor cannot resolve to the wrong path.
#[terminating]
def Watch.reap_dead (dirs : List (Pair I64 Path)) (evs : Shared (List WatchEvent))
    : List (Pair I64 Path) :=
    match dirs {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Pair.pair w d =>
                    let wd : I64 := w in
                    if Watch.wd_dead (Shared.get evs) wd
                    then Watch.reap_dead rest evs
                    else List.cons (Pair.pair wd d) (Watch.reap_dead rest evs)
            }
    }

/// A watch is retired only by `IN_IGNORED` (the kernel dropped it) or by its
/// directory being deleted. `IN_MOVE_SELF` does NOT retire it: a directory
/// renamed inside the tree keeps the same descriptor, and the matching
/// `moved_to` is what re-resolves its entry to the new path.
#[terminating]
def Watch.wd_dead (evs : List WatchEvent) (handle : I64) : Bool :=
    match evs {
        List.empty => false,
        List.cons e rest =>
            if Bool.and (I64.beq e.watch handle)
                (Bool.or (WatchEvent.ignored e) (WatchEvent.self_deleted e))
            then true
            else Watch.wd_dead rest handle
    }
