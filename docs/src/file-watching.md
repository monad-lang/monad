# Watching Files

A development loop wants to know when a source file changed. Polling for it
means walking the tree and hashing every file on a timer; `std::watch` asks the
operating system instead. On Linux it is [inotify]: one file descriptor per
watched tree, and a blocking `poll(2)` that stays asleep until something
happens.

The library is `std::watch`. It has two layers: the queue itself (one fd, the
same kind of value `std::stream` hands back) and a **tree form** that walks a
directory once and resolves every event's bare name back to a full path.

[inotify]: https://man7.org/linux/man-pages/man7/inotify.7.html

## Watching a tree

This one opts out of `scripts/check-docs.sh`'s type check (`monad,ignore`):
`one_batch` hands the same `Watch` to `Watch.drain` and then to
`Watch.close`, and the affine rule -- an unannotated binder is used at most
once unless its type is `Copy` -- is enforced as an error on every check
path while `std` still migrates (`std/mote.toml` runs `[affine] mode =
"warn"`, and `cli`'s `script --watch` loop, this example's real-world
twin, relies on the same window). The shape is the one a program actually
writes; the fence goes back to being checked the day the watch API can
express it.

```monad,ignore
use std::list {List.length}
use std::path {Path}
use std::stream {StreamError}
use std::watch {
  Watch, Watch.close, Watch.default_ignored, Watch.drain, Watch.recursive, WatchBatch, WatchEvent,
}

def WatchBatch.changed (b : WatchBatch) : I64 := List.length b.events

def show (r : Result StreamError WatchBatch) : IO Unit :=
  match r {
    Result.err e => IO.write_stderr (String.concat "watch: " e.message),
    Result.ok b => IO.println (String.concat "events: " (I64.to_string (WatchBatch.changed b))),
  }

def one_batch (w : Watch) : IO Unit := do {
  let batch <- Watch.drain (Shared.of w) 1000 50;
  let _ <- Watch.close w;
  show batch
}

def main (args : List String) : IO Unit := do {
  let opened <- Watch.recursive (Path.path ".") Watch.default_ignored;
  match opened {
    Result.err e => IO.write_stderr (String.concat "watch: " e.message),
    Result.ok w => one_batch w,
  }
}
```

`Watch.recursive` walks the directory once, adds one watch per directory (the
directories named by `Watch.default_ignored` and `target-*` are skipped), and
returns a `Watch` carrying the queue, the root and a descriptor → directory map.
`Path.path "."` is the tree to watch; pass the directory you care about.

`Watch.drain` takes the watch by `Shared` — draining only reads the handle and
updates the map through its `Ref` cell, so the handle is still yours to close.
It waits up to its first argument for *something* to happen, then
keeps reading until a quiet window of the second argument passes with nothing
new, so one editor save arrives as one batch -- not as its `IN_MODIFY`,
`IN_CLOSE_WRITE` and `IN_MOVED_TO` events separately.

## The events

A batch has `events : List (Pair WatchEvent Path)` and `overflow : Bool`.
`WatchEvent` is the kernel's record, decoded: the descriptor, the mask, the
cookie (which pairs the two halves of a rename) and the child's bare name --
already joined onto its directory for you. The mask has named predicates:

| Predicate | Means |
|---|---|
| `WatchEvent.created` | a child appeared |
| `WatchEvent.closed_for_write` | a writer finished -- the file is complete |
| `WatchEvent.modified` | contents or metadata changed (fires MID-write) |
| `WatchEvent.deleted`, `moved_from`, `moved_to` | removal and the two halves of a rename |
| `WatchEvent.is_dir` | the entry is a directory (a new one is watched from then on) |
| `WatchEvent.self_deleted`, `self_moved` | the watched directory itself was deleted / moved |
| `WatchEvent.overflowed` | the kernel lost events |

`WatchBatch.overflow` is `true` when the kernel's queue overflowed: events were
lost, so rescan the tree rather than trusting what the batch reports.

## What the tree form does for you

- **Watches directories, not files.** An inotify watch is bound to an *inode*,
  so an editor that saves by writing a temporary file and renaming it over the
  target would silently kill a file watch. A directory watch reports the
  rename, which is why `IN_MOVED_TO` is the signal an atomic save produces.
- **Follows directories created later.** A newly created or moved-in
  directory is walked during the drain, so its children are watched from then
  on. A directory renamed *within* the tree keeps its descriptor (same inode),
  and its map entry is re-resolved to the new path.
- **Drops dead descriptors.** A delete or an `IN_IGNORED` removes the entry, so
  a reused descriptor cannot resolve to a stale path.
- **Resolves names to paths.** Each event arrives with its directory joined in,
  from the map above, so a caller filters on `Path.to_string` and nothing else.

## Portability

inotify is Linux's. On any other POSIX target the four natives report `ENOSYS`
and `Watch.recursive` fails with an ordinary `StreamError`; on wasm the target
gate refuses a reachable `Watch.recursive` at compile time rather than failing
at link. Callers that need a watcher everywhere keep a polling signature as the
fallback -- that is exactly what `motes/moon`'s live reload does, and the
`monad script --watch` mode below reports the error instead of guessing.

## `monad script --watch`

```bash
monad script dev --watch
```

builds the named `[[script]]` and runs it, then watches the tree its manifest
lives in: a change kills the running child (SIGKILL, reaped), the build runs
again -- the store decides whether that compiles -- and the new binary starts
with the same arguments. A failed build is not fatal: the watcher stays alive
with no child, so fixing the error reruns it.

Everything under `target/` (and `target-*`) is ignored, which is what keeps the
build from retriggering itself. A script that writes into the watched tree
*will* retrigger, so generated files belong under `target/` or outside the tree.

The child is spawned with `Proc.spawn`, so its three standard streams are
**pipes**: stdout and stderr are copied through to yours (line by line, as they
are written), but it sees a pipe rather than a terminal -- no TTY detection --
and its stdin is a pipe it never reads from, so an interactive script should
not be run under `--watch`.

The watch root is the manifest's directory. A `--mote` that names a path
dependency *outside* that tree still builds correctly, but edits under it do not
trigger a rerun. A child that exits on its own is reaped at the next change,
not the moment it exits.

## Caveats

- **Linux.** Other platforms get the error, not a slower watch.
- **`max_user_watches`** bounds how many directories can be watched at once
  (8192 on older systems). A recursive watch of a very large tree can exhaust
  it; `Watch.recursive` reports the failure instead of half-watching.
- **A directory moved out of the tree** keeps its watch -- inotify binds to
  inodes -- and its events keep arriving with a path that no longer exists,
  until the watch is closed. Treat `overflow` as the rescan signal.
- **One reader per watch.** Two fibers calling `Watch.drain` race for the same
  events.
