// Channels and select.
//
// An MVar-style channel: at most one value in flight. `Channel.put` parks
// while it is full, `Channel.take` while it is empty, and `select` parks
// until ANY of its channels holds a value.
//
// Native targets only: both wasm profiles have no threads and no fibers,
// so the target gate rejects a reachable channel native there, exactly as
// it does `forkIO`.
//
// A cancelled fiber blocked in put/take/select gives the wait up and
// unwinds at the next bind, the same cooperative rule as every other
// native. The wake is PUSHED by `monad_cancel_fiber` rather than polled
// for: the wait used to be a bounded 50 ms `pthread_cond_timedwait` that
// re-checked the cancel flag, so a cancel was noticed up to a tick late
// and every blocked fiber woke 20 times a second for the life of its
// wait. `platform_posix.c`'s channel section has the registry that
// replaced it.

/// Channel handles are opaque runtime objects; do not construct or pattern
/// match on them (the `channel` constructor is never built at run time).
pub type Channel (A : Type) {
    channel
}

#[native "channel_new"]
priv def channel_new : RawIO (Channel A)

#[native "channel_put"]
priv def channel_put (c : Channel A) (v : A) : RawIO Unit

#[native "channel_take"]
priv def channel_take (c : Channel A) : RawIO A

#[native "channel_try_take"]
priv def channel_try_take (c : Channel A) : RawIO (Option A)

/// Block until any of `chs` holds a value, then take it. `none` when the
/// waiting fiber was cancelled first. Compiled-only, the same gate as
/// every other channel native.
#[native "channel_take_any"]
priv def channel_take_any (chs : List (Channel A)) : RawIO (Option A)

/// A fresh, empty channel.
pub def Channel.new : IO (Channel A) :=
    IO.mk channel_new

/// Put `v`, blocking while the channel is full. The Rust host cannot
/// block (its fibers are lazy thunks), so there a put into a full channel
/// replaces the value that was never taken.
pub def Channel.put (c : Channel A) (v : A) : IO Unit :=
    IO.mk (channel_put c v)

/// Take a value, blocking while the channel is empty. On the Rust host an
/// empty channel is a loud eval error instead of a block -- there is no
/// other thread that could ever fill it.
pub def Channel.take (c : Channel A) : IO A :=
    IO.mk (channel_take c)

/// Take a value if one is waiting, without blocking.
pub def Channel.tryTake (c : Channel A) : IO (Option A) :=
    IO.mk (channel_try_take c)

/// Take from whichever of `chs` has a value first, blocking until one
/// does; `none` when the waiting fiber is cancelled first.
///
/// This used to probe every channel with `tryTake` and `sleepIO 1`
/// between passes, which cost a timer wakeup per millisecond and delayed
/// a value by up to a millisecond. It now parks once on the channels
/// themselves (`channel_take_any`), so a value is seen as soon as it
/// arrives and an idle select costs nothing.
///
/// The result is an `Option` rather than a bare `A` because cancellation
/// is a real outcome: a cancelled waiter has no value to hand back, and
/// inventing one would be exactly the silent-IO-failure the project
/// forbids. Callers that know their select cannot be cancelled unwrap
/// it.
///
/// On the Rust host there is no parking (its fibers are deferred
/// thunks), so the host answers `none` immediately -- the same lazy
/// degradation `race` has, for the same reason. Note this is a BEHAVIOUR
/// CHANGE on the host as well as a type change: the old polling `select`
/// blocked until a value arrived, where the host's now scans once and
/// gives up. Nothing in the tree calls `select` outside `channel_test.mo`,
/// so no caller is affected today.
///
/// A NOTE ON THE TYPE: `IO A` became `IO (Option A)`. This is a breaking
/// change to a `pub` API, made because cancellation is a real outcome with
/// no value of `A` to report; the polling version had no way to say it.
pub def select {A : Type} (chs : List (Channel A)) : IO (Option A) :=
    IO.mk (channel_take_any chs)
