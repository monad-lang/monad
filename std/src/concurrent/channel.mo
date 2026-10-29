// Channels and select.
//
// An MVar-style channel: at most one value in flight. `Channel.put` parks
// while it is full, `Channel.take` while it is empty, and
// `Channel.tryTake` is the non-blocking probe `select` is built from.
//
// Native targets only: both wasm profiles have no threads and no fibers,
// so the target gate rejects a reachable channel native there, exactly as
// it does `forkIO`.
//
// A cancelled fiber blocked in put/take gives the wait up (the runtime
// re-checks the cancel flag on every wake-up) and unwinds at the next
// bind, the same cooperative rule as every other native.

use init::shared {Shared, Shared.get}
use lib::concurrent::combine {sleepIO}

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

// The first channel in `chs` that has a value, probing in list order.
def try_first {A : Type} (chs : List (Channel A)) : IO (Option A) :=
  match chs {
    List.empty => IO.pure Option.none,
    List.cons c rest =>
      Monad.bind (Channel.tryTake c) (fn v =>
        match v {
          Option.some a => IO.pure (Option.some a),
          Option.none => try_first rest
        })
  }

#[partial]
def select_loop {A : Type} (chs : Shared (List (Channel A))) : IO A :=
  Monad.bind (try_first (Shared.get chs)) (fn v =>
    match v {
      Option.some a => IO.pure a,
      Option.none => Monad.bind (sleepIO 1) (fn _ => select_loop chs)
    })

/// Take from whichever of `chs` has a value first, blocking until one
/// does. Probes every millisecond, the same shape `race` uses -- a wake-up
/// primitive belongs to S3's reactor. Racing zero channels never returns:
/// there is no value of `A` to hand back.
#[partial]
pub def select {A : Type} (chs : List (Channel A)) : IO A :=
  select_loop (Shared.of chs)
