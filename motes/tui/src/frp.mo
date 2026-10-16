// Terminal UI Library - FRP core (Phase 9)
//
// Discrete FRP over REPLAYABLE streams: an `EventStream` is a fixed
// list of events, a `Signal` is a current value plus the full
// trajectory that produced it. Everything here is pure -- constructing
// and combining the graph is list surgery, which is exactly what makes
// the plan's test seam work: `EventStream.of_list` builds a stream
// from a literal, the combinators transform it, and the tests assert on
// `to_list`/`Signal.history` with no terminal, no fibers, no raw
// mode.
//
// This resolves the plan's `Mailbox` open item by DECLINE rather than
// by native: a synchronized cross-fiber mailbox buys nothing the pull
// reader (input.mo, Phase 6) plus this cold core cannot do, because
// the app loop is the single scheduler of a TUI -- nothing else ever
// writes into the event graph. The live producer is `Input.produce`;
// `run_app` (tui.mo, Phase 7) folds its events through the app's
// `update` with exactly the step semantics `EventStream.fold` pins
// here, and this module is where those semantics are tested.
//
// Deviation from the plan's sketch, recorded: `Signal.history` is
// pure `Signal A -> List A`, not `IO (List A)`. The IO in the sketch
// was the live-recording case; with a cold signal the whole trajectory
// already exists as data.
//
// Both types are single-constructor `type`s, not `struct`s, because a
// parameterized struct does not parse on the current nightly (the
// plan's App-record note; `init/src/transformers.mo`'s `StateT`
// records the same rule).

// `List.filter` is the one list operation here the prelude does not
// carry.
use std::list { List.filter }

/// A discrete stream of `A`s, in arrival order. Cold: the events are
/// a fixed list, so every combinator is total and deterministic.
pub type EventStream (A : Type) {
    mk (events : List A)
}

/// The value of a fold plus every value it took: `current` is the
/// latest, `history` is the whole trajectory with the fold's seed
/// first (and therefore never empty).
pub type Signal (A : Type) {
    signal (current : A) (history : List A)
}

// ==================== the test seam ====================

/// The test seam's front door: a stream that replays `xs`.
pub def EventStream.of_list {A : Type} (xs : List A) : EventStream A :=
    EventStream.mk xs

/// Every event in the stream, in order -- the seam's other door.
pub def EventStream.to_list {A : Type} (s : EventStream A) : List A :=
    match s {
        EventStream.mk xs => xs
    }

// ==================== combinators ====================

/// Apply `f` to every event.
pub def EventStream.map {A : Type} {B : Type} (f : A -> B) (s : EventStream A) : EventStream B :=
    EventStream.mk (List.map f (EventStream.to_list s))

/// Keep only the events `p` accepts.
pub def EventStream.filter {A : Type} (p : A -> Bool) (s : EventStream A) : EventStream A :=
    EventStream.mk (List.filter p (EventStream.to_list s))

/// One stream from two: `l`'s events, then `r`'s. A cold merge has no
/// arrival interleaving to reconstruct -- this is the semantics the
/// table tests pin, and the live path matches it by folding the
/// reader's already-ordered batches.
pub def EventStream.merge {A : Type} (l : EventStream A) (r : EventStream A) : EventStream A :=
    EventStream.mk (List.append (EventStream.to_list l) (EventStream.to_list r))

/// Fold `step` over the stream from `init`, producing the signal of
/// every value the fold took: `init` first, then one value per event.
/// This is the exact step semantics `run_app` applies to `update`.
pub def EventStream.fold {S : Type} {A : Type} (step : S -> A -> S) (init : S) (s : EventStream A) : Signal S :=
    match fold_go step init (EventStream.to_list s) (List.cons init List.empty) {
        Pair.pair cur rev_hist => Signal.signal cur (EventStream.rev rev_hist List.empty)
    }

def fold_go {S : Type} {A : Type} (step : S -> A -> S) (acc : S) (rest : List A) (rev_hist : List S) : Pair S (List S) :=
    match rest {
        empty => Pair.pair acc rev_hist,
        cons e t =>
            let next : S := step acc e in
            fold_go step next t (List.cons next rev_hist)
    }

/// The signal's latest value.
pub def Signal.current {A : Type} (s : Signal A) : A :=
    match s {
        Signal.signal cur _ => cur
    }

/// Every value after the seed: the signal's change stream, one event
/// per fold step. This is what a renderer redraws on.
pub def Signal.changes {A : Type} (s : Signal A) : EventStream A :=
    match s {
        Signal.signal _ hist => EventStream.mk (drop_first hist)
    }

/// Every value the signal took, seed first -- the test seam.
pub def Signal.history {A : Type} (s : Signal A) : List A :=
    match s {
        Signal.signal _ hist => hist
    }

// ==================== small list helpers ====================
//
// Local because `List.reverse`/`List.tail` are package-private in
// `init`'s modules, and this is all this module needs of them.

def EventStream.rev {A : Type} (l : List A) (out : List A) : List A :=
    match l {
        empty => out,
        cons a t => EventStream.rev t (List.cons a out)
    }

def drop_first {A : Type} (xs : List A) : List A :=
    match xs {
        empty => List.empty,
        cons _ t => t
    }
