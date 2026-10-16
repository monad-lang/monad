// Phase 9 table tests: the FRP graph is pure, so every case pumps a
// literal stream through the combinators and asserts on the lists the
// test seam exposes -- no terminal, no fibers, no raw mode, exactly
// the plan's cold-path testing story.
//
// Lists compare through `ints_be` element-wise (generic `BEq (List A)`
// dispatch is the runtime bug this mote avoids throughout); integers,
// not `Event`s, keep the fold/merge assertions about SEMANTICS rather
// than about any one event type.

use lib::frp { EventStream, Signal }
use std::list { List.length }

def ints_be (a : List I64) (b : List I64) : Bool :=
    match a {
        empty => List.length b == 0,
        cons x xs =>
            match b {
                empty => false,
                cons y ys => x == y && ints_be xs ys
            }
    }


def stream_events (s : EventStream I64) : List I64 :=
    EventStream.to_list s

// ==================== map / filter / merge ====================

#[test]
def test_of_list_roundtrip : Bool :=
    ints_be (stream_events (EventStream.of_list [1, 2, 3])) [1, 2, 3]
    && ints_be (stream_events (EventStream.of_list [])) []

#[test]
def test_map : Bool :=
    ints_be
        (stream_events (EventStream.map (fn (x : I64) => x * 2) (EventStream.of_list [1, 2, 3])))
        [2, 4, 6]

#[test]
def test_filter : Bool :=
    ints_be
        (stream_events (EventStream.filter (fn (x : I64) => Bool.not (x == 2)) (EventStream.of_list [1, 2, 3, 4])))
        [1, 3, 4]

#[test]
def test_merge_left_then_right : Bool :=
    ints_be
        (stream_events (EventStream.merge (EventStream.of_list [1, 2]) (EventStream.of_list [3])))
        [1, 2, 3]

#[test]
def test_composed_graph : Bool :=
    // filter -> map -> merge: the shape run_app composes, minus the
    // event types.
    let left : EventStream I64 :=
        EventStream.map (fn (x : I64) => x * 10) (EventStream.filter (fn (x : I64) => Bool.not (x == 0)) (EventStream.of_list [0, 1, 2])) in
    ints_be (stream_events (EventStream.merge left (EventStream.of_list [7]))) [10, 20, 7]

// ==================== fold: the signal ====================

/// `history` pins the trajectory the fold took: seed first, one value
/// per event.
#[test]
def test_fold_history : Bool :=
    ints_be
        (Signal.history (EventStream.fold (fn (s : I64) (e : I64) => s + e) 0 (EventStream.of_list [1, 2, 3])))
        [0, 1, 3, 6]

#[test]
def test_fold_current : Bool :=
    Signal.current (EventStream.fold (fn (s : I64) (e : I64) => s + e) 0 (EventStream.of_list [1, 2, 3])) == 6

#[test]
def test_fold_empty_stream : Bool :=
    // No events: the signal is just the seed, and `changes` is empty.
    let sig : Signal I64 := EventStream.fold (fn (s : I64) (e : I64) => s + e) 5 (EventStream.of_list []) in
    ints_be (Signal.history sig) [5]
    && Signal.current sig == 5
    && ints_be (stream_events (Signal.changes sig)) []

#[test]
def test_changes_skips_seed : Bool :=
    ints_be
        (stream_events (Signal.changes (EventStream.fold (fn (s : I64) (e : I64) => s + e) 0 (EventStream.of_list [1, 2, 3]))))
        [1, 3, 6]

#[test]
def test_fold_then_map_changes : Bool :=
    // The classic redraw chain: fold to a signal, render from its
    // change stream.
    let sig : Signal I64 := EventStream.fold (fn (s : I64) (e : I64) => s + e) 0 (EventStream.of_list [1, 2]) in
    ints_be (stream_events (EventStream.map (fn (v : I64) => v * 100) (Signal.changes sig))) [100, 300]
