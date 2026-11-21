// Cancel tests: a fired parent fires its children (transitively), a fired
// child leaves its parent alone, and the stop-seam adapter reads the same
// state. A child fired from another fiber is seen by the observer.

use std::concurrent::cancel {Cancel, Cancel.new, Cancel.child, Cancel.fire, Cancel.is_fired, Cancel.as_stop}
use std::concurrent::fiber {await_fiber, forkIO}

#[test]
def test_a_new_token_is_not_fired : IO Bool := do {
    let c <- Cancel.new;
    let f <- Cancel.is_fired c;
    IO.pure (Bool.not f)
}

#[test]
def test_a_parent_fires_its_children : IO Bool := do {
    let root <- Cancel.new;
    let kid <- Cancel.child root;
    let grandkid <- Cancel.child kid;
    let before <- Cancel.is_fired grandkid;
    let _ <- Cancel.fire root;
    let k <- Cancel.is_fired kid;
    let g <- Cancel.is_fired grandkid;
    IO.pure (Bool.not before && k && g)
}

#[test]
def test_a_child_does_not_fire_its_parent : IO Bool := do {
    let root <- Cancel.new;
    let kid <- Cancel.child root;
    let _ <- Cancel.fire kid;
    let k <- Cancel.is_fired kid;
    let r <- Cancel.is_fired root;
    IO.pure (k && Bool.not r)
}

#[test]
def test_as_stop_reads_the_token : IO Bool := do {
    let c <- Cancel.new;
    let stop : Unit -> IO Bool := Cancel.as_stop c;
    let before <- stop unit;
    let _ <- Cancel.fire c;
    let after <- stop unit;
    IO.pure (Bool.not before && after)
}

/// Fired on another fiber, seen here once that fiber is done.
#[test]
def test_firing_crosses_fibers : IO Bool := do {
    let c <- Cancel.new;
    let f <- forkIO (fn (_ : Unit) => Cancel.fire c);
    let _ <- await_fiber f;
    Cancel.is_fired c
}
