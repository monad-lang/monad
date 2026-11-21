// Cooperative cancellation as a value.
//
// A `Cancel` is a token one side fires and any number of others observe. A
// child token is fired by its own `fire` or by any ancestor's, so a parent
// stopping stops its children (a turn stopping stops its subagents) while a
// child stopping leaves the parent running. Observers poll `is_fired` at
// their own boundaries; `as_stop` adapts a token to the `Unit -> IO Bool`
// stop seams the agent loop and the HTTP client already take.
//
// The flags are `Ref`s, which are atomic across fibers, so the firing side
// and the observing side may run on different fibers.

use std::ref {Ref, Ref.new, Ref.get, Ref.set}

pub struct Cancel {
    flag : Ref Bool,
    ancestors : List (Ref Bool),
}

/// A token is a shared handle (like the `Ref`s inside it): copying it
/// copies the reference, so every copy sees the same firing.
pub instance Copy Cancel {
    def copy (c : Cancel) : Pair Cancel Cancel := Pair.pair c c
}

/// A fresh, unfired token with no parent.
pub def Cancel.new : IO Cancel := do {
    let f <- Ref.new false;
    let c : Cancel := { flag := f, ancestors := List.empty };
    IO.pure c
}

/// A token fired by its own `fire` or by `parent`'s (or any of its
/// ancestors').
pub def Cancel.child (parent : Cancel) : IO Cancel :=
    match parent {
        { flag, ancestors } => do {
            let f <- Ref.new false;
            let c : Cancel := { flag := f, ancestors := List.cons flag ancestors };
            IO.pure c
        },
    }

/// Fire the token. Firing twice is the same as once.
pub def Cancel.fire (c : Cancel) : IO Unit :=
    match c { { flag, .. } => Ref.set flag true }

/// Has this token, or any ancestor, been fired?
pub def Cancel.is_fired (c : Cancel) : IO Bool :=
    match c { { flag, ancestors } => any_set (List.cons flag ancestors) }

#[partial]
def any_set (rs : List (Ref Bool)) : IO Bool :=
    match rs {
        List.empty => IO.pure false,
        List.cons r rest => do {
            let v <- Ref.get r;
            if v then IO.pure true else any_set rest
        },
    }

/// The token as a stop seam (`RunState.should_stop`, an HTTP client's halt).
pub def Cancel.as_stop (c : Cancel) : Unit -> IO Bool :=
    fn (_ : Unit) => Cancel.is_fired c
