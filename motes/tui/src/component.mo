// Terminal UI Library - composable Elm components
//
// An app built on `App` is one model, one message type and one `update`.
// A component is the same four pieces at a smaller scale -- its own model,
// message type, `update`, `view` and `subscriptions` -- and the parent
// embeds it as a field, wraps its messages in one constructor of its own,
// and lifts the child's commands and subscriptions with `Cmd.map` and
// `Subs.map`.
//
// `Subs` is the frame clock's half: what a component wants delivered on a
// tick. `App`'s loop knows nothing about it; the app's tick handler asks
// `Subs.on_tick` for the one command that delivers every due message, so a
// tick still folds through exactly one `Cmd` (the loop's contract).

use lib::tui {Cmd}
use std::concurrent::fiber {FiberError}

/// Lift a child's command into the parent's message type.
pub def Cmd.map {A : Type} {B : Type} (f : A -> B) (c : Cmd A) : Cmd B :=
    match c {
        Cmd.none => Cmd.none,
        Cmd.quit => Cmd.quit,
        Cmd.dispatch m => Cmd.dispatch (f m),
        Cmd.perform action => Cmd.perform (map_action f action),
        Cmd.inspect action => Cmd.inspect (map_action f action),
        Cmd.perform_async action on_error =>
            Cmd.perform_async (map_action f action) (fn (e : FiberError) => f (on_error e)),
    }

def map_action {A : Type} {B : Type} (f : A -> B) (action : Unit -> IO A) : Unit -> IO B :=
    fn (u : Unit) => do {
        let a <- action u;
        IO.pure (f a)
    }

/// What a component wants from the frame clock. Cadences count the app's
/// frame number (one per tick), so `every 3` is ~3 Hz at a 100 ms tick.
pub type Subs (M : Type) {
    /// Nothing; an idle component.
    none,
    /// `msg` on every `n`th frame (`n` below 1 means every frame).
    every (n : I64) (msg : M),
    /// Run `action` on every `n`th frame and deliver its message: a poll
    /// of a file or a fiber's progress. It runs without forcing a repaint.
    poll (n : I64) (action : Unit -> IO M),
    /// Several subscriptions at once.
    batch (subs : List (Subs M)),
}

#[partial]
pub def Subs.map {A : Type} {B : Type} (f : A -> B) (s : Subs A) : Subs B :=
    match s {
        Subs.none => Subs.none,
        Subs.every n msg => Subs.every n (f msg),
        Subs.poll n action => Subs.poll n (map_action f action),
        Subs.batch subs => Subs.batch (List.map (fn (x : Subs A) => Subs.map f x) subs),
    }

/// Whether anything is subscribed: an app's `tick_redraw` can skip a
/// tick-only frame when nothing is.
#[partial]
pub def Subs.active {M : Type} (s : Subs M) : Bool :=
    match s {
        Subs.none => false,
        Subs.every _ _ => true,
        Subs.poll _ _ => true,
        Subs.batch subs => sub_any_active subs,
    }

#[partial]
def sub_any_active {M : Type} (subs : List (Subs M)) : Bool :=
    match subs {
        List.empty => false,
        List.cons s rest => if Subs.active s then true else sub_any_active rest,
    }

def due (frame : I64) (n : I64) : Bool :=
    if n < 2 then true else I64.beq (frame - ((frame / n) * n)) 0

/// A due subscription, in order: a pure message or a poll to run.
type Due (M : Type) {
    due_msg (msg : M),
    due_poll (action : Unit -> IO M),
}

#[partial]
def due_go {M : Type} (frame : I64) (s : Subs M) (acc : List (Due M)) : List (Due M) :=
    match s {
        Subs.none => acc,
        Subs.every n msg => if due frame n then List.cons (Due.due_msg msg) acc else acc,
        Subs.poll n action => if due frame n then List.cons (Due.due_poll action) acc else acc,
        Subs.batch subs => due_list frame subs acc,
    }

#[partial]
def due_list {M : Type} (frame : I64) (subs : List (Subs M)) (acc : List (Due M)) : List (Due M) :=
    match subs {
        List.empty => acc,
        List.cons s rest => due_list frame rest (due_go frame s acc),
    }

#[partial]
def pure_msgs {M : Type} (ds : List (Due M)) (acc : List M) : List M :=
    match ds {
        List.empty => List.reverse acc,
        List.cons d rest => match d {
            Due.due_msg msg => pure_msgs rest (List.cons msg acc),
            Due.due_poll _ => pure_msgs rest acc,
        },
    }

#[partial]
def poll_actions {M : Type} (ds : List (Due M)) (acc : List (Unit -> IO M)) : List (Unit -> IO M) :=
    match ds {
        List.empty => List.reverse acc,
        List.cons d rest => match d {
            Due.due_msg _ => poll_actions rest acc,
            Due.due_poll action => poll_actions rest (List.cons action acc),
        },
    }

#[partial]
def run_polls {M : Type} (actions : List (Unit -> IO M)) (acc : List M) : IO (List M) :=
    match actions {
        List.empty => IO.pure (List.reverse acc),
        List.cons action rest => run_poll action rest acc,
    }

#[partial]
def run_poll {M : Type} (action : Unit -> IO M) (rest : List (Unit -> IO M)) (acc : List M) : IO (List M) := do {
    let msg <- action unit;
    run_polls rest (List.cons msg acc)
}

/// What `s` delivers on `frame`: the pure messages, in subscription order,
/// for the tick's own fold (so an animation frame moves on the tick that
/// drew it), and ONE command running every due poll -- a `Cmd.inspect`
/// (no forced repaint) whose result `many` wraps into the app's batch
/// message. No due poll is `Cmd.none`.
pub def Subs.on_tick {M : Type} (frame : I64) (s : Subs M) (many : List M -> M) : Pair (List M) (Cmd M) :=
    let ds : List (Due M) := List.reverse (due_go frame s List.empty) in
    let polls : List (Unit -> IO M) := poll_actions ds List.empty in
    let cmd : Cmd M :=
        match polls {
            List.empty => Cmd.none,
            List.cons _ _ => Cmd.inspect (fn (_ : Unit) => do {
                let msgs <- run_polls polls List.empty;
                IO.pure (many msgs)
            }),
        } in
    Pair.pair (pure_msgs ds List.empty) cmd

/// The pure messages a subscription delivers on `frame`, without its
/// polls: for tests and for folding a tick by hand.
pub def Subs.pure_on {M : Type} (frame : I64) (s : Subs M) : List M :=
    pure_msgs (List.reverse (due_go frame s List.empty)) List.empty
