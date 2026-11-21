/// Loom Phase 4: the `Reactor`, the runtime half that is not purely typed.
/// It owns the mounted plugin set on its own fiber and takes events from a
/// `Channel`: unmounting a plugin first unmounts everything that depends on
/// it (newest first) and parks them; remounting it brings the parked
/// dependents back as soon as their needs are served again.
///
/// The planning (which plugins an event touches, in which order) is pure
/// and tested on its own; the fiber only applies the plan.
use loom::loader {Plugin, Mounted, Loader.unmount}
use loom::strand {StrandRun.disposers, Strand.activate}
use std::concurrent::fiber {Fiber, FiberError, forkIO, await_fiber}
use std::concurrent::channel {Channel, Channel.new, Channel.put, Channel.take}
use std::list {List.any, List.all, List.filter}

/// What the reactor is asked to do.
pub type ReactorEvent {
    unmount_plugin (name : String),
    remount_plugin (name : String),
    stop_reactor,
}

/// A plugin waiting to mount, and the unmount that parked it ("" while it
/// has never mounted: it waits for its services). A remount brings back
/// only what that plugin's own unmount took down.
pub struct Parked {
    plugin : Plugin,
    cause : String,
}

/// The reactor's state: services that need no plugin, the mounted plugins
/// in mount order, and the parked ones in their old mount order.
pub struct ReactorState {
    base : List String,
    mounted : List Mounted,
    parked : List Parked,
}

/// A running reactor: its event queue and the fiber that drains it.
pub struct Reactor {
    events : Channel ReactorEvent,
    fiber : Fiber ReactorState,
}

// -- planning (pure) --

/// Every service available: the base ones and what mounted plugins give.
pub def Reactor.available (base : List String) (mounted : List Plugin) : List String :=
    List.append base (List.flat_map (fn (p : Plugin) => p.provides) mounted)

def needs_met (avail : List String) (p : Plugin) : Bool :=
    List.all (fn (n : String) => List.any (fn (a : String) => a == n) avail) p.requires

/// The plugins that must come down when `name` does, in mount order:
/// `name` itself and everything that (transitively) stops having its
/// needs served without it.
pub def Reactor.affected (name : String) (base : List String) (mounted : List Plugin) : List String :=
    let kept : List Plugin := List.filter (fn (p : Plugin) => Bool.not (p.name == name)) mounted in
    let survivors : List Plugin := settle base kept in
    List.map (fn (p : Plugin) => p.name)
        (List.filter (fn (p : Plugin) => Bool.not (List.any (fn (s : Plugin) => s.name == p.name) survivors)) mounted)

/// Drop plugins whose needs are no longer served, until nothing changes.
#[partial]
def settle (base : List String) (ps : List Plugin) : List Plugin :=
    let avail : List String := Reactor.available base ps in
    let ok : List Plugin := List.filter (needs_met avail) ps in
    if List.length ok == List.length ps then ps else settle base ok

/// The parked plugins that can mount now, in parked order, each one's
/// services counting for the next.
#[partial]
pub def Reactor.mountable (base : List String) (mounted : List Plugin) (parked : List Plugin) : List String :=
    match pick_ready (Reactor.available base mounted) parked {
        Option.none => List.empty,
        Option.some p =>
            List.cons p.name (Reactor.mountable base (List.append mounted [p])
                (List.filter (fn (q : Plugin) => Bool.not (q.name == p.name)) parked)),
    }

#[partial]
def pick_ready (avail : List String) (ps : List Plugin) : Option Plugin :=
    match ps {
        List.empty => Option.none,
        List.cons p rest => if needs_met avail p then Option.some p else pick_ready avail rest,
    }

// -- applying a plan --

def plugins_of (ms : List Mounted) : List Plugin :=
    List.map (fn (m : Mounted) => m.plugin) ms

def in_names (names : List String) (n : String) : Bool :=
    List.any (fn (x : String) => x == n) names

/// Unmount `name` and its dependents, newest first, and park them.
pub def Reactor.unmount (sink : String -> IO Unit) (name : String) (st : ReactorState) : IO ReactorState := do {
    let names : List String := Reactor.affected name st.base (plugins_of st.mounted);
    let going : List Mounted := List.filter (fn (m : Mounted) => in_names names m.plugin.name) st.mounted;
    let _ <- unmount_all sink (List.reverse going);
    let out : ReactorState := {
        base := st.base,
        mounted := List.filter (fn (m : Mounted) => Bool.not (in_names names m.plugin.name)) st.mounted,
        parked := List.append st.parked (List.map (fn (p : Plugin) => park name p) (plugins_of going)),
    };
    IO.pure out
}

#[partial]
def unmount_all (sink : String -> IO Unit) (ms : List Mounted) : IO Unit :=
    match ms {
        List.empty => IO.pure unit,
        List.cons m rest => do {
            let _ <- Loader.unmount sink m;
            unmount_all sink rest
        },
    }

def park (cause : String) (p : Plugin) : Parked :=
    let out : Parked := { plugin := p, cause := cause } in
    out

def parked_plugins (ps : List Parked) : List Plugin :=
    List.map (fn (q : Parked) => q.plugin) ps

/// Remount what `name`'s unmount parked (itself and its dependents) and any
/// never-mounted plugin now served, in dependency order. A plugin parked by
/// another unmount stays down; `remount` of a plugin that is not parked
/// changes nothing.
pub def Reactor.remount (name : String) (st : ReactorState) : IO ReactorState :=
    if Bool.not (List.any (fn (q : Parked) => q.plugin.name == name) st.parked)
    then IO.pure st
    else
        let wanted : List Parked :=
            List.filter (fn (q : Parked) => Bool.or (q.cause == name) (String.is_empty q.cause)) st.parked in
        mount_parked (Reactor.mountable st.base (plugins_of st.mounted) (parked_plugins wanted)) st

/// Mount the named parked plugins in order.
#[partial]
def mount_parked (names : List String) (st : ReactorState) : IO ReactorState :=
    match names {
        List.empty => IO.pure st,
        List.cons n rest => do {
            let st2 <- mount_one n st;
            mount_parked rest st2
        },
    }

def mount_one (n : String) (st : ReactorState) : IO ReactorState :=
    match List.filter (fn (q : Parked) => q.plugin.name == n) st.parked {
        List.empty => IO.pure st,
        List.cons q _ => mount_plugin q.plugin st,
    }

def mount_plugin (p : Plugin) (st : ReactorState) : IO ReactorState := do {
    let r <- Strand.activate (p.mount unit);
    let m : Mounted := { plugin := p, disposers := StrandRun.disposers r };
    let out : ReactorState := {
        base := st.base,
        mounted := List.append st.mounted [m],
        parked := List.filter (fn (q : Parked) => Bool.not (q.plugin.name == p.name)) st.parked,
    };
    IO.pure out
}

// -- the fiber --

/// Start a reactor over `plugins`: every plugin whose needs are served is
/// mounted now, on the caller's fiber (in dependency order), the rest wait
/// parked; then a fiber takes events until `Reactor.stop`.
pub def Reactor.start (sink : String -> IO Unit) (base : List String) (plugins : List Plugin) : IO Reactor := do {
    let empty : List Mounted := List.empty;
    let waiting : List Parked := List.map (fn (p : Plugin) => park "" p) plugins;
    let st0 : ReactorState := { base := base, mounted := empty, parked := waiting };
    let st <- mount_parked (Reactor.mountable base List.empty plugins) st0;
    let events <- Channel.new;
    let fiber <- forkIO (fn (_ : Unit) => react sink events st);
    let r : Reactor := { events := events, fiber := fiber };
    IO.pure r
}

#[partial]
def react (sink : String -> IO Unit) (events : Channel ReactorEvent) (st : ReactorState) : IO ReactorState := do {
    let e <- Channel.take events;
    react_on sink events st e
}

#[partial]
def react_on (sink : String -> IO Unit) (events : Channel ReactorEvent) (st : ReactorState) (e : ReactorEvent)
    : IO ReactorState :=
    match e {
        ReactorEvent.stop_reactor => IO.pure st,
        ReactorEvent.unmount_plugin n => react_after sink events (Reactor.unmount sink n st),
        ReactorEvent.remount_plugin n => react_after sink events (Reactor.remount n st),
    }

#[partial]
def react_after (sink : String -> IO Unit) (events : Channel ReactorEvent) (step : IO ReactorState)
    : IO ReactorState := do {
    let st2 <- step;
    react sink events st2
}

/// Queue an event; the reactor applies events in order.
pub def Reactor.send (r : Reactor) (e : ReactorEvent) : IO Unit :=
    Channel.put r.events e

/// Stop after every queued event, and hand back the final state (its
/// mounted plugins are still mounted -- `Reactor.shutdown` takes them down).
pub def Reactor.stop (r : Reactor) : IO (Result FiberError ReactorState) := do {
    let _ <- Channel.put r.events ReactorEvent.stop_reactor;
    await_fiber r.fiber
}

/// Unmount everything still mounted, newest first.
pub def Reactor.shutdown (sink : String -> IO Unit) (st : ReactorState) : IO Unit :=
    unmount_all sink (List.reverse st.mounted)
