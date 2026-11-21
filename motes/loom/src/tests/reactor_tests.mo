/// Loom Phase 4: `Loader.plugin` refuses a plugin whose needs are not
/// served, and the `Reactor` cascades an unmount to dependents (newest
/// first) and brings them back on remount. The integration test is the
/// plan's two-plugin program: B injects A's service.
use loom::warp {ServiceName, Warp}
use loom::service {Provides, Provides.empty, Provides.add}
use loom::strand {Strand, Pending, Active, StrandRun, Strand.pending}
use loom::disposer {Disposer}
use loom::loader {Plugin, Mounted, Loader.plugin, Loader.missing, Loader.extend, Loader.unmount}
use loom::reactor {
    Reactor, ReactorState, ReactorEvent, Parked, Reactor.affected, Reactor.mountable,
    Reactor.start, Reactor.send, Reactor.stop, Reactor.shutdown,
}
use std::ref {Ref, Ref.new, Ref.get, Ref.modify}
use std::list {List.intercalate}

def note (r : Ref (List String)) (s : String) : IO Unit :=
    Ref.modify r (fn (xs : List String) => List.append xs [s])

def silent_sink : String -> IO Unit :=
    fn (_ : String) => IO.pure unit

/// A strand that logs "mount <name>" now and "unmount <name>" on disposal.
def logged_mount (log : Ref (List String)) (name : String) : Strand Pending Active Unit :=
    Strand.pending (fn (_ : Unit) => do {
        let _ <- note log (String.concat "mount " name);
        let d : Disposer := { run := fn (_ : Unit) => do {
            let _ <- note log (String.concat "unmount " name);
            IO.pure (Result.ok unit)
        } };
        let out : StrandRun Unit := StrandRun.run_result unit [d];
        IO.pure out
    })

def plugin (log : Ref (List String)) (name : String) (requires : List String) (provides : List String) : Plugin :=
    let p : Plugin := { name := name, requires := requires, provides := provides,
        mount := fn (_ : Unit) => logged_mount log name } in
    p

/// A bare plugin for the pure planning tests: mounting it does nothing.
def shape (name : String) (requires : List String) (provides : List String) : Plugin :=
    let p : Plugin := { name := name, requires := requires, provides := provides,
        mount := fn (_ : Unit) => Strand.pending (fn (_ : Unit) =>
            let out : StrandRun Unit := StrandRun.run_result unit List.empty in
            IO.pure out) } in
    p

def empty_warp : Warp Provides Unit := Warp.warp Provides.empty unit

def joined (r : Ref (List String)) : IO String := do {
    let xs <- Ref.get r;
    IO.pure (List.intercalate "," xs)
}

// -- the loader --

#[test]
def test_loader_refuses_a_missing_service : IO Bool := do {
    let log <- Ref.new List.empty;
    let b : Plugin := plugin log "b" ["greeter"] [];
    let r <- Loader.plugin b empty_warp;
    let text <- joined log;
    return (match r {
        Result.err e => String.contains e "b needs greeter" && String.is_empty text,
        Result.ok _ => false,
    })
}

#[test]
def test_loader_mounts_once_the_warp_serves_it : IO Bool := do {
    let log <- Ref.new List.empty;
    let a : Plugin := plugin log "a" [] ["greeter"];
    let b : Plugin := plugin log "b" ["greeter"] [];
    let w : Warp Provides Unit := Loader.extend empty_warp a;
    let r <- Loader.plugin b w;
    let ok : Bool := match r { Result.ok _ => true, Result.err _ => false };
    let _ <- match r { Result.ok m => Loader.unmount silent_sink m, Result.err _ => IO.pure unit };
    let text <- joined log;
    return (ok && String.beq text "mount b,unmount b" && List.is_empty (Loader.missing b w))
}

// -- planning --

#[test]
def test_affected_follows_dependents : Bool :=
    let a : Plugin := shape "a" [] ["greeter"] in
    let b : Plugin := shape "b" ["greeter"] ["shout"] in
    let c : Plugin := shape "c" ["shout"] [] in
    let d : Plugin := shape "d" [] [] in
    String.beq (List.intercalate "," (Reactor.affected "a" [] [a, b, c, d])) "a,b,c"
        && String.beq (List.intercalate "," (Reactor.affected "c" [] [a, b, c, d])) "c"

#[test]
def test_a_base_service_keeps_a_dependent_up : Bool :=
    let a : Plugin := shape "a" [] ["greeter"] in
    let b : Plugin := shape "b" ["greeter"] [] in
    String.beq (List.intercalate "," (Reactor.affected "a" ["greeter"] [a, b])) "a"

#[test]
def test_mountable_orders_by_dependency : Bool :=
    let a : Plugin := shape "a" [] ["greeter"] in
    let b : Plugin := shape "b" ["greeter"] [] in
    let z : Plugin := shape "z" ["nothing"] [] in
    String.beq (List.intercalate "," (Reactor.mountable [] [] [b, z, a])) "a,b"

// -- the two-plugin program --

def stop_and_log (r : Reactor) (log : Ref (List String)) : IO (Pair Bool String) := do {
    let res <- Reactor.stop r;
    let ok <- match res {
        Result.ok st => do { let _ <- Reactor.shutdown silent_sink st; IO.pure true },
        Result.err _ => IO.pure false,
    };
    let text <- joined log;
    IO.pure (Pair.pair ok text)
}

/// B injects A's service: unmounting A takes B down first, remounting A
/// brings B back after it.
#[test]
def test_unmount_and_remount_cascade : IO Bool := do {
    let log <- Ref.new List.empty;
    let a : Plugin := plugin log "a" [] ["greeter"];
    let b : Plugin := plugin log "b" ["greeter"] [];
    let r <- Reactor.start silent_sink [] [b, a];
    let _ <- Reactor.send r (ReactorEvent.unmount_plugin "a");
    let _ <- Reactor.send r (ReactorEvent.remount_plugin "a");
    let out <- stop_and_log r log;
    return (match out {
        Pair.pair ok text =>
            ok && String.beq text "mount a,mount b,unmount b,unmount a,mount a,mount b,unmount b,unmount a",
    })
}

/// Unmounting a plugin nobody depends on leaves the rest mounted.
#[test]
def test_unmount_a_leaf_only : IO Bool := do {
    let log <- Ref.new List.empty;
    let a : Plugin := plugin log "a" [] ["greeter"];
    let b : Plugin := plugin log "b" ["greeter"] [];
    let r <- Reactor.start silent_sink [] [a, b];
    let _ <- Reactor.send r (ReactorEvent.unmount_plugin "b");
    let out <- stop_and_log r log;
    return (match out {
        Pair.pair ok text => ok && String.beq text "mount a,mount b,unmount b,unmount a",
    })
}

/// A plugin unmounted on its own stays down when another one is remounted.
#[test]
def test_remount_brings_back_only_its_own_cascade : IO Bool := do {
    let log <- Ref.new List.empty;
    let a : Plugin := plugin log "a" [] ["greeter"];
    let b : Plugin := plugin log "b" ["greeter"] [];
    let r <- Reactor.start silent_sink [] [a, b];
    let _ <- Reactor.send r (ReactorEvent.unmount_plugin "b");
    let _ <- Reactor.send r (ReactorEvent.unmount_plugin "a");
    let _ <- Reactor.send r (ReactorEvent.remount_plugin "a");
    let out <- stop_and_log r log;
    return (match out {
        Pair.pair ok text => ok && String.beq text "mount a,mount b,unmount b,unmount a,mount a,unmount a",
    })
}
