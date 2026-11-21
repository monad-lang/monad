/// Loom Phase 4 (plans/library-ideas/plugin-framework.md): `Loader.plugin`,
/// the typed counterpart of Cordis's `ctx.plugin()`. A plugin names the
/// services it needs and gives; mounting it under a `Warp` checks the needs
/// against the warp's `Provides` proof, then activates the plugin's own
/// `Strand` and keeps its disposers for the unmount.
///
/// Service names travel as `String` here: `ServiceName` is affine, and a
/// plugin's name lists are read many times (the reactor re-plans on every
/// event). `Provides.has_text` is the bridge to the proof.
use loom::warp {ServiceName, Warp}
use loom::service {Provides, Provides.has_text, Provides.add}
use loom::strand {Strand, StrandRun, Pending, Active, StrandRun.disposers, Strand.activate, Strand.dispose}
use loom::disposer {Disposer}
use std::list {List.filter}

/// A mountable unit: its name, the services it needs and gives, and the
/// strand that mounts it (a thunk, so building the record runs nothing).
pub struct Plugin {
    name : String,
    requires : List String,
    provides : List String,
    mount : Unit -> Strand Pending Active Unit,
}

/// A mounted plugin and the disposers its mount registered.
pub struct Mounted {
    plugin : Plugin,
    disposers : List Disposer,
}

/// The plugin's needs that this warp does not serve, in order.
pub def Loader.missing (p : Plugin) (w : Warp Provides A) : List String :=
    let reg : Provides := Warp.registry w in
    List.filter (fn (n : String) => Bool.not (Provides.has_text n reg)) p.requires

/// Mount `p` under `w`: refused (a value, never a panic) while a needed
/// service is missing; otherwise the plugin's strand runs and its
/// disposers are kept.
pub def Loader.plugin (p : Plugin) (w : Warp Provides A) : IO (Result String Mounted) :=
    match Loader.missing p w {
        List.cons n _ => IO.pure (Result.err (String.concat_list [p.name, " needs ", n])),
        List.empty => mount_now p,
    }

def mount_now (p : Plugin) : IO (Result String Mounted) := do {
    let r <- Strand.activate (p.mount unit);
    let m : Mounted := { plugin := p, disposers := StrandRun.disposers r };
    IO.pure (Result.ok m)
}

/// Run a mounted plugin's disposers, newest first; a failing one is
/// reported to `sink` and the rest still run.
pub def Loader.unmount (sink : String -> IO Unit) (m : Mounted) : IO Unit :=
    Strand.dispose sink m.disposers

/// The warp after `p` is mounted: its services join the proof.
pub def Loader.extend (w : Warp Provides A) (p : Plugin) : Warp Provides A :=
    match w {
        Warp.warp reg a => Warp.warp (add_all p.provides reg) a,
    }

#[partial]
def add_all (names : List String) (p : Provides) : Provides :=
    match names {
        List.empty => p,
        List.cons n rest => add_all rest (Provides.add (ServiceName.name n) p),
    }
