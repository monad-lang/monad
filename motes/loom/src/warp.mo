/// `Warp` -- Loom Phase 1 (plugin-framework.md), fixed/closed-`Gamma`
/// stepping stone. `Gamma` (the service registry a position in the
/// plugin tree can see) is a plain generic parameter here, concrete at
/// each call site (`List ServiceName`, typically) -- the same "closed
/// List known at each call site" escape hatch `indexed-monads.md`
/// already used before general dependent indices existed.
///
/// `Warp`'s `Comonad` instance is copied verbatim from `init/src/
/// prelude.mo`'s already-landed, already-tested `instance {E : Type}
/// Comonad (Pair E)` (commit `f3acb8a0`) -- `Pair E` already generically
/// IS the environment comonad this plan calls `Warp0`, so this is a
/// distinctly-named wrapper for Loom's own vocabulary, not a new
/// comonad design.
use std::list {List.any}

pub type ServiceName {
    name (s : String)
}

pub type Warp (Gamma : Type) (A : Type) {
    warp (registry : Gamma) (val : A)
}

pub def Warp.registry (w : Warp Gamma A) : Gamma :=
    match w { warp g _ => g }

pub instance {Gamma : Type} Comonad (Warp Gamma) {
    def extract (w : Warp Gamma A) : A :=
        match w { warp _ a => a }

    def duplicate (w : Warp Gamma A) : Warp Gamma (Warp Gamma A) :=
        match w { warp g a => Warp.warp g (Warp.warp g a) }

    def extend (f : Warp Gamma A -> B) (w : Warp Gamma A) : Warp Gamma B :=
        match w { warp g a => Warp.warp g (f (Warp.warp g a)) }
}

def service_name_eq (a : ServiceName) (b : ServiceName) : Bool :=
    match a { name sa => match b { name sb => String.beq sa sb } }

/// Does `name` appear in the closed service list a `Warp (List
/// ServiceName) A` carries?
pub def Warp.provides (n : ServiceName) (w : Warp (List ServiceName) A) : Bool :=
    List.any (service_name_eq n) (Warp.registry w)

/// Restrict/shadow `Gamma` for a subtree -- the typed counterpart of
/// Cordis's `ctx.isolate()`. The VALUE carried through is unchanged;
/// only the visible service list is replaced.
pub def Warp.isolate (names : List ServiceName) (w : Warp (List ServiceName) A) : Warp (List ServiceName) A :=
    match w { warp _ a => Warp.warp names a }
