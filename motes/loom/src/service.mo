/// `Service` -- Loom Phase 3 (plans/library-ideas/plugin-framework.md).
///
/// The plan spec asks for a dependent record `(name, Config : Type, cfg :
/// Config)`. Monad has no type-valued record field, so this is the honest
/// stepping stone Phase 1 already sanctioned for `Gamma`: `Service Config`
/// carries ONE concrete config, and `Provides` is a closed proof record
/// over the service NAMES visible at a position in the plugin tree.
///
/// What that means in practice, stated plainly so nobody mistakes the
/// proof for something stronger:
///   * `Provides` proves names, not config types. A heterogeneous list of
///     configs needs a dependent/sigma type, so a service's config is
///     supplied by the caller and `Service.inject` re-checks the name at
///     run time -- exactly the roadmap's accepted shape ("a missing
///     provider is a runtime `Result.err` until Gamma can be dependent").
///   * `Multiplicity` is a runtime policy check, not an affine
///     guarantee: `quantitative-types` still drops multiplicity in
///     lowering, the same standing as `Disposer`'s `!`.
///   * Isolation is as typed as the closed proof allows: a
///     `Warp Provides A` can only be isolated to another `Provides`, and
///     `Service.inject` reads that proof. A caller can still build a
///     `Provides` by hand, so this is a discipline, not a sealed handle.
use loom::warp {ServiceName, Warp}
use std::list {List.any}

/// How many owners a service admits at one position. Linear is a
/// singleton (`Multiplicity.check` refuses a second owner); Many is
/// shared and admits any number.
pub type Multiplicity {
    multiplicity_linear,
    multiplicity_many,
}

/// The runtime half of the multiplicity policy. `outstanding` is the
/// caller's current owner count; the first mount passes 0.
pub def Multiplicity.check (m : Multiplicity) (outstanding : I64) : Result String Unit :=
    match m {
        Multiplicity.multiplicity_linear =>
            if I64.beq outstanding 0
            then Result.ok unit
            else Result.err "linear service already has an owner (singleton)",
        Multiplicity.multiplicity_many => Result.ok unit,
    }

/// One service: its name, its multiplicity policy, and one config value.
/// Built through `Service.linear`/`Service.many`, never a bare literal:
/// generic literal inference is the recorded hazard that shaped
/// `StrandRun`.
pub type Service (Config : Type) {
    service (name : ServiceName) (multiplicity : Multiplicity) (cfg : Config)
}

pub def Service.name (s : Service Config) : ServiceName :=
    match s { service n _ _ => n }

pub def Service.multiplicity (s : Service Config) : Multiplicity :=
    match s { service _ m _ => m }

pub def Service.config (s : Service Config) : Config :=
    match s { service _ _ c => c }

/// A singleton service: one owner per position.
pub def Service.linear {Config : Type} (name : ServiceName) (cfg : Config) : Service Config :=
    Service.service name Multiplicity.multiplicity_linear cfg

/// A shared service: any number of owners.
pub def Service.many {Config : Type} (name : ServiceName) (cfg : Config) : Service Config :=
    Service.service name Multiplicity.multiplicity_many cfg

/// The closed availability proof a subtree's `Warp` carries. Names only;
/// see the module doc for why config values cannot travel with them yet.
pub type Provides {
    provides (names : List ServiceName)
}

pub def Provides.names (p : Provides) : List ServiceName :=
    match p { provides ns => ns }

pub def Provides.empty : Provides :=
    Provides.provides List.empty

def name_eq (a : ServiceName) (b : ServiceName) : Bool :=
    match a { name sa => match b { name sb => String.beq sa sb } }

def name_text (n : ServiceName) : String :=
    match n { name s => s }

/// Membership by the name's TEXT, so a caller that also needs the text
/// (to build an error) uses the affine `ServiceName` once. `String` is
/// Copy; `ServiceName` is not.
pub def Provides.has_text (text : String) (p : Provides) : Bool :=
    List.any (fn (n : ServiceName) => match n { name t => String.beq t text }) (Provides.names p)

pub def Provides.has (n : ServiceName) (p : Provides) : Bool :=
    match n { name text => Provides.has_text text p }

pub def Provides.add (n : ServiceName) (p : Provides) : Provides :=
    Provides.provides (List.cons n (Provides.names p))

/// The proof a single-service mount site starts from.
pub def Provides.of_service {Config : Type} (s : Service Config) : Provides :=
    Provides.provides (List.cons (Service.name s) List.empty)

/// Does this warp expose the service? The `Provides`-typed counterpart of
/// `Warp.provides`, which stays specialised to `List ServiceName`.
pub def Warp.serves (n : ServiceName) (w : Warp Provides A) : Bool :=
    Provides.has n (Warp.registry w)

/// Restrict/shadow the visible proof for a subtree. The carried value is
/// untouched -- the typed counterpart of Cordis's `ctx.isolate()`, over
/// the proof rather than a raw name list.
pub def Warp.isolate_services (p : Provides) (w : Warp Provides A) : Warp Provides A :=
    match w { warp _ a => Warp.warp p a }

/// The inject body, split out so the `Service` (affine) is destructured
/// once per entry point and only `String`/`Config` are shared.
def inject_parts {Config : Type} (n : ServiceName) (cfg : Config) (w : Warp Provides A) : Result String Config :=
    match n { name text =>
        if Provides.has_text text (Warp.registry w)
        then Result.ok cfg
        else Result.err (String.concat "missing provider: " text)
    }

/// Inject a service at this position: the config, once the position's
/// proof carries its name. A missing provider is a value (`Result.err`),
/// never a panic.
pub def Service.inject {Config : Type} (s : Service Config) (w : Warp Provides A) : Result String Config :=
    match s { service n _ cfg => inject_parts n cfg w }

/// Inject AND apply the multiplicity policy.
pub def Service.acquire {Config : Type} (s : Service Config) (w : Warp Provides A) (outstanding : I64) : Result String Config :=
    match s { service n m cfg =>
        match Multiplicity.check m outstanding {
            Result.err e => Result.err e,
            Result.ok _ => inject_parts n cfg w,
        }
    }
