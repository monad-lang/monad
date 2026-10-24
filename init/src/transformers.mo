// Monad transformers -- the stack-building layer over any `Monad`.
//
// Opt-in like `init.foldable` (not re-exported from `lib.mo`). `StateT`,
// `ReaderT`, `ResultT` and `OptionT` are here; `IdentityT` and `WriterT`
// are the intended rest, each to follow the same shape: a
// `Functor`/`Applicative`/`Monad` instance over any underlying monad, plus
// `run`/`lift` and the effect operations.
//
// Every instance here is `[Monad M]`-constrained: resolving e.g.
// `Monad (StateT S M)` at a concrete call site recursively resolves
// `Monad M` underneath it, so stacks resolve one level at a time down
// to a base monad (`Id`, `IO`, ...). Because instance resolution is a
// run-time step in Monad, `transformers_tests.mo` has to EXECUTE every
// instance -- `check` alone cannot see a missing one. (The `bind` half
// of the `StateT` instance was long unexercised, blamed on a
// StateT-specific lowering bug; the real cause was the checker's
// dictionary-resolution gap for `[Monad M]` dictionary arguments
// resolved from a partially-applied spine, and `test_statet_bind` now
// passes.)

// Future transformers (WriterT) will need Monoid/Semigroup from foldable.
// use lib::foldable {Monoid, Semigroup}

/// State transformer: `StateT S M A = S -> M (Pair S A)` threads a state
/// `S` through the underlying monad `M`.
///
/// A single-constructor `type` rather than a `struct`, deliberately: a
/// parameterized `struct`'s constructor does not generalize its type
/// parameters on the Rust host (construction at `StateT.mk` fails with
/// ``type mismatch: `StateT` vs. `((StateT ?) ?) ?` `` while pattern
/// matching works), and no parameterized struct exists anywhere in the
/// corpus to prove otherwise. The single-constructor `type` is the shape
/// `examples/state_monad.mo` already uses; construction (`StateT.mk`),
/// matching, and everything else are spelled identically.
pub type StateT (S : Type) (M : Type -> Type) (A : Type) {
    mk (run : S -> M (Pair S A))
}

/// Run a `StateT` computation from an initial state, giving the final
/// state paired with the result.
pub def StateT.run (m : StateT S M A) (s : S) : M (Pair S A) :=
    match m {
        StateT.mk r => r s
    }

/// Evaluate the stateful computation, returning only the result.
pub def StateT.eval [Monad M] {S : Type} {A : Type} (m : StateT S M A) (s : S) : M A :=
    match m {
        StateT.mk r => Monad.bind (r s) (fn p =>
            match p {
                Pair.pair _ a => Monad.pure a
            })
    }

/// Execute the stateful computation, returning only the final state.
pub def StateT.exec [Monad M] {S : Type} {A : Type} (m : StateT S M A) (s : S) : M S :=
    match m {
        StateT.mk r => Monad.bind (r s) (fn p =>
            match p {
                Pair.pair st _ => Monad.pure st
            })
    }

/// Lift an underlying computation, leaving the state untouched.
pub def StateT.lift [Monad M] {S : Type} {A : Type} (m : M A) : StateT S M A :=
    StateT.mk (fn s => Monad.bind m (fn a => Monad.pure (Pair.pair s a)))

/// Internal: unwrap a `Pair S A` and run the continuation in the new
/// state. Extracted so the instance body stays single-line (the parser
/// doesn't accept multi-line lambdas inside instance bodies); it is the
/// `ResultT`/`OptionT` `bind_step` pattern exactly, and it carries no
/// `[Monad M]` dictionary parameter of its own -- its body never
/// references the class, so the call the instance body makes to it needs
/// no dictionary argument (see `collect_def_constraints`, lang/scope.mo).
def StateT.bind_step [Monad M] {S : Type} {A : Type} {B : Type} (f : A -> StateT S M B) (p : Pair S A) : M (Pair S B) :=
    match p {
        Pair.pair s2 a => StateT.run (f a) s2
    }

/// The state-threading bind step. Its body references `Monad.bind`, so
/// `qualifying_dict_constraints` (lang/src/scope.mo) gives it a leading
/// dictionary parameter; the instance body reaches `Monad` only through
/// this call, and the checker's see-through table forwards the
/// instance's own `[Monad M]` binding to it.
def StateT.bind_go [Monad M] {S : Type} {A : Type} {B : Type} (ma : StateT S M A) (f : A -> StateT S M B) (s : S) : M (Pair S B) :=
    Monad.bind (StateT.run ma s) (StateT.bind_step f)

/// `bind` goes through `StateT.bind_go`, the same shape `ResultT`/`OptionT`
/// use: the helper carries the dict parameter and the see-through table
/// forwards it here, so the instance body itself names no class.
pub instance [Monad M] Monad (StateT S M) {
    def pure (a : A) : StateT S M A :=
        StateT.mk (fn s => Monad.pure (Pair.pair s a))
    def bind (ma : StateT S M A) (f : A -> StateT S M B) : StateT S M B :=
        StateT.mk (StateT.bind_go ma f)
}

/// Reader transformer: `ReaderT R M A = R -> M A` threads a read-only
/// environment `R` through the underlying monad `M`.
///
/// A single-constructor `type`, not a `struct`, for `StateT`'s recorded
/// reason: parameterized struct construction does not generalize its type
/// parameters on the Rust host.
pub type ReaderT (R : Type) (M : Type -> Type) (A : Type) {
    mk (run : R -> M A)
}

/// Run a `ReaderT` computation in an environment.
pub def ReaderT.run (m : ReaderT R M A) (r : R) : M A :=
    match m {
        ReaderT.mk f => f r
    }

/// Lift an underlying computation, leaving the environment untouched.
pub def ReaderT.lift {R : Type} {M : Type -> Type} {A : Type} (m : M A) : ReaderT R M A :=
    ReaderT.mk (fn (_r : R) => m)

/// Read the environment.
pub def ReaderT.ask [Monad M] {R : Type} : ReaderT R M R :=
    ReaderT.mk (fn (r : R) => Monad.pure r)

/// Read the environment and apply a pure projection.
///
/// The body goes through `Monad.bind`/`Monad.pure` rather than the direct
/// `ReaderT.mk (fn (r : R) => Monad.pure (f r))`: the direct form triggers
/// the compiled constrained-generic dictionary miscompile
/// (`plans/implementations/2026-10-18-compiled-constrained-generic-dict-call-miscompiles.md`)
/// and crashes the self-hosted test driver (`driver exited -1`), while
/// `ReaderT.ask`'s variable-argument body is unaffected. Keep this shape
/// until that bug is fixed.
pub def ReaderT.asks [Monad M] {R : Type} {A : Type} (f : R -> A) : ReaderT R M A :=
    ReaderT.mk (fn (r : R) => Monad.bind (Monad.pure r) (fn (x : R) => Monad.pure (f x)))

/// Run `m` in a locally modified environment.
pub def ReaderT.local {R : Type} {R2 : Type} {M : Type -> Type} {A : Type}
        (f : R2 -> R) (m : ReaderT R M A) : ReaderT R2 M A :=
    ReaderT.mk (fn (r2 : R2) => ReaderT.run m (f r2))

/// Internal: run the continuation in the same environment. Extracted so
/// the instance body stays single-line (the parser doesn't accept
/// multi-line lambdas inside instance bodies), and it carries no `[Monad
/// M]` dictionary of its own -- its body never references the class.
def ReaderT.bind_step [Monad M] {R : Type} {A : Type} {B : Type}
        (f : A -> ReaderT R M B) (r : R) : A -> M B :=
    fn (a : A) => ReaderT.run (f a) r

/// The instance body references `Monad.bind`/`Monad.pure` DIRECTLY, the
/// `StateT`/`ResultT`/`OptionT` precedent: the promoted method's own
/// `[Monad M]` dictionary parameter (Phase 3) forwards them (D5), and a
/// helper call in between would be resolved against abstract carriers.
pub instance [Monad M] Monad (ReaderT R M) {
    def pure (a : A) : ReaderT R M A :=
        ReaderT.mk (fn (_r : R) => Monad.pure a)
    def bind (ma : ReaderT R M A) (f : A -> ReaderT R M B) : ReaderT R M B :=
        ReaderT.mk (fn (r : R) => Monad.bind (ReaderT.run ma r) (ReaderT.bind_step f r))
}

/// Result transformer: `ResultT E M A = M (Result E A)` short-circuits the
/// underlying monad's sequencing on `Result.err`, the same way `IO (Result
/// String A)` already does by hand everywhere in this codebase (`motes/
/// moose/src/client.mo`'s continuation chaining, for one) -- this gives
/// that exact shape real `do`-notation instead.
pub type ResultT (E : Type) (M : Type -> Type) (A : Type) {
    mk (run : M (Result E A))
}

pub def ResultT.run (m : ResultT E M A) : M (Result E A) :=
    match m { ResultT.mk r => r }

/// Lift an underlying computation that cannot itself fail.
pub def ResultT.lift [Monad M] {E : Type} {A : Type} (m : M A) : ResultT E M A :=
    ResultT.mk (Monad.bind m (fn a => Monad.pure (Result.ok a)))

/// Internal: run the continuation only on `Result.ok`, short-circuiting
/// `Result.err` straight through -- extracted for the same reason
/// `StateT.bind_go` is (the parser doesn't accept a multi-line lambda
/// inside an instance body).
def ResultT.bind_step [Monad M] {E : Type} {A : Type} {B : Type} (f : A -> ResultT E M B) (r : Result E A) : M (Result E B) :=
    match r {
        Result.ok a => ResultT.run (f a),
        Result.err e => Monad.pure (Result.err e)
    }

pub instance [Monad M] Monad (ResultT E M) {
    def pure (a : A) : ResultT E M A :=
        ResultT.mk (Monad.pure (Result.ok a))
    def bind (ma : ResultT E M A) (f : A -> ResultT E M B) : ResultT E M B :=
        ResultT.mk (Monad.bind (ResultT.run ma) (ResultT.bind_step f))
}

/// Option transformer: `OptionT M A = M (Option A)` short-circuits on
/// `Option.none`, the `ResultT` shape with no error payload to carry.
pub type OptionT (M : Type -> Type) (A : Type) {
    mk (run : M (Option A))
}

pub def OptionT.run (m : OptionT M A) : M (Option A) :=
    match m { OptionT.mk r => r }

/// Lift an underlying computation that always produces a value.
pub def OptionT.lift [Monad M] {A : Type} (m : M A) : OptionT M A :=
    OptionT.mk (Monad.bind m (fn a => Monad.pure (Option.some a)))

def OptionT.bind_step [Monad M] {A : Type} {B : Type} (f : A -> OptionT M B) (o : Option A) : M (Option B) :=
    match o {
        Option.some a => OptionT.run (f a),
        Option.none => Monad.pure Option.none
    }

pub instance [Monad M] Monad (OptionT M) {
    def pure (a : A) : OptionT M A :=
        OptionT.mk (Monad.pure (Option.some a))
    def bind (ma : OptionT M A) (f : A -> OptionT M B) : OptionT M B :=
        OptionT.mk (Monad.bind (OptionT.run ma) (OptionT.bind_step f))
}
