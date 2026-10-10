// Monad transformers -- the stack-building layer over any `Monad`.
//
// Opt-in like `init.foldable` (not re-exported from `lib.mo`). `StateT`,
// `ResultT` and `OptionT` are here; `IdentityT`, `ReaderT`, and `WriterT`
// are the intended rest, each to follow the same shape: a
// `Functor`/`Applicative`/`Monad` instance over any underlying monad, plus
// `run`/`lift` and the effect operations.
//
// Every instance here is `[Monad M]`-constrained: resolving e.g.
// `Monad (StateT S M)` at a concrete call site recursively resolves
// `Monad M` underneath it, so stacks resolve one level at a time down
// to a base monad (`Id`, `IO`, ...). Because instance resolution is a
// run-time step in Monad, `transformers_tests.mo` has to EXECUTE every
// instance -- `check` alone cannot see a missing one. (The `bind` half of
// the `StateT` instance is currently unexercised: the lowering bug its own
// note describes. `ResultT`/`OptionT`'s `bind` do NOT hit that bug --
// probed directly, see their own tests -- so stay suspicious of blaming
// "Monad.bind + a pattern match in one file" in general; it was
// `StateT`-specific.)

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

/// Internal: unwrap a `Pair S A` and run the continuation in the new state.
def StateT.bind_step [Monad M] {S : Type} {A : Type} {B : Type} (f : A -> StateT S M B) (p : Pair S A) : M (Pair S B) :=
    match p {
        Pair.pair s2 a => StateT.run (f a) s2
    }

/// Internal: the state-threading bind step. Extracted so the instance
/// body stays single-line (the parser doesn't accept multi-line lambdas
/// inside instance bodies).
def StateT.bind_go [Monad M] {S : Type} {A : Type} {B : Type} (ma : StateT S M A) (f : A -> StateT S M B) (s : S) : M (Pair S B) :=
    Monad.bind (StateT.run ma s) (StateT.bind_step f)

pub instance [Monad M] Monad (StateT S M) {
    def pure (a : A) : StateT S M A :=
        StateT.mk (fn s => Monad.pure (Pair.pair s a))
    def bind (ma : StateT S M A) (f : A -> StateT S M B) : StateT S M B :=
        StateT.mk (StateT.bind_go ma f)
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
