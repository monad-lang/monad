// Monad transformers -- the stack-building layer over any `Monad`.
//
// Opt-in like `init.foldable` (not re-exported from `lib.mo`). `StateT`,
// `ReaderT`, `ResultT`, `OptionT`, `WriterT` and `IdentityT` are here, each
// with a `Monad` instance over any underlying monad plus `run`/`lift` and
// its effect operations.
//
// `MonadTrans`, `MonadReader`, `MonadError` and a `MonadState` class are
// deliberately NOT declared:
//   * `MonadTrans` needs a parameter of kind
//     `(Type -> Type) -> Type -> Type`, which the parser does not accept;
//   * multi-parameter classes (`MonadReader R M`, `MonadError E M`) parse
//     but never resolve -- the instance resolver keys on one carrier, so
//     even a fully concrete `instance MonadReader I64 (ReaderT I64 Id)` is
//     not found (measured 2026-10-30).
// The operations those classes would name are provided directly instead:
// `ReaderT.ask/asks/local`, `StateT.get/put/modify` (with `[Copy S]` where
// duplication is needed), and `ResultT.throw/catch/map_error` (`ExceptT`'s
// names; `ResultT E M A` IS `ExceptT E M A`).
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

use lib::copy {Copy}
use lib::foldable {Monoid, Semigroup}

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

/// Read the current state, keeping it threaded. `Copy S` is what lets the
/// state be both returned and kept; there is no automatic duplication.
pub def StateT.get [Monad M, Copy S] {S : Type} : StateT S M S :=
    StateT.mk (fn (s : S) =>
        match Copy.copy s {
            Pair.pair s1 s2 => Monad.pure (Pair.pair s1 s2)
        })

/// Replace the state.
pub def StateT.put [Monad M] {S : Type} (s : S) : StateT S M Unit :=
    StateT.mk (fn (_ : S) => Monad.pure (Pair.pair s unit))

/// Modify the state and produce unit.
pub def StateT.modify [Monad M] {S : Type} (f : S -> S) : StateT S M Unit :=
    StateT.mk (fn (s : S) => Monad.pure (Pair.pair (f s) unit))

/// Internal: unwrap a `Pair S A` and run the continuation in the new
/// state. Extracted so the instance body stays single-line (the parser
/// doesn't accept multi-line lambdas inside instance bodies); it is the
/// `ResultT`/`OptionT` `bind_step` pattern exactly. Its declared `[Monad
/// M]` is a dictionary parameter like any other constraint
/// (`qualifying_dict_constraints`, lang/src/scope.mo), which the instance
/// body's call forwards from its own binding.
def StateT.bind_step [Monad M] {S : Type} {A : Type} {B : Type} (f : A -> StateT S M B) (p : Pair S A) : M (Pair S B) :=
    match p {
        Pair.pair s2 a => StateT.run (f a) s2
    }

/// The state-threading bind step. Its `[Monad M]` is a leading dictionary
/// parameter (`qualifying_dict_constraints`, lang/src/scope.mo); the
/// instance body reaches `Monad` only through this call, which forwards
/// the instance's own `[Monad M]` binding to it.
def StateT.bind_go [Monad M] {S : Type} {A : Type} {B : Type} (ma : StateT S M A) (f : A -> StateT S M B) (s : S) : M (Pair S B) :=
    Monad.bind (StateT.run ma s) (StateT.bind_step f)

/// `bind` goes through `StateT.bind_go`, the same shape `ResultT`/`OptionT`
/// use: the helper carries the dict parameter and the instance body's
/// call forwards its own binding, so the body itself names no class.
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
/// multi-line lambdas inside instance bodies).
///
/// The environment is used twice (once for `ma`, once for its
/// continuation). `Shared R` cannot be used here: `Shared.get` yields a
/// view, and passing a view to `ReaderT.run`'s owning `R` parameter is
/// `borrowed_value_escapes`. The binder is an unattributable type
/// variable, so the affine rule's fail-open path exempts it (the same
/// reason main's `init` reaches zero diagnostics with this body).
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

/// `ExceptT`'s `throwError`: fail with `e`, skipping the rest of the block.
/// `ResultT E M A` IS `ExceptT E M A` (`M (Result E A)`), so this is the
/// error-aware name for a shape this module already provides.
pub def ResultT.throw [Monad M] {E : Type} {A : Type} (e : E) : ResultT E M A :=
    ResultT.mk (Monad.pure (Result.err e))

def ResultT.catch_step [Monad M] {E : Type} {A : Type}
    (on_error : E -> ResultT E M A) (r : Result E A) : M (Result E A) :=
    match r {
        Result.ok a => Monad.pure (Result.ok a),
        Result.err e => ResultT.run (on_error e)
    }

/// `ExceptT`'s `catchError` / `handleError`: run `on_error` on `Err`.
pub def ResultT.catch [Monad M] {E : Type} {A : Type}
    (m : ResultT E M A) (on_error : E -> ResultT E M A) : ResultT E M A :=
    ResultT.mk (Monad.bind (ResultT.run m) (ResultT.catch_step on_error))

/// Map the error payload, leaving a successful value alone.
///
/// The mapping is written as an inline lambda rather than a
/// `map_error_step f` helper: passing a partially-applied constrained
/// helper whose body transforms the payload crashes the compiled backend
/// (measured: `driver exited -1`), while the same body in a lambda works.
pub def ResultT.map_error [Monad M] {E : Type} {E2 : Type} {A : Type}
    (f : E -> E2) (m : ResultT E M A) : ResultT E2 M A :=
    ResultT.mk (Monad.bind (ResultT.run m) (fn (r : Result E A) =>
        match r {
            Result.ok a => Monad.pure (Result.ok a),
            Result.err e => Monad.pure (Result.err (f e))
        }))

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

/// Writer transformer: `WriterT W M A = M (Pair W A)` accumulates a monoid
/// `W` alongside the result. `bind` appends the second computation's log
/// after the first, the usual `Writer` order.
///
/// `W` needs BOTH `Semigroup` (for `combine`) and `Monoid` (for `mempty`):
/// a superclass constraint gets no dictionary slot in this compiler (the
/// same note `Comonad` carries), so the two are named explicitly.
pub type WriterT (W : Type) (M : Type -> Type) (A : Type) {
    mk (run : M (Pair W A))
}

pub def WriterT.run (m : WriterT W M A) : M (Pair W A) :=
    match m { WriterT.mk r => r }

/// Lift an underlying computation with an empty log.
pub def WriterT.lift [Monad M, Monoid W] {A : Type} (m : M A) : WriterT W M A :=
    WriterT.mk (Monad.bind m (fn a => Monad.pure (Pair.pair (Monoid.mempty unit) a)))

/// Append `w` to the log, producing unit.
pub def WriterT.tell [Monad M] {W : Type} (w : W) : WriterT W M Unit :=
    WriterT.mk (Monad.pure (Pair.pair w unit))

def WriterT.bind_step [Monad M, Semigroup W] {W : Type} {A : Type} {B : Type}
    (f : A -> WriterT W M B) (p : Pair W A) : M (Pair W B) :=
    match p {
        Pair.pair w a => Monad.bind (WriterT.run (f a)) (fn q =>
            match q {
                Pair.pair w2 b => Monad.pure (Pair.pair (Semigroup.combine w w2) b)
            })
    }

def WriterT.bind_run [Monad M, Semigroup W] {W : Type} {A : Type} {B : Type}
    (ma : WriterT W M A) (f : A -> WriterT W M B) : M (Pair W B) :=
    Monad.bind (WriterT.run ma) (WriterT.bind_step f)

pub instance [Monad M, Semigroup W, Monoid W] Monad (WriterT W M) {
    def pure (a : A) : WriterT W M A :=
        WriterT.mk (Monad.pure (Pair.pair (Monoid.mempty unit) a))
    def bind (ma : WriterT W M A) (f : A -> WriterT W M B) : WriterT W M B :=
        WriterT.mk (WriterT.bind_run ma f)
}

/// `listen`: pair the result with the log it wrote. Requires `Copy W`
/// because the log is returned AND kept as the WriterT's own output.
pub def WriterT.listen [Monad M, Copy W] {W : Type} {A : Type}
    (m : WriterT W M A) : WriterT W M (Pair A W) :=
    WriterT.mk (Monad.bind (WriterT.run m) (fn (p : Pair W A) =>
        match p {
            Pair.pair w a =>
                match Copy.copy w {
                    Pair.pair w1 w2 => Monad.pure (Pair.pair w1 (Pair.pair a w2))
                }
        }))

/// `censor`: transform the log a computation wrote. Inline lambda for the
/// same compiled-backend reason as `ResultT.map_error`.
pub def WriterT.censor [Monad M] {W : Type} {A : Type}
    (f : W -> W) (m : WriterT W M A) : WriterT W M A :=
    WriterT.mk (Monad.bind (WriterT.run m) (fn (p : Pair W A) =>
        match p {
            Pair.pair w a => Monad.pure (Pair.pair (f w) a)
        }))

/// Identity transformer: `IdentityT M A = M A`. A pass-through layer for
/// stacks that want to name every level uniformly.
pub type IdentityT (M : Type -> Type) (A : Type) {
    mk (run : M A)
}

pub def IdentityT.run (m : IdentityT M A) : M A :=
    match m { IdentityT.mk r => r }

pub def IdentityT.lift {M : Type -> Type} {A : Type} (m : M A) : IdentityT M A :=
    IdentityT.mk m

pub instance [Monad M] Monad (IdentityT M) {
    def pure (a : A) : IdentityT M A :=
        IdentityT.mk (Monad.pure a)
    def bind (ma : IdentityT M A) (f : A -> IdentityT M B) : IdentityT M B :=
        IdentityT.mk (Monad.bind (IdentityT.run ma) (fn a => IdentityT.run (f a)))
}
