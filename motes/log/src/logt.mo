/// `LogT`: a reader transformer over `Logger`, so a computation can ask
/// for the run's logger instead of taking it as a parameter.
///
/// `LogT M A = Logger -> M A`, the same shape as `init::transformers`'
/// `ReaderT`, kept in this mote so logging does not force a dependency on
/// the whole transformer library. `lift`/`ask`/`local` stay generic over
/// any `Monad M`; the level helpers are `LogT IO Unit` because a
/// `Logger`'s sink is `String -> IO Unit`.
///
/// A single-constructor `type`, not a `struct`: a parameterized struct's
/// constructor does not generalize its type parameters on the Rust host
/// (`ReaderT`/`StateT` recorded the same reason).
use log::logger {
    Logger, Logger.with_field,
    Logger.trace, Logger.debug, Logger.info, Logger.warn, Logger.error,
}

pub type LogT (M : Type -> Type) (A : Type) {
    mk (run : Logger -> M A)
}

/// Run a `LogT` computation with an explicit logger -- the one place the
/// logger still appears.
pub def LogT.run (m : LogT M A) (log : Logger) : M A :=
    match m {
        LogT.mk f => f log
    }

/// Lift an underlying computation, leaving the environment untouched.
pub def LogT.lift [Monad M] {A : Type} (m : M A) : LogT M A :=
    LogT.mk (fn (_log : Logger) => m)

/// Read the environment's logger.
pub def LogT.ask [Monad M] : LogT M Logger :=
    LogT.mk (fn (log : Logger) => Monad.pure log)

/// Run `m` with a locally modified logger.
pub def LogT.local {M : Type -> Type} {A : Type} (f : Logger -> Logger) (m : LogT M A) : LogT M A :=
    LogT.mk (fn (log : Logger) => LogT.run m (f log))

/// Add one structured field for the duration of `m`.
pub def LogT.with_field {M : Type -> Type} {A : Type}
        (key : String) (value : String) (m : LogT M A) : LogT M A :=
    LogT.mk (fn (log : Logger) => LogT.run m (Logger.with_field log key value))

/// Internal: run the continuation in the same environment. Extracted so
/// the instance body stays single-line (the parser does not accept
/// multi-line lambdas inside instance bodies).
def LogT.bind_step [Monad M] {A : Type} {B : Type}
        (f : A -> LogT M B) (log : Logger) : A -> M B :=
    fn (a : A) => LogT.run (f a) log

/// The instance body references `Monad.bind`/`Monad.pure` directly, the
/// `ReaderT`/`StateT`/`ResultT` precedent: the promoted method's own
/// `[Monad M]` dictionary forwards them.
pub instance [Monad M] Monad (LogT M) {
    def pure (a : A) : LogT M A :=
        LogT.mk (fn (_log : Logger) => Monad.pure a)
    def bind (ma : LogT M A) (f : A -> LogT M B) : LogT M B :=
        LogT.mk (fn (log : Logger) => Monad.bind (LogT.run ma log) (LogT.bind_step f log))
}

// ── the IO-specialized level helpers ────────────────────────────────────

pub def LogT.trace (msg : String) : LogT IO Unit :=
    LogT.mk (fn (log : Logger) => Logger.trace log msg)

pub def LogT.debug (msg : String) : LogT IO Unit :=
    LogT.mk (fn (log : Logger) => Logger.debug log msg)

pub def LogT.info (msg : String) : LogT IO Unit :=
    LogT.mk (fn (log : Logger) => Logger.info log msg)

pub def LogT.warn (msg : String) : LogT IO Unit :=
    LogT.mk (fn (log : Logger) => Logger.warn log msg)

pub def LogT.error (msg : String) : LogT IO Unit :=
    LogT.mk (fn (log : Logger) => Logger.error log msg)
