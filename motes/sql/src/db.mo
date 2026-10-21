// monad-sql / db -- the transformer stack a SQL program runs in.
//
// `DbM Bk A = ReaderT Bk (ResultT SqlError IO) A`: the connection is a
// read-only environment and a failure short-circuits every remaining
// step. `do` notation works through the `Monad (DbM Bk)` instance.
//
// KNOWN COMPILER LIMITATION: generic definitions constrained over a
// `Type`-kinded class (here `[Backend Bk]`) are miscompiled by the
// self-hosted backend
// (`plans/implementations/2026-10-18-compiled-constrained-generic-dict-call-miscompiles.md`).
// `DbM`'s own `pure`/`bind`/`run`/`lift_io`/`ask` carry no such
// constraint and are safe; backend operations are supplied by each
// driver as concrete `SqliteM` functions until that bug is fixed.

use init::transformers {ReaderT, ResultT}
use lib::value {SqlError}

/// A SQL computation: read the connection from the environment, fail with
/// `SqlError`, and perform `IO`.
pub type DbM (Bk : Type) (A : Type) {
    mk (run : ReaderT Bk (ResultT SqlError IO) A)
}

pub def DbM.underlying {Bk : Type} {A : Type} (m : DbM Bk A) :
        ReaderT Bk (ResultT SqlError IO) A :=
    match m {
        DbM.mk r => r
    }

/// Run the computation against a connection.
pub def DbM.run {Bk : Type} {A : Type} (m : DbM Bk A) (conn : Bk) :
        IO (Result SqlError A) :=
    ResultT.run (ReaderT.run (DbM.underlying m) conn)

pub def DbM.pure {Bk : Type} {A : Type} (a : A) : DbM Bk A :=
    DbM.mk (ReaderT.mk (fn (_conn : Bk) => ResultT.mk (IO.pure (Result.ok a))))

/// Lift an `IO` action that cannot fail. Built directly rather than with
/// `ResultT.lift`: the lift-inside-a-do-block shape crashes the compiled
/// backend (motes/shuttle/src/loop.mo:258).
pub def DbM.lift_io {Bk : Type} {A : Type} (m : IO A) : DbM Bk A :=
    DbM.mk (ReaderT.mk (fn (_conn : Bk) =>
        ResultT.mk (Monad.bind m (fn (a : A) => IO.pure (Result.ok a)))))

/// Read the connection.
pub def DbM.ask {Bk : Type} : DbM Bk Bk :=
    DbM.mk (ReaderT.mk (fn (conn : Bk) => ResultT.mk (IO.pure (Result.ok conn))))

/// Run the continuation on `Result.ok` and short-circuit `Result.err`.
/// The bind is written against the concrete `IO` layer below rather than
/// by resolving `Monad (ReaderT Bk (ResultT SqlError IO))`: the generic
/// instance miscompiles self-hosted at a concrete `Bk` (same dictionary
/// family as the constrained-generic bug), while `PageM`'s
/// `page_bind_run` shows this direct shape is reliable.
def dbm_bind_step {Bk : Type} {A : Type} {B : Type}
        (f : A -> DbM Bk B) (conn : Bk) (r : Result SqlError A) :
        IO (Result SqlError B) :=
    match r {
        Result.ok a => ResultT.run (ReaderT.run (DbM.underlying (f a)) conn),
        Result.err e => IO.pure (Result.err e)
    }

def dbm_bind_run {Bk : Type} {A : Type} {B : Type}
        (ma : DbM Bk A) (f : A -> DbM Bk B) (conn : Bk) :
        ResultT SqlError IO B :=
    ResultT.mk (Monad.bind (ResultT.run (ReaderT.run (DbM.underlying ma) conn))
        (dbm_bind_step f conn))

def dbm_bind {Bk : Type} {A : Type} {B : Type}
        (ma : DbM Bk A) (f : A -> DbM Bk B) : DbM Bk B :=
    DbM.mk (ReaderT.mk (dbm_bind_run ma f))

pub instance Monad (DbM Bk) {
    def pure (a : A) : DbM Bk A := DbM.pure a
    def bind (ma : DbM Bk A) (f : A -> DbM Bk B) : DbM Bk B :=
        dbm_bind ma f
}
