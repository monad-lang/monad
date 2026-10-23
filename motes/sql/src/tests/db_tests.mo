// Tests for the common transformer stack and for the dispatch boundary the
// compiled backend currently enforces.
//
// A `Fake` connection needs no FFI, so this file runs under both hosts. It
// pins three things:
//
//   * `Monad (DbM Bk)` works at a concrete `Bk` (the bind is written
//     directly against the concrete IO layer; resolving
//     `Monad (ReaderT Bk (ResultT ...))` miscompiled self-hosted);
//   * concrete `Backend` method calls work (`Backend.exec conn ...`);
//   * generic `[Backend Bk]` helpers do NOT go through this file -- they
//     are documented as blocked by the constrained-generic bug, and the
//     driver supplies concrete operations instead.

use std::test {}
use init::transformers {ReaderT, ResultT}
use lib::value {SqlError, Value, ResultSet}
use lib::backend {Backend}
use lib::db {DbM, DbM.run, DbM.pure, DbM.lift_io}

type Fake {
    fake
}

pub instance Backend Fake {
    def close (b : Fake) : IO (Result SqlError Unit) :=
        IO.pure (Result.ok Unit.unit)
    def exec (b : Fake) (sql : String) (params : List Value) : IO (Result SqlError I64) :=
        IO.pure (Result.ok 1)
    def exec_script (b : Fake) (sql : String) : IO (Result SqlError Unit) :=
        IO.pure (Result.ok Unit.unit)
    def query (b : Fake) (sql : String) (params : List Value) : IO (Result SqlError ResultSet) :=
        IO.pure (Result.err (SqlError.backend "no query" 0))
    def begin_tx (b : Fake) : IO (Result SqlError Unit) :=
        IO.pure (Result.ok Unit.unit)
    def commit_tx (b : Fake) : IO (Result SqlError Unit) :=
        IO.pure (Result.ok Unit.unit)
    def rollback_tx (b : Fake) : IO (Result SqlError Unit) :=
        IO.pure (Result.ok Unit.unit)
}

def dbm_bind_test : DbM Fake I64 := do {
    let n <- DbM.pure 5;
    return (n + 1)
}

#[test]
def test_dbm_pure_run : IO Bool := do {
    let r <- DbM.run (DbM.pure 42) Fake.fake;
    match r {
        Result.ok n => return (n == 42),
        Result.err _ => return false
    }
}

#[test]
def test_dbm_bind : IO Bool := do {
    let r <- DbM.run dbm_bind_test Fake.fake;
    match r {
        Result.ok n => return (n == 6),
        Result.err _ => return false
    }
}

#[test]
def test_dbm_lift_io : IO Bool := do {
    let r <- DbM.run (DbM.lift_io (IO.pure 9)) Fake.fake;
    match r {
        Result.ok n => return (n == 9),
        Result.err _ => return false
    }
}

def failing : DbM Fake I64 :=
    DbM.mk (ReaderT.mk (fn (_c : Fake) =>
        ResultT.mk (IO.pure (Result.err (SqlError.backend "boom" 1)))))

def failing_then : DbM Fake I64 := do {
    let n <- failing;
    return (n + 1)
}

#[test]
def test_dbm_short_circuits : IO Bool := do {
    let r <- DbM.run failing_then Fake.fake;
    match r {
        Result.ok _ => return false,
        Result.err e => return (String.beq (SqlError.message e) "boom")
    }
}

#[test]
def test_concrete_backend_exec : IO Bool := do {
    let r <- Backend.exec Fake.fake "SELECT 1" List.empty;
    match r {
        Result.ok n => return (n == 1),
        Result.err _ => return false
    }
}
