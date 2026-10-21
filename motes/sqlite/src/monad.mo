// monad-sqlite / monad -- the concrete transformer stack for SQLite.
//
// `SqliteM A = DbM SqliteConn A` behind a newtype, the `PageM` pattern in
// motes/oak/src/html_t.mo. The newtype is load-bearing, not cosmetic:
// generic `[Backend Bk]` helpers are miscompiled self-hosted, while a
// concrete-head `Monad SqliteM` instance and concrete `Backend` calls work.
// When the compiler bug is fixed, the common `Db.exec`/`Db.query`/
// `Db.transaction` can replace these thin wrappers.

use init::transformers {ReaderT, ResultT}
use sql::value {Row, ResultSet, SqlError, Value}
use sql::backend {Backend}
use sql::db {DbM, DbM.run, DbM.pure, DbM.lift_io}
use lib::conn {SqliteConn}
use lib::backend {Sqlite.exec_script_io, Sqlite.last_insert_rowid}

pub type SqliteM (A : Type) {
    sqlite_m (run : DbM SqliteConn A)
}

pub def SqliteM.underlying {A : Type} (m : SqliteM A) : DbM SqliteConn A :=
    match m {
        SqliteM.sqlite_m r => r
    }

pub def SqliteM.run {A : Type} (m : SqliteM A) (conn : SqliteConn) :
        IO (Result SqlError A) :=
    DbM.run (SqliteM.underlying m) conn

pub def SqliteM.pure {A : Type} (a : A) : SqliteM A :=
    SqliteM.sqlite_m (DbM.pure a)

pub def SqliteM.lift_io {A : Type} (m : IO A) : SqliteM A :=
    SqliteM.sqlite_m (DbM.lift_io m)

def sqlite_bind_run {A : Type} {B : Type} (ma : SqliteM A) (f : A -> SqliteM B) :
        DbM SqliteConn B :=
    Monad.bind (SqliteM.underlying ma) (fn (a : A) => SqliteM.underlying (f a))

pub instance Monad SqliteM {
    def pure (a : A) : SqliteM A := SqliteM.pure a
    def bind (ma : SqliteM A) (f : A -> SqliteM B) : SqliteM B :=
        SqliteM.sqlite_m (sqlite_bind_run ma f)
}

/// Run one statement with parameters; reports the affected-row count.
pub def Sqlite.exec (sql : String) (params : List Value) : SqliteM I64 :=
    SqliteM.sqlite_m (DbM.mk (ReaderT.mk (fn (conn : SqliteConn) =>
        ResultT.mk (Backend.exec conn sql params))))

/// Run a multi-statement script (DDL, migrations).
pub def Sqlite.exec_script (sql : String) : SqliteM Unit :=
    SqliteM.sqlite_m (DbM.mk (ReaderT.mk (fn (conn : SqliteConn) =>
        ResultT.mk (Sqlite.exec_script_io conn sql))))

/// Run one query and collect every row.
pub def Sqlite.query (sql : String) (params : List Value) : SqliteM ResultSet :=
    SqliteM.sqlite_m (DbM.mk (ReaderT.mk (fn (conn : SqliteConn) =>
        ResultT.mk (Backend.query conn sql params))))

/// The first row, or `none`. Extra rows are ignored.
pub def Sqlite.query_one (sql : String) (params : List Value) :
        SqliteM (Option Row) := do {
    let rs <- Sqlite.query sql params;
    match rs.rows {
        List.empty => return Option.none,
        List.cons r _ => return (Option.some r)
    }
}

/// `sqlite3_last_insert_rowid` for the connection in the environment.
pub def Sqlite.last_insert_rowid_m : SqliteM I64 :=
    SqliteM.sqlite_m (DbM.mk (ReaderT.mk (fn (conn : SqliteConn) =>
        ResultT.mk (IO.pure (Result.ok (Sqlite.last_insert_rowid conn))))))

/// Run `m` inside `BEGIN IMMEDIATE`/`COMMIT`, rolling back on any
/// `SqlError`. Not reentrant: SQLite has no nested `BEGIN`; use savepoints
/// explicitly if a body needs them.
pub def Sqlite.transaction {A : Type} (m : SqliteM A) : SqliteM A :=
    SqliteM.sqlite_m (DbM.mk (ReaderT.mk (fn (conn : SqliteConn) =>
        ResultT.mk (Sqlite.transaction_io conn m))))

def Sqlite.transaction_io {A : Type} (conn : SqliteConn) (m : SqliteM A) :
        IO (Result SqlError A) := do {
    let b <- Sqlite.exec_script_io conn "BEGIN IMMEDIATE";
    match b {
        Result.err e => return (Result.err e),
        Result.ok _ => Sqlite.transaction_body conn m
    }
}

def Sqlite.transaction_body {A : Type} (conn : SqliteConn) (m : SqliteM A) :
        IO (Result SqlError A) := do {
    let r <- SqliteM.run m conn;
    match r {
        Result.ok a => Sqlite.transaction_commit conn a,
        Result.err e => Sqlite.transaction_abort conn e
    }
}

def Sqlite.transaction_commit {A : Type} (conn : SqliteConn) (a : A) :
        IO (Result SqlError A) := do {
    let c <- Sqlite.exec_script_io conn "COMMIT";
    match c {
        Result.ok _ => return (Result.ok a),
        Result.err e => Sqlite.transaction_abort conn e
    }
}

def Sqlite.transaction_abort {A : Type} (conn : SqliteConn) (e : SqlError) :
        IO (Result SqlError A) := do {
    let _ <- Sqlite.exec_script_io conn "ROLLBACK";
    return (Result.err e)
}
