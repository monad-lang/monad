// monad-sqlite / conn -- opening, configuring and closing a connection.
//
// `sqlite3_open_v2` returns the handle through a `sqlite3**` out-parameter.
// The slot is a zero-filled 8-byte `ByteBuf`; `ByteBuf.take_ptr` reads the
// pointer back from it (validating the buffer's kind and length).

use std::bytebuf {ByteBuf.alloc, ByteBuf.free, ByteBuf.ptr, ByteBuf.take_ptr}
use sql::value {SqlError}
use lib::ffi {sqlite3_open_v2, sqlite3_close_v2, sqlite3_busy_timeout,
    sqlite3_errmsg, sqlite3_errstr, sqlite3_extended_errcode, sqlite3_exec,
    Sqlite.ok, Sqlite.open_flags}
use lib::cstring {CString.read}

/// The connection handle. `db` is an FFI detail: do not pass it to another
/// C function; use the `Backend`/`SqliteM` operations instead.
pub struct SqliteConn {
    db : Ptr
}

/// A failure on a live connection: the driver's message plus its extended
/// result code.
def Sqlite.error_at {A : Type} (db : Ptr) (rc : I32) : IO (Result SqlError A) := do {
    let msg <- CString.read (sqlite3_errmsg db);
    let code := I32.to_i64 (sqlite3_extended_errcode db);
    return (Result.err (SqlError.backend msg code))
}

/// A failure with no usable handle (open/close): `sqlite3_errstr` does not
/// touch the connection.
def Sqlite.errstr_result {A : Type} (rc : I32) : IO (Result SqlError A) := do {
    let msg <- CString.read (sqlite3_errstr rc);
    return (Result.err (SqlError.backend msg (I32.to_i64 rc)))
}

def Sqlite.exec_pragma (db : Ptr) (sql : String) : IO (Result SqlError Unit) := do {
    let rc := sqlite3_exec db sql Ptr.null Ptr.null Ptr.null;
    if I32.beq rc Sqlite.ok
    then return (Result.ok Unit.unit)
    else Sqlite.error_at db rc
}

def Sqlite.configure_failed (db : Ptr) (e : SqlError) :
        IO (Result SqlError SqliteConn) := do {
    let _ := sqlite3_close_v2 db;
    return (Result.err e)
}

def Sqlite.ready (db : Ptr) : IO (Result SqlError SqliteConn) := do {
    let c : SqliteConn := { db := db };
    return (Result.ok c)
}

def Sqlite.configure_wal (db : Ptr) : IO (Result SqlError SqliteConn) := do {
    let wal <- Sqlite.exec_pragma db "PRAGMA journal_mode = WAL";
    match wal {
        Result.err e => Sqlite.configure_failed db e,
        Result.ok _ => Sqlite.ready db
    }
}

def Sqlite.configure (db : Ptr) : IO (Result SqlError SqliteConn) := do {
    let _ := sqlite3_busy_timeout db (I64.to_i32 5000);
    let fk <- Sqlite.exec_pragma db "PRAGMA foreign_keys = ON";
    match fk {
        Result.err e => Sqlite.configure_failed db e,
        Result.ok _ => Sqlite.configure_wal db
    }
}

def Sqlite.open_failed (db : Ptr) (rc : I32) :
        IO (Result SqlError SqliteConn) := do {
    let msg <- CString.read (sqlite3_errstr rc);
    let _ := sqlite3_close_v2 db;
    return (Result.err (SqlError.backend msg (I32.to_i64 rc)))
}

/// Open (or create) a database file, or use `":memory:"`.
///
/// Enables `foreign_keys`, a 5000 ms busy timeout and WAL. Any pragma
/// failure closes the handle and is returned as an error; WAL on an
/// in-memory database is not a failure (SQLite reports `memory`).
pub def Sqlite.connect (path : String) : IO (Result SqlError SqliteConn) := do {
    let slot <- ByteBuf.alloc 8;
    let rc := sqlite3_open_v2 path (ByteBuf.ptr slot) Sqlite.open_flags Ptr.null;
    let db : Ptr := ByteBuf.take_ptr slot;
    let _ <- ByteBuf.free slot;
    if I32.beq rc Sqlite.ok
    then Sqlite.configure db
    else Sqlite.open_failed db rc
}

/// Close the connection. `sqlite3_close_v2(NULL)` is a no-op, and every
/// statement is finalized inside its own call, so this normally
/// succeeds; a failure is reported rather than swallowed.
pub def Sqlite.close (conn : SqliteConn) : IO (Result SqlError Unit) := do {
    let rc := sqlite3_close_v2 conn.db;
    if I32.beq rc Sqlite.ok
    then return (Result.ok Unit.unit)
    else Sqlite.errstr_result rc
}
