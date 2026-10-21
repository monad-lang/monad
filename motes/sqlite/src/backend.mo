// monad-sqlite / backend -- prepared statements, binding, stepping and
// column decoding.
//
// Lifecycle rule: every statement prepared here is finalized before the
// call returns, on every path (bind failure, step failure, decode failure,
// success). `sqlite3_finalize(NULL)` is a no-op, so the failure helpers can
// finalize unconditionally.
//
// `sqlite3_exec` is the multi-statement path (DDL and migrations); a
// prepared statement executes only the first statement in its string.

use std::bytebuf {ByteBuf.alloc, ByteBuf.of_list, ByteBuf.free, ByteBuf.length, ByteBuf.ptr, ByteBuf.take_ptr}
use sql::value {Row, ResultSet, SqlError, Value}
use sql::backend {Backend}
use lib::ffi {sqlite3_prepare_v2, sqlite3_finalize, sqlite3_step,
    sqlite3_bind_null, sqlite3_bind_int64, sqlite3_bind_double,
    sqlite3_bind_text, sqlite3_bind_blob,
    sqlite3_column_count, sqlite3_column_name, sqlite3_column_type,
    sqlite3_column_int64, sqlite3_column_double, sqlite3_column_text,
    sqlite3_column_blob, sqlite3_column_bytes, sqlite3_changes,
    sqlite3_last_insert_rowid, sqlite3_exec,
    Sqlite.ok, Sqlite.row, Sqlite.done, Sqlite.type_null, Sqlite.type_integer,
    Sqlite.type_real, Sqlite.type_text, Sqlite.type_blob,
    Sqlite.transient_destructor}
use std::cstring {CString.read, CString.read_n, CString.bytes}
use lib::conn {SqliteConn, Sqlite.close, Sqlite.error_at}

// ─── Statement lifecycle ─────────────────────────────────────────────────

def Sqlite.finalize_with {A : Type} (stmt : Ptr) (r : Result SqlError A) :
        IO (Result SqlError A) := do {
    let _ <- IO.mk (sqlite3_finalize stmt);
    return r
}

def Sqlite.finalize_error {A : Type} (db : Ptr) (stmt : Ptr) (rc : I32) :
        IO (Result SqlError A) := do {
    let _ <- IO.mk (sqlite3_finalize stmt);
    Sqlite.error_at db rc
}

def Sqlite.prepare (conn : SqliteConn) (sql : String) :
        IO (Result SqlError Ptr) := do {
    let slot <- ByteBuf.alloc 8;
    let rc <- IO.mk (sqlite3_prepare_v2 conn.db sql (I64.to_i32 (0 - 1))
        (ByteBuf.ptr slot) Ptr.null);
    let stmt : Ptr := ByteBuf.take_ptr slot;
    let _ <- ByteBuf.free slot;
    if I32.beq rc Sqlite.ok
    then return (Result.ok stmt)
    else Sqlite.finalize_error conn.db stmt rc
}

// ─── Binding ────────────────────────────────────────────────────────────

def Sqlite.bind_rc (db : Ptr) (rc : I32) : IO (Result SqlError Unit) :=
    if I32.beq rc Sqlite.ok
    then IO.pure (Result.ok Unit.unit)
    else Sqlite.error_at db rc

def Sqlite.bind_blob (db : Ptr) (stmt : Ptr) (idx : I32) (bytes : List U8) :
        IO (Result SqlError Unit) := do {
    let buf <- ByteBuf.of_list bytes;
    let rc <- IO.mk (sqlite3_bind_blob stmt idx (ByteBuf.ptr buf)
        (I64.to_i32 (ByteBuf.length buf)) Sqlite.transient_destructor);
    let out <- Sqlite.bind_rc db rc;
    let _ <- ByteBuf.free buf;
    return out
}

/// Sequence a side-effecting bind call (`RawIO I32`) and turn its result
/// code into the driver's `Result`. Kept as a separate def because a
/// `let .. <- ..` directly in a `match` arm of `Sqlite.bind_one` is a
/// shape the self-hosted parser rejects.
def Sqlite.bind_call (db : Ptr) (raw : RawIO I32) : IO (Result SqlError Unit) := do {
    let rc <- IO.mk raw;
    Sqlite.bind_rc db rc
}

def Sqlite.bind_one (db : Ptr) (stmt : Ptr) (idx : I32) (v : Value) :
        IO (Result SqlError Unit) :=
    match v {
        Value.null =>
            Sqlite.bind_call db (sqlite3_bind_null stmt idx),
        Value.integer n =>
            Sqlite.bind_call db (sqlite3_bind_int64 stmt idx n),
        Value.real x =>
            Sqlite.bind_call db (sqlite3_bind_double stmt idx x),
        Value.boolean b =>
            Sqlite.bind_call db (sqlite3_bind_int64 stmt idx (if b then 1 else 0)),
        Value.text s =>
            Sqlite.bind_call db (sqlite3_bind_text stmt idx s
                (I64.to_i32 (String.length s)) Sqlite.transient_destructor),
        Value.blob bytes => Sqlite.bind_blob db stmt idx bytes
    }

#[terminating]
def Sqlite.bind_params (db : Ptr) (stmt : Ptr) (params : List Value) (idx : I32) :
        IO (Result SqlError Unit) :=
    match params {
        List.empty => IO.pure (Result.ok Unit.unit),
        List.cons v rest => do {
            let r <- Sqlite.bind_one db stmt idx v;
            match r {
                Result.err e => return (Result.err e),
                Result.ok _ =>
                    Sqlite.bind_params db stmt rest (I64.to_i32 (I32.to_i64 idx + 1))
            }
        }
    }

// ─── Decoding ────────────────────────────────────────────────────────────

type ColumnKind {
    null_kind,
    integer_kind,
    real_kind,
    text_kind,
    blob_kind,
    other_kind
}

def Sqlite.column_kind (t : I32) : ColumnKind :=
    if I32.beq t Sqlite.type_null then ColumnKind.null_kind
    else if I32.beq t Sqlite.type_integer then ColumnKind.integer_kind
    else if I32.beq t Sqlite.type_real then ColumnKind.real_kind
    else if I32.beq t Sqlite.type_text then ColumnKind.text_kind
    else if I32.beq t Sqlite.type_blob then ColumnKind.blob_kind
    else ColumnKind.other_kind

def Sqlite.decode_text (stmt : Ptr) (i : I32) : IO Value := do {
    let n := I32.to_i64 (sqlite3_column_bytes stmt i);
    if n < 1
    then return (Value.text "")
    else do {
        let s <- CString.read_n (sqlite3_column_text stmt i) n;
        return (Value.text s)
    }
}

def Sqlite.decode_blob (stmt : Ptr) (i : I32) : IO Value := do {
    let n := I32.to_i64 (sqlite3_column_bytes stmt i);
    if n < 1
    then return (Value.blob List.empty)
    else do {
        let bytes <- CString.bytes (sqlite3_column_blob stmt i) n;
        return (Value.blob bytes)
    }
}

def Sqlite.decode_column (stmt : Ptr) (i : I32) : IO Value := do {
    let kind := Sqlite.column_kind (sqlite3_column_type stmt i);
    match kind {
        ColumnKind.null_kind => return Value.null,
        ColumnKind.integer_kind => return (Value.integer (sqlite3_column_int64 stmt i)),
        ColumnKind.real_kind => return (Value.real (sqlite3_column_double stmt i)),
        ColumnKind.text_kind => Sqlite.decode_text stmt i,
        ColumnKind.blob_kind => Sqlite.decode_blob stmt i,
        ColumnKind.other_kind => return Value.null
    }
}

/// Column names in declaration order.
///
/// Walks indices downward and CONSES each name onto an accumulator: the
/// last column is consed first, so the final list reads left-to-right.
/// (Consing while walking upward would reverse the names against the
/// values decoded in `decode_row`.)
#[terminating]
def Sqlite.column_names (stmt : Ptr) (i : I32) (acc : List String) :
        IO (List String) :=
    if I32.to_i64 i < 0
    then IO.pure acc
    else do {
        let name <- CString.read (sqlite3_column_name stmt i);
        Sqlite.column_names stmt (I64.to_i32 (I32.to_i64 i - 1)) (List.cons name acc)
    }

def Sqlite.make_row (cells : List (Pair String Value)) : Row :=
    let r : Row := { cells := cells } in r

def Sqlite.make_result_set (columns : List String) (rows : List Row) : ResultSet :=
    let rs : ResultSet := { columns := columns, rows := rows } in rs

def Sqlite.decode_row (stmt : Ptr) (names : List String) (index : I64)
        (acc : List (Pair String Value)) : IO (Result SqlError Row) :=
    match names {
        List.empty =>
            IO.pure (Result.ok (Sqlite.make_row (List.reverse acc))),
        List.cons name rest => do {
            let value <- Sqlite.decode_column stmt (I64.to_i32 index);
            Sqlite.decode_row stmt rest (index + 1) (List.cons (Pair.pair name value) acc)
        }
    }

// ─── Stepping ────────────────────────────────────────────────────────────

#[terminating]
def Sqlite.step_rows (db : Ptr) (stmt : Ptr) (names : List String)
        (acc : List Row) : IO (Result SqlError (List Row)) := do {
    let rc <- IO.mk (sqlite3_step stmt);
    if I32.beq rc Sqlite.row
    then do {
        let row <- Sqlite.decode_row stmt names 0 List.empty;
        match row {
            Result.err e => return (Result.err e),
            Result.ok r => Sqlite.step_rows db stmt names (List.cons r acc)
        }
    }
    else if I32.beq rc Sqlite.done
    then return (Result.ok (List.reverse acc))
    else Sqlite.error_at db rc
}

#[terminating]
def Sqlite.step_discard (db : Ptr) (stmt : Ptr) : IO (Result SqlError I64) := do {
    let rc <- IO.mk (sqlite3_step stmt);
    if I32.beq rc Sqlite.done
    then Sqlite.exec_done db stmt
    else if I32.beq rc Sqlite.row
    then Sqlite.step_discard db stmt
    else Sqlite.finalize_error db stmt rc
}

def Sqlite.exec_done (db : Ptr) (stmt : Ptr) : IO (Result SqlError I64) := do {
    let n := I32.to_i64 (sqlite3_changes db);
    let _ <- IO.mk (sqlite3_finalize stmt);
    return (Result.ok n)
}

def Sqlite.query_bound (db : Ptr) (stmt : Ptr) :
        IO (Result SqlError ResultSet) := do {
    let count := sqlite3_column_count stmt;
    let names <- Sqlite.column_names stmt (I64.to_i32 (I32.to_i64 count - 1)) List.empty;
    let rows <- Sqlite.step_rows db stmt names List.empty;
    match rows {
        Result.err e => Sqlite.finalize_with stmt (Result.err e),
        Result.ok rs =>
            Sqlite.finalize_with stmt (Result.ok (Sqlite.make_result_set names rs))
    }
}

def Sqlite.query_prepared (db : Ptr) (stmt : Ptr) (params : List Value) :
        IO (Result SqlError ResultSet) := do {
    let br <- Sqlite.bind_params db stmt params (I64.to_i32 1);
    match br {
        Result.err e => Sqlite.finalize_with stmt (Result.err e),
        Result.ok _ => Sqlite.query_bound db stmt
    }
}

def Sqlite.exec_prepared (db : Ptr) (stmt : Ptr) (params : List Value) :
        IO (Result SqlError I64) := do {
    let br <- Sqlite.bind_params db stmt params (I64.to_i32 1);
    match br {
        Result.err e => Sqlite.finalize_with stmt (Result.err e),
        Result.ok _ => Sqlite.step_discard db stmt
    }
}

// ─── Public driver entry points ──────────────────────────────────────────

pub def Sqlite.query_io (conn : SqliteConn) (sql : String) (params : List Value) :
        IO (Result SqlError ResultSet) := do {
    let prep <- Sqlite.prepare conn sql;
    match prep {
        Result.err e => return (Result.err e),
        Result.ok stmt => Sqlite.query_prepared conn.db stmt params
    }
}

pub def Sqlite.exec_io (conn : SqliteConn) (sql : String) (params : List Value) :
        IO (Result SqlError I64) := do {
    let prep <- Sqlite.prepare conn sql;
    match prep {
        Result.err e => return (Result.err e),
        Result.ok stmt => Sqlite.exec_prepared conn.db stmt params
    }
}

pub def Sqlite.exec_script_io (conn : SqliteConn) (sql : String) :
        IO (Result SqlError Unit) := do {
    let rc <- IO.mk (sqlite3_exec conn.db sql Ptr.null Ptr.null Ptr.null);
    if I32.beq rc Sqlite.ok
    then return (Result.ok Unit.unit)
    else Sqlite.error_at conn.db rc
}

pub def Sqlite.last_insert_rowid (conn : SqliteConn) : I64 :=
    sqlite3_last_insert_rowid conn.db

// ─── The class instance ──────────────────────────────────────────────────

instance Backend SqliteConn {
    def close (b : SqliteConn) : IO (Result SqlError Unit) := Sqlite.close b
    def exec (b : SqliteConn) (sql : String) (params : List Value) :
            IO (Result SqlError I64) := Sqlite.exec_io b sql params
    def exec_script (b : SqliteConn) (sql : String) : IO (Result SqlError Unit) :=
        Sqlite.exec_script_io b sql
    def query (b : SqliteConn) (sql : String) (params : List Value) :
            IO (Result SqlError ResultSet) := Sqlite.query_io b sql params
    def begin_tx (b : SqliteConn) : IO (Result SqlError Unit) :=
        Sqlite.exec_script_io b "BEGIN IMMEDIATE"
    def commit_tx (b : SqliteConn) : IO (Result SqlError Unit) :=
        Sqlite.exec_script_io b "COMMIT"
    def rollback_tx (b : SqliteConn) : IO (Result SqlError Unit) :=
        Sqlite.exec_script_io b "ROLLBACK"
}
