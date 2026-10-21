// Integration tests for motes/sqlite.
//
// Compiled-backend only: `#[extern "c"]`, `ByteBuf.ptr` and the runtime
// pointer helper exist only on the self-hosted/LLVM path. Run with
// `monad test motes/sqlite` inside the devshell (which supplies sqlite3).

use std::test {}
use std::list {List.length}
use std::process {exec_cmd, process_id}
use sql::value {Row, Row.get, Row.get_i64, Row.get_text, Row.get_bool,
    Row.get_f64, Row.get_blob, ResultSet, SqlError, SqlError.message, Value}
use lib::conn {SqliteConn, Sqlite.connect, Sqlite.close}
use lib::backend {Sqlite.exec_io, Sqlite.query_io}
use lib::monad {SqliteM, SqliteM.run, Sqlite.exec, Sqlite.query,
    Sqlite.transaction, Sqlite.last_insert_rowid_m}

// ─── Assertion helpers ───────────────────────────────────────────────────

def i64_is (r : Result SqlError I64) (expected : I64) : Bool :=
    match r {
        Result.ok n => n == expected,
        Result.err _ => false
    }

def text_is (r : Result SqlError String) (expected : String) : Bool :=
    match r {
        Result.ok s => String.beq s expected,
        Result.err _ => false
    }

def bool_is (r : Result SqlError Bool) (expected : Bool) : Bool :=
    match r {
        Result.ok b => b == expected,
        Result.err _ => false
    }

def f64_is (r : Result SqlError F64) (expected : F64) : Bool :=
    match r {
        Result.ok x => F64.beq x expected,
        Result.err _ => false
    }

def blob_len_is (r : Result SqlError (List U8)) (expected : I64) : Bool :=
    match r {
        Result.ok xs => List.length xs == expected,
        Result.err _ => false
    }

def is_null_value (v : Value) : Bool :=
    match v {
        Value.null => true,
        _ => false
    }

/// Open an in-memory connection, run `f`, and close it. A failure to open
/// (or any false result) is a test failure.
def with_memory (f : SqliteConn -> IO Bool) : IO Bool := do {
    let opened <- Sqlite.connect ":memory:";
    match opened {
        Result.err _ => return false,
        Result.ok conn => do {
            let result <- f conn;
            let _ <- Sqlite.close conn;
            return result
        }
    }
}

// ─── CRUD and type round-trips ───────────────────────────────────────────

def row_ok (rs : ResultSet) : Bool :=
    match rs.rows {
        List.empty => false,
        List.cons r _ =>
            i64_is (Row.get_i64 r "id") 1
            && text_is (Row.get_text r "name") "ada"
            && f64_is (Row.get_f64 r "score") 1.5
            && bool_is (Row.get_bool r "ok") true
            && blob_len_is (Row.get_blob r "data") 3
    }

def crud : SqliteM Bool := do {
    let _ <- Sqlite.exec
        "CREATE TABLE t (id INTEGER PRIMARY KEY, name TEXT, score REAL, ok INTEGER, data BLOB)"
        List.empty;
    let inserted <- Sqlite.exec
        "INSERT INTO t (name, score, ok, data) VALUES (?, ?, ?, ?)"
        [Value.text "ada", Value.real 1.5, Value.boolean true,
         Value.blob [0u8, 255u8, 0u8]];
    let rowid <- Sqlite.last_insert_rowid_m;
    let rs <- Sqlite.query "SELECT id, name, score, ok, data FROM t" List.empty;
    return (inserted == 1 && rowid == 1 && row_ok rs)
}

#[test]
def test_crud_and_value_roundtrip : IO Bool :=
    with_memory (fn conn => do {
        let r <- SqliteM.run crud conn;
        match r {
            Result.ok b => return b,
            Result.err _ => return false
        }
    })

def null_row_ok (rs : ResultSet) : Bool :=
    match rs.rows {
        List.empty => false,
        List.cons r _ =>
            match Row.get r "name" {
                Option.some v => is_null_value v,
                Option.none => false
            }
    }

def null_program : SqliteM Bool := do {
    let _ <- Sqlite.exec "CREATE TABLE t (id INTEGER, name TEXT)" List.empty;
    let _ <- Sqlite.exec "INSERT INTO t (id, name) VALUES (?, ?)"
        [Value.integer 1, Value.null];
    let rs <- Sqlite.query "SELECT id, name FROM t" List.empty;
    return (null_row_ok rs)
}

#[test]
def test_null_roundtrip : IO Bool :=
    with_memory (fn conn => do {
        let r <- SqliteM.run null_program conn;
        match r {
            Result.ok b => return b,
            Result.err _ => return false
        }
    })

def empty_program : SqliteM Bool := do {
    let _ <- Sqlite.exec "CREATE TABLE t (id INTEGER)" List.empty;
    let rs <- Sqlite.query "SELECT id FROM t" List.empty;
    return (List.length rs.rows == 0 && List.length rs.columns == 1)
}

#[test]
def test_empty_result_set : IO Bool :=
    with_memory (fn conn => do {
        let r <- SqliteM.run empty_program conn;
        match r {
            Result.ok b => return b,
            Result.err _ => return false
        }
    })

#[test]
def test_open_invalid_path_errors : IO Bool := do {
    let r <- Sqlite.connect "/no/such/dir/monad_sqlite_test.db";
    match r {
        Result.ok conn => do {
            let _ <- Sqlite.close conn;
            return false
        },
        Result.err e => return (Bool.not (String.is_empty (SqlError.message e)))
    }
}

// ─── Errors ──────────────────────────────────────────────────────────────

def bad_program : SqliteM Unit := do {
    let _ <- Sqlite.exec "THIS IS NOT SQL" List.empty;
    return Unit.unit
}

#[test]
def test_bad_sql_reports_error : IO Bool :=
    with_memory (fn conn => do {
        let r <- SqliteM.run bad_program conn;
        match r {
            Result.ok _ => return false,
            Result.err e => return (Bool.not (String.is_empty (SqlError.message e)))
        }
    })

// A failed statement must leave the connection usable and the statement
// finalized (no leaked handle).
def after_error_program : SqliteM Bool := do {
    let _ <- Sqlite.exec "CREATE TABLE t (n INTEGER)" List.empty;
    let ok <- Sqlite.exec "INSERT INTO t VALUES (?)" [Value.integer 4];
    let rs <- Sqlite.query "SELECT n FROM t" List.empty;
    return (ok == 1 && first_n_is rs 4)
}

def first_n_is (rs : ResultSet) (expected : I64) : Bool :=
    match rs.rows {
        List.empty => false,
        List.cons r _ => i64_is (Row.get_i64 r "n") expected
    }

#[test]
def test_connection_usable_after_failed_statement : IO Bool :=
    with_memory (fn conn => do {
        let _ <- SqliteM.run bad_program conn;
        let r <- SqliteM.run after_error_program conn;
        match r {
            Result.ok b => return b,
            Result.err _ => return false
        }
    })

// ─── Transactions ────────────────────────────────────────────────────────

def count_of (rs : ResultSet) : I64 :=
    match rs.rows {
        List.empty => 0,
        List.cons r _ =>
            match Row.get_i64 r "n" {
                Result.ok n => n,
                Result.err _ => 0
            }
    }

def count_rows : SqliteM I64 := do {
    let rs <- Sqlite.query "SELECT COUNT(*) AS n FROM t" List.empty;
    return (count_of rs)
}

def commit_program : SqliteM Bool := do {
    let _ <- Sqlite.exec "CREATE TABLE t (n INTEGER)" List.empty;
    let _ <- Sqlite.transaction (Sqlite.exec "INSERT INTO t VALUES (1)" List.empty);
    let n <- count_rows;
    return (n == 1)
}

#[test]
def test_transaction_commits : IO Bool :=
    with_memory (fn conn => do {
        let r <- SqliteM.run commit_program conn;
        match r {
            Result.ok b => return b,
            Result.err _ => return false
        }
    })

def failing_tx : SqliteM Unit := do {
    let _ <- Sqlite.exec "INSERT INTO t VALUES (1)" List.empty;
    let _ <- Sqlite.exec "THIS IS NOT SQL" List.empty;
    return Unit.unit
}

def count_is (r : Result SqlError I64) (expected : I64) : IO Bool :=
    match r {
        Result.ok n => IO.pure (n == expected),
        Result.err _ => IO.pure false
    }

def check_rolled_back (conn : SqliteConn) (tx : Result SqlError Unit) : IO Bool :=
    match tx {
        Result.ok _ => IO.pure false,
        Result.err _ => do {
            let count <- SqliteM.run count_rows conn;
            count_is count 0
        }
    }

def run_failing_tx (conn : SqliteConn) : IO Bool := do {
    let tx <- SqliteM.run (Sqlite.transaction failing_tx) conn;
    check_rolled_back conn tx
}

def setup_then_rollback (conn : SqliteConn) (setup : Result SqlError I64) : IO Bool :=
    match setup {
        Result.err _ => IO.pure false,
        Result.ok _ => run_failing_tx conn
    }

#[test]
def test_transaction_rolls_back : IO Bool :=
    with_memory (fn conn => do {
        let setup <- SqliteM.run (Sqlite.exec "CREATE TABLE t (n INTEGER)" List.empty) conn;
        setup_then_rollback conn setup
    })

// ─── File database and WAL ───────────────────────────────────────────────

def file_path : String :=
    String.concat "/tmp/monad_sqlite_test_"
        (String.concat (I64.to_string process_id) ".db")

def journal_is_wal (rs : ResultSet) : Bool :=
    match rs.rows {
        List.empty => false,
        List.cons r _ =>
            match Row.get_text r "journal_mode" {
                Result.ok s => String.beq s "wal",
                Result.err _ => false
            }
    }

def file_setup : SqliteM Bool := do {
    let _ <- Sqlite.exec "CREATE TABLE t (n INTEGER)" List.empty;
    let _ <- Sqlite.exec "INSERT INTO t VALUES (?)" [Value.integer 7];
    let rs <- Sqlite.query "PRAGMA journal_mode" List.empty;
    return (journal_is_wal rs)
}

def n_is_seven (r : Result SqlError ResultSet) : Bool :=
    match r {
        Result.err _ => false,
        Result.ok rs =>
            match rs.rows {
                List.empty => false,
                List.cons row _ => i64_is (Row.get_i64 row "n") 7
            }
    }

def reopen_and_check (wal_ok : Bool) : IO Bool := do {
    let opened <- Sqlite.connect file_path;
    match opened {
        Result.err _ => return false,
        Result.ok conn => do {
            let r <- SqliteM.run (Sqlite.query "SELECT n FROM t" List.empty) conn;
            let _ <- Sqlite.close conn;
            let _ <- exec_cmd "rm" ["-f", file_path];
            return (wal_ok && n_is_seven r)
        }
    }
}

def file_roundtrip (conn : SqliteConn) : IO Bool := do {
    let setup <- SqliteM.run file_setup conn;
    match setup {
        Result.err _ => return false,
        Result.ok wal_ok => do {
            let _ <- Sqlite.close conn;
            reopen_and_check wal_ok
        }
    }
}

#[test]
def test_file_database_and_wal : IO Bool := do {
    let _ <- exec_cmd "rm" ["-f", file_path];
    let opened <- Sqlite.connect file_path;
    match opened {
        Result.err _ => return false,
        Result.ok conn => file_roundtrip conn
    }
}
