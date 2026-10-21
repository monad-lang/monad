// monad-sql / backend -- the interface every driver implements.
//
// Every method takes the connection `Bk` in ARGUMENT position. Connection
// construction is deliberately not a class method: `connect (path :
// String) : IO (Result SqlError Bk)` would place `Bk` only in the return
// type, which the checker cannot dispatch on. A driver therefore exposes
// its own `open` (e.g. `Sqlite.open`).

use lib::value {ResultSet, SqlError, Value}

pub class Backend (Bk : Type) {
    /// Close the connection. A failure is reported, never swallowed.
    def close (b : Bk) : IO (Result SqlError Unit)

    /// Run one statement with parameters and report the affected-row count.
    def exec (b : Bk) (sql : String) (params : List Value) : IO (Result SqlError I64)

    /// Run a script that may contain several statements (DDL and
    /// migrations). A single prepared statement would execute only the
    /// first, so drivers must use their multi-statement entry point.
    def exec_script (b : Bk) (sql : String) : IO (Result SqlError Unit)

    /// Run one query and collect every row.
    def query (b : Bk) (sql : String) (params : List Value) : IO (Result SqlError ResultSet)

    def begin_tx (b : Bk) : IO (Result SqlError Unit)
    def commit_tx (b : Bk) : IO (Result SqlError Unit)
    def rollback_tx (b : Bk) : IO (Result SqlError Unit)
}
