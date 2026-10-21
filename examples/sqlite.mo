/// A SQLite end-to-end demo: migrate a file database, insert a row with a
/// bound parameter, query it back, and close.
///
/// Compiled-backend only (`#[extern "c"]`); run it with the self-hosted
/// `monad` binary inside the devshell so `-lsqlite3` resolves.
#![mote { name := "sqlite_example", deps := [sql, sqlite] }]

open IO {println}
use std::process {exec_cmd}
use sql::value {Row, Row.get_i64, Row.get_text, ResultSet, SqlError, SqlError.message, Value}
use sql::migrations {Migration, Migrations.migration}
use sqlite::conn {SqliteConn, Sqlite.connect, Sqlite.close}
use sqlite::monad {SqliteM, SqliteM.run, Sqlite.exec, Sqlite.query}
use sqlite::migrations {Sqlite.migrate}

def db_path : String := "/tmp/monad_sqlite_example.db"

def migrations : List Migration :=
  [Migrations.migration 1 "create_notes"
     "CREATE TABLE notes (id INTEGER PRIMARY KEY, body TEXT);"
     (Option.some "DROP TABLE notes;")]

def app : SqliteM ResultSet := do {
  let _ <- Sqlite.exec "INSERT INTO notes (body) VALUES (?)"
    [Value.text "hello from Monad + SQLite"];
  Sqlite.query "SELECT id, body FROM notes ORDER BY id" List.empty
}

def show_row (r : Row) : String :=
  match Row.get_i64 r "id" {
    Result.ok id =>
      match Row.get_text r "body" {
        Result.ok body => String.concat (I64.to_string id) (String.concat ": " body),
        Result.err _ => "<bad body>"
      },
    Result.err _ => "<bad id>"
  }

def print_rows (rows : List Row) : IO Unit :=
  match rows {
    List.empty => println "rows end",
    List.cons r rest => do {
      println (show_row r);
      print_rows rest
    }
  }

def report_error (label : String) (e : SqlError) : IO Unit :=
  println (String.concat label (SqlError.message e))

def run_app (conn : SqliteConn) : IO Unit := do {
  let migrated <- Sqlite.migrate conn migrations;
  match migrated {
    Result.err e => report_error "migrate failed: " e,
    Result.ok _ => run_query conn
  }
}

def run_query (conn : SqliteConn) : IO Unit := do {
  let r <- SqliteM.run app conn;
  match r {
    Result.err e => report_error "query failed: " e,
    Result.ok rs => print_rows rs.rows
  }
}

def main (args : List String) : IO Unit := do {
  let _ <- exec_cmd "rm" ["-f", db_path];
  let opened <- Sqlite.connect db_path;
  match opened {
    Result.err e => report_error "open failed: " e,
    Result.ok conn => do {
      run_app conn;
      let _ <- Sqlite.close conn;
      let _ <- exec_cmd "rm" ["-f", db_path];
      println "done"
    }
  }
}
