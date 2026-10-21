// Integration tests for the SQLite migration runner, over `:memory:` and a
// real directory of `.up.sql`/`.down.sql` files.
//
// Compiled-backend only, like sqlite_tests.mo.

use std::test {}
use std::list {List.length}
use std::process {exec_cmd, process_id}
use std::path {Path}
use std::io {IO.write_file}
use sql::value {Row, ResultSet, SqlError, Value}
use sql::migrations {Migration, MigrationState, Migrations.migration}
use lib::conn {SqliteConn, Sqlite.connect, Sqlite.close}
use lib::backend {Sqlite.query_io}
use lib::migrations {Sqlite.migrate, Sqlite.migrate_dir, Sqlite.rollback_to,
    Sqlite.rollback_last, Sqlite.status}

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

def migrations_dir : Path :=
    Path.path (String.concat "/tmp/monad_sqlite_migrations_test_"
        (I64.to_string process_id))

def write_named (p : Path) (name : String) (content : String) : IO Bool := do {
    let r <- IO.write_file (Path.join p (Path.path name)) content;
    match r {
        Result.ok _ => return true,
        Result.err _ => return false
    }
}

// ─── Fixtures ────────────────────────────────────────────────────────────

def create_users : Migration :=
    Migrations.migration 1 "create_users"
        "CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT); CREATE INDEX users_name ON users (name);"
        (Option.some "DROP TABLE users;")

def add_email : Migration :=
    Migrations.migration 2 "add_email"
        "ALTER TABLE users ADD COLUMN email TEXT;"
        (Option.some "ALTER TABLE users DROP COLUMN email;")

def changed_users : Migration :=
    Migrations.migration 1 "create_users"
        "CREATE TABLE users (id INTEGER PRIMARY KEY, name TEXT, extra TEXT);"
        Option.none

def no_down : Migration :=
    Migrations.migration 1 "no_down"
        "CREATE TABLE no_down (n INTEGER);"
        Option.none

def bad_migration : Migration :=
    Migrations.migration 2 "bad"
        "THIS IS NOT SQL;"
        Option.none

// ─── Assertions ──────────────────────────────────────────────────────────

def applied_count_is (r : Result SqlError (List I64)) (expected : I64) : Bool :=
    match r {
        Result.ok vs => List.length vs == expected,
        Result.err _ => false
    }

def sql_error_is_migration (e : SqlError) : Bool :=
    match e {
        SqlError.migration _ => true,
        _ => false
    }

def migration_error_is (r : Result SqlError (List I64)) : Bool :=
    match r {
        Result.err e => sql_error_is_migration e,
        Result.ok _ => false
    }

def states_all_applied (states : List MigrationState) : Bool :=
    match states {
        List.empty => true,
        List.cons s rest => s.applied && s.checksum_ok && states_all_applied rest
    }

def states_none_applied (states : List MigrationState) : Bool :=
    match states {
        List.empty => true,
        List.cons s rest => Bool.not s.applied && states_none_applied rest
    }

def status_is (r : Result SqlError (List MigrationState)) (check : List MigrationState -> Bool) : Bool :=
    match r {
        Result.err _ => false,
        Result.ok states => check states
    }

def first_applied_second_not (states : List MigrationState) : Bool :=
    match states {
        List.cons a rest =>
            match rest {
                List.cons b _ => a.applied && Bool.not b.applied,
                List.empty => false
            },
        List.empty => false
    }

// ─── Tests ───────────────────────────────────────────────────────────────

def migrate_twice (conn : SqliteConn) : IO Bool := do {
    let first <- Sqlite.migrate conn [create_users, add_email];
    match first {
        Result.err _ => return false,
        Result.ok _ => do {
            let again <- Sqlite.migrate conn [create_users, add_email];
            let st <- Sqlite.status conn [create_users, add_email];
            return (applied_count_is (Result.ok [1, 2]) 2
                && applied_count_is again 0
                && status_is st states_all_applied)
        }
    }
}

#[test]
def test_migrate_applies_and_is_idempotent : IO Bool :=
    with_memory migrate_twice

def drift_check (conn : SqliteConn) : IO Bool := do {
    let first <- Sqlite.migrate conn [create_users];
    match first {
        Result.err _ => return false,
        Result.ok _ => do {
            let second <- Sqlite.migrate conn [changed_users];
            return (migration_error_is second)
        }
    }
}

#[test]
def test_checksum_drift_is_rejected : IO Bool :=
    with_memory drift_check

def rollback_all_check (conn : SqliteConn) : IO Bool := do {
    let first <- Sqlite.migrate conn [create_users, add_email];
    match first {
        Result.err _ => return false,
        Result.ok _ => do {
            let rb <- Sqlite.rollback_to conn [create_users, add_email] 0;
            let st <- Sqlite.status conn [create_users, add_email];
            return (applied_count_is rb 2 && status_is st states_none_applied)
        }
    }
}

#[test]
def test_rollback_to_zero : IO Bool :=
    with_memory rollback_all_check

def rollback_last_check (conn : SqliteConn) : IO Bool := do {
    let first <- Sqlite.migrate conn [create_users, add_email];
    match first {
        Result.err _ => return false,
        Result.ok _ => do {
            let rb <- Sqlite.rollback_last conn [create_users, add_email];
            let st <- Sqlite.status conn [create_users, add_email];
            return (applied_count_is rb 1 && status_is st first_applied_second_not)
        }
    }
}

#[test]
def test_rollback_last_only : IO Bool :=
    with_memory rollback_last_check

def missing_down_check (conn : SqliteConn) : IO Bool := do {
    let first <- Sqlite.migrate conn [no_down];
    match first {
        Result.err _ => return false,
        Result.ok _ => do {
            let rb <- Sqlite.rollback_last conn [no_down];
            let st <- Sqlite.status conn [no_down];
            return (migration_error_is rb && status_is st states_all_applied)
        }
    }
}

#[test]
def test_rollback_preflight_requires_down : IO Bool :=
    with_memory missing_down_check

def failing_migration_check (conn : SqliteConn) : IO Bool := do {
    let first <- Sqlite.migrate conn [create_users, bad_migration];
    match first {
        Result.ok _ => return false,
        Result.err _ => do {
            let st <- Sqlite.status conn [create_users, bad_migration];
            return (status_is st first_applied_second_not)
        }
    }
}

#[test]
def test_failing_migration_rolls_back_and_is_not_recorded : IO Bool :=
    with_memory failing_migration_check

// ─── Directory loader end-to-end ─────────────────────────────────────────

def dir_check (conn : SqliteConn) (written : Bool) : IO Bool := do {
    let r <- Sqlite.migrate_dir conn migrations_dir;
    let st <- Sqlite.status conn
        [Migrations.migration 1 "a" "CREATE TABLE a (n INTEGER);" (Option.some "DROP TABLE a;"),
         Migrations.migration 2 "b" "CREATE TABLE b (n INTEGER);" Option.none];
    return (written && applied_count_is r 2 && status_is st states_all_applied)
}

#[test]
def test_migrate_dir : IO Bool := do {
    let p := migrations_dir;
    let _ <- exec_cmd "rm" ["-rf", Path.to_string p];
    let _ <- exec_cmd "mkdir" ["-p", Path.to_string p];
    let a <- write_named p "0001_a.up.sql" "CREATE TABLE a (n INTEGER);";
    let b <- write_named p "0001_a.down.sql" "DROP TABLE a;";
    let c <- write_named p "0002_b.up.sql" "CREATE TABLE b (n INTEGER);";
    let result <- with_memory (fn conn => dir_check conn (a && b && c));
    let _ <- exec_cmd "rm" ["-rf", Path.to_string p];
    return result
}
