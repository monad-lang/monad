// monad-sqlite / migrations -- the SQLite execution shell around the
// common, pure migration planner.
//
// The planner (ordering, prefix/checksum validation, status) lives in
// motes/sql; this module only performs the reads, the per-migration
// transactions, and the tracking-table writes. It is deliberately concrete
// over `SqliteConn`: generic `[Backend Bk]` code is miscompiled self-hosted.

use std::path {Path}
use std::sha256 {Sha256.hash}
use sql::value {Row, Row.get_i64, Row.get_text, SqlError, SqlResult.and_then, Value}
use sql::migrations {AppliedMigration, Migration, MigrationState, MigrationError,
    MigrationError.message, Migrations.pending, Migrations.sort_and_check,
    Migrations.status}
use sql::migrations_files {load_dir}
use lib::conn {SqliteConn}
use lib::backend {Sqlite.exec_io, Sqlite.query_io, Sqlite.exec_script_io}

def create_table_sql : String :=
    "CREATE TABLE IF NOT EXISTS _monad_migrations (version BIGINT PRIMARY KEY, name TEXT NOT NULL, checksum TEXT NOT NULL, applied_at TEXT NOT NULL)"

def Sqlite.migration_error_to_sql (e : MigrationError) : SqlError :=
    SqlError.migration (MigrationError.message e)

// ─── Tracking table ──────────────────────────────────────────────────────

def Sqlite.ensure_table (conn : SqliteConn) : IO (Result SqlError Unit) :=
    Sqlite.exec_script_io conn create_table_sql

def Sqlite.decode_applied_row (row : Row) : Result SqlError AppliedMigration :=
    SqlResult.and_then (Row.get_i64 row "version") (fn (version : I64) =>
        SqlResult.and_then (Row.get_text row "name") (fn (name : String) =>
            SqlResult.and_then (Row.get_text row "checksum") (fn (checksum : String) =>
                let a : AppliedMigration :=
                    { version := version, name := name, checksum := checksum } in
                Result.ok a)))

#[terminating]
def Sqlite.reverse_applied (acc : List AppliedMigration)
        (rest : List AppliedMigration) : List AppliedMigration :=
    match rest {
        List.empty => acc,
        List.cons a xs => Sqlite.reverse_applied (List.cons a acc) xs
    }

#[terminating]
def Sqlite.decode_applied_step (rest : List Row) (acc : List AppliedMigration)
        (r : Result SqlError AppliedMigration) :
        Result SqlError (List AppliedMigration) :=
    match r {
        Result.err e => Result.err e,
        Result.ok a => Sqlite.decode_applied_rows rest (List.cons a acc)
    }

def Sqlite.decode_applied_rows (rows : List Row) (acc : List AppliedMigration) :
        Result SqlError (List AppliedMigration) :=
    match rows {
        List.empty => Result.ok (Sqlite.reverse_applied List.empty acc),
        List.cons row rest =>
            Sqlite.decode_applied_step rest acc (Sqlite.decode_applied_row row)
    }

pub def Sqlite.read_applied (conn : SqliteConn) :
        IO (Result SqlError (List AppliedMigration)) := do {
    let rs <- Sqlite.query_io conn
        "SELECT version, name, checksum FROM _monad_migrations ORDER BY version ASC"
        List.empty;
    match rs {
        Result.err e => return (Result.err e),
        Result.ok result_set =>
            return (Sqlite.decode_applied_rows result_set.rows List.empty)
    }
}

// ─── Applying migrations ─────────────────────────────────────────────────

#[terminating]
def Sqlite.reverse_i64 (acc : List I64) (rest : List I64) : List I64 :=
    match rest {
        List.empty => acc,
        List.cons v vs => Sqlite.reverse_i64 (List.cons v acc) vs
    }

def Sqlite.abort_tx {A : Type} (conn : SqliteConn) (e : SqlError) :
        IO (Result SqlError A) := do {
    let _ <- Sqlite.exec_script_io conn "ROLLBACK";
    return (Result.err e)
}

def Sqlite.commit_one (conn : SqliteConn) (version : I64) :
        IO (Result SqlError I64) := do {
    let c <- Sqlite.exec_script_io conn "COMMIT";
    match c {
        Result.ok _ => return (Result.ok version),
        Result.err e => Sqlite.abort_tx conn e
    }
}

def Sqlite.record_migration (conn : SqliteConn) (m : Migration) :
        IO (Result SqlError I64) := do {
    let ins <- Sqlite.exec_io conn
        "INSERT INTO _monad_migrations (version, name, checksum, applied_at) VALUES (?, ?, ?, datetime('now'))"
        [Value.integer m.version, Value.text m.name, Value.text (Sha256.hash m.up)];
    match ins {
        Result.err e => Sqlite.abort_tx conn e,
        Result.ok _ => Sqlite.commit_one conn m.version
    }
}

def Sqlite.apply_in_tx (conn : SqliteConn) (m : Migration) :
        IO (Result SqlError I64) := do {
    let up <- Sqlite.exec_script_io conn m.up;
    match up {
        Result.err e => Sqlite.abort_tx conn e,
        Result.ok _ => Sqlite.record_migration conn m
    }
}

def Sqlite.apply_one (conn : SqliteConn) (m : Migration) :
        IO (Result SqlError I64) := do {
    let b <- Sqlite.exec_script_io conn "BEGIN IMMEDIATE";
    match b {
        Result.err e => return (Result.err e),
        Result.ok _ => Sqlite.apply_in_tx conn m
    }
}

#[terminating]
def Sqlite.apply_pending (conn : SqliteConn) (ms : List Migration) (acc : List I64) :
        IO (Result SqlError (List I64)) :=
    match ms {
        List.empty => IO.pure (Result.ok (Sqlite.reverse_i64 List.empty acc)),
        List.cons m rest => do {
            let r <- Sqlite.apply_one conn m;
            match r {
                Result.err e => return (Result.err e),
                Result.ok version =>
                    Sqlite.apply_pending conn rest (List.cons version acc)
            }
        }
    }

def Sqlite.migrate_plan (conn : SqliteConn) (history : List AppliedMigration)
        (available : List Migration) : IO (Result SqlError (List I64)) :=
    match Migrations.pending history available {
        Result.err e => IO.pure (Result.err (Sqlite.migration_error_to_sql e)),
        Result.ok ms => Sqlite.apply_pending conn ms List.empty
    }

def Sqlite.migrate_with_history (conn : SqliteConn)
        (history : Result SqlError (List AppliedMigration))
        (available : List Migration) : IO (Result SqlError (List I64)) :=
    match history {
        Result.err e => IO.pure (Result.err e),
        Result.ok h => Sqlite.migrate_plan conn h available
    }

def Sqlite.migrate_checked (conn : SqliteConn) (available : List Migration) :
        IO (Result SqlError (List I64)) := do {
    let history <- Sqlite.read_applied conn;
    Sqlite.migrate_with_history conn history available
}

def Sqlite.migrate_source (conn : SqliteConn) (ms : List Migration) :
        IO (Result SqlError (List I64)) :=
    match Migrations.sort_and_check ms {
        Result.err e => IO.pure (Result.err (Sqlite.migration_error_to_sql e)),
        Result.ok available => Sqlite.migrate_checked conn available
    }

/// Apply every pending migration in version order. Each runs in its own
/// `BEGIN IMMEDIATE` transaction and is recorded only if it succeeds.
/// Returns the versions applied by this call.
pub def Sqlite.migrate (conn : SqliteConn) (ms : List Migration) :
        IO (Result SqlError (List I64)) := do {
    let t <- Sqlite.ensure_table conn;
    match t {
        Result.err e => return (Result.err e),
        Result.ok _ => Sqlite.migrate_source conn ms
    }
}

/// Load the migrations from a directory, then `migrate`.
pub def Sqlite.migrate_dir (conn : SqliteConn) (dir : Path) :
        IO (Result SqlError (List I64)) := do {
    let loaded <- load_dir dir;
    match loaded {
        Result.err e => return (Result.err (Sqlite.migration_error_to_sql e)),
        Result.ok ms => Sqlite.migrate conn ms
    }
}

// ─── Status ──────────────────────────────────────────────────────────────

def Sqlite.status_with_history (available : List Migration)
        (history : Result SqlError (List AppliedMigration)) :
        IO (Result SqlError (List MigrationState)) :=
    match history {
        Result.err e => IO.pure (Result.err e),
        Result.ok h => IO.pure (Result.ok (Migrations.status h available))
    }

def Sqlite.status_source (conn : SqliteConn) (ms : List Migration) :
        IO (Result SqlError (List MigrationState)) :=
    match Migrations.sort_and_check ms {
        Result.err e => IO.pure (Result.err (Sqlite.migration_error_to_sql e)),
        Result.ok available => do {
            let history <- Sqlite.read_applied conn;
            Sqlite.status_with_history available history
        }
    }

pub def Sqlite.status (conn : SqliteConn) (ms : List Migration) :
        IO (Result SqlError (List MigrationState)) := do {
    let t <- Sqlite.ensure_table conn;
    match t {
        Result.err e => return (Result.err e),
        Result.ok _ => Sqlite.status_source conn ms
    }
}

// ─── Rollback ────────────────────────────────────────────────────────────

#[terminating]
def Sqlite.find_migration (version : I64) (ms : List Migration) :
        Option Migration :=
    match ms {
        List.empty => Option.none,
        List.cons m rest =>
            if m.version == version then Option.some m
            else Sqlite.find_migration version rest
    }

/// Applied rows strictly above `target`, in descending order (history is
/// ascending, and each accepted row is prepended).
#[terminating]
def Sqlite.filter_above (target : I64) (history : List AppliedMigration)
        (acc : List AppliedMigration) : List AppliedMigration :=
    match history {
        List.empty => acc,
        List.cons a rest =>
            if a.version > target
            then Sqlite.filter_above target rest (List.cons a acc)
            else Sqlite.filter_above target rest acc
    }

def Sqlite.has_down (m : Migration) : Bool :=
    match m.down {
        Option.some _ => true,
        Option.none => false
    }

def Sqlite.preflight_one (a : AppliedMigration) (available : List Migration) :
        Result MigrationError Unit :=
    match Sqlite.find_migration a.version available {
        Option.none => Result.err (MigrationError.missing_migration a.version),
        Option.some m =>
            if Sqlite.has_down m
            then Result.ok Unit.unit
            else Result.err (MigrationError.missing_down a.version)
    }

#[terminating]
def Sqlite.preflight_step (rest : List AppliedMigration) (available : List Migration)
        (r : Result MigrationError Unit) : Result MigrationError Unit :=
    match r {
        Result.err e => Result.err e,
        Result.ok _ => Sqlite.preflight rest available
    }

/// Every candidate must have a `down` before anything is executed, so a
/// rollback never stops halfway for a missing script.
#[terminating]
def Sqlite.preflight (candidates : List AppliedMigration) (available : List Migration) :
        Result MigrationError Unit :=
    match candidates {
        List.empty => Result.ok Unit.unit,
        List.cons a rest =>
            Sqlite.preflight_step rest available (Sqlite.preflight_one a available)
    }

def Sqlite.delete_migration (conn : SqliteConn) (version : I64) :
        IO (Result SqlError Unit) := do {
    let r <- Sqlite.exec_io conn
        "DELETE FROM _monad_migrations WHERE version = ?" [Value.integer version];
    match r {
        Result.ok _ => return (Result.ok Unit.unit),
        Result.err e => return (Result.err e)
    }
}

def Sqlite.rollback_commit (conn : SqliteConn) (version : I64) :
        IO (Result SqlError I64) := do {
    let c <- Sqlite.exec_script_io conn "COMMIT";
    match c {
        Result.ok _ => return (Result.ok version),
        Result.err e => Sqlite.abort_tx conn e
    }
}

def Sqlite.rollback_delete (conn : SqliteConn) (version : I64) :
        IO (Result SqlError I64) := do {
    let del <- Sqlite.delete_migration conn version;
    match del {
        Result.err e => Sqlite.abort_tx conn e,
        Result.ok _ => Sqlite.rollback_commit conn version
    }
}

def Sqlite.rollback_script (conn : SqliteConn) (down : String) (version : I64) :
        IO (Result SqlError I64) := do {
    let d <- Sqlite.exec_script_io conn down;
    match d {
        Result.err e => Sqlite.abort_tx conn e,
        Result.ok _ => Sqlite.rollback_delete conn version
    }
}

def Sqlite.rollback_candidate (conn : SqliteConn) (candidate : AppliedMigration)
        (available : List Migration) : IO (Result SqlError I64) :=
    match Sqlite.find_migration candidate.version available {
        Option.none => IO.pure (Result.err (Sqlite.migration_error_to_sql
            (MigrationError.missing_migration candidate.version))),
        Option.some m =>
            match m.down {
                Option.none => IO.pure (Result.err (Sqlite.migration_error_to_sql
                    (MigrationError.missing_down candidate.version))),
                Option.some down => do {
                    let b <- Sqlite.exec_script_io conn "BEGIN IMMEDIATE";
                    match b {
                        Result.err e => return (Result.err e),
                        Result.ok _ => Sqlite.rollback_script conn down candidate.version
                    }
                }
            }
    }

#[terminating]
def Sqlite.rollback_candidates (conn : SqliteConn) (candidates : List AppliedMigration)
        (available : List Migration) (acc : List I64) :
        IO (Result SqlError (List I64)) :=
    match candidates {
        List.empty => IO.pure (Result.ok (Sqlite.reverse_i64 List.empty acc)),
        List.cons c rest => do {
            let r <- Sqlite.rollback_candidate conn c available;
            match r {
                Result.err e => return (Result.err e),
                Result.ok version =>
                    Sqlite.rollback_candidates conn rest available (List.cons version acc)
            }
        }
    }

def Sqlite.rollback_plan (conn : SqliteConn) (available : List Migration)
        (target : I64) (history : List AppliedMigration) :
        IO (Result SqlError (List I64)) :=
    match Migrations.pending history available {
        Result.err e => IO.pure (Result.err (Sqlite.migration_error_to_sql e)),
        Result.ok _ =>
            Sqlite.rollback_preflight conn available target history
    }

def Sqlite.rollback_preflight (conn : SqliteConn) (available : List Migration)
        (target : I64) (history : List AppliedMigration) :
        IO (Result SqlError (List I64)) :=
    let candidates := Sqlite.filter_above target history List.empty in
    match Sqlite.preflight candidates available {
        Result.err e => IO.pure (Result.err (Sqlite.migration_error_to_sql e)),
        Result.ok _ => Sqlite.rollback_candidates conn candidates available List.empty
    }

def Sqlite.rollback_with_history (conn : SqliteConn) (available : List Migration)
        (target : I64) (history : Result SqlError (List AppliedMigration)) :
        IO (Result SqlError (List I64)) :=
    match history {
        Result.err e => IO.pure (Result.err e),
        Result.ok h => Sqlite.rollback_plan conn available target h
    }

def Sqlite.rollback_source (conn : SqliteConn) (ms : List Migration) (target : I64) :
        IO (Result SqlError (List I64)) :=
    match Migrations.sort_and_check ms {
        Result.err e => IO.pure (Result.err (Sqlite.migration_error_to_sql e)),
        Result.ok available => do {
            let history <- Sqlite.read_applied conn;
            Sqlite.rollback_with_history conn available target history
        }
    }

/// Roll back every applied migration newer than `target` (0 = all), newest
/// first, each in its own transaction. Returns the versions rolled back.
pub def Sqlite.rollback_to (conn : SqliteConn) (ms : List Migration) (target : I64) :
        IO (Result SqlError (List I64)) :=
    Sqlite.rollback_source conn ms target

#[terminating]
def Sqlite.previous_version (previous : I64) (rest : List AppliedMigration) : I64 :=
    match rest {
        List.empty => previous,
        List.cons a xs => Sqlite.previous_step previous a.version xs
    }

#[terminating]
def Sqlite.previous_step (previous : I64) (version : I64)
        (rest : List AppliedMigration) : I64 :=
    match rest {
        List.empty => previous,
        List.cons _ _ => Sqlite.previous_version version rest
    }

/// The version to keep when rolling back only the newest migration: the
/// second-newest applied version, or 0 when fewer than two are applied.
def Sqlite.second_newest (history : List AppliedMigration) : I64 :=
    match history {
        List.empty => 0,
        List.cons first rest =>
            match rest {
                List.empty => 0,
                List.cons _ _ => Sqlite.previous_version first.version rest
            }
    }

/// Roll back the newest applied migration only.
pub def Sqlite.rollback_last (conn : SqliteConn) (ms : List Migration) :
        IO (Result SqlError (List I64)) := do {
    let history <- Sqlite.read_applied conn;
    match history {
        Result.err e => return (Result.err e),
        Result.ok h => Sqlite.rollback_to conn ms (Sqlite.second_newest h)
    }
}
