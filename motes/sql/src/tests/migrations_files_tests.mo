// IO tests for the `.up.sql`/`.down.sql` directory loader. These use only
// Path/IO, so both hosts run them.
//
// Every test owns a distinct directory under /tmp: the suite may run test
// files (and potentially test defs) concurrently, and a shared fixture
// would make a failure depend on scheduling.

use std::test {}
use std::list {List.length}
use std::process {exec_cmd}
use std::path {Path}
use std::io {IO.write_file}
use lib::migrations {Migration, MigrationError, MigrationError.message}
use lib::migrations_files {load_dir}

def test_dir (name : String) : Path :=
    Path.path (String.concat "/tmp/monad_sql_migrations_test_" name)

def setup_at (p : Path) : IO Unit := do {
    let path := Path.to_string p;
    let _ <- exec_cmd "rm" ["-rf", path];
    let _ <- exec_cmd "mkdir" ["-p", path];
    return Unit.unit
}

def write_at (p : Path) (name : String) (content : String) : IO Bool := do {
    let r <- IO.write_file (Path.join p (Path.path name)) content;
    match r {
        Result.ok _ => return true,
        Result.err _ => return false
    }
}

def down_is (m : Migration) (expected : String) : Bool :=
    match m.down {
        Option.some d => String.beq d expected,
        Option.none => false
    }

def no_down (m : Migration) : Bool :=
    match m.down {
        Option.some _ => false,
        Option.none => true
    }

def happy_shape (ms : List Migration) : Bool :=
    match ms {
        List.cons first rest => match rest {
            List.cons second tail =>
                first.version == 1
                && String.beq first.name "create_users"
                && down_is first "DROP TABLE users;"
                && second.version == 2
                && String.beq second.name "add_email"
                && no_down second
                && List.length tail == 0,
            List.empty => false
        },
        List.empty => false
    }

def is_io_error (e : MigrationError) : Bool :=
    match e {
        MigrationError.io_error _ => true,
        _ => false
    }

def is_bad_filename (e : MigrationError) : Bool :=
    match e {
        MigrationError.bad_filename _ => true,
        _ => false
    }

def is_duplicate (e : MigrationError) : Bool :=
    match e {
        MigrationError.duplicate_version _ => true,
        _ => false
    }

def dir_error_is (p : Path) (pred : MigrationError -> Bool) : IO Bool := do {
    let r <- load_dir p;
    match r {
        Result.ok _ => return false,
        Result.err e => return (pred e)
    }
}

def dir_error_message_is (p : Path) (expected : String) : IO Bool := do {
    let r <- load_dir p;
    match r {
        Result.ok _ => return false,
        Result.err e => return (String.beq (MigrationError.message e) expected)
    }
}

#[test]
def test_load_dir_pairs_up_and_down : IO Bool := do {
    let p := test_dir "pairs";
    let _ <- setup_at p;
    let a <- write_at p "0001_create_users.up.sql" "CREATE TABLE users (id INTEGER);";
    let b <- write_at p "0001_create_users.down.sql" "DROP TABLE users;";
    let c <- write_at p "0002_add_email.up.sql" "ALTER TABLE users ADD COLUMN email TEXT;";
    let d <- write_at p "README.txt" "ignored";
    let loaded <- load_dir p;
    match loaded {
        Result.ok ms => return (a && b && c && d && happy_shape ms),
        Result.err _ => return false
    }
}

#[test]
def test_load_missing_dir_is_error : IO Bool :=
    dir_error_is (Path.path "/tmp/monad_sql_no_such_migrations_dir") is_io_error

#[test]
def test_load_duplicate_version_is_error : IO Bool := do {
    let p := test_dir "duplicate";
    let _ <- setup_at p;
    let a <- write_at p "0001_a.up.sql" "SELECT 1;";
    let b <- write_at p "0001_b.up.sql" "SELECT 2;";
    let bad <- dir_error_is p is_duplicate;
    return (a && b && bad)
}

#[test]
def test_load_orphan_down_is_error : IO Bool := do {
    let p := test_dir "orphan";
    let _ <- setup_at p;
    let a <- write_at p "0001_a.down.sql" "SELECT 1;";
    let bad <- dir_error_message_is p "bad migration filename: 0001_a.down.sql";
    return (a && bad)
}

#[test]
def test_load_down_name_must_match_up : IO Bool := do {
    let p := test_dir "downname";
    let _ <- setup_at p;
    let a <- write_at p "0001_create_users.up.sql" "CREATE TABLE users (id INTEGER);";
    let b <- write_at p "0001_create_user.down.sql" "DROP TABLE users;";
    let bad <- dir_error_message_is p "bad migration filename: 0001_create_user.down.sql";
    return (a && b && bad)
}

#[test]
def test_load_overlong_version_is_error : IO Bool := do {
    let p := test_dir "overflow";
    let _ <- setup_at p;
    let a <- write_at p "18446744073709551617_a.up.sql" "SELECT 1;";
    let bad <- dir_error_is p is_bad_filename;
    return (a && bad)
}

#[test]
def test_load_bad_sql_filename_is_error : IO Bool := do {
    let p := test_dir "badname";
    let _ <- setup_at p;
    let a <- write_at p "notes.sql" "SELECT 1;";
    let bad <- dir_error_is p is_bad_filename;
    return (a && bad)
}
