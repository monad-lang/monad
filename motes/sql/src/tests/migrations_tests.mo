// Pure tests for the migration planner: ordering, duplicate detection, the
// applied-history prefix rule, checksums, and status. Both hosts.

use std::test {}
use std::list {List.length}
use std::sha256 {Sha256.hash}
use lib::migrations {*}

def mig (version : I64) (name : String) (up : String) : Migration :=
    Migrations.migration version name up Option.none

def applied (version : I64) (name : String) (up : String) : AppliedMigration :=
    let a : AppliedMigration :=
        { version := version, name := name, checksum := Sha256.hash up } in a

def versions_of (ms : List Migration) : List I64 :=
    List.map (fn (m : Migration) => m.version) ms

def i64_list_eq (a : List I64) (b : List I64) : Bool :=
    match a {
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false
        },
        List.cons x xs => match b {
            List.empty => false,
            List.cons y ys => x == y && i64_list_eq xs ys
        }
    }

def sort_is (ms : List Migration) (expected : List I64) : Bool :=
    match Migrations.sort_and_check ms {
        Result.ok sorted => i64_list_eq (versions_of sorted) expected,
        Result.err _ => false
    }

def error_is_duplicate (e : MigrationError) : Bool :=
    match e {
        MigrationError.duplicate_version _ => true,
        _ => false
    }

def error_is_zero (e : MigrationError) : Bool :=
    match e {
        MigrationError.zero_version => true,
        _ => false
    }

def error_is_checksum (e : MigrationError) : Bool :=
    match e {
        MigrationError.checksum_mismatch _ => true,
        _ => false
    }

def error_is_name (e : MigrationError) : Bool :=
    match e {
        MigrationError.name_mismatch _ _ _ => true,
        _ => false
    }

def error_is_missing (e : MigrationError) : Bool :=
    match e {
        MigrationError.missing_migration _ => true,
        _ => false
    }

def error_is_order (e : MigrationError) : Bool :=
    match e {
        MigrationError.out_of_order _ _ => true,
        _ => false
    }

def sort_fails_with (ms : List Migration) (pred : MigrationError -> Bool) : Bool :=
    match Migrations.sort_and_check ms {
        Result.ok _ => false,
        Result.err e => pred e
    }

def pending_fails_with (a : List AppliedMigration) (ms : List Migration)
        (pred : MigrationError -> Bool) : Bool :=
    match Migrations.pending a ms {
        Result.ok _ => false,
        Result.err e => pred e
    }

#[test]
def test_sort_is_numeric_not_lexicographic : Bool :=
    sort_is [mig 10 "ten" "u10", mig 2 "two" "u2", mig 1 "one" "u1"] [1, 2, 10]

#[test]
def test_duplicate_version_rejected : Bool :=
    sort_fails_with [mig 1 "a" "u", mig 1 "b" "u"] error_is_duplicate

#[test]
def test_zero_version_rejected : Bool :=
    sort_fails_with [mig 0 "a" "u"] error_is_zero

#[test]
def test_pending_all_when_none_applied : Bool :=
    match Migrations.pending List.empty [mig 1 "a" "u1", mig 2 "b" "u2"] {
        Result.ok ms => i64_list_eq (versions_of ms) [1, 2],
        Result.err _ => false
    }

#[test]
def test_pending_returns_tail_of_prefix : Bool :=
    match Migrations.pending [applied 1 "a" "u1"] [mig 1 "a" "u1", mig 2 "b" "u2"] {
        Result.ok ms => i64_list_eq (versions_of ms) [2],
        Result.err _ => false
    }

#[test]
def test_pending_none_when_all_applied : Bool :=
    match Migrations.pending [applied 1 "a" "u1"] [mig 1 "a" "u1"] {
        Result.ok ms => List.length ms == 0,
        Result.err _ => false
    }

#[test]
def test_pending_rejects_changed_up_script : Bool :=
    pending_fails_with [applied 1 "a" "changed"]
        [mig 1 "a" "u1"] error_is_checksum

#[test]
def test_pending_rejects_changed_name : Bool :=
    pending_fails_with [applied 1 "renamed" "u1"]
        [mig 1 "a" "u1"] error_is_name

#[test]
def test_pending_rejects_missing_migration : Bool :=
    pending_fails_with [applied 1 "a" "u1", applied 2 "b" "u2", applied 3 "c" "u3"]
        [mig 1 "a" "u1", mig 2 "b" "u2"] error_is_missing

#[test]
def test_pending_rejects_out_of_order_history : Bool :=
    pending_fails_with [applied 2 "b" "u2"]
        [mig 1 "a" "u1", mig 2 "b" "u2"] error_is_order

#[test]
def test_status_marks_applied_and_pending : Bool :=
    let states := Migrations.status [applied 1 "a" "u1"] [mig 1 "a" "u1", mig 2 "b" "u2"] in
    match states {
        List.cons first rest => match rest {
            List.cons second _ =>
                first.applied && first.checksum_ok && Bool.not second.applied,
            List.empty => false
        },
        List.empty => false
    }

#[test]
def test_status_reports_bad_checksum : Bool :=
    let bad : AppliedMigration := { version := 1, name := "a", checksum := "stale" } in
    let states := Migrations.status [bad] [mig 1 "a" "u1"] in
    match states {
        List.cons first _ => first.applied && Bool.not first.checksum_ok,
        List.empty => false
    }

#[test]
def test_latest_applied : Bool :=
    Migrations.latest_applied [applied 3 "c" "u3", applied 1 "a" "u1"] == 3

#[test]
def test_error_messages_are_nonempty : Bool :=
    String.is_empty (MigrationError.message MigrationError.zero_version) == false
