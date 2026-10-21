// monad-sql / migrations -- the backend-independent migration model and
// planner.
//
// Everything here is pure: ordering, duplicate/zero checks, the
// applied-history prefix rule, checksums, and status. A driver supplies
// the execution shell (transaction, script execution, tracking-table
// reads/writes), because that needs the `Backend` class and therefore
// stays concrete until the constrained-generic compiler bug is fixed.

use std::sha256 {Sha256.hash}

/// One migration. `up` is applied in ascending version order; `down`, when
/// present, reverses it.
pub struct Migration {
    version : I64,
    name : String,
    up : String,
    down : Option String
}

/// A row of the tracking table, as read by a driver.
pub struct AppliedMigration {
    version : I64,
    name : String,
    checksum : String
}

/// One entry of `status`.
pub struct MigrationState {
    version : I64,
    name : String,
    applied : Bool,
    checksum_ok : Bool
}

pub type MigrationError {
    zero_version,
    duplicate_version (version : I64),
    missing_migration (version : I64),
    out_of_order (version : I64) (expected : I64),
    name_mismatch (version : I64) (expected : String) (actual : String),
    checksum_mismatch (version : I64),
    missing_down (version : I64),
    bad_filename (name : String),
    io_error (message : String)
}

with MigrationError {
    pub def message (e : MigrationError) : String :=
        match e {
            MigrationError.zero_version => "migration versions must be positive",
            MigrationError.duplicate_version version =>
                String.concat "duplicate migration version: " (I64.to_string version),
            MigrationError.missing_migration version =>
                String.concat "applied migration is not in the supplied list: " (I64.to_string version),
            MigrationError.out_of_order version expected =>
                String.concat "migration order differs at version " (I64.to_string expected),
            MigrationError.name_mismatch version expected actual =>
                String.concat "migration name changed at version " (I64.to_string version),
            MigrationError.checksum_mismatch version =>
                String.concat "migration contents changed at version " (I64.to_string version),
            MigrationError.missing_down version =>
                String.concat "migration has no down script: " (I64.to_string version),
            MigrationError.bad_filename name =>
                String.concat "bad migration filename: " name,
            MigrationError.io_error message => message
        }
}

/// The struct literal lives in a def with a declared return type (a bare
/// literal in argument position can compile to garbage self-hosted).
with Migrations {
    pub def migration (version : I64) (name : String) (up : String)
            (down : Option String) : Migration :=
        let m : Migration := { version := version, name := name, up := up, down := down } in m

    def insert (m : Migration) (sorted : List Migration) : List Migration :=
        match sorted {
            List.empty => List.cons m List.empty,
            List.cons head rest =>
                if head.version > m.version
                then List.cons m sorted
                else List.cons head (Migrations.insert m rest)
        }

    def sort_list (ms : List Migration) : List Migration :=
        match ms {
            List.empty => List.empty,
            List.cons m rest => Migrations.insert m (Migrations.sort_list rest)
        }

    def check_sorted (previous : I64) (ms : List Migration) :
            Result MigrationError Unit :=
        match ms {
            List.empty => Result.ok Unit.unit,
            List.cons m rest =>
                if m.version < 1 then Result.err MigrationError.zero_version
                else if m.version == previous then Result.err (MigrationError.duplicate_version m.version)
                else Migrations.check_sorted m.version rest
        }

    /// Sort by numeric version and reject zero or duplicate versions.
    pub def sort_and_check (ms : List Migration) :
            Result MigrationError (List Migration) :=
        let sorted := Migrations.sort_list ms in
        match Migrations.check_sorted 0 sorted {
            Result.ok _ => Result.ok sorted,
            Result.err e => Result.err e
        }

    /// Compare one applied row against the next available migration and
    /// return the remaining available list, or the first mismatch.
    def check_applied_one (a : AppliedMigration) (available : List Migration) :
            Result MigrationError (List Migration) :=
        match available {
            List.empty => Result.err (MigrationError.missing_migration a.version),
            List.cons m rest =>
                if Bool.not (m.version == a.version)
                then Result.err (MigrationError.out_of_order m.version a.version)
                else if String.beq m.name a.name && String.beq (Sha256.hash m.up) a.checksum
                then Result.ok rest
                else if String.beq m.name a.name
                then Result.err (MigrationError.checksum_mismatch m.version)
                else Result.err (MigrationError.name_mismatch m.version a.name m.name)
        }

    def check_prefix_step (rest : List AppliedMigration)
            (r : Result MigrationError (List Migration)) :
            Result MigrationError (List Migration) :=
        match r {
            Result.ok available => Migrations.check_prefix rest available,
            Result.err e => Result.err e
        }

    def check_prefix (applied : List AppliedMigration) (available : List Migration) :
            Result MigrationError (List Migration) :=
        match applied {
            List.empty => Result.ok available,
            List.cons a rest =>
                Migrations.check_prefix_step rest (Migrations.check_applied_one a available)
        }

    /// The migrations still to apply, given the applied history.
    ///
    /// `available` must already be `sort_and_check`ed. The applied history
    /// must be an exact prefix of it: same versions, same names, and the
    /// same SHA-256 of each `up` script. A non-prefix history is an error,
    /// never silently skipped.
    pub def pending (applied : List AppliedMigration) (available : List Migration) :
            Result MigrationError (List Migration) :=
        Migrations.check_prefix applied available

    def find_applied (version : I64) (applied : List AppliedMigration) :
            Option AppliedMigration :=
        match applied {
            List.empty => Option.none,
            List.cons a rest =>
                if a.version == version then Option.some a
                else Migrations.find_applied version rest
        }

    def state_of (m : Migration) (applied : List AppliedMigration) : MigrationState :=
        match Migrations.find_applied m.version applied {
            Option.none =>
                let s : MigrationState := { version := m.version, name := m.name, applied := false, checksum_ok := true } in s,
            Option.some a =>
                let ok := String.beq (Sha256.hash m.up) a.checksum in
                let s : MigrationState := { version := m.version, name := m.name, applied := true, checksum_ok := ok } in s
        }

    /// Applied/pending state for every supplied migration. Checksums are
    /// checked for applied entries; unapplied entries report `true`.
    pub def status (applied : List AppliedMigration) (available : List Migration) :
            List MigrationState :=
        List.map (fn (m : Migration) => Migrations.state_of m applied) available

    /// The newest applied version, or 0 when nothing is applied.
    pub def latest_applied (applied : List AppliedMigration) : I64 :=
        match applied {
            List.empty => 0,
            List.cons a rest =>
                if a.version > Migrations.latest_applied rest
                then a.version
                else Migrations.latest_applied rest
        }
}
