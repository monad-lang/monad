// monad-sql / migrations_files -- build a `List Migration` from a
// directory of SQL files.
//
// Naming contract:
//
//     NNNN_name.up.sql      required
//     NNNN_name.down.sql    optional
//
// `NNNN` is a positive decimal version (zero padding is conventional, not
// required); `name` may contain further underscores. Non-`.sql` files are
// ignored. Any other `*.sql` name, an orphan `down`, or a duplicate
// version is a `MigrationError.bad_filename`; versions are also checked by
// `Migrations.sort_and_check` before use.
//
// The loader reads every script during discovery, so the result is a plain
// `List Migration` and the pure planner needs no further IO.

use std::path {Path}
use std::io {IO.is_dir, IO.list_dir, IO.read_file}
use lib::migrations {Migration, MigrationError, Migrations.migration}

type ParsedKind {
    up_kind,
    down_kind
}

struct ParsedMeta {
    version : I64,
    name : String,
    kind : ParsedKind
}

struct ParsedFile {
    version : I64,
    name : String,
    kind : ParsedKind,
    text : String
}

// ─── Filename parsing ───────────────────────────────────────────────────

def has_suffix (suffix : String) (s : String) : Bool :=
    let suffix_len := String.length suffix in
    let len := String.length s in
    if len < suffix_len
    then false
    else String.beq (String.slice s (len - suffix_len) suffix_len) suffix

def strip_suffix (suffix : String) (s : String) : String :=
    String.slice s 0 (String.length s - String.length suffix)

#[terminating]
def underscore_index (s : String) (i : I64) : Option I64 :=
    if Bool.not (i < String.length s)
    then Option.none
    else if String.beq (String.slice s i 1) "_"
    then Option.some i
    else underscore_index s (i + 1)

/// `U8.to_string` renders the BYTE VALUE in decimal ("48" for the byte
/// `'0'`), so subtract `'0'` first: the result is 0..9 and renders as the
/// single digit. The numeric narrowing helpers are module-private, so the
/// string table is the portable route to an `I64`.
def digit_string_value (s : String) : Option I64 :=
    if String.beq s "0" then Option.some 0
    else if String.beq s "1" then Option.some 1
    else if String.beq s "2" then Option.some 2
    else if String.beq s "3" then Option.some 3
    else if String.beq s "4" then Option.some 4
    else if String.beq s "5" then Option.some 5
    else if String.beq s "6" then Option.some 6
    else if String.beq s "7" then Option.some 7
    else if String.beq s "8" then Option.some 8
    else if String.beq s "9" then Option.some 9
    else Option.none

def digit_value (b : U8) : Option I64 :=
    if U8.gt b 47u8 && U8.gt 58u8 b
    then digit_string_value (U8.to_string (U8.sub b 48u8))
    else Option.none

#[terminating]
def parse_version_step (rest : List U8) (acc : I64) (d : Option I64) :
        Option I64 :=
    match d {
        Option.some n => parse_version_list rest (acc * 10 + n),
        Option.none => Option.none
    }

def parse_version_list (bytes : List U8) (acc : I64) : Option I64 :=
    match bytes {
        List.empty => Option.some acc,
        List.cons b rest => parse_version_step rest acc (digit_value b)
    }

def parse_version (s : String) : Option I64 :=
    if String.is_empty s
    then Option.none
    else parse_version_list (String.to_list s) 0

def parse_meta_name (file_name : String) (stem : String) (kind : ParsedKind)
        (idx : I64) (version : I64) : Result MigrationError ParsedMeta :=
    let name := String.slice stem (idx + 1) (String.length stem - idx - 1) in
    if version < 1 then Result.err (MigrationError.bad_filename file_name)
    else if String.is_empty name then Result.err (MigrationError.bad_filename file_name)
    else
        let meta : ParsedMeta := { version := version, name := name, kind := kind } in
        Result.ok meta

def parse_meta_version (file_name : String) (stem : String) (kind : ParsedKind)
        (idx : I64) : Result MigrationError ParsedMeta :=
    match parse_version (String.slice stem 0 idx) {
        Option.none => Result.err (MigrationError.bad_filename file_name),
        Option.some version => parse_meta_name file_name stem kind idx version
    }

def parse_meta_split (file_name : String) (stem : String) (kind : ParsedKind)
        (idx : Option I64) : Result MigrationError ParsedMeta :=
    match idx {
        Option.none => Result.err (MigrationError.bad_filename file_name),
        Option.some i => parse_meta_version file_name stem kind i
    }

/// `none` means "not a migration file"; `some (err ...)` means a `.sql`
/// file whose name does not follow the contract.
def parse_meta (file_name : String) : Option (Result MigrationError ParsedMeta) :=
    if has_suffix ".up.sql" file_name
    then Option.some (parse_meta_split file_name (strip_suffix ".up.sql" file_name)
        ParsedKind.up_kind (underscore_index (strip_suffix ".up.sql" file_name) 0))
    else if has_suffix ".down.sql" file_name
    then Option.some (parse_meta_split file_name (strip_suffix ".down.sql" file_name)
        ParsedKind.down_kind (underscore_index (strip_suffix ".down.sql" file_name) 0))
    else if has_suffix ".sql" file_name
    then Option.some (Result.err (MigrationError.bad_filename file_name))
    else Option.none

// ─── IO: read and collect ────────────────────────────────────────────────

def read_meta (path : Path) (meta : ParsedMeta) :
        IO (Result MigrationError (Option ParsedFile)) := do {
    let contents <- IO.read_file path;
    match contents {
        Result.ok text =>
            let f : ParsedFile :=
                { version := meta.version, name := meta.name, kind := meta.kind, text := text } in
            return (Result.ok (Option.some f)),
        Result.err e =>
            return (Result.err (MigrationError.io_error e.message))
    }
}

def read_meta_result (path : Path) (r : Result MigrationError ParsedMeta) :
        IO (Result MigrationError (Option ParsedFile)) :=
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok meta => read_meta path meta
    }

def load_one (path : Path) : IO (Result MigrationError (Option ParsedFile)) := do {
    let meta := parse_meta (Path.file_name path);
    match meta {
        Option.none => return (Result.ok Option.none),
        Option.some r => read_meta_result path r
    }
}

#[terminating]
def add_parsed (rest : List Path) (acc : List ParsedFile) (maybe : Option ParsedFile) :
        IO (Result MigrationError (List ParsedFile)) :=
    match maybe {
        Option.none => load_all rest acc,
        Option.some f => load_all rest (List.cons f acc)
    }

#[terminating]
def load_all_step (rest : List Path) (acc : List ParsedFile)
        (r : Result MigrationError (Option ParsedFile)) :
        IO (Result MigrationError (List ParsedFile)) :=
    match r {
        Result.err e => IO.pure (Result.err e),
        Result.ok maybe => add_parsed rest acc maybe
    }

def load_all (paths : List Path) (acc : List ParsedFile) :
        IO (Result MigrationError (List ParsedFile)) :=
    match paths {
        List.empty => IO.pure (Result.ok acc),
        List.cons p rest => do {
            let r <- load_one p;
            load_all_step rest acc r
        }
    }

// ─── Ordering and assembly ───────────────────────────────────────────────

def kind_rank (k : ParsedKind) : I64 :=
    match k {
        ParsedKind.up_kind => 0,
        ParsedKind.down_kind => 1
    }

def kind_is_down (k : ParsedKind) : Bool :=
    match k {
        ParsedKind.up_kind => false,
        ParsedKind.down_kind => true
    }

def parsed_less (a : ParsedFile) (b : ParsedFile) : Bool :=
    if a.version < b.version then true
    else if a.version > b.version then false
    else kind_rank a.kind < kind_rank b.kind

def insert_parsed (f : ParsedFile) (sorted : List ParsedFile) : List ParsedFile :=
    match sorted {
        List.empty => List.cons f List.empty,
        List.cons head rest =>
            if parsed_less f head
            then List.cons f sorted
            else List.cons head (insert_parsed f rest)
    }

def sort_parsed (files : List ParsedFile) : List ParsedFile :=
    match files {
        List.empty => List.empty,
        List.cons f rest => insert_parsed f (sort_parsed rest)
    }

def take_down (f : ParsedFile) (rest : List ParsedFile) :
        Pair (Option ParsedFile) (List ParsedFile) :=
    match rest {
        List.empty => Pair.pair Option.none rest,
        List.cons d rest2 =>
            if d.version == f.version && kind_is_down d.kind
            then Pair.pair (Option.some d) rest2
            else Pair.pair Option.none rest
    }

def make_migration (f : ParsedFile) (down : Option ParsedFile) : Migration :=
    let down_sql :=
        match down {
            Option.none => Option.none,
            Option.some d => Option.some d.text
        } in
    Migrations.migration f.version f.name f.text down_sql

def same_version_head (version : I64) (files : List ParsedFile) : Bool :=
    match files {
        List.empty => false,
        List.cons f _ => f.version == version
    }

#[terminating]
def assemble_rest (f : ParsedFile) (down : Option ParsedFile) (rest : List ParsedFile) :
        Result MigrationError (List Migration) :=
    if same_version_head f.version rest
    then Result.err (MigrationError.duplicate_version f.version)
    else
        match assemble rest {
            Result.ok migrations => Result.ok (List.cons (make_migration f down) migrations),
            Result.err e => Result.err e
        }

#[terminating]
def assemble_up (f : ParsedFile) (rest : List ParsedFile) :
        Result MigrationError (List Migration) :=
    match take_down f rest {
        Pair.pair down rest2 => assemble_rest f down rest2
    }

#[terminating]
def assemble (files : List ParsedFile) : Result MigrationError (List Migration) :=
    match files {
        List.empty => Result.ok List.empty,
        List.cons f rest =>
            if kind_is_down f.kind
            then Result.err (MigrationError.bad_filename f.name)
            else assemble_up f rest
    }

// ─── Public entry point ──────────────────────────────────────────────────

def load_done (loaded : Result MigrationError (List ParsedFile)) :
        IO (Result MigrationError (List Migration)) :=
    match loaded {
        Result.err e => IO.pure (Result.err e),
        Result.ok files => IO.pure (assemble (sort_parsed files))
    }

def load_present (dir : Path) : IO (Result MigrationError (List Migration)) := do {
    let paths <- IO.list_dir dir;
    let loaded <- load_all paths List.empty;
    load_done loaded
}

/// Load every migration in `dir`. A missing directory is an error, never
/// an empty list.
pub def load_dir (dir : Path) : IO (Result MigrationError (List Migration)) := do {
    let present <- IO.is_dir dir;
    if present
    then load_present dir
    else IO.pure (Result.err (MigrationError.io_error
        (String.concat "not a directory: " (Path.to_string dir))))
}
