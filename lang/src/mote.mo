/// Mote manifests, read by the self-hosted compiler.
///
/// A mote is Monad's unit of distribution (`plans/packaging/
/// package-system.md`): a directory with a `mote.toml` and a `src/` tree.
/// This module answers the two questions module resolution asks -- which
/// mote does this file belong to, and which motes did that mote declare --
/// so that `use` can be checked against the manifest rather than against
/// whatever happens to exist on disk.
///
/// Built on `lang.toml`'s parser, following `lang/src/toml.mo`'s own
/// pattern: own types, own glue over `Toml.parse`, no shared
/// serialize/deserialize class machinery.

use lib::toml {}
use std::io {file_exists, read_file}
use std::map {}
use io {IO}

/// What resolution needs from a `mote.toml`: who this mote is, where it
/// lives, and what it declared. `[dependencies]` and `[dev-dependencies]`
/// are merged here -- the distinction is about which TARGETS may use an
/// edge, and this corpus has no lib/test target split to enforce it
/// against yet (`init/src/tests.mo` is an ordinary module). Merging keeps
/// `init` pure in its manifest, which is the part that documents intent.
struct MoteManifest {
    name : String,
    dir : String,
    deps : List String,
}

/// The mote's source root -- `<dir>/src`, always.
def MoteManifest.src_root (m : MoteManifest) : String :=
    String.concat m.dir "/src"

/// Does this mote declare `name` as a dependency (or is `name` the mote
/// itself)? A mote may always refer to itself.
def MoteManifest.declares (m : MoteManifest) (name : String) : Bool :=
    if String.beq m.name name
    then true
    else list_contains_string name m.deps

def list_contains_string (needle : String) (xs : List String) : Bool :=
    match xs {
        List.empty => false,
        List.cons x rest =>
            if String.beq x needle then true else list_contains_string needle rest
    }

/// Walk up from `dir` looking for a `mote.toml`, parse the first one found.
/// `Option.none` for a file outside any mote (script mode -- `examples/`,
/// a one-off file) or under a virtual workspace root, which declares
/// `[workspace]` and no `[mote]`.
///
/// Bounded by `depth` rather than by reaching the filesystem root: the
/// walk is `parent_dir` on a string, and a relative path bottoms out at
/// `""` while an absolute one bottoms out at `"/"` -- a bound is the one
/// termination argument that holds for both.
#[partial]
def Mote.discover (dir : String) : IO (Option MoteManifest) :=
    Mote.discover_go dir 32

#[partial]
def Mote.discover_go (dir : String) (depth : I64) : IO (Option MoteManifest) := do {
    if I64.lt depth 1
    then return Option.none
    else do {
        let candidate := if String.beq dir "" then "mote.toml" else String.concat dir "/mote.toml";
        let exists <- IO.file_exists (Path.path candidate);
        if exists
        then do {
            let text <- IO.read_file (Path.path candidate);
            match Mote.parse_manifest dir text {
                Option.some m => return (Option.some m),
                // A `mote.toml` with no `[mote]` is a virtual workspace
                // root: stop there rather than walking past it, since
                // nothing above a workspace root is part of this mote.
                Option.none => return Option.none
            }
        }
        else if String.beq dir "" || String.beq dir "/"
        then return Option.none
        else Mote.discover_go (raw_parent_dir dir) (depth - 1)
    }
}

/// Parse a manifest's text into the resolution-relevant fields.
def Mote.parse_manifest (dir : String) (text : String) : Option MoteManifest :=
    match Toml.parse text {
        err _ => Option.none,
        ok root => Mote.manifest_of_table dir root
    }

def Mote.manifest_of_table (dir : String) (root : BTreeMap String Toml.Value) : Option MoteManifest :=
    match Mote.table_string (Toml.table_get "mote" root) "name" {
        Option.none => Option.none,
        Option.some name =>
            let deps := List.append
                (Mote.table_keys (Toml.table_get "dependencies" root))
                (Mote.table_keys (Toml.table_get "dev-dependencies" root)) in
            let m : MoteManifest := { name := name, dir := dir, deps := deps } in
            Option.some m
    }

/// A string field of a sub-table, if both the table and the field are there.
def Mote.table_string (found : Option Toml.Value) (key : String) : Option String :=
    match found {
        Option.none => Option.none,
        Option.some v => match v {
            Toml.Value.table sub => Mote.string_value (Toml.table_get key sub),
            _ => Option.none
        }
    }

def Mote.string_value (found : Option Toml.Value) : Option String :=
    match found {
        Option.none => Option.none,
        Option.some v => match v {
            Toml.Value.string s => Option.some s,
            _ => Option.none
        }
    }

/// The keys of a dependency table. Each dependency is its own sub-table
/// (`[dependencies.std]`), so the KEY is the mote name and the value is
/// where it came from -- which resolution does not need, only the name.
def Mote.table_keys (found : Option Toml.Value) : List String :=
    match found {
        Option.none => List.empty,
        Option.some v => match v {
            Toml.Value.table sub => List.map Pair.first (BTreeMap.to_list sub),
            _ => List.empty
        }
    }

def Pair.first (p : Pair String Toml.Value) : String :=
    match p { Pair.pair k _ => k }

// ─── Tests ───

def mote_manifest_fixture : String :=
  "# a comment\n[mote]\nname = \"lang\"\nversion = \"0.1.2\"\n\n[lib]\npath = \"src/lib.mo\"\n\n[dependencies.init]\npath = \"../init\"\n\n[dependencies.std]\npath = \"../std\"\n"

#[test]
def test_parse_manifest_reads_name_and_deps : Bool :=
    match Mote.parse_manifest "lang" mote_manifest_fixture {
        Option.none => false,
        Option.some m =>
            if String.beq m.name "lang"
            then if String.beq (MoteManifest.src_root m) "lang/src"
                then if MoteManifest.declares m "init"
                    then MoteManifest.declares m "std"
                    else false
                else false
            else false
    }

#[test]
def test_manifest_declares_itself : Bool :=
    match Mote.parse_manifest "lang" mote_manifest_fixture {
        Option.none => false,
        Option.some m => MoteManifest.declares m "lang"
    }

#[test]
def test_manifest_rejects_undeclared_mote : Bool :=
    match Mote.parse_manifest "lang" mote_manifest_fixture {
        Option.none => false,
        Option.some m => not (MoteManifest.declares m "llvm")
    }

/// A dev-dependency counts as declared -- this is how `init` stays free of
/// production dependencies while its own test files use `std.test`.
def init_manifest_fixture : String :=
  "[mote]\nname = \"init\"\nversion = \"0.1.2\"\n\n[dev-dependencies.std]\npath = \"../std\"\n"

#[test]
def test_dev_dependencies_count_as_declared : Bool :=
    match Mote.parse_manifest "init" init_manifest_fixture {
        Option.none => false,
        Option.some m => MoteManifest.declares m "std"
    }

/// A virtual workspace root has `[workspace]` and no `[mote]` -- it is not
/// itself a mote, and nothing belongs to it.
#[test]
def test_virtual_workspace_root_is_not_a_mote : Bool :=
    match Mote.parse_manifest "" "[workspace]\nmembers = [\"init\", \"std\"]\n" {
        Option.none => true,
        Option.some _ => false
    }
