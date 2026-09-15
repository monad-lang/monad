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
pub struct MoteManifest {
    name : String,
    dir : String,
    deps : List String,
    /// C libraries this mote links against, from `[link] libs = [...]`.
    /// A LINK-time property of the package, not of any one declaration:
    /// which C functions a module calls is `#[extern "c"]`'s business,
    /// but what the linker is handed is the mote's, the same way Cargo
    /// keeps `-l` flags out of `extern "C"` blocks.
    link_libs : List String,
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
/// Bounded by `depth` as well as by the root, because the walk is string
/// surgery on a path: a relative path bottoms out at `""`, an absolute one
/// at `"/"`, and `depth` is the argument that holds for both.
/// The `mote.toml` inside `dir`, with `""` meaning the working directory
/// and `"/"` the filesystem root.
def mote_toml_in (dir : String) : String :=
    if String.beq dir "" then "mote.toml"
    else if String.beq dir "/" then "/mote.toml"
    else String.concat dir "/mote.toml"

/// The parent of `dir`, keeping an absolute path absolute.
///
/// `raw_parent_dir "/home"` is `""` -- a root child's parent is the ROOT,
/// and `""` here means the WORKING DIRECTORY. Without this distinction the
/// walk-up of an absolute path outside any mote would end by probing
/// `mote.toml` relative to the CWD and adopt whatever mote happens to live
/// there, rewriting that file's `use lib::x` to an unrelated mote's name.
def parent_of (dir : String) : String :=
    let parent := raw_parent_dir dir in
    if String.beq parent "" && String.starts_with "/" dir
    then "/"
    else parent

#[partial]
def Mote.discover (dir : String) : IO (Option MoteManifest) :=
    Mote.discover_go dir 32

#[partial]
def Mote.discover_go (dir : String) (depth : I64) : IO (Option MoteManifest) := do {
    if I64.lt depth 1
    then return Option.none
    else do {
        let candidate := mote_toml_in dir;
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
        else Mote.discover_go (parent_of dir) (depth - 1)
    }
}

// ─── Workspace members ──────────────────────────────────────────────

/// Every mote directory belonging to the workspace rooted at `dir`.
///
/// Mirrors the Rust reference's `Workspace::resolve_members`
/// (`core/src/term/mote.rs`): each `[workspace] members` entry is a
/// directory relative to the root, except a trailing `/*`, which
/// expands ONE level to those children that are themselves motes (a
/// directory containing a `mote.toml`). `IO.list_dir` already returns
/// entries sorted, so the expansion needs no sort of its own.
///
/// `List.empty` when `dir` holds no manifest, or one with no
/// `[workspace] members` -- a single-mote checkout is not an error,
/// just a workspace of one, and the caller decides what to do about
/// that.
///
/// A member that does not exist is DROPPED rather than reported: the
/// Rust reference errors, but this is the test runner's path
/// enumeration, where a stale entry should not stop the other members
/// from being tested. The caller sees a shorter list, and the manifest
/// is checked by the Rust host in CI anyway.
#[partial]
def Mote.workspace_members (dir : String) : IO (List String) := do {
    let candidate := mote_toml_in dir;
    let exists <- IO.file_exists (Path.path candidate);
    if Bool.not exists then do { return List.empty }
    else do {
        let text <- IO.read_file (Path.path candidate);
        match Toml.parse text {
            err _ => do { return List.empty },
            ok root =>
                match Mote.workspace_member_patterns root {
                    List.empty => do { return List.empty },
                    List.cons p rest => Mote.expand_members dir (List.cons p rest),
                }
        }
    }
}

/// The raw `[workspace] members` strings, before glob expansion.
def Mote.workspace_member_patterns (root : BTreeMap String Toml.Value) : List String :=
    match Toml.table_get "workspace" root {
        Option.none => List.empty,
        Option.some v => match v {
            Toml.Value.table sub => Mote.string_list (Toml.table_get "members" sub),
            _ => List.empty
        }
    }

def Mote.string_list (found : Option Toml.Value) : List String :=
    match found {
        Option.none => List.empty,
        Option.some v => match v {
            Toml.Value.array xs => Mote.strings_of_values xs,
            _ => List.empty
        }
    }

def Mote.strings_of_values (xs : List Toml.Value) : List String :=
    match xs {
        List.empty => List.empty,
        List.cons v rest =>
            match v {
                Toml.Value.string sv => List.cons sv (Mote.strings_of_values rest),
                _ => Mote.strings_of_values rest
            }
    }

#[partial]
def Mote.expand_members (root_dir : String) (patterns : List String) : IO (List String) :=
    match patterns {
        List.empty => do { return List.empty },
        List.cons pat rest => do {
            let here <- Mote.expand_one_member root_dir pat;
            let tail <- Mote.expand_members root_dir rest;
            return (List.append here tail)
        }
    }

/// One member pattern: a `/*` suffix expands one level, anything else
/// is a single directory, kept only if it really is a mote.
#[partial]
def Mote.expand_one_member (root_dir : String) (pat : String) : IO (List String) :=
    if String.ends_with pat "/*"
    then do {
        // `String.slice` takes a LENGTH, not an end index.
        let prefix := String.slice pat 0 (String.length pat - 2);
        let parent := Mote.member_path root_dir prefix;
        let is_there <- IO.is_dir (Path.path parent);
        if Bool.not is_there then do { return List.empty }
        else do {
            let entries <- IO.list_dir (Path.path parent);
            Mote.keep_mote_dirs parent entries
        }
    }
    else do {
        let d := Mote.member_path root_dir pat;
        let ok <- IO.file_exists (Path.path (mote_toml_in d));
        if ok then do { return (List.cons d List.empty) } else do { return List.empty }
    }

/// A member directory, relative to the workspace root -- `""` (the
/// working directory) leaves the member path as written, so a
/// workspace root discovered as `""` yields `init`, not `/init`.
def Mote.member_path (root_dir : String) (name : String) : String :=
    if String.beq root_dir "" then name else raw_path_join root_dir name

#[partial]
def Mote.keep_mote_dirs (parent : String) (entries : List String) : IO (List String) :=
    match entries {
        List.empty => do { return List.empty },
        List.cons name rest => do {
            let path := raw_path_join parent name;
            let is_mote <- IO.file_exists (Path.path (mote_toml_in path));
            let tail <- Mote.keep_mote_dirs parent rest;
            return (if is_mote then List.cons path tail else tail)
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
            let libs := Mote.table_string_array (Toml.table_get "link" root) "libs" in
            let m : MoteManifest := { name := name, dir := dir, deps := deps, link_libs := libs } in
            Option.some m
    }

/// A string-array field of a sub-table (`[link] libs = ["m", "pthread"]`),
/// empty when the table, the key, or the array is absent. Non-string
/// entries are skipped rather than failing the whole manifest: a bad
/// `libs` entry should not stop the mote from resolving.
def Mote.table_string_array (found : Option Toml.Value) (key : String) : List String :=
    match found {
        Option.none => List.empty,
        Option.some v => match v {
            Toml.Value.table sub => Mote.string_array_value (Toml.table_get key sub),
            _ => List.empty
        }
    }

def Mote.string_array_value (found : Option Toml.Value) : List String :=
    match found {
        Option.none => List.empty,
        Option.some v => match v {
            Toml.Value.array items =>
                // The local annotation is load-bearing: `List.filter_map`
                // is polymorphic in its result, and nothing else in this
                // position pins `B` to `String`.
                let as_string : Toml.Value -> Option String :=
                    fn item => match item {
                        Toml.Value.string str => Option.some str,
                        _ => Option.none,
                    } in
                List.filter_map as_string items,
            _ => List.empty
        }
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

/// `[link] libs` is what hands the linker `-lm`. Declared by the MOTE
/// rather than by the `#[extern "c"]` def, because it is a property of
/// the package's build, not of the function being declared.
def link_manifest_fixture : String :=
  "[mote]\nname = \"ffi\"\nversion = \"0.1.0\"\n\n[link]\nlibs = [\"m\", \"pthread\"]\n"

#[test]
def test_manifest_reads_link_libs : Bool :=
    match Mote.parse_manifest "ffi" link_manifest_fixture {
        Option.none => false,
        Option.some m =>
            match m.link_libs {
                List.empty => false,
                List.cons a rest => match rest {
                    List.empty => false,
                    List.cons b _ => String.beq a "m" && String.beq b "pthread",
                },
            }
    }

/// A mote with no `[link]` table links nothing extra -- the overwhelmingly
/// common case, and the one that must not regress the argv.
#[test]
def test_manifest_without_link_table_has_no_libs : Bool :=
    match Mote.parse_manifest "lang" mote_manifest_fixture {
        Option.none => false,
        Option.some m => match m.link_libs { List.empty => true, List.cons _ _ => false }
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

/// The walk-up must keep an absolute path absolute. `raw_parent_dir` of a
/// root child is `""`, which means the WORKING DIRECTORY -- so without
/// `parent_of` a file outside any mote would end up adopting whatever mote
/// happens to sit in the CWD.
#[test]
def test_parent_of_root_child_is_the_root : Bool :=
    String.beq (parent_of "/home") "/"

#[test]
def test_parent_of_relative_bottoms_out_at_the_cwd : Bool :=
    String.beq (parent_of "init") ""

#[test]
def test_parent_of_keeps_walking_an_absolute_path : Bool :=
    String.beq (parent_of "/home/u/proj") "/home/u"

#[test]
def test_mote_toml_in_names_the_root_and_the_cwd : Bool :=
    if String.beq (mote_toml_in "") "mote.toml"
    then if String.beq (mote_toml_in "/") "/mote.toml"
        then String.beq (mote_toml_in "lang") "lang/mote.toml"
        else false
    else false

/// A virtual workspace root has `[workspace]` and no `[mote]` -- it is not
/// itself a mote, and nothing belongs to it.
#[test]
def test_virtual_workspace_root_is_not_a_mote : Bool :=
    match Mote.parse_manifest "" "[workspace]\nmembers = [\"init\", \"std\"]\n" {
        Option.none => true,
        Option.some _ => false
    }

// ─── Workspace member expansion ─────────────────────────────────────
//
// `Mote.workspace_members` itself is IO (it reads a manifest and lists
// directories), so these cover the pure half: pulling the patterns out
// of a parsed manifest, and the glob/plain distinction.
//
// Nested constructor patterns do not parse in this grammar, hence the
// `two_strings_are` helper rather than a `List.cons a (List.cons b ...)`
// pattern.

def two_strings_are (xs : List String) (a : String) (b : String) : Bool :=
    match xs {
        List.cons x rest =>
            match rest {
                List.cons y tail =>
                    match tail {
                        List.empty => String.beq x a && String.beq y b,
                        List.cons _ _ => false,
                    },
                List.empty => false,
            },
        List.empty => false,
    }

#[test]
def test_workspace_member_patterns_reads_members : Bool :=
    match Toml.parse "[workspace]\nmembers = [\"init\", \"std\"]\n" {
        ok root => two_strings_are (Mote.workspace_member_patterns root) "init" "std",
        err _ => false
    }

// The shape this repo's own root manifest actually uses: multi-line,
// trailing comma, and a `motes/*` glob among plain entries.
#[test]
def test_workspace_member_patterns_multiline_with_glob : Bool :=
    match Toml.parse "[workspace]\nmembers = [\n  \"init\",\n  \"motes/*\",\n]\n" {
        ok root => two_strings_are (Mote.workspace_member_patterns root) "init" "motes/*",
        err _ => false
    }

#[test]
def test_workspace_member_patterns_empty_without_workspace_table : Bool :=
    match Toml.parse "[mote]\nname = \"solo\"\n" {
        ok root => List.is_empty (Mote.workspace_member_patterns root),
        err _ => false
    }

#[test]
def test_member_path_leaves_root_relative_names_alone : Bool :=
    String.beq (Mote.member_path "" "init") "init"
    && String.beq (Mote.member_path "/repo" "init") "/repo/init"

#[test]
def test_strings_of_values_drops_non_strings : Bool :=
    two_strings_are (Mote.strings_of_values [Toml.Value.string "a", Toml.Value.integer 1, Toml.Value.string "b"]) "a" "b"
