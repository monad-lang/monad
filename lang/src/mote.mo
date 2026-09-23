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
use lib::types {AttrArg, Attribute, show_identifier}
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
    /// Where each declared dependency LIVES: `(name, dir)` pairs, `dir`
    /// being the `path` from `[dependencies.<name>]`/`[dev-dependencies].
    /// <name>]` joined onto this mote's own `dir`, so it is usable as a
    /// path exactly as stored. A dependency whose manifest declares no
    /// `path` gets `""`, which resolution reads as "declared, but not
    /// located" -- the name still satisfies `declares` (so a `use` on it
    /// is legal), it just has no directory to resolve into.
    ///
    /// Without this, a dependency resolved purely by the NAME convention
    /// (`mote_relative_file`: the mote's directory is its name, at the
    /// working directory), which is only true from a checkout root. This
    /// is what `resolve_module_file` consults on its miss path, and it is
    /// what makes resolution key off the mote root rather than the CWD.
    dep_dirs : List (Pair String String),
    /// C libraries this mote links against, from `[link] libs = [...]`.
    /// A LINK-time property of the package, not of any one declaration:
    /// which C functions a module calls is `#[extern "c"]`'s business,
    /// but what the linker is handed is the mote's, the same way Cargo
    /// keeps `-l` flags out of `extern "C"` blocks.
    link_libs : List String,
    /// The `[bin]` target's declared source, from `[bin] path = "..."`,
    /// joined onto `dir` the same way `dep_dirs` entries are -- what
    /// `monad compile <mote dir>` builds. `none` for a mote with no binary
    /// target (`lang`, `llvm`, `runtime`) or a manifest with no `[bin]`
    /// table at all.
    bin_path : Option String,
    /// The `[bin]` target's output name, from `[bin] name = "..."`.
    /// `none` when the manifest declares a `[bin] path` without a name;
    /// the caller then falls back to the source file's own stem.
    bin_name : Option String,
}

/// The mote's source root -- `<dir>/src`, always.
///
/// `raw_path_join`, not `++`, and the difference is load-bearing exactly
/// when the mote's `dir` is `""` -- the mote whose `mote.toml` sits in the
/// WORKING DIRECTORY, which is every mote found by walking up from a
/// relative path (`Mote.discover`'s own `dir = ""` case). Concatenating
/// gives `/src`, an ABSOLUTE path, so `mote_path_within` would answer
/// `use <mote>::x` with `/src/x.mo` and miss every time. Same empty-
/// component rule the dependency paths already follow
/// (`test_manifest_reads_dependency_paths`).
def MoteManifest.src_root (m : MoteManifest) : String :=
    raw_path_join m.dir "src"

/// The directory a declared dependency lives in, or `none` when the mote
/// does not declare `name` or its entry carries no `path`. A dependency
/// with no path is DECLARED but not LOCATED, which is not an error here:
/// the name-convention cascade above is still allowed to find it.
///
/// A mote's OWN name answers with its own `dir`, the same "a mote may
/// always refer to itself" rule `MoteManifest.declares` already states --
/// and here it is load-bearing rather than a convenience: `prelude`
/// belongs to `init` (`mote_dep_files` routes it there, since `prelude` is
/// the one module whose NAME is not its FILE name), and `init` is exactly
/// the mote that cannot declare itself as a dependency. Without this arm
/// the prelude of the mote `init` is unreachable from inside `init/`
/// itself, which is why `monad check src/list.mo` from `init/` reported
/// `unknown variable '==' in List.get`.
///
/// `Option.some ""` is a REAL answer here, unlike `dep_dir_in`'s: `dir` is
/// `""` for the mote whose `mote.toml` sits in the working directory, and
/// that is precisely the case this arm exists for.
def MoteManifest.dep_dir_of (m : MoteManifest) (name : String) : Option String :=
    if String.beq m.name name
    then Option.some m.dir
    else dep_dir_in m.dep_dirs name

def dep_dir_in (entries : List (Pair String String)) (name : String) : Option String :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            // A bare `Pair.pair` pattern, not `mk`: this file imports no
            // `mk` from `lib::types`, so the unqualified constructor name
            // would not resolve.
            match e {
                Pair.pair k v =>
                    if String.beq k name
                    then (if String.is_empty v then Option.none else Option.some v)
                    else dep_dir_in rest name
            }
    }

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
            let dep_dirs := List.append
                (Mote.table_dep_dirs dir (Toml.table_get "dependencies" root))
                (Mote.table_dep_dirs dir (Toml.table_get "dev-dependencies" root)) in
            let libs := Mote.table_string_array (Toml.table_get "link" root) "libs" in
            let bin := Toml.table_get "bin" root in
            let bin_path := Mote.bin_target_path dir bin in
            let bin_name := Mote.table_string bin "name" in
            let m : MoteManifest := {
                name := name,
                dir := dir,
                deps := deps,
                dep_dirs := dep_dirs,
                link_libs := libs,
                bin_path := bin_path,
                bin_name := bin_name,
            } in
            Option.some m
    }

/// `[dependencies]`/`[dev-dependencies]` as `(name, dir)` pairs: the
/// KEY is the mote name (exactly as `table_keys` reads it), and the
/// value is that entry's own `path`, joined onto `mote_dir`.
///
/// Written with sub-table headers (`[dependencies.std] path = "../std"`),
/// not inline tables (`std = { path = "../std" }`) -- `lang/src/toml.mo`
/// supports the former and not the latter, which is the spelling every
/// manifest in this repo already uses (`mote.toml`'s own header says so).
///
/// `raw_path_join`, not `++`: an empty `mote_dir` (the working directory
/// IS the mote root) must join to the bare `path` and not to `/path`, and
/// that empty-component rule lives in exactly one place. (`raw_path_join`
/// itself is used bare, un-imported, exactly as `lang/module.mo`'s own
/// `path_join` and `cli/src/main.mo`'s walk already do -- an explicit
/// `use std::path {...}` for it is what makes the checker warn that a
/// package-private name is crossing a mote boundary.)
def Mote.table_dep_dirs (mote_dir : String) (found : Option Toml.Value) : List (Pair String String) :=
    match found {
        Option.none => List.empty,
        Option.some v => match v {
            Toml.Value.table sub => dep_dir_entries mote_dir sub,
            _ => List.empty
        }
    }

def dep_dir_entries (mote_dir : String) (sub : BTreeMap String Toml.Value) : List (Pair String String) :=
    dep_dir_entries_go mote_dir (BTreeMap.to_list sub)

/// `[bin] path`, joined onto the mote's own directory so the value is a
/// path usable exactly as stored (see `MoteManifest.bin_path`).
def Mote.bin_target_path (dir : String) (bin : Option Toml.Value) : Option String :=
    match Mote.table_string bin "path" {
        Option.none => Option.none,
        Option.some p => Option.some (raw_path_join dir p)
    }

def dep_dir_entries_go (mote_dir : String) (entries : List (Pair String Toml.Value)) : List (Pair String String) :=
    match entries {
        List.empty => List.empty,
        List.cons e rest =>
            match e {
                Pair.pair k v =>
                    let path := match Mote.table_string (Option.some v) "path" {
                        Option.none => "",
                        Option.some p => p
                    } in
                    List.cons (Pair.pair k (raw_path_join mote_dir path))
                        (dep_dir_entries_go mote_dir rest)
            }
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

// ─── The inline `#![mote { ... }]` annotation ────────────────────────
//
// A file outside any mote can declare its own inline instead of shipping a
// `mote.toml`. The spelling mirrors the manifest's own fields so a reader
// who knows one knows the other:
//
//     #![mote { name := "structs", deps := [init, std], libs := [m] }]
//
// Only `name`, `deps` and `libs` are accepted, and an unknown key is a
// DIAGNOSTIC rather than a silent drop (`mote_attr_unknown_keys`): the
// whole point of moving `examples/` off the resolution cascade is that the
// annotation is load-bearing, and a key no reader consumes would look
// load-bearing while doing nothing.

/// Flatten an attribute's arg list into a plain list of entries.
///
/// This is the load-bearing part of reading the attribute at all, because
/// the two parsers spell a `{ ... }` block differently and NEITHER spelling
/// is wrong: `lang/src/parser.mo`'s `attr_arg_named_close` wraps the
/// block's entries in ONE `AttrArg.group`, while `core/src/parser.rs`'s
/// `attr_arg_parser` returns a `Vec` per call and so flattens the very same
/// entries straight onto `attr.args`. A reader that assumed either shape
/// would silently find nothing under the other compiler — the same class of
/// divergence that let the A2/A3 registry causes go stale for two commits.
def mote_attr_flatten (args : List AttrArg) : List AttrArg :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            match a {
                AttrArg.group items => List.append items (mote_attr_flatten rest),
                _ => List.cons a (mote_attr_flatten rest)
            }
    }

/// The value bound to `key` in the annotation's `{ ... }` block, or `none`.
def Mote.mote_attr_named (attr : Attribute) (key : String) : Option AttrArg :=
    mote_attr_named_in (mote_attr_flatten attr.args) key

def mote_attr_named_in (entries : List AttrArg) (key : String) : Option AttrArg :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                AttrArg.named name value =>
                    if String.beq (show_identifier name) key
                    then Option.some value
                    else mote_attr_named_in rest key,
                _ => mote_attr_named_in rest key
            }
    }

/// One entry rendered as a plain string: `init` and `"init"` name the same
/// mote, so both spellings are accepted. `none` for a number or a nested
/// block, which name nothing.
def attr_arg_as_string (a : AttrArg) : Option String :=
    match a {
        AttrArg.ident i => Option.some (show_identifier i),
        AttrArg.str s => Option.some s,
        AttrArg.num _ => Option.none,
        AttrArg.named _ _ => Option.none,
        AttrArg.group _ => Option.none
    }

/// A `[a, b]` / `[a]` / `a` entry rendered as a list of names.
///
/// The single-element case is not politeness: the two parsers disagree
/// about it. `deps := [init, std]` is an `AttrArg.group` under both, but
/// `deps := [init]` is a group of one self-hosted and a BARE
/// `AttrArg.ident` under the Rust reference, whose `wrap_args` collapses a
/// one-element vector. (`deps := []` is empty self-hosted and a parse error
/// in Rust, whose block grammar is `many1`; no real annotation writes one,
/// and "absent" and "empty" mean the same thing here either way.)
def attr_arg_as_string_list (a : AttrArg) : List String :=
    match a {
        AttrArg.group items =>
            let as_string : AttrArg -> Option String := fn item => attr_arg_as_string item in
            List.filter_map as_string items,
        _ => match attr_arg_as_string a {
            Option.none => List.empty,
            Option.some s => List.cons s List.empty
        }
    }

/// The `deps`/`libs` list field of the annotation, empty when absent.
def Mote.mote_attr_list (attr : Attribute) (key : String) : List String :=
    match Mote.mote_attr_named attr key {
        Option.none => List.empty,
        Option.some v => attr_arg_as_string_list v
    }

/// The single string field of the annotation, if it is a string and not a
/// number or a block.
def Mote.mote_attr_string (attr : Attribute) (key : String) : Option String :=
    match Mote.mote_attr_named attr key {
        Option.none => Option.none,
        Option.some v => attr_arg_as_string v
    }

/// Every key the annotation's block sets, in source order.
def Mote.mote_attr_keys (attr : Attribute) : List String :=
    mote_attr_keys_of (mote_attr_flatten attr.args) List.empty

def mote_attr_keys_of (entries : List AttrArg) (acc : List String) : List String :=
    match entries {
        List.empty => List.reverse acc,
        List.cons e rest =>
            match e {
                AttrArg.named name _ => mote_attr_keys_of rest (List.cons (show_identifier name) acc),
                _ => mote_attr_keys_of rest acc
            }
    }

/// The keys the inline annotation understands.
def mote_attr_known_keys : List String :=
    List.cons "name" (List.cons "deps" (List.cons "libs" List.empty))

/// Keys the annotation sets that no reader consumes — one error per key,
/// each naming the accepted set.
def Mote.mote_attr_unknown_keys (attr : Attribute) : List String :=
    mote_attr_unknown_keys_of (Mote.mote_attr_keys attr) List.empty

def mote_attr_unknown_keys_of (keys : List String) (acc : List String) : List String :=
    match keys {
        List.empty => List.reverse acc,
        List.cons k rest =>
            if list_contains_string k mote_attr_known_keys
            then mote_attr_unknown_keys_of rest acc
            else mote_attr_unknown_keys_of rest (List.cons (unknown_mote_key_error k) acc)
    }

def unknown_mote_key_error (key : String) : String :=
    String.concat "error: unknown `#![mote { ... }]` key `" (String.concat key
    (String.concat "`\n  accepted keys: " (join_with_commas mote_attr_known_keys)))

def join_with_commas (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x rest => match rest {
            List.empty => x,
            List.cons _ _ => String.concat x (String.concat ", " (join_with_commas rest))
        }
    }

/// The inline manifest an `#![mote { ... }]` declares, or `none` when it
/// does not name itself — a nameless mote has no identity for `declares`
/// to match a `use` head against, so it cannot be one.
///
/// `dir` is the FILE's own directory. An inline mote has no `src/` tree, so
/// `MoteManifest.src_root` is `<dir>/src` and means nothing for it; its
/// siblings resolve relative to the file itself, which is why
/// `resolve_module_file` (lang/module.mo) must not route an inline mote
/// through the manifest's `src_root`.
def Mote.manifest_of_attr (dir : String) (attr : Attribute) : Option MoteManifest :=
    match Mote.mote_attr_string attr "name" {
        Option.none => Option.none,
        Option.some name =>
            let m : MoteManifest := {
                name := name,
                dir := dir,
                deps := Mote.mote_attr_list attr "deps",
                // No `[dependencies.<name>] path` spelling exists in the
                // inline form: an inline mote's siblings sit beside it, so
                // the only directory it could name is the one it already
                // is in, and `dep_dir_of`'s empty case is exactly that
                // ("declared, resolved by convention").
                dep_dirs := List.empty,
                link_libs := Mote.mote_attr_list attr "libs",
                // An inline mote declares no `[bin]`: the annotation's own
                // file IS the binary, and `compile` already takes a file.
                bin_path := Option.none,
                bin_name := Option.none,
            } in
            Option.some m
    }

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

/// A declared dependency's `path` is READ, not dropped: this is the whole
/// difference between "the mote's directory is its name" (a convention
/// that only holds at a checkout root) and "the manifest says where it
/// is" (which holds anywhere).
///
/// Parsed with `dir = ""` on purpose: the joined form is then the
/// manifest's own spelling, so the assertion says what the manifest says
/// rather than re-deriving the join.
#[test]
def test_manifest_reads_dependency_paths : Bool :=
    match Mote.parse_manifest "" mote_manifest_fixture {
        Option.none => false,
        Option.some m =>
            match MoteManifest.dep_dir_of m "init" {
                Option.none => false,
                Option.some p => String.beq p "../init"
            }
    }

/// The join is onto the MOTE's directory, so the stored value is a path
/// from the working directory, not from the mote. (`raw_path_join`'s
/// empty-component rule is why the `dir = ""` case above is not `/../init`.)
#[test]
def test_dependency_path_is_joined_onto_the_mote_dir : Bool :=
    match Mote.parse_manifest "lang" mote_manifest_fixture {
        Option.none => false,
        Option.some m =>
            match MoteManifest.dep_dir_of m "std" {
                Option.none => false,
                Option.some p => String.beq p "lang/../std"
            }
    }

/// `[dependencies.foo]` with no `path` is DECLARED but not LOCATED. The
/// two are deliberately different answers: `declares` still says yes (so
/// a `use foo::x` is legal), while resolution has no directory to try and
/// falls through to the name convention.
def no_path_manifest_fixture : String :=
  "[mote]\nname = \"here\"\nversion = \"0.1.0\"\n\n[dependencies.there]\nversion = \"0.1.0\"\n"

#[test]
def test_dependency_without_a_path_is_declared_but_not_located : Bool :=
    match Mote.parse_manifest "" no_path_manifest_fixture {
        Option.none => false,
        Option.some m =>
            if MoteManifest.declares m "there"
            then match MoteManifest.dep_dir_of m "there" {
                Option.none => true,
                Option.some _ => false
            }
            else false
    }

#[test]
def test_manifest_without_dependencies_has_no_dep_dir : Bool :=
    match Mote.parse_manifest "" init_manifest_fixture {
        Option.none => false,
        Option.some m => match MoteManifest.dep_dir_of m "llvm" {
            Option.none => true,
            Option.some _ => false
        }
    }

/// The `[bin]` target, which is what `monad compile <mote dir>` builds.
/// Same shape as `cli/mote.toml`.
def bin_manifest_fixture : String :=
  "[mote]\nname = \"cli\"\nversion = \"0.1.0\"\n\n[lib]\npath = \"src/lib.mo\"\n\n[bin]\nname = \"monad\"\npath = \"src/main.mo\"\n"

#[test]
def test_manifest_reads_the_bin_target : Bool :=
    match Mote.parse_manifest "" bin_manifest_fixture {
        Option.none => false,
        Option.some m =>
            match m.bin_path {
                Option.none => false,
                Option.some p =>
                    if String.beq p "src/main.mo"
                    then match m.bin_name {
                        Option.none => false,
                        Option.some n => String.beq n "monad"
                    }
                    else false
            }
    }

#[test]
def test_manifest_without_a_bin_table_has_no_bin_target : Bool :=
    match Mote.parse_manifest "" mote_manifest_fixture {
        Option.none => false,
        Option.some m => match m.bin_path {
            Option.none => true,
            Option.some _ => false
        }
    }

/// `[bin] path` is joined like a dependency path, so `compile` needs no
/// join of its own.
#[test]
def test_bin_path_is_joined_onto_the_mote_dir : Bool :=
    match Mote.parse_manifest "cli" bin_manifest_fixture {
        Option.none => false,
        Option.some m =>
            match m.bin_path {
                Option.none => false,
                Option.some p => String.beq p "cli/src/main.mo"
            }
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

// ─── The inline annotation, both parser shapes ───────────────────────
//
// These pin the one thing that can silently break: `lang/src/parser.mo`
// and `core/src/parser.rs` produce DIFFERENT `Attribute.args` shapes for
// the same source. A reader that handles one shape reports "no deps" under
// the other compiler, which looks exactly like a file that declared
// nothing -- so both shapes are built by hand here rather than only the one
// this compiler's own parser happens to produce.

def attr_named (key : String) (v : AttrArg) : AttrArg :=
    AttrArg.named (Identifier.id key) v

/// What `#![mote { name := "structs", deps := [init, std] }]` lowers to
/// under `lang/src/parser.mo`: ONE `AttrArg.group` wrapping the entries.
def attr_mote_self_hosted : Attribute :=
    Attribute.mk (Identifier.id "mote")
        [AttrArg.group [
            attr_named "name" (AttrArg.str "structs"),
            attr_named "deps" (AttrArg.group [
                AttrArg.ident (Identifier.id "init"),
                AttrArg.ident (Identifier.id "std")]),
        ]]

/// The same source under `core/src/parser.rs`: the entries FLATTENED onto
/// `args` directly, because its `attr_arg_parser` returns a `Vec` per call.
def attr_mote_rust : Attribute :=
    Attribute.mk (Identifier.id "mote")
        [attr_named "name" (AttrArg.str "structs"),
         attr_named "deps" (AttrArg.group [
            AttrArg.ident (Identifier.id "init"),
            AttrArg.ident (Identifier.id "std")])]

#[test]
def test_manifest_of_attr_reads_both_parser_shapes : Bool :=
    match Mote.manifest_of_attr "examples" attr_mote_self_hosted {
        Option.none => false,
        Option.some ma =>
            match Mote.manifest_of_attr "examples" attr_mote_rust {
                Option.none => false,
                Option.some mb =>
                    String.beq ma.name "structs" &&
                    MoteManifest.declares ma "init" &&
                    MoteManifest.declares ma "std" &&
                    MoteManifest.declares mb "init" &&
                    MoteManifest.declares mb "std" &&
                    MoteManifest.declares mb "structs"
            }
    }

/// The single-element case, where the two parsers diverge in SHAPE rather
/// than only in nesting: self-hosted keeps `[init]` a group of one, and the
/// Rust reference's `wrap_args` collapses it to a bare `ident`.
def attr_one_dep_self_hosted : Attribute :=
    Attribute.mk (Identifier.id "mote")
        [AttrArg.group [
            attr_named "name" (AttrArg.str "solo"),
            attr_named "deps" (AttrArg.group [AttrArg.ident (Identifier.id "init")]),
        ]]

def attr_one_dep_rust : Attribute :=
    Attribute.mk (Identifier.id "mote")
        [attr_named "name" (AttrArg.str "solo"),
         attr_named "deps" (AttrArg.ident (Identifier.id "init"))]

#[test]
def test_manifest_of_attr_reads_one_element_deps_both_shapes : Bool :=
    match Mote.manifest_of_attr "examples" attr_one_dep_self_hosted {
        Option.none => false,
        Option.some a =>
            match Mote.manifest_of_attr "examples" attr_one_dep_rust {
                Option.none => false,
                Option.some b =>
                    MoteManifest.declares a "init" &&
                    MoteManifest.declares b "init" &&
                    not (MoteManifest.declares b "std")
            }
    }

#[test]
def test_mote_attr_quoted_names_are_accepted : Bool :=
    // `deps := ["init"]` names the same mote as `deps := [init]` -- the
    // attribute is a manifest, and a manifest's names are strings.
    let a := Attribute.mk (Identifier.id "mote")
        [attr_named "name" (AttrArg.str "solo"),
         attr_named "deps" (AttrArg.str "init")] in
    match Mote.manifest_of_attr "examples" a {
        Option.none => false,
        Option.some m => MoteManifest.declares m "init"
    }

#[test]
def test_mote_attr_without_a_name_is_not_a_manifest : Bool :=
    let a := Attribute.mk (Identifier.id "mote")
        [attr_named "deps" (AttrArg.group [AttrArg.ident (Identifier.id "init")])] in
    match Mote.manifest_of_attr "examples" a {
        Option.none => true,
        Option.some _ => false
    }

#[test]
def test_mote_attr_known_keys_are_not_reported : Bool :=
    match Mote.mote_attr_unknown_keys attr_mote_self_hosted {
        List.empty => true,
        List.cons _ _ => false
    }

/// An unsupported key is REPORTED, not dropped -- the whole reason the
/// annotation exists is to be load-bearing. `bin` is the concrete case:
/// the plan's own example writes `bin := true`, and nothing in this
/// compiler consumes a `bin` flag yet, so accepting it silently would be
/// exactly the "looks load-bearing, does nothing" failure this plan keeps
/// finding in the gap registries.
#[test]
def test_mote_attr_unsupported_key_is_reported : Bool :=
    let a := Attribute.mk (Identifier.id "mote")
        [attr_named "name" (AttrArg.str "solo"),
         attr_named "bin" (AttrArg.ident (Identifier.id "true"))] in
    match Mote.mote_attr_unknown_keys a {
        List.empty => false,
        List.cons _ rest => match rest { List.empty => true, List.cons _ _ => false }
    }

#[test]
def test_mote_attr_unknown_key_error_names_the_key : Bool :=
    let a := Attribute.mk (Identifier.id "mote")
        [attr_named "name" (AttrArg.str "solo"),
         attr_named "bin" (AttrArg.ident (Identifier.id "true"))] in
    match Mote.mote_attr_unknown_keys a {
        List.empty => false,
        List.cons e _ => String.beq e (unknown_mote_key_error "bin")
    }
