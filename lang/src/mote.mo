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

use std::list {List.filter_map}
use toml::toml {
  Toml.Value, Toml.parse, Toml.table_get, Toml.array_at, array, integer, string, table,
}
use lang::types {AffineMode, AttrArg, Attribute, id, show_identifier}
use std::io {}
use std::map {BTreeMap, BTreeMap.to_list}
use std::process {exec_cmd, process_id}
use std::stream {StreamError, StreamError.is_not_found}

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
    /// pkg-config packages that say WHERE `link_libs` live, from
    /// `[link] pkg-config = [...]`. `llvm.link`'s `link_ir` asks
    /// `pkg-config --libs-only-L` for these and passes the `-L` flags
    /// itself, so a mote's link does not depend on the caller's
    /// environment happening to carry the right search path. The names in
    /// `link_libs` still supply the `-l` flags.
    link_pkgs : List String,
    /// Where this mote's library root would be: `[lib] path`, else the
    /// conventional `src/lib.mo`. `none` only for an inline mote, which has
    /// no `src/` tree at all.
    ///
    /// A PATH, not a promise that the file is there: `manifest_of_table` is
    /// pure and cannot probe the filesystem. Whether it exists is
    /// `gate_mote_targets`' question (lang/module.mo).
    lib_path : Option String,
    /// This mote's binary targets, from `[[bin]]` (or the legacy singular
    /// `[bin]` spelling, which means the same thing here). Empty only for an
    /// inline mote, whose own file IS its binary.
    ///
    /// A manifest with no bin table at all still gets exactly ONE target --
    /// the conventional `src/main.mo`, named after the mote -- so
    /// `monad build <mote>` works without a manifest edit. Whether that file
    /// exists is what `build_target` checks before building it, which is what
    /// keeps a default from becoming an invention.
    bins : List BinTarget,
    /// `[mote] targets = [...]`: the build PROFILES this mote's side effects
    /// are implemented for (`"web"` for the browser boundary). Informational
    /// only -- availability is enforced per extern/native at codegen
    /// (`validate_native_target_availability`), not per mote, because a
    /// mote's pure parts (an ABI spec, a generator) must stay usable on
    /// every target. Do not confuse it with `Mote.target_roots`, which is
    /// about SOURCE files.
    targets : List String,
}

/// One binary target: what `monad build` selects between.
///
/// Both fields are already resolved -- a declared value or the conventional
/// default, joined onto the mote's own `dir` -- so a consumer needs no rule
/// of its own. `plans/packaging/package-system.md` §2a is the spec.
pub struct BinTarget {
    /// `[[bin]] path`, or `src/main.mo` when the entry names none, joined
    /// onto the mote's own `dir` the same way `dep_dirs` entries are.
    path : String,
    /// `[[bin]] name`, or the mote's own name when the entry names none. Not
    /// optional: it is what `monad build <mote>` names the output after, so
    /// the fallback to a source file's own stem is the FILE compile's rule
    /// and no longer this one's.
    name : String,
}

/// `BinTarget.path`, and its `name` sibling below. Accessors rather than
/// bare field reads because a `#[test] def ... : Bool` body reading a field
/// directly is the shape `test-def-struct-field-access-codegen` warns about
/// (the def can be emitted with the FIELD's LLVM type as its return type).
/// A one-line accessor whose return type IS the field's type costs nothing
/// and sidesteps it.
def BinTarget.target_path (b : BinTarget) : String := b.path

def BinTarget.target_name (b : BinTarget) : String := b.name

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

/// Walk up from `dir` for the monad tool's own config, `.monad/config.toml`,
/// and answer the `[build] target-dir` it names, joined onto the config's
/// directory so the value is usable as stored.
///
/// A TOOL setting, not a mote's. Where output goes is a property of the tool
/// that writes it, so it is read from the tool's config rather than from the
/// `mote.toml` of whichever mote is being built -- which also means this walk
/// has no mote boundary to stop at. That is what makes it the right lookup
/// for a script-mode file: `monad build examples/hello.mo` must land where
/// the rest of the tree does, and `examples/` sits under no `[mote]` for
/// `Mote.discover` to find.
///
/// A config that names no target dir does not stop the walk, so a nested
/// `.monad/config.toml` inherits from the one above it -- the same rule a
/// manifest used to follow for its workspace.
#[partial]
pub def Mote.discover_config_target_dir (dir : String) : IO (Option String) :=
    Mote.discover_config_target_dir_go dir 32

#[partial]
def Mote.discover_config_target_dir_go (dir : String) (depth : I64) : IO (Option String) := do {
    if I64.lt depth 1
    then return Option.none
    else do {
        let text <- read_file_or_none (Path.path (tool_config_in dir));
        match Mote.config_target_dir_of_found dir text {
            Option.some d => return (Option.some d),
            Option.none => Mote.discover_config_target_dir_above dir (depth - 1)
        }
    }
}

/// `config_target_dir_of_text` of a config file that may not exist.
def Mote.config_target_dir_of_found (dir : String) (text : Option String) : Option String :=
    match text {
        Option.none => Option.none,
        Option.some t => Mote.config_target_dir_of_text dir t
    }

#[partial]
def Mote.discover_config_target_dir_above (dir : String) (depth : I64) : IO (Option String) :=
    if String.beq dir "/"
    then return Option.none
    else Mote.discover_config_target_dir_go (config_dir_above dir) depth

/// One step up from a directory this walk is standing in.
///
/// Not `parent_of`, because `""` is BOTH "the working directory" (see
/// `tool_config_in`) and "no directory component" -- so `parent_of ""` is
/// `""`, and a walk that stopped there never left the working directory.
/// Same tree, two answers:
///
///   `monad build examples/hello.mo` (cwd = root) probes `examples/`, then
///   `""` -- the cwd -- and finds the root config. `cd examples && monad
///   build hello.mo` starts AT `""`, so `parent_of ""` is `""` and the walk
///   stops after one probe: it silently falls back to `target/`.
///
/// A bare filename has genuinely no directory component (`raw_parent_dir
/// "hello.mo"` is `""`), so the empty result cannot be reinterpreted at the
/// call site -- `""` is a legitimate argument meaning CWD. An empty ascent
/// therefore continues by `..`, the one spelling a path string has for
/// "the directory above the working directory", and a path already made of
/// `..` segments keeps going rather than bouncing (`raw_parent_dir ".."`
/// is `.`, which would otherwise re-probe the cwd forever, bounded only by
/// `depth`). Absolute paths still bottom out at `/`.
///
/// `Mote.discover`'s walk has the same shape and the same wart; it is left
/// alone deliberately. Its consequence is a script module -- a documented,
/// legitimate mode -- while this one quietly writes the binary somewhere
/// other than where the tree says.
def config_dir_above (dir : String) : String :=
    if String.beq dir "" || String.beq dir "."
    then ".."
    else if String.starts_with ".." dir
    then String.concat dir "/.."
    else parent_of dir

def Mote.config_target_dir_of_text (dir : String) (text : String) : Option String :=
    match Toml.parse text {
        err _ => Option.none,
        ok root => Mote.joined_table_string dir (Toml.table_get "build" root) "target-dir"
    }

/// The `mote.toml` inside `dir`, with `""` meaning the working directory
/// and `"/"` the filesystem root.
def mote_toml_in (dir : String) : String :=
    if String.beq dir "" then "mote.toml"
    else if String.beq dir "/" then "/mote.toml"
    else String.concat dir "/mote.toml"

/// The monad tool's config inside `dir` -- `.monad/config.toml`, with `""`
/// meaning the working directory and `"/"` the filesystem root.
def tool_config_in (dir : String) : String :=
    if String.beq dir "" then ".monad/config.toml"
    else if String.beq dir "/" then "/.monad/config.toml"
    else String.concat dir "/.monad/config.toml"

/// The directories a mote's own declared targets live in: the `[lib]`
/// root's, then each `[[bin]]`'s, deduplicated in that order.
///
/// This is what a bare `monad check`/`monad test` covers, and it covers it
/// because the alternative was the whole subtree. Walking the mote's
/// DIRECTORY swept every `*.mo` under it, and `.mo` is also GNU gettext's
/// extension -- so in any project that has run `devenv shell` (which
/// materializes `.devenv/bash-bash/share/locale/*/LC_MESSAGES/bash.mo`),
/// `monad test` reported 85 parse failures beside the 2 real files
/// (`plans/implementations/2026-10-04-monad-test-no-path-globs-unrelated-
/// dot-mo-files.md`). A declared target is the mote saying where its own
/// sources are; nothing else under the directory is its business.
///
/// `fallback` (the mote's own directory) is the answer for an inline mote,
/// which declares no targets at all. An explicit path argument never
/// reaches here -- `monad test .` still means that directory, literally.
pub def Mote.target_roots (m : MoteManifest) (fallback : String) : List String :=
    let from_lib : List String := match m.lib_path {
        Option.some p => List.cons (Mote.target_root_of p) List.empty,
        Option.none => List.empty,
    } in
    let roots : List String := Mote.push_unique_roots (Mote.bin_target_roots m.bins) from_lib in
    if List.is_empty roots then List.cons fallback List.empty else roots

/// A target FILE's directory, with the mote root spelled the way a path
/// expander wants it: `src/lib.mo` -> `src`, but a target at the mote root
/// (`main.mo`) -> `.`, not `""`.
def Mote.target_root_of (path : String) : String :=
    let d : String := raw_parent_dir path in
    if String.beq d "" then "." else d

def Mote.bin_target_roots (bs : List BinTarget) : List String :=
    match bs {
        List.empty => List.empty,
        List.cons b rest => List.cons (Mote.target_root_of (BinTarget.target_path b)) (Mote.bin_target_roots rest),
    }

/// Append each of `more` to `acc` unless it is already there -- declaration
/// order preserved, so the `[lib]` root stays first. Hand-rolled rather
/// than a generic fold: `acc` is the small list and the comparison is
/// `String.beq`.
def Mote.push_unique_roots (more : List String) (acc : List String) : List String :=
    match more {
        List.empty => acc,
        List.cons r rest =>
            let next : List String := if Mote.roots_contain acc r then acc else List.append acc (List.cons r List.empty) in
            Mote.push_unique_roots rest next,
    }

def Mote.roots_contain (roots : List String) (wanted : String) : Bool :=
    match roots {
        List.empty => false,
        List.cons r rest => if String.beq r wanted then true else Mote.roots_contain rest wanted,
    }

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
/// `pub`: this is the reader's entry point and it already crosses a mote
/// boundary -- `cli/src/main.mo` calls it twice (`:156` for `monad build
/// <dir>`, `:668` for the bare-command mote lookup), and `build/src/
/// closure.mo` needs it to walk a dependency closure. The cross-mote
/// warning did not catch those because it only inspects names listed in a
/// `use` filter and `Mote.discover` is called qualified; that is a hole in
/// the warning, not permission.
///
/// Walks up from `dir` for the first `mote.toml` and parses it; `Option.none`
/// for a file outside any mote (script mode -- `examples/`, a one-off file)
/// or under a virtual workspace root, which declares `[workspace]` and no
/// `[mote]`. Bounded by `depth` as well as by the root, because the walk is
/// string surgery on a path: a relative path bottoms out at `""`, an
/// absolute one at `"/"`, and `depth` is the argument that holds for both.
pub def Mote.discover (dir : String) : IO (Option MoteManifest) :=
    Mote.discover_go dir 32

#[partial]
def Mote.discover_go (dir : String) (depth : I64) : IO (Option MoteManifest) := do {
    if I64.lt depth 1
    then return Option.none
    else do {
        let found <- read_file_or_none (Path.path (mote_toml_in dir));
        match found {
            // A `mote.toml` with no `[mote]` is a virtual workspace
            // root: stop there rather than walking past it, since
            // nothing above a workspace root is part of this mote.
            Option.some text => return (Mote.parse_manifest dir text),
            Option.none => Mote.discover_above dir depth
        }
    }
}

#[partial]
def Mote.discover_above (dir : String) (depth : I64) : IO (Option MoteManifest) :=
    if String.beq dir "" || String.beq dir "/"
    then return Option.none
    else Mote.discover_go (parent_of dir) (depth - 1)

/// The manifest AT `dir`, with no walk -- unlike `Mote.discover`, whose
/// walk is right for a file's own mote and wrong for a DECLARED dependency:
/// `[dependencies.x] path` names `x`'s directory, so a manifest further up
/// is somebody else's. Resolution needs the dependency's own `[lib] path`.
pub def Mote.manifest_at (dir : String) : IO (Option MoteManifest) := do {
    let text <- read_file_or_none (Path.path (mote_toml_in dir));
    return (match text {
        Option.none => Option.none,
        Option.some t => Mote.parse_manifest dir t
    })
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
    let found <- read_file_or_none (Path.path (mote_toml_in dir));
    match found {
        Option.none => return List.empty,
        Option.some text => Mote.workspace_members_of_text dir text
    }
}

#[partial]
def Mote.workspace_members_of_text (dir : String) (text : String) : IO (List String) :=
    match Toml.parse text {
        err _ => IO.pure List.empty,
        ok root =>
            match Mote.workspace_member_patterns root {
                List.empty => IO.pure List.empty,
                List.cons p rest => Mote.expand_members dir (List.cons p rest),
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
            Mote.keep_mote_dirs entries
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
def Mote.keep_mote_dirs (entries : List Path) : IO (List String) :=
    match entries {
        List.empty => do { return List.empty },
        List.cons entry rest => do {
            let path := Path.to_string entry;
            let is_mote <- IO.file_exists (Path.path (mote_toml_in path));
            let tail <- Mote.keep_mote_dirs rest;
            return (if is_mote then List.cons path tail else tail)
        }
    }

/// Parse a manifest's text into the resolution-relevant fields.
def Mote.parse_manifest (dir : String) (text : String) : Option MoteManifest :=
    match Toml.parse text {
        err _ => Option.none,
        ok root => Mote.manifest_of_table dir root
    }

// --- Affine enforcement policy -------------------------------------

/// How a mote enforces the affine-by-default usage rule, from
/// `[affine] mode` in its nearest `mote.toml`.
///
/// The default -- no manifest, no key, a parse error, or any value other
/// than `"warn"` -- is `affine_error`. A typo must never silently
/// weaken enforcement, so only one spelling opts out.
///
/// **This deliberately does not go through `Mote.discover`.** That walk
/// returns `none` at a virtual workspace root (a `mote.toml` with no
/// `[mote]`; see `Mote.discover_go`), which is exactly the manifest a
/// file outside every member resolves to -- this repository's
/// `examples/`, for one. The policy walk stops at the nearest
/// `mote.toml` whether or not it declares a `[mote]`, so a workspace
/// root can carry the fallback and a member can override it.
pub def Mote.affine_mode_of_path (file : String) : IO AffineMode :=
    Mote.affine_mode_of_dir (raw_parent_dir file) 32

#[partial]
def Mote.affine_mode_of_dir (dir : String) (depth : I64) : IO AffineMode := do {
    if I64.lt depth 1 then return AffineMode.affine_error
    else do {
        let found <- read_file_or_none (Path.path (mote_toml_in dir));
        match found {
            Option.some text => return (Mote.affine_mode_of_text text),
            // `config_dir_above`, not `parent_of`: when the walk starts at
            // `""` (the working directory) `parent_of` answers `""` again,
            // so a member's own file checked from inside the member would
            // never reach `../mote.toml`. `config_dir_above` steps to `..`
            // in that case, the same walk `Mote.discover_config_target_dir_go`
            // already uses.
            Option.none => Mote.affine_mode_of_dir (config_dir_above dir) (depth - 1),
        }
    }
}

/// `[affine] mode` in a manifest's text. See `Mote.affine_mode_of_path`
/// for why every non-`"warn"` answer is the strict default.
pub def Mote.affine_mode_of_text (text : String) : AffineMode :=
    match Toml.parse text {
        err _ => AffineMode.affine_error,
        ok root =>
            match Mote.table_string (Toml.table_get "affine" root) "mode" {
                Option.some m =>
                    if String.beq m "warn" then AffineMode.affine_warn
                    else AffineMode.affine_error,
                Option.none => AffineMode.affine_error,
            },
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
            let pkgs := Mote.table_string_array (Toml.table_get "link" root) "pkg-config" in
            let lib_path := Mote.lib_target_path dir root in
            let bins := Mote.bin_targets dir name root in
            let targets := Mote.table_string_array (Toml.table_get "mote" root) "targets" in
            let m : MoteManifest := {
                name := name,
                dir := dir,
                deps := deps,
                dep_dirs := dep_dirs,
                link_libs := libs,
                link_pkgs := pkgs,
                lib_path := lib_path,
                bins := bins,
                targets := targets,
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
///
/// That empty-component rule is not the only one this join needs: an
/// ABSOLUTE `path` must replace `mote_dir` outright rather than being
/// appended to it, which is what an external mote declaring
/// `path = "/home/me/monad/std"` needs, and what a bare `monad check`
/// (where `mote_dir` is `"."`, not `""`) got wrong until
/// `raw_path_join` grew the rule `Path.join` already had -- `".//home/me/…"`
/// resolved to nothing and the dependency silently went missing.
/// `Mote.bin_target_of` below joins `[[bin]] path` the same way and
/// inherits the same fix.
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

/// `[lib] path`, joined onto the mote's own directory, or the conventional
/// `src/lib.mo` when the table (or its `path`) is absent.
///
/// The default is the whole point of the field existing: an undeclared
/// `[lib]` already resolves to `src/lib.mo` (that filename is hardcoded in
/// resolution), so a manifest that restates it says nothing. Recording the
/// resolved path here is what lets the gate below ask the filesystem a
/// question the pure parser cannot.
///
/// `[[bin]]` is deliberately NOT the same shape: a bin table can name
/// several targets, so those default per ENTRY (see `Mote.bin_targets`),
/// and an absent table defaults to one target rather than to a filename.
def Mote.lib_target_path (dir : String) (root : BTreeMap String Toml.Value) : Option String :=
    match Mote.joined_table_string dir (Toml.table_get "lib" root) "path" {
        Option.some p => Option.some p,
        Option.none => Option.some (raw_path_join dir "src/lib.mo"),
    }

/// The mote's binary targets, in declaration order.
///
/// Three cases, and the middle one is a spelling rather than a second
/// meaning: `[[bin]]` (the canonical form, an array of tables) wins; the
/// singular `[bin]` table is read as one target (`[bin]` and `[[bin]]` are
/// the same table read two ways, and `Toml.header_conflict` already refuses
/// to have both); and with neither, the conventional `src/main.mo` named
/// after the mote.
///
/// `Toml.array_at` is what separates the first two: an array of tables
/// parses to `Toml.Value.array`, so it answers with the elements, while the
/// singular table answers with nothing and falls through.
def Mote.bin_targets (dir : String) (mote_name : String) (root : BTreeMap String Toml.Value) : List BinTarget :=
    match Toml.array_at "bin" root {
        List.empty => match Toml.table_get "bin" root {
            Option.some v => match v {
                Toml.Value.table sub => List.cons (Mote.bin_target_of dir mote_name sub) List.empty,
                _ => List.cons (Mote.default_bin_target dir mote_name) List.empty
            },
            Option.none => List.cons (Mote.default_bin_target dir mote_name) List.empty
        },
        List.cons _ _ => Mote.bin_targets_of_values dir mote_name (Toml.array_at "bin" root)
    }

def Mote.bin_targets_of_values (dir : String) (mote_name : String) (entries : List Toml.Value) : List BinTarget :=
    match entries {
        List.empty => List.empty,
        List.cons v rest =>
            match v {
                Toml.Value.table sub =>
                    List.cons (Mote.bin_target_of dir mote_name sub)
                        (Mote.bin_targets_of_values dir mote_name rest),
                // A `[[bin]]` element that is not a table declares nothing to
                // build; skipped rather than failing the whole manifest, the
                // same rule `Mote.strings_of_values` applies to `[link] libs`.
                _ => Mote.bin_targets_of_values dir mote_name rest
            }
    }

/// The one implicit target: `src/main.mo`, named after the mote.
///
/// Not a check that the file is there -- this is pure.
/// `choose_bin_target` (cli/src/main.mo) refuses when it is not
/// (`error: mote \`lang\` has no [bin] target to build`), which is how a
/// library mote keeps needing no `[[bin]]` while a binary mote keeps building
/// without declaring one.
def Mote.default_bin_target (dir : String) (mote_name : String) : BinTarget :=
    let t : BinTarget := {
        path := raw_path_join dir "src/main.mo",
        name := mote_name,
    } in
    t

/// One `[[bin]]` entry: its own `path` and `name`, each falling back to the
/// conventional value when the entry names none.
def Mote.bin_target_of (dir : String) (mote_name : String) (sub : BTreeMap String Toml.Value) : BinTarget :=
    let declared := Mote.joined_table_string dir (Option.some (Toml.Value.table sub)) "path" in
    let path : String := match declared {
        Option.some p => p,
        Option.none => raw_path_join dir "src/main.mo",
    } in
    let named := Mote.string_value (Toml.table_get "name" sub) in
    let name : String := match named {
        Option.some n => n,
        Option.none => mote_name,
    } in
    let t : BinTarget := { path := path, name := name } in
    t

/// A table's string field, joined onto the mote's own directory so the
/// value is a path usable exactly as stored -- `raw_path_join`'s rules
/// for an empty `dir` and an absolute value included. Shared by the
/// manifest's `[lib] path` and `[[bin]] path` and the tool config's
/// `[build] target-dir`, which want it identically.
def Mote.joined_table_string (dir : String) (table : Option Toml.Value) (key : String) : Option String :=
    match Mote.table_string table key {
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
            // The lambda's parameter type is written; the field read needs
            // it, because `p.first` desugars to a bare `{ .. }` field-pattern
            // match. This replaced a monomorphic `def Pair.first` helper
            // (`mote.mo`'s own un-workaround, after the field-pattern fix),
            // and two spellings of that removal were tried and both fail --
            // worth recording, because this is the corpus's only site with
            // the shape. An UNANNOTATED lambda (`fn p => p.first`) leaves the
            // parameter a hole: `List.map`'s type variable is solved from its
            // SECOND argument, so the check of the first reports
            // `cannot resolve `{ .. }`: the matched value's type isn't known
            // here`. A GENERIC accessor passed as a value (`List.map
            // Pair.first`) keeps its own type variables unsolved at the call
            // and reports `type mismatch: expected (List ((Pair A) B)),
            // found (List String)`. Neither is the field-pattern bug.
            Toml.Value.table sub => List.map (fn (p : Pair String Toml.Value) => p.first) (BTreeMap.to_list sub),
            _ => List.empty
        }
    }

// ─── The installed toolchain root ────────────────────────────────────
//
// A mote in its own repository has no compiler checkout to resolve
// `init`/`std`/`runtime` from, so resolution needs one more anchor: the
// directory of an INSTALLED toolchain -- what `scripts/monadup` unpacks
// into `~/.monad/downloads/<tag>/` and marks active with `~/.monad/
// active`. This section discovers that directory.
//
// What consumes it is `module.mo` (module resolution), `lang/src/
// codegen/test/*` and `cli/src/main.mo` (the C runtime), so nothing here
// knows about modules or files beyond joining segments: `module.mo`
// imports THIS file, so the dependency cannot run the other way.
//
// Every function that touches the environment or the filesystem has its
// DECISION factored out into a pure one beside it. That is not style:
// there is no `set_env` native in this corpus and the test runner is one
// process, so a branch that reads an environment variable can only be
// exercised from outside it. The pure half is what a row can assert.

/// An environment variable's value, or the contents of a file that
/// carries one, reduced to `none` when there is nothing usable in it.
///
/// Two callers, one rule, and both halves of it are load-bearing.
/// `monadup` writes the active version with `echo "$tag" > "$active_file"`,
/// so those CONTENTS carry a trailing newline which must not survive into
/// a path: `downloads/nightly-1\n` is a directory that never exists, and
/// the failure mode of keeping it is a silent "no toolchain installed".
/// As an environment reader the same rule covers the other shape --
/// `MONAD_HOME=` in a shell that inherited the variable unset is the same
/// situation as not setting it, where a home named `""` would build every
/// candidate path one level off the working directory.
def non_empty_env (v : Option String) : Option String :=
    match v {
        Option.none => Option.none,
        Option.some s =>
            let t := String.trim s in
            if String.is_empty t then Option.none else Option.some t
    }

/// `<home>/downloads/<tag>` -- the version directory `monadup` installs a
/// tag into, and the only shape of a toolchain home this module assumes.
def Mote.version_dir (home : String) (tag : String) : String :=
    raw_path_join (raw_path_join home "downloads") tag

/// `<home>/.monad` -- the install root `scripts/monadup` uses when
/// `MONAD_HOME` says nothing (`${MONAD_HOME:-$HOME/.monad}`), and therefore
/// what an unset variable has to mean here too. Reading `$HOME` as the home
/// itself would look one level too high for `active` and one too high for
/// `downloads/`, i.e. find nothing on exactly the machines that installed a
/// nightly the ordinary way.
def Mote.monad_default_home (home : String) : String :=
    raw_path_join home ".monad"

/// Which home an installed toolchain lives under: `$MONAD_HOME` when it
/// is set -- monadup's own variable, and the one that makes the layout
/// testable against a fixture -- else `$HOME/.monad`. `none` when neither
/// is set: a process with no home has nowhere to look, and that is not an
/// error.
def Mote.toolchain_home_of (monad_home : Option String) (home : Option String) : Option String :=
    match non_empty_env monad_home {
        Option.some h => Option.some h,
        Option.none =>
            match non_empty_env home {
                Option.none => Option.none,
                Option.some h => Option.some (Mote.monad_default_home h)
            }
    }

/// The version directory an `active` file's contents name, or `none` when
/// they name no tag. Split out from the decision below so that the IO side
/// can probe exactly this ONE directory before committing to it.
def Mote.active_version_dir (home : String) (active : Option String) : Option String :=
    match non_empty_env active {
        Option.none => Option.none,
        Option.some tag => Option.some (Mote.version_dir home tag)
    }

/// The toolchain root under `home`, given the `active` file's raw contents
/// and whether the version directory they name exists.
///
/// Pure by construction -- both reads are arguments -- which is the whole
/// reason the layout is assertable from a unit row (see this section's
/// header on the missing `set_env` native).
///
/// `version_dir_exists` is worth checking: an `active` file naming a
/// version that has since been deleted (a hand `rm -rf`, `monadup clean`)
/// must resolve to NO toolchain rather than to a directory that is not
/// there, because a wrong root is worse than no root -- it produces
/// candidate paths that look plausible in a resolution error and open
/// nothing.
def Mote.toolchain_root_in_home (home : String) (active : Option String) (version_dir_exists : Bool) : Option String :=
    match Mote.active_version_dir home active {
        Option.none => Option.none,
        Option.some dir =>
            if version_dir_exists then Option.some dir else Option.none
    }

/// A file's contents, or `none` when it is not there at all (`not_found`)
/// -- "no `~/.monad/active`", "no `mote.toml` in this directory" are the
/// ordinary states every caller here probes for.
///
/// Any OTHER read failure is reported on stderr before it reads as
/// absent: the callers' own types (`Option MoteManifest`, a member list)
/// have no error channel, and an unreadable manifest must not pass
/// silently for a missing one.
pub def read_file_or_none (path : Path) : IO (Option String) := do {
    let r <- IO.read_file path;
    read_result_or_none path r
}

def read_result_or_none (path : Path) (r : Result StreamError String) : IO (Option String) :=
    match r {
        Result.ok text => IO.pure (Option.some text),
        Result.err e =>
            if StreamError.is_not_found e
            then IO.pure Option.none
            else do {
                IO.write_stderr ("error: reading " ++ Path.to_string path ++ ": " ++ e.message ++ "\n");
                return Option.none
            }
    }

/// `IO.is_dir` of a directory that may not have been named at all --
/// `false` when nothing named one, so a caller probes unconditionally.
/// `Path.path ""` would answer `false` too (`is_dir` on an empty path),
/// but only by accident of the native, which is not something to rely on.
def path_option_is_dir (p : Option String) : IO Bool := do {
    match p {
        Option.none => return false,
        Option.some dir => IO.is_dir (Path.path dir)
    }
}

/// Where an installed toolchain's mote sources live, if there is one.
///
/// `$MONAD_ROOT` first, honoured VERBATIM and deliberately neither
/// existence- nor shape-checked: an explicit variable is an instruction,
/// and a user who points it somewhere useless should get an ordinary
/// "unknown module" listing the candidate paths rather than a silent
/// fallback to a `~/.monad` they may not even have. It is also the one
/// root a test can install with nothing but a shell variable.
///
/// Otherwise monadup's install: `$MONAD_HOME` (default `$HOME/.monad`),
/// the tag its `active` file names, and `<home>/downloads/<tag>` -- which
/// IS existence-checked, because that one is a guess rather than an
/// instruction.
///
/// `none`, never an error: a development checkout has no `~/.monad`, and
/// resolution reads "no root" as "no candidates from this tier".
def Mote.toolchain_root : IO (Option String) := do {
    let root <- IO.get_env "MONAD_ROOT";
    match non_empty_env root {
        Option.some r => return (Option.some r),
        Option.none => Mote.toolchain_root_from_home
    }
}

/// The monadup half of `Mote.toolchain_root`, split out so that the
/// `$MONAD_ROOT` branch above reads as the one-line precedence rule it is.
def Mote.toolchain_root_from_home : IO (Option String) := do {
    let monad_home <- IO.get_env "MONAD_HOME";
    let home <- IO.get_env "HOME";
    match Mote.toolchain_home_of monad_home home {
        Option.none => return Option.none,
        Option.some h => do {
            let contents <- read_file_or_none (Path.path (raw_path_join h "active"));
            let dir_exists <- path_option_is_dir (Mote.active_version_dir h contents);
            return (Mote.toolchain_root_in_home h contents dir_exists)
        }
    }
}

/// The paths a toolchain root offers for one file, given as segments:
/// `Mote.toolchain_candidates root ["std", "src", "map.mo"]` is
/// `["<root>/std/src/map.mo"]`, and the same call with
/// `["runtime", "src", "runtime.c"]` is the C runtime.
///
/// A LIST of one rather than a bare `String`, because both callers splice
/// it into a candidate cascade they already have (`resolve_module_file`'s
/// miss tier, `resolve_runtime_src`'s list), and because segments keep the
/// `prelude` alias at the CALL SITE: `prelude` lives in `init`, so its
/// segments are `["init", "src", "prelude.mo"]`, and that special case
/// already belongs to `module.mo`'s `ambient_file`.
///
/// `raw_path_join` fold, not `++`, for the same reason
/// `MoteManifest.src_root` uses it: a relative root (`.`, which is what a
/// bare `monad check` produces) must still yield a path resolution can
/// open, and an absolute root must not acquire a prefix.
def Mote.toolchain_candidates (root : String) (segs : List String) : List String :=
    [join_segments root segs]

def join_segments (base : String) (segs : List String) : String :=
    match segs {
        List.empty => base,
        List.cons s rest => join_segments (raw_path_join base s) rest
    }

/// The line to print when an AMBIENT module (`prelude`/`init`/`std`) misses
/// because this machine has no usable toolchain root, or `none` when there
/// is nothing to say.
///
/// This is the out-of-the-box failure an external mote hits: with no
/// checkout above the working directory and no install, resolution has no
/// anchor for `init`/`std` at all, and what the user sees is one
/// `unresolved module:` line per module followed by a wall of `unknown
/// variable` for every name those modules would have provided -- none of
/// which names `monadup`, `MONAD_ROOT` or `MONAD_HOME`. Naming the three
/// ways out is the whole function.
///
/// Pure -- the root and whether that root carries the ambient motes are
/// both ARGUMENTS -- so the wording is assertable from a row and the IO
/// half is one caller (`lang/src/module.mo`'s `report_missing_toolchain`).
///
/// It takes both facts rather than the root alone because the two failure
/// shapes need different sentences: "no toolchain on this machine" is
/// answered by installing one, while "the root you pointed at has no
/// `init/src`" is answered by correcting it. Advice to install a toolchain
/// the user already has is worse than no advice, which is exactly what a
/// `root`-only signature could not avoid saying.
///
/// `root_has_sources` is not consulted for the `none` arm: a machine with
/// no root has nothing for it to describe.
def Mote.toolchain_missing_hint (root : Option String) (root_has_sources : Bool) : Option String :=
    match root {
        Option.none => Option.some (String.concat_all [
            "hint: this machine has no monad toolchain, and `init`/`std` come from one -- ",
            "`monadup install` (latest nightly), or point MONAD_ROOT at a monad checkout ",
            "(MONAD_HOME at an install home), or declare them as [dependencies.<name>] ",
            "path entries in mote.toml",
        ]),
        Option.some r =>
            if root_has_sources then Option.none
            else Option.some (String.concat "hint: MONAD_ROOT=" (String.concat r
                (String.concat_all [
                    " has no init/src -- point it at a monad checkout or an unpacked toolchain ",
                    "root (what `monadup` installs), or declare the motes as ",
                    "[dependencies.<name>] path entries in mote.toml",
                ])))
    }

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
    List.cons "name" (List.cons "deps" (List.cons "libs" (List.cons "pkg_config" List.empty)))

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
                link_pkgs := Mote.mote_attr_list attr "pkg_config",
                // An inline mote declares no targets: the annotation's own
                // file IS the binary, and `build` already takes a file.
                // `none`/empty rather than the conventional defaults, for
                // that reason -- `src/main.mo` would name a path it has no
                // `src/` tree to hold.
                lib_path := Option.none,
                bins := List.empty,
                // The inline annotation carries no `targets` key; it is a
                // target FILE, and profile availability is per declaration.
                targets := List.empty,
            } in
            Option.some m
    }

// ─── Tests ───

def mote_manifest_fixture : String :=
  "# a comment\n[mote]\nname = \"lang\"\nversion = \"0.1.2\"\n\n[lib]\npath = \"src/lib.mo\"\n\n[dependencies.init]\npath = \"../init\"\n\n[dependencies.std]\npath = \"../std\"\n"

// --- What a bare `monad check`/`monad test` covers ------------------
//
// `Mote.target_roots` answers it from the manifest's own declared targets.
// The rows below are the three manifest shapes that exist: a declared
// `[lib]`, a declared `[[bin]]` somewhere other than `src/`, and a
// manifest that declares neither and takes the conventional defaults. The
// fourth shape -- an inline mote, which declares no targets at all -- is
// the fallback row.
//
// A list of one string per row, compared by joining: `List.length` plus a
// `String.beq` per element reads worse than one comparison of the rendered
// list, and the rendering is what a reader can check against a manifest.

def roots_joined (roots : List String) : String :=
    match roots {
        List.empty => "",
        List.cons r rest =>
            if List.is_empty rest then r else String.concat r (String.concat "," (roots_joined rest)),
    }

/// A manifest that declares no targets at all, so the conventional
/// defaults are what `Mote.target_roots` has to work from.
def no_target_manifest_fixture : String :=
  "[mote]\nname = \"plain\"\nversion = \"0.1.0\"\n"

/// `[mote] targets` is parsed so the declaration is real data. Availability
/// itself is enforced per extern/native at codegen, not per mote.
#[test]
def test_parse_manifest_targets : Bool :=
    match Mote.parse_manifest "web_wasm" "[mote]\nname = \"web_wasm\"\nversion = \"0.1.0\"\ntargets = [\"web\"]\n" {
        Option.none => false,
        Option.some m => String.beq (roots_joined m.targets) "web",
    }

/// A declared `[lib] path = "src/lib.mo"` means the mote's sources are
/// under `src`, not under the whole mote directory.
#[test]
def test_target_roots_of_a_lib_manifest : Bool :=
    match Mote.parse_manifest "lang" mote_manifest_fixture {
        Option.none => false,
        Option.some m => String.beq (roots_joined (Mote.target_roots m "lang")) "lang/src",
    }

/// A `[[bin]]` outside `src/` is covered where it actually lives -- the
/// row that fails if the roots are hardcoded to `src`.
/// `two_bin_manifest_fixture` declares `src/main.mo` and
/// `src/bin/tool.mo`, so both roots appear and neither is invented.
#[test]
def test_target_roots_of_a_bin_outside_src : Bool :=
    match Mote.parse_manifest "cli" two_bin_manifest_fixture {
        Option.none => false,
        Option.some m => String.beq (roots_joined (Mote.target_roots m "cli")) "cli/src,cli/src/bin",
    }

/// A `[lib]` and a `[[bin]]` in the same directory (this repository's own
/// `cli/mote.toml`) is ONE root: the dedup is what keeps the same
/// directory from being walked twice.
#[test]
def test_target_roots_dedup_a_shared_directory : Bool :=
    match Mote.parse_manifest "cli" bin_manifest_fixture {
        Option.none => false,
        Option.some m => String.beq (roots_joined (Mote.target_roots m "cli")) "cli/src",
    }

/// A manifest that declares no targets still gets the conventional ones
/// (`src/lib.mo` and `src/main.mo`), which share that one root.
#[test]
def test_target_roots_of_the_conventional_defaults : Bool :=
    match Mote.parse_manifest "plain" no_target_manifest_fixture {
        Option.none => false,
        Option.some m => String.beq (roots_joined (Mote.target_roots m "plain")) "plain/src",
    }

/// A target at the mote root has no directory component, and `""` is not a
/// path a walk can be given -- `.` is.
#[test]
def test_target_roots_of_a_root_level_target : Bool :=
    String.beq (Mote.target_root_of "main.mo") "."

/// An inline mote declares no targets at all, so the fallback (the mote's
/// own directory) is the answer rather than an empty list -- an empty one
/// would make a bare command cover nothing and report success.
#[test]
def test_target_roots_falls_back_for_an_inline_mote : Bool :=
    match Mote.manifest_of_attr "examples" attr_mote_self_hosted {
        Option.none => false,
        Option.some m => String.beq (roots_joined (Mote.target_roots m "examples")) "examples",
    }

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

/// `[link] pkg-config` names where the libs live, beside the `libs` that
/// name what to link -- the shape `motes/tls` declares.
def link_pkg_config_manifest_fixture : String :=
  "[mote]\nname = \"tls\"\nversion = \"0.1.0\"\n\n[link]\nlibs = [\"ssl\", \"crypto\"]\npkg-config = [\"openssl\"]\n"

#[test]
def test_manifest_reads_link_pkg_config : Bool :=
    match Mote.parse_manifest "tls" link_pkg_config_manifest_fixture {
        Option.none => false,
        Option.some m =>
            match m.link_pkgs {
                List.empty => false,
                List.cons a rest => String.beq a "openssl" && List.is_empty rest,
            }
    }

/// `libs` without `pkg-config` resolves no packages: the link stays on the
/// toolchain's own search path, exactly as before the key existed.
#[test]
def test_manifest_link_libs_alone_has_no_pkg_config : Bool :=
    match Mote.parse_manifest "ffi" link_manifest_fixture {
        Option.none => false,
        Option.some m => match m.link_pkgs { List.empty => true, List.cons _ _ => false }
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

/// The `[[bin]]` target, which is what `monad build <mote dir>` builds.
/// Same shape as `cli/mote.toml` (spelled out as an array of tables).
def bin_manifest_fixture : String :=
  "[mote]\nname = \"cli\"\nversion = \"0.1.0\"\n\n[lib]\npath = \"src/lib.mo\"\n\n[[bin]]\nname = \"monad\"\npath = \"src/main.mo\"\n"

/// Two targets, which is what the singular `[bin]` spelling could not say.
def two_bin_manifest_fixture : String :=
  "[mote]\nname = \"cli\"\nversion = \"0.1.0\"\n\n[[bin]]\nname = \"app\"\npath = \"src/main.mo\"\n\n[[bin]]\nname = \"tool\"\npath = \"src/bin/tool.mo\"\n"

/// The `n`th bin target, or `none` past the end. Recursive rather than
/// `List.get` so the tests need no import this module does not already
/// carry.
def bin_target_at (bs : List BinTarget) (n : I64) : Option BinTarget :=
    match bs {
        List.empty => Option.none,
        List.cons b rest =>
            if I64.beq n 0 then Option.some b
            else bin_target_at rest (n - 1)
    }

#[test]
def test_manifest_reads_the_bin_target : Bool :=
    match Mote.parse_manifest "" bin_manifest_fixture {
        Option.none => false,
        Option.some m =>
            match m.bins {
                List.empty => false,
                List.cons b rest =>
                    if Bool.not (List.is_empty rest) then false
                    else if String.beq (BinTarget.target_path b) "src/main.mo"
                        then String.beq (BinTarget.target_name b) "monad"
                        else false
            }
    }

/// `[[bin]]` is an ARRAY: several targets, each with its own name and
/// path. The old singular model could not express this at all.
#[test]
def test_manifest_reads_several_bin_targets : Bool :=
    match Mote.parse_manifest "" two_bin_manifest_fixture {
        Option.none => false,
        Option.some m =>
            match bin_target_at m.bins 1 {
                Option.none => false,
                Option.some second =>
                    if Bool.not (String.beq (BinTarget.target_name second) "tool") then false
                    else match bin_target_at m.bins 2 {
                        Option.some _ => false,
                        Option.none => String.beq (BinTarget.target_path second) "src/bin/tool.mo"
                    }
            }
    }

/// A manifest with NO bin table still gets exactly one target -- the
/// conventional `src/main.mo`, named after the mote. That default is what
/// makes `monad build <mote>` work without a manifest edit; whether the
/// file is actually there is `build_target`'s check, not this one's.
#[test]
def test_manifest_without_a_bin_table_has_the_default_bin_target : Bool :=
    match Mote.parse_manifest "lang" mote_manifest_fixture {
        Option.none => false,
        Option.some m =>
            match m.bins {
                List.empty => false,
                List.cons b rest =>
                    if Bool.not (List.is_empty rest) then false
                    else if String.beq (BinTarget.target_path b) "lang/src/main.mo"
                        then String.beq (BinTarget.target_name b) "lang"
                        else false
            }
    }

/// A `[[bin]]` entry that names only a target still gets a PATH: the
/// conventional `src/main.mo`. The name and the path default
/// independently, which is what `package-system.md` §2a's sketch says.
#[test]
def test_bin_entry_without_a_path_defaults_to_main : Bool :=
    match Mote.parse_manifest "cli" "[mote]\nname = \"cli\"\n\n[[bin]]\nname = \"tool\"\n" {
        Option.none => false,
        Option.some m =>
            match bin_target_at m.bins 0 {
                Option.none => false,
                Option.some b =>
                    if String.beq (BinTarget.target_name b) "tool"
                    then String.beq (BinTarget.target_path b) "cli/src/main.mo"
                    else false
            }
    }

/// The library root is a PATH like the bin ones, defaulting to the
/// conventional `src/lib.mo` when `[lib]` is absent -- which is why the 12
/// motes this change adds a hub to need no manifest edit.
#[test]
def test_lib_path_defaults_to_src_lib : Bool :=
    match Mote.parse_manifest "lang" "[mote]\nname = \"lang\"\n" {
        Option.none => false,
        Option.some m => match m.lib_path {
            Option.none => false,
            Option.some p => String.beq p "lang/src/lib.mo"
        }
    }

/// A manifest declaring a library root that is NOT the default -- a different
/// directory and a different stem, so neither half of the convention can
/// answer by accident. No manifest in this repo has one, which is why the
/// fixture is written here rather than borrowed.
def declared_lib_manifest_fixture : String :=
  "[mote]\nname = \"lang\"\nversion = \"0.1.0\"\n\n[lib]\npath = \"lib/main.mo\"\n"

/// ...and a declared `[lib] path` wins over that default.
///
/// Against a NON-default path, necessarily: `mote_manifest_fixture` declares
/// `src/lib.mo`, which is what an absent `[lib]` already yields, so this test
/// read the same string whether the declaration was honoured or ignored.
#[test]
def test_lib_path_reads_the_declaration : Bool :=
    match Mote.parse_manifest "lang" declared_lib_manifest_fixture {
        Option.none => false,
        Option.some m => match m.lib_path {
            Option.none => false,
            Option.some p => String.beq p "lang/lib/main.mo"
        }
    }

/// `[[bin]] path` is joined like a dependency path, so `build` needs no
/// join of its own.
#[test]
def test_bin_target_path_is_joined_onto_the_mote_dir : Bool :=
    match Mote.parse_manifest "cli" bin_manifest_fixture {
        Option.none => false,
        Option.some m =>
            match m.bins {
                List.empty => false,
                List.cons b _ => String.beq (BinTarget.target_path b) "cli/src/main.mo"
            }
    }

/// The legacy singular `[bin]` spelling still means one target -- the
/// reader accepts both, so an external mote written against the old
/// spelling keeps resolving.
#[test]
def test_singular_bin_table_is_read_as_one_target : Bool :=
    match Mote.parse_manifest "cli" "[mote]\nname = \"cli\"\n\n[bin]\nname = \"monad\"\npath = \"src/main.mo\"\n" {
        Option.none => false,
        Option.some m =>
            match bin_target_at m.bins 0 {
                Option.none => false,
                Option.some b =>
                    if String.beq (BinTarget.target_name b) "monad"
                    then String.beq (BinTarget.target_path b) "cli/src/main.mo"
                    else false
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

/// The walk had no test of its own, and this is the step the bug was in:
/// `""` is both "the working directory" and "no directory component", so a
/// walk that ascended with `parent_of` stopped where it started. Same tree,
/// two answers -- a bare filename in a subdirectory found no config above
/// it, while the same file spelled `<sub>/file.mo` did.
///
/// The empty branch is pinned HERE, on the pure helper, rather than in the
/// IO row below, because reaching it needs the process's working directory
/// to be a directory that has no config of its own with one above it -- and
/// the test runner's is this checkout's root, which has one. There is no
/// `chdir` native to arrange otherwise, and a row that started anywhere
/// else would pass on the old code too.
#[test]
def test_config_dir_above_leaves_the_working_directory : Bool :=
    if String.beq (config_dir_above "") ".."
    then String.beq (config_dir_above ".") ".."
    else false

/// ...and keeps going once it is out, rather than bouncing back to the
/// working directory: `raw_parent_dir ".."` is `"."`, which would re-probe
/// the cwd forever, bounded only by the depth argument.
#[test]
def test_config_dir_above_keeps_going_above_the_working_directory : Bool :=
    if String.beq (config_dir_above "..") "../.."
    then String.beq (config_dir_above "../..") "../../.."
    else false

/// The ordinary case is undisturbed: a named directory still ascends by
/// `parent_of`, absolute paths included.
#[test]
def test_config_dir_above_still_steps_one_directory : Bool :=
    if String.beq (config_dir_above "examples") ""
    then if String.beq (config_dir_above "lang/src") "lang"
        then String.beq (config_dir_above "/home") "/"
        else false
    else false

/// What the ascent is FOR, read through the probe it feeds: the second
/// thing the walk looks at when it starts in the working directory is the
/// working directory's parent -- not the working directory again.
#[test]
def test_the_walk_probes_above_the_working_directory : Bool :=
    String.beq (tool_config_in (config_dir_above "")) "../.monad/config.toml"

/// The walk itself, over a tree this row writes: a file in a subdirectory
/// finds the config in the tree's root, and the answer is joined onto the
/// directory the config was FOUND in rather than onto the file's.
///
/// The tree's name carries the pid, like every other file a test writes
/// here: a fixed `/tmp/monad_cfgwalk` is one name shared by every
/// concurrent `monad test` on the machine, so a sibling run's leftover
/// config would satisfy this row even if its own write never happened -- and
/// the row would pass without having walked anything. The `rm` is the other
/// half of that: the tree is built from scratch, not merged into whatever a
/// previous run left at this pid.
///
/// `IO.write_file` does NOT create the directory it writes into (it fails
/// `not_found`), so `.monad/` is made explicitly beside `sub/deeper`. The
/// first version of this row made only `sub/deeper`, the write failed
/// unseen, and the walk was left with no config to find -- which reads
/// exactly like the walk being broken. The write's result is checked now.
#[test]
def test_discover_config_target_dir_walks_up_a_real_tree : IO Bool := do {
    let root := "/tmp/monad_cfgwalk_" ++ I64.to_string process_id;
    exec_cmd "rm" ["-rf", root];
    exec_cmd "mkdir" ["-p", root ++ "/sub/deeper", root ++ "/.monad"];
    let w <- IO.write_file (Path.path (root ++ "/.monad/config.toml")) "[build]\ntarget-dir = \"out\"\n";
    let found <- Mote.discover_config_target_dir (root ++ "/sub/deeper");
    return (Result.is_ok w && (match found {
        Option.none => false,
        Option.some d => String.beq d (root ++ "/out")
    }))
}

#[test]
def test_tool_config_in_names_the_root_and_the_cwd : Bool :=
    if String.beq (tool_config_in "") ".monad/config.toml"
    then if String.beq (tool_config_in "/") "/.monad/config.toml"
        then String.beq (tool_config_in "lang") "lang/.monad/config.toml"
        else false
    else false

/// The config's one setting, joined onto the config's own directory so the
/// answer is usable as stored -- the `raw_path_join` rule the manifest's
/// `[[bin]] path` follows. A relative value is relative to the `.monad/`
/// directory the config was found in, not to the CWD, which is what makes an
/// absolute invocation of a file inside the tree give an absolute directory.
#[test]
def test_config_target_dir_is_joined_onto_the_configs_directory : Bool :=
    match Mote.config_target_dir_of_text "lang" "[build]\ntarget-dir = \"target-monad\"\n" {
        Option.none => false,
        Option.some d => String.beq d "lang/target-monad"
    }

/// The empty-directory case: the config found in the working directory
/// itself, where the join must drop the empty component rather than produce
/// the ABSOLUTE `/target-monad`.
#[test]
def test_config_target_dir_of_the_working_directory_is_relative : Bool :=
    match Mote.config_target_dir_of_text "" "[build]\ntarget-dir = \"target-monad\"\n" {
        Option.none => false,
        Option.some d => String.beq d "target-monad"
    }

/// A config that names no directory answers `none`, which is what lets the
/// walk continue to the config above it rather than stopping at this one.
#[test]
def test_config_without_a_build_table_names_nothing : Bool :=
    match Mote.config_target_dir_of_text "" "# nothing but a comment\n" {
        Option.none => true,
        Option.some _ => false
    }

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

// ─── The installed toolchain root (tests) ────────────────────────────
//
// The IO half (`Mote.toolchain_root`) reads the process environment and
// cannot be driven from a row: there is no `set_env` native and the test
// runner is one process. Its DECISION is pure and is what these rows
// cover; the discovery half is covered from outside, by
// `scripts/check-external-mote.sh`'s `MONAD_ROOT=<tmp>` configuration and
// `scripts/monadup`'s fixture install.

/// The candidate list has exactly one element, and it is this -- asserts
/// the count as well as the path, since a second, wrong candidate is
/// exactly the kind of thing a "first existing wins" cascade must not
/// grow by accident.
def candidate_is (root : String) (segs : List String) (expected : String) : Bool :=
    match Mote.toolchain_candidates root segs {
        List.empty => false,
        List.cons p rest => match rest {
            List.empty => String.beq p expected,
            List.cons _ _ => false
        }
    }

/// The one shape of a `~/.monad` this module assumes, spelled out.
#[test]
def test_version_dir_is_the_monadup_layout : Bool :=
    String.beq (Mote.version_dir "/home/u/.monad" "nightly-2026-09-21")
              "/home/u/.monad/downloads/nightly-2026-09-21"

/// `monadup` writes the active tag with `echo`, so the file's contents end
/// in a newline. Keeping it names a directory that never exists, and the
/// failure mode is a silent "no toolchain" -- which is the kind of bug
/// this row exists to fail loudly instead.
#[test]
def test_active_tag_survives_the_trailing_newline : Bool :=
    match non_empty_env (Option.some "nightly-1\n") {
        Option.none => false,
        Option.some tag => String.beq tag "nightly-1"
    }

#[test]
def test_active_tag_rejects_whitespace_only : Bool :=
    match non_empty_env (Option.some "  \n\t") { Option.none => true, Option.some _ => false }

#[test]
def test_active_tag_of_no_file_is_none : Bool :=
    match non_empty_env Option.none { Option.none => true, Option.some _ => false }

/// `$MONAD_HOME` is monadup's own variable, so it wins over `$HOME`.
#[test]
def test_toolchain_home_prefers_monad_home : Bool :=
    match Mote.toolchain_home_of (Option.some "/mh") (Option.some "/home/u") {
        Option.none => false,
        Option.some h => String.beq h "/mh"
    }

/// The fallback is `$HOME/.monad`, NOT `$HOME`: that is monadup's own
/// default (`${MONAD_HOME:-$HOME/.monad}`), and it is the difference between
/// finding an ordinarily-installed nightly and looking one directory above
/// both `active` and `downloads/`. Getting this wrong fails silently -- an
/// installed toolchain simply never resolves.
#[test]
def test_toolchain_home_falls_back_to_dot_monad_under_home : Bool :=
    match Mote.toolchain_home_of Option.none (Option.some "/home/u") {
        Option.none => false,
        Option.some h => String.beq h "/home/u/.monad"
    }

/// `$HOME` with a trailing separator joins to the same place -- the join
/// owns the separator rule, so this row pins that the fallback composes it
/// rather than pasting `/`.monad` onto whatever it was handed.
#[test]
def test_toolchain_home_of_a_home_with_a_trailing_slash : Bool :=
    match Mote.toolchain_home_of Option.none (Option.some "/home/u/") {
        Option.none => false,
        Option.some h => String.beq h "/home/u/.monad"
    }

#[test]
def test_toolchain_home_of_neither_is_none : Bool :=
    match Mote.toolchain_home_of Option.none Option.none { Option.none => true, Option.some _ => false }

/// `MONAD_HOME=` -- set-but-empty is unset, or a home named `""` would put
/// every candidate path one level off.
#[test]
def test_toolchain_home_ignores_an_empty_monad_home : Bool :=
    match Mote.toolchain_home_of (Option.some "") (Option.some "/home/u") {
        Option.none => false,
        Option.some h => String.beq h "/home/u/.monad"
    }

/// The acceptance shape: `~/.monad/active` says `nightly-1` and
/// `~/.monad/downloads/nightly-1/` is there, so that directory is the root.
#[test]
def test_toolchain_root_of_an_active_version : Bool :=
    match Mote.toolchain_root_in_home "/home/u/.monad" (Option.some "nightly-1\n") true {
        Option.none => false,
        Option.some root => String.beq root "/home/u/.monad/downloads/nightly-1"
    }

/// A stale `active` naming a deleted download resolves to NOTHING rather
/// than to a path that is not there -- a wrong root is worse than no root,
/// because it makes a resolution error look plausible.
#[test]
def test_toolchain_root_requires_the_version_dir : Bool :=
    match Mote.toolchain_root_in_home "/home/u/.monad" (Option.some "nightly-1") false {
        Option.none => true,
        Option.some _ => false
    }

#[test]
def test_toolchain_root_without_an_active_file : Bool :=
    match Mote.toolchain_root_in_home "/home/u/.monad" Option.none true {
        Option.none => true,
        Option.some _ => false
    }

/// An `active` file that exists but names nothing is the same state as no
/// file at all.
#[test]
def test_toolchain_root_with_a_blank_active_file : Bool :=
    match Mote.toolchain_root_in_home "/home/u/.monad" (Option.some "\n") true {
        Option.none => true,
        Option.some _ => false
    }

/// `use std::map` from an installed toolchain -- the segment list
/// `resolve_module_file` actually builds.
#[test]
def test_toolchain_candidates_for_a_module : Bool :=
    candidate_is "/tc" ["std", "src", "map.mo"] "/tc/std/src/map.mo"

/// `prelude` is the one ambient module whose MOTE is not its name: it
/// lives in `init`, which the segments have to say.
#[test]
def test_toolchain_candidates_for_the_prelude_alias : Bool :=
    candidate_is "/tc" ["init", "src", "prelude.mo"] "/tc/init/src/prelude.mo"

#[test]
def test_toolchain_candidates_for_the_c_runtime : Bool :=
    candidate_is "/tc" ["runtime", "src", "runtime.c"] "/tc/runtime/src/runtime.c"

/// A bare invocation resolves the mote's directory as `"."`, and the
/// candidates built from it must still be openable paths -- which is
/// `raw_path_join`'s job, not `++`'s.
#[test]
def test_toolchain_candidates_from_a_relative_root : Bool :=
    candidate_is "." ["std", "src", "map.mo"] "./std/src/map.mo"

/// No segments is the fold's base case: the root itself, no trailing
/// separator. Keeps the caller from special-casing an empty head.
#[test]
def test_toolchain_candidates_with_no_segments : Bool :=
    candidate_is "/tc" [] "/tc"

/// The out-of-the-box failure, as a row: no root anywhere, so the hint has
/// to name all three ways out. Asserted on the three NAMES rather than the
/// sentence, because the point is that a user who has never installed a
/// toolchain learns what to type -- a rewording that keeps naming them is
/// still a pass.
#[test]
def test_missing_toolchain_hint_names_the_ways_out : Bool :=
    match Mote.toolchain_missing_hint Option.none false {
        Option.none => false,
        Option.some line =>
            if String.contains line "monadup"
            then (if String.contains line "MONAD_ROOT" then String.contains line "MONAD_HOME"
                  else false)
            else false
    }

/// A root that is there but has no `init/src` is a DIFFERENT sentence: the
/// name the user typed is what is wrong, so the hint repeats it back rather
/// than telling them to install what they already have.
#[test]
def test_missing_toolchain_hint_names_a_root_without_sources : Bool :=
    match Mote.toolchain_missing_hint (Option.some "/opt/monad") false {
        Option.none => false,
        Option.some line =>
            if String.contains line "/opt/monad"
            then Bool.not (String.contains line "monadup install")
            else false
    }

/// A root that carries the ambient motes is the working case: nothing to
/// say. (The caller reaches this arm only when a module resolved as ambient
/// failed, so a silent hint here means the failure had another cause and is
/// named by its own `unresolved module:` line.)
#[test]
def test_missing_toolchain_hint_is_silent_for_a_usable_root : Bool :=
    match Mote.toolchain_missing_hint (Option.some "/opt/monad") true {
        Option.none => true,
        Option.some _ => false
    }

// --- Affine policy tests -------------------------------------------

#[test]
def test_affine_mode_defaults_to_error_without_a_table : Bool :=
    match Mote.affine_mode_of_text "[mote]\nname = \"x\"\n" {
        AffineMode.affine_error => true,
        AffineMode.affine_warn => false,
    }

#[test]
def test_affine_mode_reads_warn : Bool :=
    match Mote.affine_mode_of_text "[affine]\nmode = \"warn\"\n" {
        AffineMode.affine_warn => true,
        AffineMode.affine_error => false,
    }

/// Only one spelling opts out. A typo must never silently weaken the
/// rule, so anything else -- including a word that looks like an off
/// switch -- is the strict default.
#[test]
def test_affine_mode_treats_unknown_values_as_error : Bool :=
    match Mote.affine_mode_of_text "[affine]\nmode = \"off\"\n" {
        AffineMode.affine_error => true,
        AffineMode.affine_warn => false,
    }
