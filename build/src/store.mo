/// Where build output goes, and what an entry in it is called.
///
/// Paths only -- this module decides names and answers "where", and does
/// not read or write anything. The I/O sits above it (phase 2a of
/// plans/packaging/mote-build-deps-artifacts-targets.md), which keeps
/// every naming rule here testable without touching a filesystem.

use std::io {}
use std::process {}
use std::stream {StreamError, StreamError.is_not_found}
use lang::module {extract_directory}
use lang::mote {Mote.discover_config_target_dir}

/// The three kinds of thing the store holds. One store rather than three
/// so that `clean`, `gc` and `verify` are written once; the kind is a
/// subdirectory, not a separate root.
pub type Entry {
    /// A compiled object or a linked binary.
    artifact,
    /// A `check` result: the rendered diagnostics, replayed verbatim on a
    /// hit. Cheap to store because `FileCheckResult.diagnostics` is
    /// already a list of fully-rendered strings (lang/src/module.mo) that
    /// `print_diagnostics` (cli/src/main.mo) just prints -- no spans are
    /// re-derived at print time, so a replay is byte-exact.
    check,
}

open Entry {artifact, check}

def Build.entry_dir (e : Entry) : String :=
    match e {
        artifact => "store",
        check => "check",
    }

/// `<target-dir>/<kind>`, for a kind spelled as a NAME rather than an
/// `Entry`.
///
/// The `test` cache uses this and not an `Entry` constructor, deliberately:
/// `Entry` has exactly two constructors and adding a third changed the
/// nullary tags enough that `entry_dir Entry.check` started answering
/// `"test"` in the self-hosted compiler (measured 2026-10-25, the compiler
/// binary itself: `dir_check=test dir_test=test dir_artifact=store`), which
/// silently moved every check entry into `test/`. A kind that is only ever
/// a directory name does not need a constructor to carry it.
pub def Build.entry_root_named (target_dir : String) (kind : String) : String :=
    String.concat target_dir (String.concat "/" kind)

/// Where artifacts go. Highest precedence first:
///
///   1. `--target-dir <dir>`      an explicit request wins outright
///   2. `MONAD_TARGET_DIR`        the environment
///   3. `.monad/config.toml`      `[build] target-dir`, the TOOL's config
///   4. `<root>/target`           the default
///
/// Four tiers rather than a bare default because a repository can hold more
/// than one toolchain. This one does, and its two outputs are named apart --
/// cargo's `rust/target/` beside monad's `target-monad/` -- rather than both
/// writing a shared `target/`, where `cargo clean` would delete monad's
/// store and `monad clean` cargo's artifacts.
///
/// Tier 3 reads the tool's own config, not the built mote's manifest. Where
/// output goes is not intrinsic to a mote: the same mote built by two
/// toolchains has no opinion on it, and a script-mode file under no mote at
/// all still needs an answer. So the repository states it once, in
/// `.monad/config.toml`, while a user with neither that file nor a
/// Cargo.toml gets the obvious plain `target/`.
///
/// Pure, and takes the env and config values as arguments rather than
/// reading them, so every tier is testable without a process environment
/// or a config file on disk.
pub def Build.resolve_target_dir (flag : String) (env : Option String) (config : Option String) (root : String) : String :=
    if Bool.not (String.is_empty flag) then flag
    else match env {
        Option.some e => if String.is_empty e then Build.target_dir_from_config config root else e,
        Option.none => Build.target_dir_from_config config root
    }

def Build.target_dir_from_config (config : Option String) (root : String) : String :=
    match config {
        Option.some m => if String.is_empty m then Build.default_target_dir root else m,
        Option.none => Build.default_target_dir root
    }

/// `<root>/target`, or plain `target` when the root is the working
/// directory. `raw_path_join`'s empty-component rule, spelled out here
/// because `root ++ "/target"` would produce the ABSOLUTE `/target` for
/// an empty root -- the same bug `MoteManifest.src_root`
/// (lang/src/mote.mo) documents for the mote whose manifest sits in the
/// working directory.
def Build.default_target_dir (root : String) : String :=
    if String.is_empty root then "target"
    else if String.beq root "." then "target"
    else String.concat root "/target"

/// The env tier, read once by a caller and passed into
/// `Build.resolve_target_dir`.
#[partial]
pub def Build.target_dir_of (flag : String) (config : Option String) (root : String) : IO String := do {
    let e <- IO.get_env "MONAD_TARGET_DIR";
    return (Build.resolve_target_dir flag e config root)
}

/// `<dir>`'s target directory: all four tiers of `resolve_target_dir`,
/// resolved from where `dir` sits in the tree.
///
/// `Mote.discover_config_target_dir`, not `Mote.discover`: the config is the
/// TOOL's, so the walk has no mote boundary to stop at -- and it must not,
/// because a script-mode file under a virtual workspace root (a root
/// declares no `[mote]`, so `Mote.discover` finds nothing there) would
/// otherwise never see the repository's `[build] target-dir` and would write
/// to plain `target/` instead of the directory it named. That is the exact
/// collision the setting exists to prevent.
#[partial]
pub def Build.target_dir_at (dir : String) : IO String := do {
    let d <- Mote.discover_config_target_dir dir;
    Build.target_dir_of "" d ""
}

/// The target directory for a SOURCE FILE, resolved from its directory.
#[partial]
pub def Build.target_dir_for (src : String) : IO String :=
    Build.target_dir_at (extract_directory src)

/// `<target-dir>/<kind>` -- the directory every entry of one kind lives
/// in, before the hash is appended. Shared by `ensure_entry_dir` and by
/// callers that make a directory PER ENTRY rather than per kind (the
/// `check` and `test` caches, whose entries are two files each).
pub def Build.entry_root_dir (target_dir : String) (e : Entry) : String :=
    Build.entry_root_named target_dir (Build.entry_dir e)

/// The name of one store entry: `<kind>/<hash>-<slug>`.
///
/// The hash comes first so the directory sorts by key rather than by
/// name, and the slug exists only so a human reading `ls` can tell what an
/// entry is. Nothing parses it back out -- the hash is the identity, and
/// the slug is allowed to be ambiguous.
///
/// **The artifact cache passes `""`.** It used to pass the output's bare
/// name, which quietly made the name an INPUT: a build under `-o a` could
/// not share with the same build under `-o b`, so one unchanged source
/// compiled twice. The name reached the artifact through the intermediate
/// `.ll` file, whose path `llc` records in the object it emits -- see
/// `artifact_ir_path` below, which is where that is fixed. With the IR
/// keyed, the artifact is a function of the key again and the entry name
/// can say so. The human-readable half belongs in `db/<hash>.json`, the
/// metadata kind the plan's layout reserves for exactly this.
pub def Build.store_path (target_dir : String) (e : Entry) (hash : String) (slug : String) : String :=
    String.concat target_dir
        (String.concat "/"
            (String.concat (Build.entry_dir e)
                (String.concat "/" (String.concat hash (Build.slug_suffix slug)))))

def Build.slug_suffix (slug : String) : String :=
    if String.is_empty slug then "" else String.concat "-" slug

/// `<target-dir>/store/<hash>.ll` -- the LLVM IR one artifact key compiles
/// from, and the file `llc` is actually pointed at.
///
/// The IR lives in the store under the KEY, and that is a correctness
/// requirement rather than tidiness. `llc` records the INPUT file's name
/// in the object it emits (an `STT_FILE` symbol, visible in the linked
/// binary's string table), so naming the IR after the user's `-o` puts the
/// output name inside the artifact -- which makes the artifact a function
/// of something that is not an input. Two builds of one source under two
/// `-o` names then differ by exactly one byte, and the whole point of a
/// cache -- hit as long as nothing important has changed -- fails for a
/// reason that has nothing to do with the source, the compiler, or the
/// profile.
///
/// Keying it fixes that by construction: the same key gives the same IR
/// path, so the same object, the same binary, and an entry that can be
/// named by the key alone. It also makes the IR safe to leave behind --
/// content-addressed, so the file a `cached:` line names is still the one
/// that build compiled, and an IR-reading gate can go and read it instead
/// of arranging an `-o` that spells its own path.
///
/// The `.ll` the caller's `-o` implies is still written beside the binary
/// (`link_ir`), as a convenience copy for exactly those readers. That copy
/// is an OUTPUT; it is never what `llc` compiles, or the leak returns.
pub def Build.artifact_ir_path (target_dir : String) (hash : String) : String :=
    String.concat (Build.entry_root_dir target_dir Entry.artifact)
        (String.concat "/" (String.concat hash ".ll"))

/// `mkdir -p` a directory. Shelled out because there is no mkdir native,
/// which is already how `llvm/src/link.mo` creates its own output
/// directory.
#[partial]
pub def Build.ensure_dir (d : String) : IO I64 := do {
    let r <- Proc.capture "sh" ["-c", String.concat "mkdir -p " (Proc.shell_quote d)];
    match r { Pair.pair code _out => return code }
}

/// A store leaf's text, or `none` when it is absent (`not_found`) -- the
/// ordinary miss. Any OTHER read failure is a miss too (a cache must not
/// stop a build), but it is reported on stderr rather than passing for an
/// absent entry: an unreadable store is something the user can fix.
pub def Build.read_leaf (path : Path) : IO (Option String) := do {
    let r <- IO.read_file path;
    Build.leaf_of_read path r
}

def Build.leaf_of_read (path : Path) (r : Result StreamError String) : IO (Option String) :=
    match r {
        Result.ok text => IO.pure (Option.some text),
        Result.err e =>
            if StreamError.is_not_found e
            then IO.pure Option.none
            else do {
                IO.write_stderr ("warning: build store: reading " ++ Path.to_string path ++ ": " ++ e.message ++ "\n");
                return Option.none
            }
    }

/// Write a store leaf; `false` after reporting the failure on stderr. A
/// failed write only costs the next run a miss, so the caller carries on.
pub def Build.write_leaf (path : Path) (text : String) : IO Bool := do {
    let r <- IO.write_file path text;
    Build.leaf_written path r
}

def Build.leaf_written (path : Path) (r : Result StreamError Unit) : IO Bool :=
    match r {
        Result.ok _ => IO.pure true,
        Result.err e => do {
            IO.write_stderr ("warning: build store: writing " ++ Path.to_string path ++ ": " ++ e.message ++ "\n");
            return false
        }
    }

/// `mkdir -p` the directory one KIND of entry lives in.
#[partial]
pub def Build.ensure_entry_dir (target_dir : String) (e : Entry) : IO I64 :=
    Build.ensure_dir (Build.entry_root_dir target_dir e)

def Build.non_blank (v : Option String) : Option String :=
    match v {
        Option.none => Option.none,
        Option.some s =>
            let t : String := String.trim s in
            if String.is_empty t then Option.none else Option.some t,
    }

/// `$MONAD_HOME` when set, else `$HOME/.monad` -- monadup's layout, so the
/// git cache lands beside the toolchain instead of somewhere of its own.
/// Blank counts as unset. `none` means a process with no home at all.
#[partial]
pub def Build.monad_home : IO (Option String) := do {
    let monad_home <- IO.get_env "MONAD_HOME";
    match Build.non_blank monad_home {
        Option.some h => return (Option.some h),
        Option.none => do {
            let home <- IO.get_env "HOME";
            match Build.non_blank home {
                Option.some h => return (Option.some (raw_path_join h ".monad")),
                Option.none => return Option.none,
            }
        }
    }
}

