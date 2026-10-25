/// The input hash: a mote, everything it declares, and the compiler.
///
/// This is the cache key. Every input that can change a result has to be
/// in it, and the ones that cannot must stay out -- a key that moves when
/// nothing meaningful moved costs a rebuild, but a key that DOESN'T move
/// when something did serves a stale answer, which is the failure a build
/// cache must not have.

use std::list {List.contains_by, List.intercalate, List.length}
use std::sha256 {Sha256.hash}
use lang::mote {
  Mote.discover, Mote.toolchain_root, Mote.workspace_members, MoteManifest,
}
use build::hash {
  Build.file_digest_with, Build.probe_digest_tool, Build.tree_digest_with,
  DigestTool,
}
use build::identity {Build.compiler_key_with}

/// The declared dependency directories of the mote at `dir`, paired with
/// its own name, or `none` when `dir` is not inside a mote.
///
/// Entries whose `path` was absent are skipped: `MoteManifest.dep_dirs`
/// stores `""` for a dependency that is DECLARED but not LOCATED
/// (lang/src/mote.mo says why that is legal), and there is nothing to
/// digest at an empty path.
#[partial]
def Build.mote_facts (dir : String) : IO (Option (Pair String (List String))) := do {
    let m <- Mote.discover dir;
    match m {
        Option.none => return Option.none,
        Option.some manifest =>
            return (Option.some (Pair.pair manifest.name (Build.located_dirs manifest.dep_dirs)))
    }
}

#[partial]
def Build.located_dirs (entries : List (Pair String String)) : List String :=
    match entries {
        List.empty => List.empty,
        List.cons e rest => List.append (Build.located_dir e) (Build.located_dirs rest)
    }

def Build.located_dir (e : Pair String String) : List String :=
    match e { Pair.pair _name d => if String.is_empty d then List.empty else [d] }

/// One line per mote: its NAME and its tree digest.
///
/// The name and not the directory, deliberately. The digest has to be
/// path-independent (see `Build.digest_script`), and putting the path
/// back in here would undo that -- two worktrees of the same commit
/// would key differently and could never share an entry.
def Build.closure_line (name : String) (digest : String) : String :=
    String.concat name (String.concat " " digest)

/// Digest a mote and its transitive declared dependencies.
///
/// **Cycles are real here, not hypothetical.** `init/mote.toml` declares
/// `std` as a DEV-dependency while `std/mote.toml` declares `init`, and
/// `MoteManifest` merges the two dependency tables into one `deps`/
/// `dep_dirs` pair (lang/src/mote.mo explains why it merges them), so
/// `init -> std -> init` is a genuine cycle in the graph this walks. The
/// visited set is load-bearing; without it this does not terminate.
///
/// Order is visit order, which is deterministic for a given root: the
/// frontier is extended from `dep_dirs`, which comes from
/// `BTreeMap.to_list` and is therefore sorted by mote name. Same root and
/// same manifests give the same order, which is all a key needs.
#[partial]
pub def Build.closure_digest_with (tool : DigestTool) (dir : String) : IO (Result String String) := do {
    let seed <- Build.closure_seed dir;
    let r <- Build.closure_walk tool seed List.empty List.empty;
    match r {
        err m => return (err m),
        ok parts => return (ok (Sha256.hash (List.intercalate "\n" parts)))
    }
}

/// What the walk starts from, in resolution's own precedence.
///
/// `resolve_module_file` tries CWD-relative candidates BEFORE it consults
/// any manifest, and the ambient pair is reachable that way whether or not
/// the mote declared it -- so a key built from the declared closure alone is
/// narrower than the compile it names. Measured on `examples/`: appending a
/// byte to `std/src/io.mo` moved no key at all, which is a false hit, the
/// one failure a build cache must not have.
///
/// Seeded AHEAD of `dir` so that the walk's name-keyed dedupe is what drops
/// the declared copy: the CWD-relative candidate is the file resolution
/// actually reads, and the key has to agree with the compiler about which
/// one that was.
///
/// A root with NO manifest has no declared closure to walk, so it widens to
/// the workspace it sits in. Coarse, and the only sound answer: such a file
/// states its dependencies in a `#![mote { ... }]` annotation, and an
/// annotation is a property of the FILE while this walk starts from a
/// directory.
#[partial]
pub def Build.closure_seed (dir : String) : IO (List String) := do {
    let cwd <- Build.cwd_ambient_dirs ["init", "std"];
    let tc <- Build.toolchain_seed cwd;
    let m <- Mote.discover dir;
    let members <- Build.workspace_seed m;
    return (List.append (List.append (List.append cwd tc) members) [dir])
}

/// The ambient motes the WORKING DIRECTORY offers, by the same probe
/// resolution accepts them with: `<name>/src/lib.mo`, the file the bare
/// `init`/`std` imports resolve to. A directory named `init` that carries no
/// sources is not a candidate, and must not shadow one that does.
#[partial]
def Build.cwd_ambient_dirs (names : List String) : IO (List String) :=
    match names {
        List.empty => return List.empty,
        List.cons n rest => do {
            let here <- IO.file_exists (Path.path (String.concat n "/src/lib.mo"));
            let tail <- Build.cwd_ambient_dirs rest;
            return (if here then (List.cons n tail) else tail)
        }
    }

/// Whether the resolved toolchain root has to be walked at all: only when
/// the working directory did NOT answer for the whole ambient pair.
///
/// `cwd` is `Build.cwd_ambient_dirs ["init", "std"]`, so two entries mean
/// `./init` and `./std` are what `resolve_module_file` will read and the
/// toolchain has nothing to do with this compile -- seeding it anyway
/// re-keys every entry in a dev checkout the night a nightly lands, for
/// sources nothing read.
///
/// Its own def, spelled as a literal `if`, because the polarity is the
/// whole content of it: the inline `not (len == 2)` this replaces had it
/// backwards in both directions at once -- a false hit where the local pair
/// is absent (the toolchain's `init`/`std` are read but unkeyed) and a
/// spurious re-key where it is present.
pub def Build.toolchain_seed_wanted (cwd : List String) : Bool :=
    if I64.beq (List.length cwd) 2 then false else true

/// The resolved toolchain root as a walk root, when the working directory
/// did not already answer for the ambient pair (`toolchain_seed_wanted`).
///
/// Seeded as a DIRECTORY, so what enters the key is its whole tree --
/// `init`, `std` and `runtime/src/runtime.c` included -- which is exactly
/// what the compile reads when the pair is not local. Probed by
/// `init/src/prelude.mo`, the file `toolchain_has_ambient_sources`
/// (lang/src/module.mo) uses for the same question, so this is not a
/// second opinion about what a root carries.
#[partial]
def Build.toolchain_seed (cwd : List String) : IO (List String) := do {
    if Build.toolchain_seed_wanted cwd then do {
        let root <- Mote.toolchain_root;
        match root {
            Option.none => return List.empty,
            Option.some r => do {
                let ok <- IO.file_exists (Path.path (String.concat r "/init/src/prelude.mo"));
                return (if ok then (List.cons r List.empty) else List.empty)
            }
        }
    } else return List.empty
}

/// A manifest-less root's stand-in for a declared closure: the workspace it
/// sits in. Empty for a root that HAS a manifest, whose declared closure is
/// the precise answer.
def Build.workspace_seed (m : Option MoteManifest) : IO (List String) :=
    match m {
        Option.none => Mote.workspace_members "",
        Option.some _ => do { return List.empty }
    }

#[partial]
def Build.closure_walk (tool : DigestTool) (pending : List String) (seen : List String) (acc : List String) : IO (Result String (List String)) :=
    match pending {
        List.empty => return (ok acc),
        List.cons d rest => Build.closure_consider tool d rest seen acc
    }

/// Identity is the mote NAME, not the directory string.
///
/// This is not a style preference, it is the difference between
/// terminating and not. `MoteManifest.dep_dirs` joins a dependency's
/// relative `path` onto the IMPORTER's own directory
/// (`raw_path_join mote_dir path`, lang/src/mote.mo:398), so walking a
/// cycle produces `<r>/a/../b`, then `<r>/a/../b/../a`, then
/// `<r>/a/../b/../a/../b` -- every hop a textually DIFFERENT string for
/// the same two motes. A visited set keyed on the path therefore never
/// matches and the walk recurses until the stack goes.
///
/// Found by `test_closure_terminates_on_a_cycle`, which overflowed the
/// interpreter's stack on the first run. The visited set was present and
/// looked sufficient; it was keyed on the wrong thing.
///
/// A mote name is unique within a closure by construction: two
/// directories claiming the same name is the version conflict
/// package-system's diamond rule already rejects. A directory outside any
/// mote keys on its path instead, which is safe because it contributes no
/// edges to follow.
def Build.closure_key (d : String) (facts : Option (Pair String (List String))) : String :=
    match facts {
        Option.some p => Build.facts_name p,
        Option.none => d,
    }

def Build.facts_name (p : Pair String (List String)) : String :=
    match p { Pair.pair name _deps => name }

def Build.facts_deps (p : Pair String (List String)) : List String :=
    match p { Pair.pair _name deps => deps }

#[partial]
def Build.closure_consider (tool : DigestTool) (d : String) (rest : List String) (seen : List String) (acc : List String) : IO (Result String (List String)) := do {
    let facts <- Build.mote_facts d;
    let key : String := Build.closure_key d facts;
    if List.contains_by String.beq key seen
    then Build.closure_walk tool rest seen acc
    else Build.closure_visit tool d rest seen acc key facts
}

#[partial]
def Build.closure_visit (tool : DigestTool) (d : String) (rest : List String) (seen : List String) (acc : List String) (key : String) (facts : Option (Pair String (List String))) : IO (Result String (List String)) := do {
    let dg <- Build.tree_digest_with tool d;
    match dg {
        err m => return (err m),
        ok h => match facts {
            // Not a mote: digest the tree, contribute it anonymously, and
            // walk no further. This is the bare-file case -- a script
            // module's directory has no manifest to read deps from.
            Option.none =>
                Build.closure_walk tool rest (List.cons key seen)
                    (List.append acc [Build.closure_line "" h]),
            Option.some p =>
                Build.closure_walk tool (List.append rest (Build.facts_deps p))
                    (List.cons key seen)
                    (List.append acc [Build.closure_line (Build.facts_name p) h])
        }
    }
}

/// The full input hash for a build: the source file's own bytes, its
/// mote's closure, the compiler that would compile it, the profile, and
/// the target triple.
///
/// `src` is a FILE and `root` is the mote directory it resolves to, i.e.
/// `Mote.mote_root_of src` -- the caller computes it because it needs it
/// for other things too, and both are needed here for different digests.
/// The file is not optional: a tree with no `mote.toml` anywhere above it
/// roots at its own directory, so every script-mode file in one directory
/// shares a root AND a closure digest, and a key without the file in it
/// serves the sibling's binary.
///
/// `profile` distinguishes a debug build from a release one; `triple` is the
/// resolved target, so one source holds one artifact per target built from it
/// and a `gc` has to spare all of them (`TargetSpec.keep_triples`).
///
/// An `err` from any digest propagates, and the caller's contract is to
/// DISABLE the cache on it rather than substitute a weaker key.
#[partial]
pub def Build.input_hash (src : String) (root : String) (profile : String) (triple : String) : IO (Result String String) := do {
    let t <- Build.probe_digest_tool;
    match t {
        err m => return (err m),
        ok tool => Build.input_hash_with tool src root profile triple
    }
}

/// The artifact key, composed from the digests it is made of.
///
/// Split out of `input_hash_with` so that a caller holding MANY files and
/// ONE compiler can take the expensive digests once: `input_hash_with`
/// takes the compiler's digest inside, and its digest is the running binary
/// (tens of megabytes), so deriving keys for a file set by calling it per
/// (file, profile) pair would digest that binary twice per file. `gc`
/// derives exactly such a set -- see `Build.collect_artifacts` in
/// `build/src/manage.mo`.
///
/// One formula, one place: `input_hash_with` is this with all three digests
/// taken inside, so the key a `build` writes and the key a `gc` derives
/// cannot drift apart.
pub def Build.artifact_key (file_digest : String) (closure : String) (compiler : String) (profile : String) (triple : String) : String :=
    Sha256.hash (List.intercalate "\n" [file_digest, closure, compiler, profile, triple])

#[partial]
pub def Build.input_hash_with (tool : DigestTool) (src : String) (root : String) (profile : String) (triple : String) : IO (Result String String) := do {
    let fd <- Build.file_digest_with tool src;
    match fd {
        err m => return (err m),
        ok f => do {
            let closure <- Build.closure_digest_with tool root;
            match closure {
                err m => return (err m),
                ok c => do {
                    let comp <- Build.compiler_key_with tool;
                    match comp {
                        err m => return (err m),
                        ok k => return (ok (Build.artifact_key f c k profile triple))
                    }
                }
            }
        }
    }
}
