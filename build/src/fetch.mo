// build / fetch -- `monad fetch` and `monad update`: resolve a mote's git
// dependencies into the content cache and write `mote.lock`.
//
// `monad fetch` is the only verb that touches the network (D6). It walks
// the dependency graph from the root manifest, resolves every git source
// to a full commit, checks it out under `<home>/cache/git/checkouts`, and
// records the commit AND the canonical tree checksum in `mote.lock`. A
// later `build`/`check`/`test` resolves from that lock and the cache and
// never speaks to git at all.
//
// The two verbs differ in one place only (`Build.planned_commit`): `fetch`
// keeps the commit an existing lock entry already names, so a tag that
// moved upstream does not silently change a locked build; `update`
// re-resolves every pin. Everything else -- the walk, the allowlist, the
// checkout, the checksum -- is shared, which is why they are one module.
//
// Nothing is written until the whole walk succeeds: a half-resolved
// closure in `mote.lock` would be worse than no lock at all.

use build::git {
  Git.available, Git.checkout, Git.checkout_dir, Git.db_dir, Git.ensure_mirror,
  Git.fetch, Git.missing_error, Git.prune, Git.resolve, Git.url_allowed, Git.url_error,
}
use build::hash {
  Build.canonical_tree_checksum_with, Build.probe_digest_tool, DigestTool,
}
use build::store {Build.monad_home}
use lang::lock {
  GitPin, Lock.pin_to_string, Lock.read, Lock.write, LockRead, LockedGit,
  LockedMote, Lockfile,
}
use lang::mote {Dependency, Mote.any_git_dep, Mote.discover, MoteManifest}
use std::io {IO.println}
use std::list {List.contains_by, List.filter, List.length}

/// `fetch` fills in what is missing; `update` re-resolves every pin.
pub type FetchMode {
    fetch,
    update,
}

/// The walk's whole state: what has been resolved, what has been visited,
/// and the home/tooling every step needs. A value threaded through the
/// recursion rather than mutable state, the shape `Build.closure_walk`
/// already uses. `seen` is what terminates the walk on a cycle, and it is
/// keyed on the mote NAME for the reason `Build.closure_key` gives: two
/// paths to one mote are textually different strings.
struct FetchState {
    home : String,
    mode : FetchMode,
    /// `--offline`: never run a network git command. The mirror and the
    /// checkout must already be there, or the verb fails naming the URL.
    offline : Bool,
    tool : DigestTool,
    existing : List LockedMote,
    seen : List String,
    entries : List LockedMote,
}

// ─── Small pure pieces ───

/// The manifest's `tag`/`branch`/`rev` triple as the lock's pin, and none
/// of them as the remote HEAD. The parser refuses more than one, so the
/// precedence here only decides what a malformed entry would pick -- and a
/// malformed entry never reaches this (its error is in `dep_errors`).
pub def Build.pin_of_dep (tag : Option String) (branch : Option String) (rev : Option String) : GitPin :=
    match tag {
        Option.some t => GitPin.tag t,
        Option.none => match branch {
            Option.some b => GitPin.branch b,
            Option.none => match rev {
                Option.some r => GitPin.rev r,
                Option.none => GitPin.head,
            }
        }
    }

/// `git_subdir` becomes a path, so it is checked before it is joined: a
/// `..` component or an absolute path would let a manifest point outside
/// the checkout it just fetched.
pub def Build.safe_subdir (subdir : Option String) : Result String (Option String) :=
    match subdir {
        Option.none => Result.ok Option.none,
        Option.some s =>
            if Build.subdir_is_safe s
            then Result.ok (Option.some s)
            else Result.err ("unsafe git `subdir` `" ++ s ++ "`: it must be a relative path inside the checkout")
    }

def Build.subdir_is_safe (s : String) : Bool :=
    Bool.not (String.is_empty s)
        && Bool.not (String.starts_with "/" s)
        && Bool.not (String.contains s "../")
        && Bool.not (String.ends_with s "/..")
        && Bool.not (String.beq s "..")
        && Bool.not (String.contains s "\\")

/// The commit an existing lock entry already pins for `url` under `pin`,
/// if any. This is what makes a moved tag harmless: the lock names a
/// commit, and `fetch` keeps it.
def Build.locked_commit (existing : List LockedMote) (url : String) (pin : GitPin) : Option String :=
    match existing {
        List.empty => Option.none,
        List.cons e rest => match e.git {
            Option.none => Build.locked_commit rest url pin,
            Option.some g =>
                if String.beq g.url url && String.beq (Lock.pin_to_string g.pin) (Lock.pin_to_string pin)
                then Option.some g.commit
                else Build.locked_commit rest url pin
        }
    }

/// The mote's directory inside a checkout: the subdir when there is one.
def Build.mote_dir_of (checkout : String) (subdir : Option String) : String :=
    match subdir {
        Option.none => checkout,
        Option.some s => raw_path_join checkout s,
    }

/// Same name, different source: `package-system` §2b's conflict. Checked
/// against the entries this walk has resolved, so the message can name
/// both sides.
def Build.entry_conflict (entries : List LockedMote) (name : String) (url : String) (commit : String) : Option String :=
    match entries {
        List.empty => Option.none,
        List.cons e rest =>
            if String.beq e.name name
            then Build.conflict_at e url commit
            else Build.entry_conflict rest name url commit
    }

def Build.conflict_at (e : LockedMote) (url : String) (commit : String) : Option String :=
    match e.git {
        Option.none => Option.none,
        Option.some g =>
            if String.beq g.url url && String.beq g.commit commit
            then Option.none
            else Option.some ("mote `" ++ e.name ++ "` is required at two different sources (`"
                ++ g.url ++ "@" ++ g.commit ++ "` and `" ++ url ++ "@" ++ commit ++ "`)")
    }

// ─── The verb ───

/// `monad fetch` / `monad update` for the mote containing `dir`. Answers
/// the process exit status, and prints its own diagnostics.
#[partial]
pub def Build.fetch_run (dir : String) (mode : FetchMode) (offline : Bool) : IO I64 := do {
    let home <- Build.monad_home;
    match home {
        Option.none => do {
            IO.println "error: MONAD_HOME and HOME are unset; there is nowhere to cache git dependencies";
            return 1
        },
        Option.some h => Build.fetch_run_with_opts h dir mode offline
    }
}

/// `fetch_run` with the cache root given, so a test can keep its cache in
/// a fixture directory instead of the user's `~/.monad`.
#[partial]
pub def Build.fetch_run_with (home : String) (dir : String) (mode : FetchMode) : IO I64 :=
    Build.fetch_run_with_opts home dir mode false

#[partial]
pub def Build.fetch_run_with_opts (home : String) (dir : String) (mode : FetchMode) (offline : Bool) : IO I64 := do {
    let found <- Mote.discover dir;
    match found {
        Option.none => do {
            IO.println ("error: no `mote.toml` at or above `" ++ dir ++ "`: `monad fetch` resolves a mote's dependencies, so it needs one");
            return 1
        },
        Option.some root => Build.fetch_with home root mode offline
    }
}

#[partial]
def Build.fetch_with (home : String) (root : MoteManifest) (mode : FetchMode) (offline : Bool) : IO I64 := do {
    let ok <- Git.available;
    if Bool.not ok then do {
        IO.println ("error: " ++ Git.missing_error);
        return 1
    } else do {
        let tool <- Build.probe_digest_tool;
        match tool {
            Result.err m => do { IO.println ("error: " ++ m); return 1 },
            Result.ok t => Build.fetch_locked home root mode offline t
        }
    }
}

#[partial]
def Build.fetch_locked (home : String) (root : MoteManifest) (mode : FetchMode) (offline : Bool) (tool : DigestTool) : IO I64 := do {
    let lock_path : String := raw_path_join root.dir "mote.lock";
    let read <- Lock.read (Path.path lock_path);
    match read {
        Result.err m => do { IO.println ("error: " ++ m); return 1 },
        Result.ok found => Build.fetch_start home root mode offline tool lock_path found
    }
}

#[partial]
def Build.fetch_start (home : String) (root : MoteManifest) (mode : FetchMode) (offline : Bool) (tool : DigestTool) (lock_path : String) (found : Option LockRead) : IO I64 := do {
    let existing <- Build.existing_entries found;
    let st : FetchState := {
        home := home,
        mode := mode,
        offline := offline,
        tool := tool,
        existing := existing,
        seen := List.empty,
        entries := List.empty,
    };
    let walked <- Build.visit_manifest st root;
    match walked {
        Result.err m => do { IO.println ("error: " ++ m); return 1 },
        Result.ok done => Build.write_fetch_lock lock_path done
    }
}

/// An unknown `version` is a warning and a fresh start, never a parse
/// failure -- the package-system lockfile-versioning rule.
#[partial]
def Build.existing_entries (found : Option LockRead) : IO (List LockedMote) :=
    match found {
        Option.none => return List.empty,
        Option.some r => match r {
            LockRead.loaded lock => return lock.motes,
            LockRead.unsupported v => do {
                IO.println ("warning: `mote.lock` has version " ++ I64.to_string v ++ ", which this monad does not understand; regenerating it");
                return List.empty
            }
        }
    }

// ─── The walk ───

/// Visit one mote: skip it when it has been seen (a cycle, or a second
/// path to the same mote), otherwise mark it and resolve its declared
/// dependencies.
#[partial]
#[terminating]
def Build.visit_manifest (st : FetchState) (m : MoteManifest) : IO (Result String FetchState) :=
    if List.contains_by String.beq m.name st.seen
    then return (Result.ok st)
    else do {
        let seen : List String := List.cons m.name st.seen;
        let st2 : FetchState := { st with seen := seen };
        Build.fetch_deps st2 m.deps_full
    }

/// A directory's manifest, if it has one. A `path` dependency is walked
/// for the same reason the root is: it may itself declare git sources.
#[partial]
#[terminating]
def Build.visit_dir (st : FetchState) (dir : String) : IO (Result String FetchState) := do {
    let found <- Mote.discover dir;
    match found {
        Option.none => return (Result.ok st),
        Option.some manifest => Build.visit_manifest st manifest
    }
}

#[partial]
#[terminating]
def Build.fetch_deps (st : FetchState) (deps : List (Pair String Dependency)) : IO (Result String FetchState) :=
    match deps {
        List.empty => return (Result.ok st),
        List.cons d rest => Build.fetch_dep st d rest
    }

#[partial]
#[terminating]
def Build.fetch_dep (st : FetchState) (d : Pair String Dependency) (rest : List (Pair String Dependency)) : IO (Result String FetchState) :=
    match d {
        Pair.pair key dep => Build.dep_source st key dep rest
    }

#[partial]
#[terminating]
def Build.dep_source (st : FetchState) (key : String) (dep : Dependency) (rest : List (Pair String Dependency)) : IO (Result String FetchState) :=
    match dep {
        Dependency.path dir => do {
            let walked <- Build.visit_dir st dir;
            match walked {
                Result.err e => return (Result.err e),
                Result.ok st2 => Build.fetch_deps st2 rest
            }
        },
        Dependency.registry _ => Build.fetch_deps st rest,
        Dependency.git url tag branch rev subdir =>
            Build.fetch_git_dep st key url tag branch rev subdir rest
    }

#[partial]
#[terminating]
def Build.fetch_git_dep (st : FetchState) (key : String) (url : String) (tag : Option String) (branch : Option String) (rev : Option String) (subdir : Option String) (rest : List (Pair String Dependency)) : IO (Result String FetchState) :=
    if Bool.not (Git.url_allowed url)
    then return (Result.err (Git.url_error url))
    else match Build.safe_subdir subdir {
        Result.err e => return (Result.err e),
        Result.ok safe =>
            Build.fetch_remote st key url (Build.pin_of_dep tag branch rev) safe rest
    }

#[partial]
#[terminating]
def Build.fetch_remote (st : FetchState) (key : String) (url : String) (pin : GitPin) (subdir : Option String) (rest : List (Pair String Dependency)) : IO (Result String FetchState) := do {
    let locked := Build.planned_commit st.existing st.mode url pin;
    match locked {
        Result.err e => return (Result.err e),
        Result.ok maybe => Build.fetch_mirror st key url pin subdir maybe rest
    }
}

/// `update` always re-resolves; `fetch` keeps a commit the lock already
/// names for this exact `(url, pin)`.
def Build.planned_commit (existing : List LockedMote) (mode : FetchMode) (url : String) (pin : GitPin) : Result String (Option String) :=
    match mode {
        FetchMode.update => Result.ok Option.none,
        FetchMode.fetch => Result.ok (Build.locked_commit existing url pin),
    }

#[partial]
#[terminating]
def Build.fetch_mirror (st : FetchState) (key : String) (url : String) (pin : GitPin) (subdir : Option String) (locked : Option String) (rest : List (Pair String Dependency)) : IO (Result String FetchState) :=
    if st.offline
    then Build.fetch_offline st key url pin subdir locked rest
    else do {
        let mirrored <- Git.ensure_mirror st.home url;
        match mirrored {
            Result.err e => return (Result.err e),
            Result.ok db => Build.fetch_synced db st key url pin subdir locked rest
        }
    }

/// `--offline`: use the mirror as it stands. No `init`, no `fetch` --
/// resolution still runs `update-ref`/`cat-file`, which are local, so a
/// missing mirror or ref is a named error rather than a silent network
/// call.
#[partial]
def Build.fetch_offline (st : FetchState) (key : String) (url : String) (pin : GitPin) (subdir : Option String) (locked : Option String) (rest : List (Pair String Dependency)) : IO (Result String FetchState) := do {
    let db : String := Git.db_dir st.home url;
    let there <- IO.is_dir (Path.path db);
    if Bool.not there
    then return (Result.err ("--offline: `" ++ url ++ "` (for `" ++ key ++ "`) is not in the git cache; run `monad fetch` once with network access"))
    else Build.fetch_pinned db st key url pin subdir locked rest
}

#[partial]
#[terminating]
def Build.fetch_synced (db : String) (st : FetchState) (key : String) (url : String) (pin : GitPin) (subdir : Option String) (locked : Option String) (rest : List (Pair String Dependency)) : IO (Result String FetchState) := do {
    let fetched <- Git.fetch db url;
    match fetched {
        Result.err e => return (Result.err e),
        Result.ok _ => Build.fetch_pinned db st key url pin subdir locked rest
    }
}

#[partial]
#[terminating]
def Build.fetch_pinned (db : String) (st : FetchState) (key : String) (url : String) (pin : GitPin) (subdir : Option String) (locked : Option String) (rest : List (Pair String Dependency)) : IO (Result String FetchState) :=
    match locked {
        Option.some commit => Build.fetch_checkout db st key url pin subdir commit rest,
        Option.none => do {
            let resolved <- Git.resolve db pin;
            match resolved {
                Result.err e => return (Result.err e),
                Result.ok commit => Build.fetch_checkout db st key url pin subdir commit rest
            }
        }
    }

#[partial]
#[terminating]
def Build.fetch_checkout (db : String) (st : FetchState) (key : String) (url : String) (pin : GitPin) (subdir : Option String) (commit : String) (rest : List (Pair String Dependency)) : IO (Result String FetchState) := do {
    let co : String := Git.checkout_dir st.home url commit;
    let sound <- Build.checkout_is_sound st.tool st.existing key commit (Build.mote_dir_of co subdir);
    let _repaired <- if sound then IO.pure (Result.ok Unit.unit) else Build.drop_checkout db co;
    Build.fetch_checkout_at db st key url pin subdir co commit rest
}

#[partial]
def Build.fetch_checkout_at (db : String) (st : FetchState) (key : String) (url : String) (pin : GitPin) (subdir : Option String) (co : String) (commit : String) (rest : List (Pair String Dependency)) : IO (Result String FetchState) := do {
    let checked <- Git.checkout db co commit;
    match checked {
        Result.err e => return (Result.err e),
        Result.ok _ => Build.fetch_dep_manifest st key url pin subdir co commit rest
    }
}

/// Whether a cached checkout still hashes to what the lock records for
/// that same commit. `true` when the lock says nothing (a first fetch, or
/// a different commit, whose checkout is a different path anyway).
///
/// This is what makes `monad fetch` REPAIR a corrupted cache instead of
/// blessing it: without it the walk would hash the tampered tree and
/// write that checksum into the lock, which is the one thing a lock must
/// never do.
#[partial]
def Build.checkout_is_sound (tool : DigestTool) (existing : List LockedMote) (key : String) (commit : String) (dir : String) : IO Bool :=
    match Build.recorded_sum existing key commit {
        Option.none => return true,
        Option.some want => do {
            let sum <- Build.canonical_tree_checksum_with tool (Path.path dir);
            match sum {
                Result.err _ => return false,
                Result.ok got => return (String.beq got want)
            }
        }
    }

/// The checksum the lock records for `key` at exactly `commit`.
#[partial]
def Build.recorded_sum (entries : List LockedMote) (key : String) (commit : String) : Option String :=
    match entries {
        List.empty => Option.none,
        List.cons e rest => match e.git {
            Option.none => Build.recorded_sum rest key commit,
            Option.some g =>
                if String.beq e.name key && String.beq g.commit commit
                then Option.some e.checksum
                else Build.recorded_sum rest key commit
        }
    }

/// Remove a bad checkout, and the mirror's `worktrees/` entry for it so
/// `git worktree add` can take the path again.
#[partial]
def Build.drop_checkout (db : String) (co : String) : IO (Result String Unit) := do {
    let _rm <- Proc.capture "rm" ["-rf", co];
    Git.prune db
}

#[partial]
#[terminating]
def Build.fetch_dep_manifest (st : FetchState) (key : String) (url : String) (pin : GitPin) (subdir : Option String) (co : String) (commit : String) (rest : List (Pair String Dependency)) : IO (Result String FetchState) := do {
    let mote_dir : String := Build.mote_dir_of co subdir;
    let found <- Mote.discover mote_dir;
    match found {
        Option.none => return (Result.err ("no `mote.toml` in the checkout of " ++ url ++ " at `" ++ mote_dir ++ "`")),
        Option.some manifest => Build.fetch_sum st key url pin subdir commit mote_dir manifest rest
    }
}

/// The checksum covers the mote's directory -- the `git_subdir` when there
/// is one -- which is exactly what `package-system` §2b says it covers, so
/// a registry tarball of the same source would agree.
#[partial]
#[terminating]
def Build.fetch_sum (st : FetchState) (key : String) (url : String) (pin : GitPin) (subdir : Option String) (commit : String) (mote_dir : String) (manifest : MoteManifest) (rest : List (Pair String Dependency)) : IO (Result String FetchState) := do {
    let sum <- Build.canonical_tree_checksum_with st.tool (Path.path mote_dir);
    match sum {
        Result.err e => return (Result.err e),
        Result.ok checksum => Build.fetch_record st key url pin subdir commit manifest checksum rest
    }
}

#[partial]
#[terminating]
def Build.fetch_record (st : FetchState) (key : String) (url : String) (pin : GitPin) (subdir : Option String) (commit : String) (manifest : MoteManifest) (checksum : String) (rest : List (Pair String Dependency)) : IO (Result String FetchState) := do {
    // The lock is looked up by the KEY the importer names in `use`,
    // which is what resolution knows; the dependency's own manifest
    // supplies only its version.
    let name : String := key;
    let conflict : Option String := Build.entry_conflict st.entries name url commit;
    match conflict {
        Option.some m => return (Result.err m),
        Option.none =>
            if Build.mentions st.entries name
            then Build.fetch_deps st rest
            else Build.record_new st name url pin subdir commit manifest checksum rest
    }
}

#[partial]
#[terminating]
def Build.record_new (st : FetchState) (name : String) (url : String) (pin : GitPin) (subdir : Option String) (commit : String) (manifest : MoteManifest) (checksum : String) (rest : List (Pair String Dependency)) : IO (Result String FetchState) := do {
    let git : LockedGit := { url := url, pin := pin, commit := commit, subdir := subdir };
    let entry : LockedMote := { name := name, version := manifest.version, checksum := checksum, git := Option.some git };
    IO.println ("fetched " ++ name ++ " " ++ commit);
    // The entry is recorded BEFORE the visit, but `seen` is deliberately
    // left alone: `visit_manifest` is what marks the mote visited, and it
    // skips a name it already knows. Marking it here would make the
    // dependency's OWN git dependencies invisible.
    let st2 : FetchState := { st with entries := List.append st.entries [entry] };
    let walked <- Build.visit_manifest st2 manifest;
    match walked {
        Result.err e => return (Result.err e),
        Result.ok st3 => Build.fetch_deps st3 rest
    }
}

// ─── Writing the lock ───

/// The resolved git entries, plus every existing NON-git entry this walk
/// does not claim -- a registry entry written by a future resolver must
/// not be erased by a `fetch` that only knows about git.
#[partial]
def Build.write_fetch_lock (lock_path : String) (st : FetchState) : IO I64 := do {
    let kept : List LockedMote := List.filter (Build.keep_existing st.entries) st.existing;
    let lock : Lockfile := { motes := List.append kept st.entries };
    let wrote <- Lock.write (Path.path lock_path) lock;
    match wrote {
        Result.err e => do { IO.println ("error: " ++ e); return 1 },
        Result.ok _ => do {
            IO.println ("wrote " ++ lock_path ++ " (" ++ I64.to_string (List.length st.entries) ++ " entries)");
            return 0
        }
    }
}

def Build.keep_existing (resolved : List LockedMote) (e : LockedMote) : Bool :=
    match e.git {
        Option.some _ => false,
        Option.none => Bool.not (Build.mentions resolved e.name)
    }

def Build.mentions (entries : List LockedMote) (name : String) : Bool :=
    match entries {
        List.empty => false,
        List.cons e rest => String.beq e.name name || Build.mentions rest name
    }

// ─── Verifying the lock ───
//
// Run by `build`, `check` and `test` before they compile anything. The
// build never rewrites a lock, so this is the only thing standing between
// a dependency that changed under its pin and a binary built from it.

/// Check `mote.lock` against the manifest in `dir`, for every git
/// dependency it declares: an entry exists for the dependency's KEY and
/// URL, the checkout is on disk, and its canonical tree checksum is the
/// one the lock records.
///
/// `locked` adds one check -- the manifest's pin must still be what the
/// lock records (`Build.pin_matches`) -- and changes the wording of a
/// missing entry, because `--locked` says the lock is stale while the
/// default advice is `monad fetch`. Nothing else differs, because there is
/// no mode in which this tool silently rewrites a lock.

/// Verify a manifest the caller already has -- the verb-side pre-flight
/// resolves targets once and must not read every manifest twice.
#[partial]
pub def Build.verify_manifest (m : MoteManifest) (locked : Bool) : IO (Result String Unit) := do {
    let home <- Build.monad_home;
    match home {
        Option.none => return (Result.err ("`" ++ m.name ++ "` declares git dependencies but MONAD_HOME and HOME are unset; there is no cache to verify against")),
        Option.some h => Build.verify_manifest_at h m locked
    }
}

/// `verify_manifest` with the cache root given -- the test suite's way in,
/// for the reason `with_locked_dirs_at` gives.
#[partial]
pub def Build.verify_manifest_at (home : String) (m : MoteManifest) (locked : Bool) : IO (Result String Unit) :=
    Build.verify_home home m locked

#[partial]
def Build.verify_home (home : String) (m : MoteManifest) (locked : Bool) : IO (Result String Unit) := do {
    if Bool.not (Mote.any_git_dep m.deps_full)
    then return (Result.ok Unit.unit)
    else do {
    let read <- Lock.read (Path.path (raw_path_join m.dir "mote.lock"));
    match read {
        Result.err e => return (Result.err e),
        Result.ok found => Build.verify_entries home locked found m.deps_full
    }
    }
}

#[partial]
def Build.verify_entries (home : String) (locked : Bool) (found : Option LockRead) (deps : List (Pair String Dependency)) : IO (Result String Unit) := do {
    let entries : List LockedMote := match found {
        Option.none => List.empty,
        Option.some r => match r {
            LockRead.loaded l => l.motes,
            LockRead.unsupported _ => List.empty
        }
    };
    let tool <- Build.probe_digest_tool;
    match tool {
        Result.err e => return (Result.err e),
        Result.ok t => Build.verify_deps home t entries locked deps
    }
}

#[partial]
def Build.verify_deps (home : String) (tool : DigestTool) (entries : List LockedMote) (locked : Bool) (deps : List (Pair String Dependency)) : IO (Result String Unit) :=
    match deps {
        List.empty => return (Result.ok Unit.unit),
        List.cons d rest => match d {
            Pair.pair key dep => Build.verify_dep home tool entries locked key dep rest
        }
    }

#[partial]
def Build.verify_dep (home : String) (tool : DigestTool) (entries : List LockedMote) (locked : Bool) (key : String) (dep : Dependency) (rest : List (Pair String Dependency)) : IO (Result String Unit) :=
    match dep {
        Dependency.git url tag branch rev subdir =>
            Build.verify_git home tool entries locked key url (Build.pin_of_dep tag branch rev) subdir rest,
        _ => Build.verify_deps home tool entries locked rest,
    }

#[partial]
def Build.verify_git (home : String) (tool : DigestTool) (entries : List LockedMote) (locked : Bool) (key : String) (url : String) (pin : GitPin) (subdir : Option String) (rest : List (Pair String Dependency)) : IO (Result String Unit) :=
    match Build.entry_for entries key url {
        Option.none => return (Result.err (Build.missing_entry_error locked key url)),
        Option.some e => match e.git {
            Option.none => return (Result.err (Build.missing_entry_error locked key url)),
            Option.some g =>
                if locked && Bool.not (Build.pin_matches g pin subdir)
                then return (Result.err (Build.stale_pin_error key pin g))
                else Build.verify_checkout home tool entries locked key g.url g.commit g.subdir e.checksum rest
        }
    }

/// `--locked`'s extra question: does the lock still pin what the manifest
/// asks for? Without the flag a changed tag is ignored -- the lock is the
/// authority -- which is the behaviour that makes a locked build stable.
def Build.pin_matches (g : LockedGit) (pin : GitPin) (subdir : Option String) : Bool :=
    String.beq (Lock.pin_to_string g.pin) (Lock.pin_to_string pin)
        && String.beq (Build.subdir_name g.subdir) (Build.subdir_name subdir)

def Build.stale_pin_error (key : String) (declared : GitPin) (g : LockedGit) : String :=
    "`--locked`: mote.lock pins `" ++ key ++ "` at `" ++ Lock.pin_to_string g.pin
        ++ "`, but the manifest asks for `" ++ Lock.pin_to_string declared ++ "`; run `monad fetch` to update it"

#[partial]
def Build.verify_checkout (home : String) (tool : DigestTool) (entries : List LockedMote) (locked : Bool) (key : String) (url : String) (commit : String) (subdir : Option String) (checksum : String) (rest : List (Pair String Dependency)) : IO (Result String Unit) := do {
    let dir : String := raw_path_join (Git.checkout_dir home url commit) (Build.subdir_name subdir);
    let there <- IO.is_dir (Path.path dir);
    if Bool.not there
    then return (Result.err ("the checkout of `" ++ key ++ "` is missing (`" ++ dir ++ "`); run `monad fetch`"))
    else do {
        let sum <- Build.canonical_tree_checksum_with tool (Path.path dir);
        match sum {
            Result.err e => return (Result.err e),
            Result.ok actual => Build.verify_sum home tool entries locked key checksum actual rest
        }
    }
}

#[partial]
def Build.verify_sum (home : String) (tool : DigestTool) (entries : List LockedMote) (locked : Bool) (key : String) (expected : String) (actual : String) (rest : List (Pair String Dependency)) : IO (Result String Unit) :=
    if String.beq actual expected
    then Build.verify_deps home tool entries locked rest
    else return (Result.err ("`" ++ key ++ "` does not match mote.lock: the lock records `"
        ++ expected ++ "`, the checkout hashes to `" ++ actual ++ "`. Run `monad fetch` to re-resolve it"))

/// The lock entry named `key`, when it is a git entry for this URL.
#[partial]
def Build.entry_for (entries : List LockedMote) (key : String) (url : String) : Option LockedMote :=
    match entries {
        List.empty => Option.none,
        List.cons e rest => match e.git {
            Option.none => Build.entry_for rest key url,
            Option.some g =>
                if String.beq e.name key && String.beq g.url url
                then Option.some e
                else Build.entry_for rest key url
        }
    }

def Build.subdir_name (subdir : Option String) : String :=
    match subdir { Option.some s => s, Option.none => "" }

def Build.missing_entry_error (locked : Bool) (key : String) (url : String) : String :=
    if locked
    then "`--locked`: mote.lock has no entry for git dependency `" ++ key ++ "` (`" ++ url ++ "`); run `monad fetch` to update it"
    else "git dependency `" ++ key ++ "` is not in mote.lock (`" ++ url ++ "`); run `monad fetch`"
