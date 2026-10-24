/// Tests for `build/src/fetch.mo`: `monad fetch` / `monad update` against
/// a `file://` repository whose history is built with `git` ARGV.
///
/// `Build.fetch_run_with` takes the cache root, so a test keeps its git
/// cache in the fixture instead of writing into the user's `~/.monad`.
///
/// Fixtures are pid-scoped (`/tmp` is shared and the corpus sweep runs
/// sharded) and their commits are DETERMINISTIC: fixed author, committer
/// and dates, so a commit id is the same on every machine.

use std::list {List.all, List.length}
use std::process {process_id}
use std::stream {StreamError}
use build::fetch {
  Build.fetch_run_with, Build.fetch_run_with_opts, Build.pin_of_dep,
  Build.safe_subdir, Build.verify_manifest_at, FetchMode,
}
use build::hash {Build.canonical_tree_checksum}
use lang::lock {GitPin, Lock.pin_to_string, Lock.read, LockRead, LockedMote}
use lang::mote {Mote.manifest_at, Mote.with_locked_dirs_at, MoteManifest}

def Build.fetch_fixture_root (tag : String) : String :=
    "/tmp/monad_fetch_fix_" ++ I64.to_string process_id ++ "_" ++ tag

def Build.git_at (dir : String) (args : List String) : IO (Pair I64 String) :=
    Proc.capture "env" (List.append [
        "GIT_AUTHOR_NAME=monad", "GIT_AUTHOR_EMAIL=monad@example.invalid",
        "GIT_COMMITTER_NAME=monad", "GIT_COMMITTER_EMAIL=monad@example.invalid",
        "GIT_AUTHOR_DATE=2020-01-01T00:00:00Z",
        "GIT_COMMITTER_DATE=2020-01-01T00:00:00Z",
        "GIT_CONFIG_GLOBAL=/dev/null", "GIT_CONFIG_SYSTEM=/dev/null",
        "GIT_TERMINAL_PROMPT=0",
    ] (List.append ["git", "-C", dir] args))

def Build.git_ok (r : Pair I64 String) : Bool :=
    match r { Pair.pair code _out => code == 0 }

/// Build `<root>/repo` (a mote with one commit tagged `v1`) and
/// `<root>/app` (a mote depending on it), and return the root.
#[partial]
def Build.make_fetch_fixture (tag : String) (dep_url_line : String) : IO String := do {
    let root : String := Build.fetch_fixture_root tag;
    let repo : String := root ++ "/repo";
    let app : String := root ++ "/app";
    let _rm <- Proc.capture "rm" ["-rf", root];
    let _mk <- Proc.capture "mkdir" ["-p", repo ++ "/src", app ++ "/src"];
    let _rman <- IO.write_file (Path.path (repo ++ "/mote.toml"))
        "[mote]\nname = \"dep\"\nversion = \"0.1.0\"\n";
    let _rlib <- IO.write_file (Path.path (repo ++ "/src/lib.mo")) "pub def answer : I64 := 42\n";
    let _aman <- IO.write_file (Path.path (app ++ "/mote.toml"))
        ("[mote]\nname = \"app\"\nversion = \"0.1.0\"\n\n[dependencies.dep]\n" ++ dep_url_line ++ "\n");
    let _alib <- IO.write_file (Path.path (app ++ "/src/lib.mo")) "pub def use_it : I64 := 1\n";
    let _init <- Build.git_at repo ["init", "-q", "-b", "main"];
    let _add <- Build.git_at repo ["add", "-A"];
    let _commit <- Build.git_at repo ["commit", "-qm", "one"];
    let _tag <- Build.git_at repo ["-c", "tag.gpgSign=false", "tag", "v1"];
    return root
}

def Build.fetch_repo (root : String) : String := root ++ "/repo"

def Build.fetch_app (root : String) : String := root ++ "/app"

def Build.fetch_lock_path (root : String) : String := root ++ "/app/mote.lock"

/// The `$MONAD_HOME` the fixture fetches into. `$MONAD_HOME/cache/git` is
/// the cache, so this is the HOME and not the cache directory itself.
def Build.fetch_home (root : String) : String := root ++ "/home"

/// The dependency source line for a `file://` URL and a tag.
def Build.git_dep_line (root : String) (pin_line : String) : String :=
    "git = \"file://" ++ Build.fetch_repo root ++ "\"\n" ++ pin_line

def Build.rm_fetch_fixture (tag : String) : IO I64 := do {
    let r <- Proc.capture "rm" ["-rf", Build.fetch_fixture_root tag];
    match r { Pair.pair code _out => return code }
}

/// The single lock entry, when the lock reads as one.
def Build.single_entry (r : Result String (Option LockRead)) : Option LockedMote :=
    match r {
        Result.err _ => Option.none,
        Result.ok found => match found {
            Option.none => Option.none,
            Option.some read => match read {
                LockRead.unsupported _ => Option.none,
                LockRead.loaded lock => match lock.motes { List.cons e _ => Option.some e, List.empty => Option.none }
            }
        }
    }

// ─── Pure ───

#[test]
def test_pin_of_dep_prefers_tag_then_branch_then_rev : Bool :=
    String.beq (Lock.pin_to_string (Build.pin_of_dep (Option.some "v1") (Option.some "main") Option.none)) "tag:v1"
        && String.beq (Lock.pin_to_string (Build.pin_of_dep Option.none (Option.some "main") (Option.some "abc"))) "branch:main"
        && String.beq (Lock.pin_to_string (Build.pin_of_dep Option.none Option.none (Option.some "abc"))) "rev:abc"
        && String.beq (Lock.pin_to_string (Build.pin_of_dep Option.none Option.none Option.none)) "head"

#[test]
def test_subdir_must_stay_inside_the_checkout : Bool :=
    is_err (Build.safe_subdir (Option.some "../etc"))
        && is_err (Build.safe_subdir (Option.some "/abs"))
        && is_err (Build.safe_subdir (Option.some "a/../../b"))
        && is_ok_option (Build.safe_subdir (Option.some "motes/dep"))
        && is_ok_option (Build.safe_subdir Option.none)

def is_err (r : Result String (Option String)) : Bool :=
    match r { Result.ok _ => false, Result.err _ => true }

def is_ok_option (r : Result String (Option String)) : Bool :=
    match r { Result.ok _ => true, Result.err _ => false }

// ─── End to end ───

/// The acceptance row: a mote depending on a local `file://` repository
/// gets a lock entry naming the full commit, the pin and a checksum that
/// equals the checksum of the repository's own tree (the checkout has no
/// `.git/`, `target/` or `mote.lock` inside the mote directory, and those
/// are the only things the checksum excludes).
#[test]
def test_fetch_writes_a_checked_lock_entry : IO Bool := do {
    let root <- Build.make_fetch_fixture "lock" (Build.git_dep_line (Build.fetch_fixture_root "lock") "tag = \"v1\"");
    let code <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let lock <- Lock.read (Path.path (Build.fetch_lock_path root));
    let repo_sum <- Build.canonical_tree_checksum (Path.path (Build.fetch_repo root));
    let _rm <- Build.rm_fetch_fixture "lock";
    return (code == 0 && Build.entry_is_sound lock repo_sum)
}

#[partial]
def Build.entry_is_sound (lock : Result String (Option LockRead)) (repo_sum : Result String String) : Bool :=
    match Build.single_entry lock {
        Option.none => false,
        Option.some e => Build.entry_matches e repo_sum
    }

#[partial]
def Build.entry_matches (e : LockedMote) (repo_sum : Result String String) : Bool :=
    match e.git {
        Option.none => false,
        Option.some g =>
            String.beq e.name "dep"
                && String.beq e.version "0.1.0"
                && String.beq (Lock.pin_to_string g.pin) "tag:v1"
                && I64.beq (String.length g.commit) 40
                && String.beq e.checksum (Build.digest_of repo_sum)
    }

/// `fetch` keeps the commit `mote.lock` already names, so a tag that
/// moved upstream does not change a locked build; `update` follows it.
#[test]
def test_fetch_keeps_a_locked_commit_and_update_follows_the_tag : IO Bool := do {
    let root <- Build.make_fetch_fixture "moved" (Build.git_dep_line (Build.fetch_fixture_root "moved") "tag = \"v1\"");
    let code <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let _second <- IO.write_file (Path.path (Build.fetch_repo root ++ "/src/lib.mo")) "pub def answer : I64 := 43\n";
    let _add <- Build.git_at (Build.fetch_repo root) ["add", "-A"];
    let _commit <- Build.git_at (Build.fetch_repo root) ["commit", "-qm", "two"];
    let _tag <- Build.git_at (Build.fetch_repo root) ["-c", "tag.gpgSign=false", "tag", "-f", "v1"];
    let kept <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let after_kept <- Build.locked_commit_of (Build.fetch_lock_path root);
    let moved <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.update;
    let after_update <- Build.locked_commit_of (Build.fetch_lock_path root);
    let _rm <- Build.rm_fetch_fixture "moved";
    return (code == 0 && kept == 0 && moved == 0
        && Bool.not (String.is_empty after_kept)
        && Bool.not (String.is_empty after_update)
        && Bool.not (String.beq after_kept after_update))
}

/// The commit the lock names for the single entry, or `""`.
def Build.locked_commit_of (lock_path : String) : IO String := do {
    let lock <- Lock.read (Path.path lock_path);
    return (match Build.single_entry lock {
        Option.none => "",
        Option.some e => match e.git { Option.some g => g.commit, Option.none => "" }
    })
}

/// A URL outside the allowlist fails the verb BEFORE git runs, and leaves
/// no lockfile behind: a half-resolved closure is worse than none.
#[test]
def test_a_disallowed_url_fails_without_writing_a_lock : IO Bool := do {
    let root <- Build.make_fetch_fixture "badurl" "git = \"ssh://example.invalid/x\"\ntag = \"v1\"";
    let code <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let lock <- Lock.read (Path.path (Build.fetch_lock_path root));
    let _rm <- Build.rm_fetch_fixture "badurl";
    return (code == 1 && is_no_lock lock)
}

/// A `subdir` that could escape the checkout is refused the same way.
#[test]
def test_an_escaping_subdir_fails_without_writing_a_lock : IO Bool := do {
    let root <- Build.make_fetch_fixture "badsub" (Build.git_dep_line (Build.fetch_fixture_root "badsub") "tag = \"v1\"\nsubdir = \"../escape\"");
    let code <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let lock <- Lock.read (Path.path (Build.fetch_lock_path root));
    let _rm <- Build.rm_fetch_fixture "badsub";
    return (code == 1 && is_no_lock lock)
}

def is_no_lock (r : Result String (Option LockRead)) : Bool :=
    match r { Result.err _ => false, Result.ok found => match found { Option.none => true, Option.some _ => false } }

/// Fetching twice with nothing changed rewrites the same bytes, so a
/// committed `mote.lock` shows no diff.
#[test]
def test_fetch_is_idempotent : IO Bool := do {
    let root <- Build.make_fetch_fixture "idem" (Build.git_dep_line (Build.fetch_fixture_root "idem") "tag = \"v1\"");
    let _one <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let first <- IO.read_file (Path.path (Build.fetch_lock_path root));
    let _two <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let second <- IO.read_file (Path.path (Build.fetch_lock_path root));
    let _rm <- Build.rm_fetch_fixture "idem";
    return (same_text first second)
}

def same_text (a : Result StreamError String) (b : Result StreamError String) : Bool :=
    match a {
        Result.err _ => false,
        Result.ok x => match b {
            Result.err _ => false,
            Result.ok y => String.beq x y,
        }
    }

/// The checksum text of a successful digest, or `""`.
def Build.digest_of (r : Result String String) : String :=
    match r { Result.ok sum => sum, Result.err _ => "" }

// ─── Transitive git dependencies ───

/// A git dependency's OWN git dependencies must be resolved too, even
/// though its manifest is only readable after its checkout exists. The
/// walk has to record `mid` and then still walk `mid`'s declared `leaf`.
#[test]
def test_a_git_dependency_s_own_git_dependencies_are_resolved : IO Bool := do {
    let root : String := Build.fetch_fixture_root "chain";
    let _mk <- Build.make_git_chain root;
    let code <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let lock <- Lock.read (Path.path (Build.fetch_lock_path root));
    let _rm <- Build.rm_fetch_fixture "chain";
    return (code == 0 && Build.lock_has_names lock ["leaf", "mid"])
}

#[partial]
def Build.make_git_chain (root : String) : IO I64 := do {
    let _rm <- Proc.capture "rm" ["-rf", root];
    let _mk <- Proc.capture "mkdir" ["-p",
        root ++ "/leaf/src", root ++ "/mid/src", root ++ "/app/src"];
    let _lm <- IO.write_file (Path.path (root ++ "/leaf/mote.toml"))
        "[mote]\nname = \"leaf\"\nversion = \"0.1.0\"\n";
    let _ll <- IO.write_file (Path.path (root ++ "/leaf/src/lib.mo")) "pub def leaf : I64 := 1\n";
    let _mm <- IO.write_file (Path.path (root ++ "/mid/mote.toml"))
        ("[mote]\nname = \"mid\"\nversion = \"0.2.0\"\n\n[dependencies.leaf]\ngit = \"file://"
            ++ (root ++ "/leaf") ++ "\"\ntag = \"v1\"\n");
    let _ml <- IO.write_file (Path.path (root ++ "/mid/src/lib.mo")) "pub def mid : I64 := 2\n";
    let _am <- IO.write_file (Path.path (root ++ "/app/mote.toml"))
        ("[mote]\nname = \"app\"\nversion = \"0.3.0\"\n\n[dependencies.mid]\ngit = \"file://"
            ++ (root ++ "/mid") ++ "\"\ntag = \"v1\"\n");
    let _al <- IO.write_file (Path.path (root ++ "/app/src/lib.mo")) "pub def app : I64 := 3\n";
    let _i1 <- Build.git_at (root ++ "/leaf") ["init", "-q", "-b", "main"];
    let _a1 <- Build.git_at (root ++ "/leaf") ["add", "-A"];
    let _c1 <- Build.git_at (root ++ "/leaf") ["commit", "-qm", "leaf"];
    let _t1 <- Build.git_at (root ++ "/leaf") ["-c", "tag.gpgSign=false", "tag", "v1"];
    let _i2 <- Build.git_at (root ++ "/mid") ["init", "-q", "-b", "main"];
    let _a2 <- Build.git_at (root ++ "/mid") ["add", "-A"];
    let _c2 <- Build.git_at (root ++ "/mid") ["commit", "-qm", "mid"];
    let _t2 <- Build.git_at (root ++ "/mid") ["-c", "tag.gpgSign=false", "tag", "v1"];
    return 0
}

def Build.lock_has_names (r : Result String (Option LockRead)) (names : List String) : Bool :=
    match r {
        Result.err _ => false,
        Result.ok found => match found {
            Option.none => false,
            Option.some read => match read {
                LockRead.unsupported _ => false,
                LockRead.loaded lock => List.all (fn (n : String) => Build.mentions lock.motes n) names
                    && I64.beq (List.length lock.motes) (List.length names)
            }
        }
    }

def Build.mentions (entries : List LockedMote) (name : String) : Bool :=
    match entries {
        List.empty => false,
        List.cons e rest => String.beq e.name name || Build.mentions rest name
    }

// ─── Resolution ───

/// The reader half, end to end: after a fetch, the manifest's git
/// dependency resolves to a real checkout directory with a real file in
/// it -- which is what `resolve_via_manifest` asks the manifest for.
#[test]
def test_a_fetched_dependency_resolves_to_its_checkout : IO Bool := do {
    let root <- Build.make_fetch_fixture "resolve" (Build.git_dep_line (Build.fetch_fixture_root "resolve") "tag = \"v1\"");
    let code <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let dir <- Build.resolved_dir root;
    let present <- IO.file_exists (Path.path (dir ++ "/src/lib.mo"));
    let _rm <- Build.rm_fetch_fixture "resolve";
    return (code == 0
        && String.starts_with (Build.fetch_home root ++ "/cache/git/checkouts/") dir
        && present)
}

#[partial]
def Build.resolved_dir (root : String) : IO String := do {
    let man <- Mote.manifest_at (Build.fetch_app root);
    match man {
        Option.none => return "",
        Option.some m => do {
            let filled <- Mote.with_locked_dirs_at (Build.fetch_home root) m;
            match MoteManifest.dep_dir_of filled "dep" {
                Option.none => return "",
                Option.some d => return d
            }
        }
    }
}

// ─── Verification ───

/// The happy path: what `fetch` just wrote verifies.
#[test]
def test_a_fresh_lock_verifies : IO Bool := do {
    let root <- Build.make_fetch_fixture "verify" (Build.git_dep_line (Build.fetch_fixture_root "verify") "tag = \"v1\"");
    let code <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let r <- Build.verify_fixture root false;
    let _rm <- Build.rm_fetch_fixture "verify";
    return (code == 0 && is_unit_ok r)
}

/// A dependency that moved under its pin must never compile: the checkout
/// no longer hashes to what the lock records, and the error names it.
#[test]
def test_a_tampered_checkout_is_rejected_by_name : IO Bool := do {
    let root <- Build.make_fetch_fixture "tamper" (Build.git_dep_line (Build.fetch_fixture_root "tamper") "tag = \"v1\"");
    let _code <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let dir <- Build.resolved_dir root;
    let _w <- IO.write_file (Path.path (dir ++ "/src/lib.mo")) "pub def answer : I64 := 99\n";
    let r <- Build.verify_fixture root false;
    let _rm <- Build.rm_fetch_fixture "tamper";
    return (names_entry r "dep" && says_mismatch r)
}

/// A missing checkout is the actionable error, not a checksum mismatch.
#[test]
def test_a_missing_checkout_says_run_fetch : IO Bool := do {
    let root <- Build.make_fetch_fixture "nocache" (Build.git_dep_line (Build.fetch_fixture_root "nocache") "tag = \"v1\"");
    let _code <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let dir <- Build.resolved_dir root;
    let _rmco <- Proc.capture "rm" ["-rf", dir];
    let r <- Build.verify_fixture root false;
    let _rm <- Build.rm_fetch_fixture "nocache";
    return (says_r r "is missing")
}

/// `--locked` also refuses a lock whose PIN is stale: the manifest now
/// asks for a tag the lock does not record. Without the flag the lock is
/// the authority and the same tree verifies.
#[test]
def test_locked_rejects_a_pin_that_moved_in_the_manifest : IO Bool := do {
    let root <- Build.make_fetch_fixture "stale" (Build.git_dep_line (Build.fetch_fixture_root "stale") "tag = \"v1\"");
    let _code <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let _w <- IO.write_file (Path.path (Build.fetch_app root ++ "/mote.toml"))
        ("[mote]\nname = \"app\"\nversion = \"0.1.0\"\n\n[dependencies.dep]\n"
            ++ Build.git_dep_line (Build.fetch_fixture_root "stale") "tag = \"v2\"");
    let loose <- Build.verify_fixture root false;
    let strict <- Build.verify_fixture root true;
    let _rm <- Build.rm_fetch_fixture "stale";
    return (is_unit_ok loose && says_r strict "--locked")
}

/// `--offline` with nothing cached names the URL instead of reaching for
/// the network.
#[test]
def test_offline_without_a_cache_names_the_url : IO Bool := do {
    let root <- Build.make_fetch_fixture "offline" (Build.git_dep_line (Build.fetch_fixture_root "offline") "tag = \"v1\"");
    let code <- Build.fetch_run_with_opts (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch true;
    let lock <- Lock.read (Path.path (Build.fetch_lock_path root));
    let _rm <- Build.rm_fetch_fixture "offline";
    return (code == 1 && is_no_lock lock)
}

/// After one online fetch, `--offline` is a no-op: everything it needs is
/// already in the cache.
#[test]
def test_offline_after_a_fetch_succeeds : IO Bool := do {
    let root <- Build.make_fetch_fixture "offline2" (Build.git_dep_line (Build.fetch_fixture_root "offline2") "tag = \"v1\"");
    let _online <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let offline <- Build.fetch_run_with_opts (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch true;
    let _rm <- Build.rm_fetch_fixture "offline2";
    return (offline == 0)
}

#[partial]
def Build.verify_fixture (root : String) (locked : Bool) : IO (Result String Unit) := do {
    let man <- Mote.manifest_at (Build.fetch_app root);
    match man {
        Option.none => return (Result.err "no manifest"),
        Option.some m => Build.verify_manifest_at (Build.fetch_home root) m locked
    }
}

def is_unit_ok (r : Result String Unit) : Bool :=
    match r { Result.ok _ => true, Result.err _ => false }

def says_r (r : Result String Unit) (needle : String) : Bool :=
    match r { Result.ok _ => false, Result.err m => String.contains m needle }

def names_entry (r : Result String Unit) (name : String) : Bool :=
    says_r r ("`" ++ name ++ "`")

def says_mismatch (r : Result String Unit) : Bool :=
    says_r r "does not match mote.lock"

/// A corrupted cache is REPAIRED by `fetch`, not blessed: the tampered
/// file comes back from the mirror and the lock still records the original
/// tree.
#[test]
def test_fetch_repairs_a_tampered_checkout : IO Bool := do {
    let root <- Build.make_fetch_fixture "repair" (Build.git_dep_line (Build.fetch_fixture_root "repair") "tag = \"v1\"");
    let _code <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let dir <- Build.resolved_dir root;
    let _w <- IO.write_file (Path.path (dir ++ "/src/lib.mo")) "pub def answer : I64 := 99\n";
    let again <- Build.fetch_run_with (Build.fetch_home root) (Build.fetch_app root) FetchMode.fetch;
    let repaired <- IO.file_exists (Path.path (dir ++ "/src/lib.mo"));
    let r <- Build.verify_fixture root false;
    let _rm <- Build.rm_fetch_fixture "repair";
    return (again == 0 && repaired && is_unit_ok r)
}
