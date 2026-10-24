/// Tests for `build/src/git.mo`: the allowlist, the cache layout, and one
/// end-to-end pass through a real `file://` repository.
///
/// The end-to-end tests build their fixture with `git` ARGV (never a shell
/// script), with the author, committer and both dates pinned, so the
/// commit id is the same on every machine and a test can compare ids
/// rather than only "something resolved".
///
/// Fixtures live under `/tmp` and are pid-scoped: the corpus sweep runs
/// sharded, and a fixed name would collide across concurrent shards.

use std::list {List.all}
use std::process {process_id}
use build::git {
  Git.available, Git.checkout, Git.checkout_dir, Git.ensure_mirror,
  Git.fetch, Git.prune, Git.repo_key, Git.resolve, Git.url_allowed,
}
use lang::lock {GitPin}

def Build.git_fixture_root (tag : String) : String :=
    "/tmp/monad_git_fix_" ++ I64.to_string process_id ++ "_" ++ tag

/// A `git` invocation whose result is DETERMINISTIC: fixed identity, fixed
/// dates, and the user's own configuration ignored (`tag.gpgSign` in a
/// global config makes a plain `git tag` fail, which is a property of the
/// machine and not of this transport).
def Build.git_at (dir : String) (args : List String) : IO (Pair I64 String) :=
    Proc.capture "env" (List.append [
        "GIT_AUTHOR_NAME=monad", "GIT_AUTHOR_EMAIL=monad@example.invalid",
        "GIT_COMMITTER_NAME=monad", "GIT_COMMITTER_EMAIL=monad@example.invalid",
        "GIT_AUTHOR_DATE=2020-01-01T00:00:00Z",
        "GIT_COMMITTER_DATE=2020-01-01T00:00:00Z",
        "GIT_CONFIG_GLOBAL=/dev/null", "GIT_CONFIG_SYSTEM=/dev/null",
        "GIT_TERMINAL_PROMPT=0",
    ] (List.append ["git", "-C", dir] args))

def Build.git_status (r : Pair I64 String) : I64 :=
    match r { Pair.pair code _out => code }

/// The fixture root, created fresh with one commit tagged `v1`. The caller
/// derives the repository, mirror and checkout paths from it, so no test
/// has to thread a tuple of paths around.
#[partial]
def Build.make_git_fixture (tag : String) : IO String := do {
    let root : String := Build.git_fixture_root tag;
    let repo : String := root ++ "/repo";
    let _rm <- Proc.capture "rm" ["-rf", root];
    let _mk <- Proc.capture "mkdir" ["-p", repo];
    let _init <- Build.git_at repo ["init", "-q", "-b", "main"];
    let _w <- IO.write_file (Path.path (repo ++ "/a.mo")) "def a : I64 := 1\n";
    let _add <- Build.git_at repo ["add", "-A"];
    let _commit <- Build.git_at repo ["commit", "-qm", "one"];
    let _tag <- Build.git_at repo ["-c", "tag.gpgSign=false", "tag", "v1"];
    return root
}

def Build.rm_git_fixture (tag : String) : IO I64 := do {
    let r <- Proc.capture "rm" ["-rf", Build.git_fixture_root tag];
    return (Build.git_status r)
}

def Build.fixture_repo (tag : String) : String :=
    Build.git_fixture_root tag ++ "/repo"

def Build.fixture_url (tag : String) : String :=
    "file://" ++ Build.fixture_repo tag

def is_ok (r : Result String Unit) : Bool :=
    match r { Result.ok _ => true, Result.err _ => false }

// ─── Pure ───

#[test]
def test_url_allowlist_accepts_https_and_file : Bool :=
    List.all Git.url_allowed [
        "https://example.org/x",
        "https://example.org/x?tag=v1",
        "file:///srv/repo",
        "file://localhost/srv/repo",
    ]

/// Every transport the plan refuses, plus the leading `-` that would
/// otherwise be read as an option.
#[test]
def test_url_allowlist_rejects_everything_else : Bool :=
    List.all (fn (u : String) => Bool.not (Git.url_allowed u)) [
        "", "http://example.org/x", "ssh://git@example.org/x",
        "git://example.org/x", "ext::sh -c touch% /tmp/pwn", "-oProxyCommand=x",
        "HTTPS://example.org/x", "/srv/repo", "example.org/x",
    ]

#[test]
def test_repo_key_is_stable_and_distinct : Bool :=
    String.beq (Git.repo_key "file:///a") (Git.repo_key "file:///a")
        && Bool.not (String.beq (Git.repo_key "file:///a") (Git.repo_key "file:///b"))
        && String.length (Git.repo_key "file:///a") == 64

/// Both cache trees hang off the URL KEY, so a URL holding `/`, `?`, `#`
/// or a space never becomes a path component of its own.
#[test]
def test_cache_paths_are_keyed_by_url : Bool :=
    String.beq (Git.checkout_dir "/h" "file:///a" "abc")
        ("/h/cache/git/checkouts/" ++ Git.repo_key "file:///a" ++ "/abc")

// ─── Against a real repository ───

#[test]
def test_git_is_available : IO Bool := Git.available

/// The whole transport, once: mirror, fetch, resolve every pin kind to
/// the SAME commit, then check it out.
#[test]
def test_fetch_and_resolve_every_pin_kind : IO Bool := do {
    let _root <- Build.make_git_fixture "pins";
    let ok <- Build.mirror_and_check_pins;
    let _rm <- Build.rm_git_fixture "pins";
    return ok
}

#[partial]
def Build.mirror_and_check_pins : IO Bool := do {
    let home : String := Build.git_fixture_root "pins";
    let url : String := Build.fixture_url "pins";
    let mirrored <- Git.ensure_mirror home url;
    match mirrored {
        Result.err _ => return false,
        Result.ok db => Build.fetch_then_check db home url
    }
}

#[partial]
def Build.fetch_then_check (db : String) (home : String) (url : String) : IO Bool := do {
    let fetched <- Git.fetch db url;
    match fetched {
        Result.err _ => return false,
        Result.ok _ => Build.check_pins db home url
    }
}

#[partial]
def Build.check_pins (db : String) (home : String) (url : String) : IO Bool := do {
    let head <- Git.resolve db GitPin.head;
    match head {
        Result.err _ => return false,
        Result.ok h => Build.check_pin_kinds db home url h
    }
}

/// Split out so the resolved id has a concrete `String` type at every use:
/// as a bare match binder it is still `A`, and an affine binder may not be
/// read twice.
#[partial]
def Build.check_pin_kinds (db : String) (home : String) (url : String) (h : String) : IO Bool := do {
    let tag <- Git.resolve db (GitPin.tag "v1");
    let branch <- Git.resolve db (GitPin.branch "main");
    let rev <- Git.resolve db (GitPin.rev h);
    let co : String := Git.checkout_dir home url h;
    let checked <- Git.checkout db co h;
    let present <- IO.file_exists (Path.path (co ++ "/a.mo"));
    let _pruned <- Git.prune db;
    return (same_commit tag h && same_commit branch h && same_commit rev h
        && String.length h == 40 && is_ok checked && present)
}

def same_commit (r : Result String String) (want : String) : Bool :=
    match r { Result.ok got => String.beq got want, Result.err _ => false }

/// A tag that does not exist is an error naming it, not an empty answer
/// that would land in the lock as a blank commit.
#[test]
def test_unknown_tag_is_an_error_naming_it : IO Bool := do {
    let _root <- Build.make_git_fixture "unknown";
    let ok <- Build.unknown_tag_names_it;
    let _rm <- Build.rm_git_fixture "unknown";
    return ok
}

#[partial]
def Build.unknown_tag_names_it : IO Bool := do {
    let home : String := Build.git_fixture_root "unknown";
    let url : String := Build.fixture_url "unknown";
    let mirrored <- Git.ensure_mirror home url;
    match mirrored {
        Result.err _ => return false,
        Result.ok db => Build.unknown_tag_in db url
    }
}

#[partial]
def Build.unknown_tag_in (db : String) (url : String) : IO Bool := do {
    let _fetched <- Git.fetch db url;
    let r <- Git.resolve db (GitPin.tag "no-such-tag");
    match r {
        Result.ok _ => return false,
        Result.err m => return (String.contains m "no-such-tag")
    }
}

/// A `rev` that is not full hex is refused before git is asked, and one
/// that is full hex but absent from the mirror is refused by git.
#[test]
def test_rev_must_be_a_full_commit_in_the_mirror : IO Bool := do {
    let _root <- Build.make_git_fixture "rev";
    let ok <- Build.rev_rules;
    let _rm <- Build.rm_git_fixture "rev";
    return ok
}

#[partial]
def Build.rev_rules : IO Bool := do {
    let home : String := Build.git_fixture_root "rev";
    let url : String := Build.fixture_url "rev";
    let mirrored <- Git.ensure_mirror home url;
    match mirrored {
        Result.err _ => return false,
        Result.ok db => Build.rev_rules_in db url
    }
}

#[partial]
def Build.rev_rules_in (db : String) (url : String) : IO Bool := do {
    let _fetched <- Git.fetch db url;
    let short <- Git.resolve db (GitPin.rev "abc123");
    let absent <- Git.resolve db (GitPin.rev "0123456789abcdef0123456789abcdef01234567");
    return (refused short && names_it absent)
}

def refused (r : Result String String) : Bool :=
    match r { Result.ok _ => false, Result.err _ => true }

def names_it (r : Result String String) : Bool :=
    match r {
        Result.ok _ => false,
        Result.err m => String.contains m "0123456789abcdef0123456789abcdef01234567"
    }

/// A second checkout of the same commit is a no-op, not an error: a
/// fetch that reruns must not fail because the worktree is already there.
#[test]
def test_checkout_is_idempotent : IO Bool := do {
    let _root <- Build.make_git_fixture "twice";
    let ok <- Build.checkout_twice;
    let _rm <- Build.rm_git_fixture "twice";
    return ok
}

#[partial]
def Build.checkout_twice : IO Bool := do {
    let home : String := Build.git_fixture_root "twice";
    let url : String := Build.fixture_url "twice";
    let mirrored <- Git.ensure_mirror home url;
    match mirrored {
        Result.err _ => return false,
        Result.ok db => Build.checkout_twice_in db home url
    }
}

#[partial]
def Build.checkout_twice_in (db : String) (home : String) (url : String) : IO Bool := do {
    let _fetched <- Git.fetch db url;
    let head <- Git.resolve db GitPin.head;
    match head {
        Result.err _ => return false,
        Result.ok commit => Build.checkout_twice_at db home url commit
    }
}

#[partial]
def Build.checkout_twice_at (db : String) (home : String) (url : String) (commit : String) : IO Bool := do {
    let co : String := Git.checkout_dir home url commit;
    let first <- Git.checkout db co commit;
    let second <- Git.checkout db co commit;
    let present <- IO.file_exists (Path.path (co ++ "/a.mo"));
    return (is_ok first && is_ok second && present)
}
