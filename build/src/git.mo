// build / git -- the `git` CLI transport for git dependencies.
//
// `plans/packaging/mote-build-deps-artifacts-targets.md` Phase 3d. Every
// call here is `exec_cmd`/`Proc.capture` ARGV and never `sh -c` (0a's
// rule), because every one of them carries manifest data -- a URL, a ref
// -- that must not be re-read by a shell.
//
// The transport is deliberately two layers of allowlist. `Git.url_allowed`
// is the gate monad enforces before any process starts; the `-c
// protocol.*` flags in `Git.safety_config` are git's own gate, so a
// redirect or a nested URL cannot reach a transport the manifest was
// never allowed to name. Credentials are not supported yet: the prompt
// is disabled and the helper cleared, so a private repository fails with
// git's own message instead of hanging on a terminal.
//
// Layout, both keyed by the sha256 of the URL so two spellings of one
// repository cannot collide and no path component has to be sanitized:
//
//   <home>/cache/git/db/<url-key>                     the bare mirror
//   <home>/cache/git/checkouts/<url-key>/<commit>     a detached checkout
//
// Resolution never reads git's STDOUT. `update-ref` writes a loose ref
// whose content IS the commit id, which is read back as a file and then
// deleted; the ref name carries our pid because the corpus runs sharded
// and two runs sharing a name would resolve each other's pins.

use build::lock {GitPin, Lock.is_commit}
use std::sha256 {Sha256.hash}
use std::process {exec_cmd, process_id}

/// The config every invocation carries.
///
/// `protocol.allow=never` with two explicit exceptions, so no redirect,
/// submodule or nested URL can reach `ext::`, `ssh://` or `git://`; and
/// an empty `credential.helper` plus `GIT_TERMINAL_PROMPT=0` (set in
/// `Git.run`) so nothing ever waits for a password on a terminal.
def Git.safety_config : List String := [
    "-c", "protocol.allow=never",
    "-c", "protocol.https.allow=always",
    "-c", "protocol.file.allow=always",
    "-c", "credential.helper=",
]

/// What `monad fetch` says when `exec_cmd` reports an unlaunchable
/// program (127 from `env`). Named rather than generic, because the
/// remedy is a different install, not a different command.
pub def Git.missing_error : String :=
    "`git` not found on PATH; monad fetch needs it (build and check do not)"

/// The transports a manifest may name. Anything else is refused by name
/// BEFORE a process starts, and a leading `-` is refused explicitly so a
/// URL can never be read as an option, whatever the argv looks like.
pub def Git.url_allowed (url : String) : Bool :=
    Bool.not (String.starts_with "-" url)
        && (String.starts_with "https://" url || String.starts_with "file://" url)

/// Why `url` was refused, naming the rule rather than only the value.
pub def Git.url_error (url : String) : String :=
    "unsupported git URL `" ++ url
        ++ "`: a git dependency may name only `https://` or `file://`, and never a value starting with `-`"

/// `env GIT_TERMINAL_PROMPT=0 git <safety config> <args...>`, with stdout
/// and stderr merged into the result. Exit 127 means `git` itself was not
/// launchable (`env` could not exec it), which `monad fetch` turns into
/// `Git.missing_error` before it gets here.
pub def Git.run (args : List String) : IO (Pair I64 String) :=
    Proc.capture "env"
        (List.append ["GIT_TERMINAL_PROMPT=0", "git"]
            (List.append Git.safety_config args))

/// Whether a launchable `git` answers at all. Probed once per verb, and
/// only by `fetch`/`update`: nothing else in the build needs `git`.
pub def Git.available : IO Bool := do {
    let r <- Git.run ["--version"];
    match r { Pair.pair code _out => return (code == 0) }
}

/// The URL's cache key: sha256 hex, so no URL character ever appears in a
/// path and two spellings cannot share a slot by accident.
pub def Git.repo_key (url : String) : String := Sha256.hash url

pub def Git.db_dir (home : String) (url : String) : String :=
    home ++ "/cache/git/db/" ++ Git.repo_key url

/// Where every checkout of one repository lives. The commit is the leaf
/// directory, so a moved tag cannot overwrite a pinned checkout.
pub def Git.co_root (home : String) (url : String) : String :=
    home ++ "/cache/git/checkouts/" ++ Git.repo_key url

pub def Git.checkout_dir (home : String) (url : String) (commit : String) : String :=
    Git.co_root home url ++ "/" ++ commit

/// Create the bare mirror if it is not there yet, and answer its path.
#[partial]
pub def Git.ensure_mirror (home : String) (url : String) : IO (Result String String) := do {
    let db : String := Git.db_dir home url;
    let there <- IO.is_dir (Path.path db);
    if there then return (Result.ok db)
    else do {
        let _ <- exec_cmd "mkdir" ["-p", raw_parent_dir db];
        let r <- Git.run ["init", "--bare", "--", db];
        match r {
            Pair.pair code out =>
                if code == 0
                then return (Result.ok db)
                else return (Result.err (Git.call_failed "git init --bare" out))
        }
    }
}

/// Bring the mirror up to date from `url`.
///
/// `+HEAD:refs/monad/remote-head` is not decoration: it is how a
/// dependency that names no tag, branch or rev gets a commit at all.
/// `git init --bare` points the mirror's own HEAD at a branch that may
/// not exist, so the remote's default branch is recorded under our own
/// ref at fetch time instead of being guessed later.
#[partial]
pub def Git.fetch (db : String) (url : String) : IO (Result String Unit) := do {
    let r <- Git.run [
        "--git-dir=" ++ db, "fetch", "--no-tags", "--", url,
        "+refs/heads/*:refs/heads/*",
        "+refs/tags/*:refs/tags/*",
        "+HEAD:refs/monad/remote-head",
    ];
    match r {
        Pair.pair code out =>
            if code == 0
            then return (Result.ok Unit.unit)
            else return (Result.err (Git.call_failed ("git fetch " ++ url) out))
    }
}

/// The full commit id `pin` names in the mirror.
///
/// A tag or branch is resolved through a loose ref, never through
/// stdout: `update-ref` writes `<db>/refs/monad/pin-<pid>` containing the
/// id, which `IO.read_file` then reads and the ref is deleted. The pid
/// suffix is what keeps sharded parallel runs apart.
#[partial]
pub def Git.resolve (db : String) (pin : GitPin) : IO (Result String String) :=
    match pin {
        GitPin.rev id => Git.resolve_rev db id,
        GitPin.tag name => Git.resolve_ref db ("refs/tags/" ++ name) ("tag `" ++ name ++ "`"),
        GitPin.branch name => Git.resolve_ref db ("refs/heads/" ++ name) ("branch `" ++ name ++ "`"),
        GitPin.head => Git.resolve_ref db "refs/monad/remote-head" "the remote HEAD",
    }

#[partial]
def Git.resolve_ref (db : String) (ref : String) (what : String) : IO (Result String String) := do {
    let name : String := "refs/monad/pin-" ++ I64.to_string process_id;
    let r <- Git.run ["--git-dir=" ++ db, "update-ref", name, ref ++ "^{commit}"];
    match r {
        Pair.pair code out =>
            if Bool.not (code == 0)
            then return (Result.err (Git.call_failed ("resolving " ++ what) out))
            else do {
                let read <- IO.read_file (Path.path (db ++ "/" ++ name));
                let _ <- Git.run ["--git-dir=" ++ db, "update-ref", "-d", name];
                match read {
                    Result.err e => return (Result.err (Git.call_failed ("reading " ++ name) e.message)),
                    Result.ok text => return (Git.commit_of_text what text)
                }
            }
    }
}

/// A `rev` is already the answer; it only has to BE a commit in the
/// mirror. Lowercased first, because `Lock.is_commit` (and the lockfile
/// it validates) accept lowercase hex only.
#[partial]
def Git.resolve_rev (db : String) (id : String) : IO (Result String String) := do {
    let lowered : String := String.to_lowercase id;
    if Bool.not (Lock.is_commit lowered)
    then return (Result.err ("`" ++ id ++ "` is not a full 40- or 64-digit hex commit id"))
    else do {
        let r <- Git.run ["--git-dir=" ++ db, "cat-file", "-e", lowered ++ "^{commit}"];
        match r {
            Pair.pair code out =>
                if code == 0
                then return (Result.ok lowered)
                else return (Result.err (Git.call_failed ("looking up commit `" ++ lowered ++ "`") out))
        }
    }
}

def Git.commit_of_text (what : String) (text : String) : Result String String :=
    let id : String := String.trim text in
    if Lock.is_commit id
    then Result.ok id
    else Result.err ("git resolved " ++ what ++ " to `" ++ id ++ "`, which is not a full commit id")

/// A detached checkout of `commit`, unless the directory is already there.
///
/// Already-there means a previous fetch (or a build) put it in place;
/// whether it is the RIGHT tree is the caller's checksum question, not
/// this function's. A `--detach`ed worktree against a mirror whose own
/// HEAD is unborn works: the commit is given explicitly.
#[partial]
pub def Git.checkout (db : String) (dir : String) (commit : String) : IO (Result String Unit) := do {
    let there <- IO.is_dir (Path.path dir);
    if there then return (Result.ok Unit.unit)
    else do {
        let _ <- exec_cmd "mkdir" ["-p", raw_parent_dir dir];
        let r <- Git.run ["--git-dir=" ++ db, "worktree", "add", "--detach", "--", dir, commit];
        match r {
            Pair.pair code out =>
                if code == 0
                then return (Result.ok Unit.unit)
                else return (Result.err (Git.call_failed ("git worktree add " ++ dir) out))
        }
    }
}

/// Drop the mirror's `worktrees/` entries for checkouts that are gone.
/// Run by `gc`/`clean --all` after they remove a checkout directory, or
/// the mirror keeps pointing at paths that no longer exist.
#[partial]
pub def Git.prune (db : String) : IO (Result String Unit) := do {
    let r <- Git.run ["--git-dir=" ++ db, "worktree", "prune"];
    match r {
        Pair.pair code out =>
            if code == 0
            then return (Result.ok Unit.unit)
            else return (Result.err (Git.call_failed "git worktree prune" out))
    }
}

/// `<what> failed[: <git's own words>]` -- never an empty reason, but
/// never a made-up one either.
pub def Git.call_failed (what : String) (out : String) : String :=
    let detail : String := String.trim out in
    if String.is_empty detail then what ++ " failed" else what ++ " failed: " ++ detail
