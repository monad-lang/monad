/// Input hashing: the content digest a cache key is built from.
///
/// The split here is the whole design. Bulk digesting -- megabytes of
/// `.mo` source -- is delegated to the platform's digest tool in ONE fork
/// per mote, because `std/src/sha256.mo` is pure Monad at several nested
/// calls per byte: correct, and fine for the few hundred bytes of LISTING
/// this module hashes itself, hopeless over a source tree. The tool's
/// output is already the sorted `(path, content hash)` pairs an input hash
/// wants, so nothing is re-sorted in Monad, and the final combining hash
/// IS Monad code, so it is unit-testable and identical on both runtimes.
///
/// Two different questions are answered here, and they are easy to
/// confuse. `tree_digest` keys the CACHE: only what the compiler reads,
/// filtered by extension, so an unrelated README edit does not invalidate
/// anything. `canonical_tree_checksum` keys IDENTITY: the value
/// `mote.lock` records and `monad fetch` verifies, where a git checkout
/// and a registry tarball of the same source must agree
/// (`plans/packaging/package-system.md` §2b). The second therefore pins
/// its encoding instead of inheriting the tool's, which is why it has its
/// own comment rather than sharing this one.

use std::process {exec_cmd}
use std::sha256 {Sha256.hash}

/// The digest tool this machine has.
///
/// Two, both testable here. `certutil -hashfile` is the Windows
/// equivalent and is deliberately NOT a constructor: an untested code
/// path claiming Windows support is worse than an error message that says
/// it is missing, which is what `Build.no_digest_tool_error` does.
pub type DigestTool {
    sha256sum,
    shasum_256,
}

open DigestTool {sha256sum, shasum_256}

/// What to hand `find -exec`.
def Build.tool_exec (t : DigestTool) : String :=
    match t {
        sha256sum => "sha256sum",
        shasum_256 => "shasum -a 256",
    }

/// Named, because this is a refusal and not a fallback.
///
/// Falling back to file timestamps would make a stale artifact look
/// fresh, which is the one failure a build cache must never have -- so a
/// missing tool stops the cache rather than weakening it. That is the
/// "only cache safe and expensive work" rule applied to its own
/// prerequisite.
def Build.no_digest_tool_error : String :=
    "no content-digest tool on PATH: tried `sha256sum` (GNU coreutils) and `shasum` (Darwin). A build cache cannot be keyed without one, and falling back to file timestamps would let a stale artifact look fresh -- so this is an error, not a warning. On Windows the equivalent is `certutil -hashfile`, which is not wired up yet."

def Build.digest_failed_error (dir : String) (out : String) : String :=
    String.concat "could not digest " (String.concat dir (String.concat ": " out))

/// Which digest tool is available.
///
/// `exec_cmd` rather than `Proc.capture`: only the exit status matters,
/// and capturing would cost a temp file and two more forks per probe.
/// Probe ONCE and pass the result down -- there is nowhere to cache it,
/// and a probe per mote is a fork per mote for nothing.
#[partial]
pub def Build.probe_digest_tool : IO (Result String DigestTool) := do {
    let has_sha256sum <- exec_cmd "sh" ["-c", "command -v sha256sum >/dev/null 2>&1"];
    if has_sha256sum == 0
    then return (ok sha256sum)
    else do {
        let has_shasum <- exec_cmd "sh" ["-c", "command -v shasum >/dev/null 2>&1"];
        if has_shasum == 0
        then return (ok shasum_256)
        else return (err Build.no_digest_tool_error)
    }
}

/// The directory the digest walks, as a shell word.
///
/// An empty root means the working directory -- the convention
/// `Build.default_target_dir` and `MoteManifest.src_root` both spell out --
/// and it arrives here for the most ordinary layout there is: a mote whose
/// `mote.toml` sits in the working directory, built as
/// `cd mymote && monad build src/main.mo`. `Mote.discover` reports that
/// manifest's directory as `""` (the same tree spelled `./src/main.mo`
/// gives `"."`), and the shell cannot take the empty one: `cd ''` fails
/// with "no such file or directory", so `tree_digest_with` is an error, so
/// `Build.input_hash` is an error, so `build_cached` falls back to
/// `compile_file` with the cache OFF -- silently, apart from one line
/// under `--verbose`. Measured, one file and one directory, two spellings:
/// `src/main.mo` wrote no store entry at all, `./src/main.mo` wrote one.
///
/// So the one consumer that forgot the convention spells it out. `.` is the
/// same directory under a name the shell accepts, and the digest does not
/// depend on which spelling it got (`find` prints `./src/main.mo` either
/// way) -- which is what makes the two spellings of one build share an
/// entry rather than each compiling.
def Build.digest_dir (dir : String) : String :=
    if String.is_empty dir then "." else dir

/// The shell pipeline. Three choices in it are load-bearing for a cache
/// key, and none of them is incidental:
///
/// `cd` first and `find .`, so the listing carries RELATIVE paths: a
/// mote's digest must not move when the checkout does, or two worktrees
/// at the same commit would never share an entry.
///
/// `LC_ALL=C sort`, so the order is byte order and not the machine's
/// locale -- otherwise the same tree hashes differently on two machines.
///
/// `-exec ... +` rather than `xargs -0`, because `find` with no matches
/// runs no command at all, whereas `xargs` without the non-POSIX `-r`
/// would run the digest tool with no arguments and it would sit reading
/// stdin. An empty tree has to produce a digest, not a hang.
///
/// The input set -- `.mo`, `.c`, `.h`, `mote.toml` -- is exactly what
/// `scripts/build-self-hosted.sh`'s staleness scan already treats as the
/// compiler's inputs, and `mote.toml` is in it because
/// `gate_declared_deps` (lang/src/module.mo) can fail a load on a
/// manifest edit alone.
///
/// Its directory arrives through `Build.digest_dir` rather than directly,
/// because the empty root names the working directory and the shell cannot
/// take it -- the two spellings of one build then share an entry instead of
/// each compiling.
def Build.digest_script (tool : DigestTool) (dir : String) : String :=
    String.concat "cd "
        (String.concat (Proc.shell_quote (Build.digest_dir dir))
            (String.concat " && find . -type f \\( -name '*.mo' -o -name '*.c' -o -name '*.h' -o -name mote.toml \\) -exec "
                (String.concat (Build.tool_exec tool) " {} + | LC_ALL=C sort")))

/// Digest everything under `dir` that the compiler reads.
#[partial]
pub def Build.tree_digest_with (tool : DigestTool) (dir : String) : IO (Result String String) := do {
    let r <- Proc.capture "sh" ["-c", Build.digest_script tool dir];
    match r {
        Pair.pair code out =>
            if code == 0
            then return (ok (Sha256.hash out))
            else return (err (Build.digest_failed_error dir out))
    }
}

/// The digest of ONE file's contents, with no path in it.
///
/// The tool reads STDIN rather than being handed a filename, so its
/// output is `<hex>  -` and carries no trace of where the file lives.
/// That is the point: this is used for the compiler binary's own
/// identity, and a key that moved when the binary moved would miss on
/// every worktree.
#[partial]
pub def Build.file_digest_with (tool : DigestTool) (path : String) : IO (Result String String) := do {
    let script : String :=
        String.concat (Build.tool_exec tool) (String.concat " < " (Proc.shell_quote path));
    let r <- Proc.capture "sh" ["-c", script];
    match r {
        Pair.pair code out =>
            if code == 0
            then return (ok (Sha256.hash out))
            else return (err (Build.digest_failed_error path out))
    }
}

/// Probe, then digest. For one mote; callers digesting a whole closure
/// should probe once themselves and use `Build.tree_digest_with`.
#[partial]
pub def Build.tree_digest (dir : String) : IO (Result String String) := do {
    let t <- Build.probe_digest_tool;
    match t {
        err m => return (err m),
        ok tool => Build.tree_digest_with tool dir
    }
}

// ─── The canonical tree checksum (`mote.lock`) ───
//
// Unlike `tree_digest` above, this answer has to be the same on every
// machine and in every producer: it is committed to `mote.lock`, and a
// registry tarball's unpacked tree must hash like a git checkout of the
// same source. So the encoding is pinned here rather than inherited from
// whatever the digest tool prints:
//
//   <relative path>\n<mode>\n<byte length>\n<content>
//
// once per regular file, concatenated in `LC_ALL=C` byte order of the
// relative path. Each choice removes something that is not the source:
//
//   * relative, `/`-separated, no leading `./` -- a checkout's LOCATION is
//     not part of its identity, so two worktrees at the same commit agree.
//   * git index modes, `100644` / `100755`, from the owner-execute bit
//     alone -- umask, group and other bits, and the owner's identity never
//     enter the stream, so the same tree written by two users agrees.
//   * the length, which also makes the stream self-delimiting: content may
//     contain newlines and NULs, and the next entry still starts where the
//     length says.
//
// Directories are not entries (git does not track them either), and any
// entry named `.git`, `target` or `mote.lock` is excluded at any depth.
// A SYMLINK is refused by name: `find -type f` would silently drop it, and
// following it could leave the tree. `package-system` §2b's security rules
// put the same ban on loading through one.
//
// A file name containing a newline cannot be represented (the listing is
// read line by line), and fails loudly rather than hashing ambiguously:
// the second half of the name is read as its own path, and `wc`/`cat`
// reject it.

/// The pruning expression both `find` runs share. Applied to any entry
/// type, so a `.git` FILE -- what a linked worktree has instead of a
/// directory -- is excluded too, and `-prune` makes the whole `-o` branch
/// false so it is never printed.
def Build.checksum_prune : String :=
    "\\( -name .git -o -name target -o -name mote.lock \\) -prune"

/// The whole walk in one `sh`, so the tree is read once and the digest
/// tool sees a single stream.
///
/// Every stage's status is checked (each step ends in `|| { cat "$e"; exit
/// 1; }`), because a truncated stream still hashes to something and would
/// otherwise pass for a valid checksum. Diagnostics go to a temp file and
/// are replayed only on failure, so STDOUT IS EXACTLY the digest line --
/// `Proc.capture` merges the two streams, and a stray `find` warning
/// ahead of the hex would otherwise land in the parse.
///
/// Exit codes: 0 success, 2 symlink (stdout is its relative path), 1
/// anything else.
///
/// `sort` is a middle pipeline stage, so its own failure would not fail
/// the pipeline. That is acceptable: its only input is the temp file whose
/// `mktemp` just created it, and `sort` reports no failure over a readable
/// file.
#[partial]
def Build.checksum_script (tool : DigestTool) (dir : String) : String :=
    String.concat_all [
        "set -u\n",
        "export LC_ALL=C\n",
        "e=$(mktemp) || exit 1\n",
        "l=$(mktemp) || exit 1\n",
        "x=$(mktemp) || exit 1\n",
        "s=$(mktemp) || exit 1\n",
        "trap 'rm -f \"$e\" \"$l\" \"$x\" \"$s\"' EXIT\n",
        "cd ", Proc.shell_quote (Build.digest_dir dir), " 2>\"$e\" || { cat \"$e\"; exit 1; }\n",
        "find . ", Build.checksum_prune, " -o -type f -print > \"$l\" 2>\"$e\" || { cat \"$e\"; exit 1; }\n",
        "find . ", Build.checksum_prune, " -o -type l -print > \"$x\" 2>\"$e\" || { cat \"$e\"; exit 1; }\n",
        "if [ -s \"$x\" ]; then IFS= read -r first < \"$x\"; printf '%s' \"${first#./}\"; exit 2; fi\n",
        "sort \"$l\" | {\n",
        "while IFS= read -r f; do\n",
        "if [ -x \"$f\" ]; then m=100755; else m=100644; fi\n",
        "n=$(wc -c < \"$f\") || exit 1\n",
        "n=${n##* }\n",
        "printf '%s\\n%s\\n%s\\n' \"${f#./}\" \"$m\" \"$n\" || exit 1\n",
        "cat \"$f\" || exit 1\n",
        "done\n",
        "} > \"$s\" 2>>\"$e\" || { cat \"$e\"; exit 1; }\n",
        Build.tool_exec tool, " < \"$s\" 2>\"$e\" || { cat \"$e\"; exit 1; }\n",
    ]

/// A digest the tool printed, or an error. `sha256sum` and `shasum -a 256`
/// both print `<hex>  -` when they read stdin, so the first 64 characters
/// of the trimmed output are the digest; anything else means the tool did
/// not do what this asked, which must not become a checksum.
def Build.checksum_of_output (dir : String) (out : String) : Result String String :=
    let hex : String := String.slice (String.trim out) 0 64 in
    if Build.is_hex_64 hex
    then ok (String.concat "sha256:" hex)
    else err (Build.checksum_bad_output_error dir out)

def Build.is_hex_64 (s : String) : Bool :=
    String.length s == 64 && Build.is_hex_from s 0

#[partial]
def Build.is_hex_from (s : String) (i : I64) : Bool :=
    if i == 64 then true
    else String.contains "0123456789abcdef" (String.slice s i 1) && Build.is_hex_from s (i + 1)

def Build.checksum_result (dir : String) (r : Pair I64 String) : Result String String :=
    match r {
        Pair.pair code out => Build.checksum_result_of dir code out
    }

/// Split out so `code` has a concrete `I64` type at each comparison: as a
/// bare pattern binder it is still `A`, and an affine binder may not be
/// read twice.
def Build.checksum_result_of (dir : String) (code : I64) (out : String) : Result String String :=
    if code == 2
    then err (Build.symlink_error dir (String.trim out))
    else if code == 0
    then Build.checksum_of_output dir out
    else err (Build.checksum_failed_error dir out)

def Build.checksum_failed_error (dir : String) (out : String) : String :=
    let detail : String := String.trim out in
    if String.is_empty detail
    then "could not checksum " ++ dir
    else "could not checksum " ++ dir ++ ": " ++ detail

def Build.checksum_bad_output_error (dir : String) (out : String) : String :=
    "could not checksum " ++ dir ++ ": the digest tool printed no sha256 digest (" ++ String.trim out ++ ")"

def Build.symlink_error (dir : String) (rel : String) : String :=
    "cannot checksum " ++ dir ++ ": it contains a symbolic link (" ++ rel ++ "); a dependency tree must have no symlinks"

/// The canonical checksum of the tree at `dir`, as `sha256:<64 hex>` --
/// the value a `mote.lock` entry records.
///
/// `_with` takes an already-probed tool so a caller verifying a whole
/// closure probes once, exactly like `tree_digest_with`.
#[partial]
pub def Build.canonical_tree_checksum_with (tool : DigestTool) (dir : Path) : IO (Result String String) := do {
    let d : String := Path.to_string dir;
    let r <- Proc.capture "sh" ["-c", Build.checksum_script tool d];
    return (Build.checksum_result d r)
}

/// Probe, then checksum. For one tree; callers checksumming many should
/// probe once themselves and use `Build.canonical_tree_checksum_with`.
#[partial]
pub def Build.canonical_tree_checksum (dir : Path) : IO (Result String String) := do {
    let t <- Build.probe_digest_tool;
    match t {
        err m => return (err m),
        ok tool => Build.canonical_tree_checksum_with tool dir
    }
}
