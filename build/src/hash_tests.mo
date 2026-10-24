/// Tests for `build/src/hash.mo`.
///
/// Every one of these is about a property a CACHE KEY needs, not about
/// SHA-256 (std/src/sha256_tests.mo already pins the FIPS vectors). The
/// interesting ones are the two negatives: a digest must not move when a
/// file's timestamp moves, and must not move when the tree does.
///
/// Fixtures are built by shelling out. `IO.write_file` is `pub` now --
/// the `build` mote's own check cache writes its entries with it -- so
/// `Build.put_file` no longer HAS to redirect through `sh`. It still
/// does, because the two helpers beside it genuinely need a shell
/// (`rm -rf`, and `rm -rf && mkdir -p` in one call), and three fixture
/// helpers of one shape read better than two shapes to save four lines.
///
/// `canonical_tree_checksum` (the `mote.lock` value) is tested here too,
/// and its tests are about the ENCODING rather than about trees in
/// general: that the mode, the path and the excluded names are in it the
/// way `package-system` §2b says, and that `.git`/`target`/`mote.lock`
/// are not.

use std::process {process_id}
use build::hash {
    Build.canonical_tree_checksum, Build.probe_digest_tool, Build.tree_digest
}

/// A pid-and-tag-scoped fixture root, created empty. Pid-scoped because
/// the corpus sweep runs sharded and a fixed `/tmp` name would collide
/// across concurrent shards.
def Build.fixture_root (tag : String) : String :=
    String.concat "/tmp/monad_hash_fix_"
        (String.concat (I64.to_string process_id) (String.concat "_" tag))

def Build.fresh_fixture (tag : String) : IO String := do {
    let d : String := Build.fixture_root tag;
    let q : String := Proc.shell_quote d;
    let _r <- Proc.capture "sh" ["-c", String.concat "rm -rf " (String.concat q (String.concat " && mkdir -p " (String.concat q "/src")))];
    return d
}

def Build.put_file (dir : String) (rel : String) (content : String) : IO I64 := do {
    let path : String := String.concat dir (String.concat "/" rel);
    let script : String :=
        String.concat "printf %s "
            (String.concat (Proc.shell_quote content)
                (String.concat " > " (Proc.shell_quote path)));
    let r <- Proc.capture "sh" ["-c", script];
    match r { Pair.pair code _out => return code }
}

def Build.rm_fixture (dir : String) : IO I64 := do {
    let r <- Proc.capture "sh" ["-c", String.concat "rm -rf " (Proc.shell_quote dir)];
    match r { Pair.pair code _out => return code }
}

/// `""` for a failure, so a test can compare two digests as plain strings
/// and a separate test asserts that success happens at all.
def Build.digest_or_empty (r : Result String String) : String :=
    match r { ok h => h, err _ => "" }

def Build.checksum_at (dir : String) : IO String := do {
    let r <- Build.canonical_tree_checksum (Path.path dir);
    return (Build.digest_or_empty r)
}

/// Fixture directories the canonical checksum needs and `put_file` does
/// not create: a nested path for `.git/objects` and `target/debug`.
def Build.mkdir_under (dir : String) (rel : String) : IO I64 := do {
    let r <- Proc.capture "sh" ["-c", String.concat "mkdir -p " (Proc.shell_quote (String.concat dir (String.concat "/" rel)))];
    match r { Pair.pair code _out => return code }
}

def Build.put_symlink (dir : String) (rel : String) (target : String) : IO I64 := do {
    let script : String :=
        String.concat "ln -s "
            (String.concat (Proc.shell_quote target)
                (String.concat " " (Proc.shell_quote (String.concat dir (String.concat "/" rel)))));
    let r <- Proc.capture "sh" ["-c", script];
    match r { Pair.pair code _out => return code }
}

def Build.chmod_exec (dir : String) (rel : String) : IO I64 := do {
    let r <- Proc.capture "sh" ["-c", String.concat "chmod +x " (Proc.shell_quote (String.concat dir (String.concat "/" rel)))];
    match r { Pair.pair code _out => return code }
}

// ─── Tests ───

/// The machine this runs on has a digest tool. If this fails, every test
/// below is meaningless rather than wrong.
#[test]
def test_probe_finds_a_digest_tool : IO Bool := do {
    let t <- Build.probe_digest_tool;
    match t { ok _ => return true, err _ => return false }
}

#[test]
def test_tree_digest_of_a_fixture_succeeds : IO Bool := do {
    let d <- Build.fresh_fixture "ok";
    let _w <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let r <- Build.tree_digest d;
    let _c <- Build.rm_fixture d;
    return (Bool.not (String.is_empty (Build.digest_or_empty r)))
}

#[test]
def test_tree_digest_is_stable_across_two_runs : IO Bool := do {
    let d <- Build.fresh_fixture "stable";
    let _w <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let r1 <- Build.tree_digest d;
    let r2 <- Build.tree_digest d;
    let _c <- Build.rm_fixture d;
    return (String.beq (Build.digest_or_empty r1) (Build.digest_or_empty r2))
}

#[test]
def test_tree_digest_changes_when_a_byte_changes : IO Bool := do {
    let d <- Build.fresh_fixture "byte";
    let _w1 <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let r1 <- Build.tree_digest d;
    let _w2 <- Build.put_file d "src/a.mo" "def a : I64 := 2\n";
    let r2 <- Build.tree_digest d;
    let _c <- Build.rm_fixture d;
    return (Bool.not (String.beq (Build.digest_or_empty r1) (Build.digest_or_empty r2)))
}

#[test]
def test_tree_digest_changes_when_a_file_is_added : IO Bool := do {
    let d <- Build.fresh_fixture "added";
    let _w1 <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let r1 <- Build.tree_digest d;
    let _w2 <- Build.put_file d "src/b.mo" "def b : I64 := 2\n";
    let r2 <- Build.tree_digest d;
    let _c <- Build.rm_fixture d;
    return (Bool.not (String.beq (Build.digest_or_empty r1) (Build.digest_or_empty r2)))
}

/// A manifest edit alone must move the digest: `gate_declared_deps`
/// (lang/src/module.mo) can fail a load on `mote.toml` with every source
/// byte unchanged, so a key that ignored the manifest would cache a
/// result the manifest had already invalidated.
#[test]
def test_tree_digest_covers_the_manifest : IO Bool := do {
    let d <- Build.fresh_fixture "manifest";
    let _w1 <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let _m1 <- Build.put_file d "mote.toml" "[mote]\nname = \"x\"\n";
    let r1 <- Build.tree_digest d;
    let _m2 <- Build.put_file d "mote.toml" "[mote]\nname = \"y\"\n";
    let r2 <- Build.tree_digest d;
    let _c <- Build.rm_fixture d;
    return (Bool.not (String.beq (Build.digest_or_empty r1) (Build.digest_or_empty r2)))
}

/// CONTENT-addressed, not timestamp-addressed. `touch` moves the mtime
/// and nothing else, and the digest must not notice -- this is the whole
/// difference between this and `scripts/build-self-hosted.sh`'s staleness
/// scan.
#[test]
def test_tree_digest_ignores_a_touch : IO Bool := do {
    let d <- Build.fresh_fixture "touch";
    let _w <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let r1 <- Build.tree_digest d;
    let _t <- Proc.capture "sh" ["-c", String.concat "touch " (Proc.shell_quote (String.concat d "/src/a.mo"))];
    let r2 <- Build.tree_digest d;
    let _c <- Build.rm_fixture d;
    return (String.beq (Build.digest_or_empty r1) (Build.digest_or_empty r2))
}

/// Identical content at two different paths digests identically, which is
/// what lets two worktrees at the same commit share a cache entry. This
/// is why the script does `cd` + `find .` instead of `find <dir>`.
#[test]
def test_tree_digest_is_independent_of_the_path : IO Bool := do {
    let d1 <- Build.fresh_fixture "here";
    let d2 <- Build.fresh_fixture "there";
    let _w1 <- Build.put_file d1 "src/a.mo" "def a : I64 := 1\n";
    let _w2 <- Build.put_file d2 "src/a.mo" "def a : I64 := 1\n";
    let r1 <- Build.tree_digest d1;
    let r2 <- Build.tree_digest d2;
    let _c1 <- Build.rm_fixture d1;
    let _c2 <- Build.rm_fixture d2;
    return (String.beq (Build.digest_or_empty r1) (Build.digest_or_empty r2))
}

/// An empty tree is a digest, not a hang. `find -exec ... +` runs nothing
/// when nothing matches; `xargs -0` without the non-POSIX `-r` would have
/// run the digest tool with no arguments and sat reading stdin.
#[test]
def test_tree_digest_of_an_empty_tree_succeeds : IO Bool := do {
    let d <- Build.fresh_fixture "empty";
    let r <- Build.tree_digest d;
    let _c <- Build.rm_fixture d;
    match r { ok _ => return true, err _ => return false }
}

/// The empty root names the working directory, and the digest has to take
/// it. `Mote.discover` reports `""` for a manifest sitting in the working
/// directory -- `cd mymote && monad build src/main.mo`, the most ordinary
/// layout there is -- and `cd ''` is not a directory the shell can enter,
/// so the key became an error and the cache quietly declined to serve.
/// `.` is the same directory; that the two agree is what makes the two
/// spellings of one build share an entry instead of each compiling.
///
/// The `is_empty` guard is the other half: both sides being `""` (from two
/// errors) would satisfy equality and prove nothing.
#[test]
def test_tree_digest_takes_the_empty_root_as_the_working_directory : IO Bool := do {
    let r1 <- Build.tree_digest "";
    let r2 <- Build.tree_digest ".";
    let a : String := Build.digest_or_empty r1;
    let b : String := Build.digest_or_empty r2;
    return (String.beq a b && Bool.not (String.is_empty a))
}

/// A directory that does not exist is an error naming the directory, not
/// a silently-empty digest that would collide with the empty tree above.
#[test]
def test_tree_digest_of_a_missing_directory_errors : IO Bool := do {
    let r <- Build.tree_digest (Build.fixture_root "nonexistent_on_purpose");
    match r { ok _ => return false, err _ => return true }
}

// ─── The canonical tree checksum (`mote.lock`) ───

#[test]
def test_checksum_is_a_prefixed_sha256 : IO Bool := do {
    let d <- Build.fresh_fixture "ck_prefix";
    let _w <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let c <- Build.checksum_at d;
    let _c <- Build.rm_fixture d;
    return (String.starts_with "sha256:" c && String.length c == 71)
}

/// The digest of an empty stream. This pins the FORMAT, not merely "some
/// hash": a change to the encoding that left an empty tree hashing
/// differently would break every lockfile written before it.
#[test]
def test_checksum_of_an_empty_tree_is_the_empty_digest : IO Bool := do {
    let d <- Build.fresh_fixture "ck_empty";
    let c <- Build.checksum_at d;
    let _c <- Build.rm_fixture d;
    return (String.beq c "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
}

#[test]
def test_checksum_is_stable_across_two_runs : IO Bool := do {
    let d <- Build.fresh_fixture "ck_stable";
    let _w <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let c1 <- Build.checksum_at d;
    let c2 <- Build.checksum_at d;
    let _c <- Build.rm_fixture d;
    return (String.beq c1 c2 && Bool.not (String.is_empty c1))
}

#[test]
def test_checksum_changes_when_a_byte_changes : IO Bool := do {
    let d <- Build.fresh_fixture "ck_byte";
    let _w1 <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let c1 <- Build.checksum_at d;
    let _w2 <- Build.put_file d "src/a.mo" "def a : I64 := 2\n";
    let c2 <- Build.checksum_at d;
    let _c <- Build.rm_fixture d;
    return (Bool.not (String.beq c1 c2))
}

#[test]
def test_checksum_changes_when_a_file_is_added : IO Bool := do {
    let d <- Build.fresh_fixture "ck_added";
    let _w1 <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let c1 <- Build.checksum_at d;
    let _w2 <- Build.put_file d "src/b.mo" "def b : I64 := 2\n";
    let c2 <- Build.checksum_at d;
    let _c <- Build.rm_fixture d;
    return (Bool.not (String.beq c1 c2))
}

/// The PATH is part of the stream, so identical content under a different
/// name is a different tree. (A key that hashed only content would let one
/// dependency's lock entry stand in for another's.)
#[test]
def test_checksum_changes_when_a_file_is_renamed : IO Bool := do {
    let d1 <- Build.fresh_fixture "ck_name_a";
    let d2 <- Build.fresh_fixture "ck_name_b";
    let _w1 <- Build.put_file d1 "src/a.mo" "def a : I64 := 1\n";
    let _w2 <- Build.put_file d2 "src/b.mo" "def a : I64 := 1\n";
    let c1 <- Build.checksum_at d1;
    let c2 <- Build.checksum_at d2;
    let _c1 <- Build.rm_fixture d1;
    let _c2 <- Build.rm_fixture d2;
    return (Bool.not (String.beq c1 c2))
}

/// CONTENT-addressed, like the cache key: `touch` moves the mtime and
/// nothing else, and identity must not notice.
#[test]
def test_checksum_ignores_a_touch : IO Bool := do {
    let d <- Build.fresh_fixture "ck_touch";
    let _w <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let c1 <- Build.checksum_at d;
    let _t <- Proc.capture "sh" ["-c", String.concat "touch " (Proc.shell_quote (String.concat d "/src/a.mo"))];
    let c2 <- Build.checksum_at d;
    let _c <- Build.rm_fixture d;
    return (String.beq c1 c2)
}

/// The visible difference from `tree_digest`: a dependency's checksum
/// covers EVERY file in it, because that is the tree a registry tarball
/// would carry. The cache key is narrower on purpose -- an unrelated
/// README edit must not invalidate a build -- so this asserts both halves
/// at once, and would fail if the two functions were ever folded together.
#[test]
def test_checksum_covers_files_the_input_hash_ignores : IO Bool := do {
    let d <- Build.fresh_fixture "ck_readme";
    let _w <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let c1 <- Build.checksum_at d;
    let key_before <- Build.tree_digest d;
    let _r <- Build.put_file d "README.md" "docs\n";
    let c2 <- Build.checksum_at d;
    let key_after <- Build.tree_digest d;
    let _c <- Build.rm_fixture d;
    return (Bool.not (String.beq c1 c2)
        && String.beq (Build.digest_or_empty key_before) (Build.digest_or_empty key_after))
}

/// `.git/` (the checkout's own metadata), `target/` (a previous build) and
/// `mote.lock` (the file being written) are not source, so a git checkout
/// and a registry tarball of the same release agree.
#[test]
def test_checksum_ignores_dot_git_target_and_mote_lock : IO Bool := do {
    let d <- Build.fresh_fixture "ck_excluded";
    let _w <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let c1 <- Build.checksum_at d;
    let _g <- Build.mkdir_under d ".git/objects";
    let _o <- Build.put_file d ".git/objects/x" "junk";
    let _t <- Build.mkdir_under d "target/debug";
    let _j <- Build.put_file d "target/debug/y" "junk";
    let _l <- Build.put_file d "mote.lock" "version = 1\n";
    let c2 <- Build.checksum_at d;
    let _c <- Build.rm_fixture d;
    return (String.beq c1 c2 && Bool.not (String.is_empty c1))
}

/// The owner-execute bit becomes git's `100755`, so a script and a data
/// file with the same bytes are different trees.
#[test]
def test_checksum_changes_with_the_executable_bit : IO Bool := do {
    let d <- Build.fresh_fixture "ck_exec";
    let _w <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let c1 <- Build.checksum_at d;
    let _x <- Build.chmod_exec d "src/a.mo";
    let c2 <- Build.checksum_at d;
    let _c <- Build.rm_fixture d;
    return (Bool.not (String.beq c1 c2))
}

/// A checkout's location is not part of its identity, and neither is the
/// spelling of the path it was reached by -- `d` and `d/.` are one tree.
#[test]
def test_checksum_is_independent_of_the_tree_path : IO Bool := do {
    let d1 <- Build.fresh_fixture "ck_here";
    let d2 <- Build.fresh_fixture "ck_there";
    let _w1 <- Build.put_file d1 "src/a.mo" "def a : I64 := 1\n";
    let _w2 <- Build.put_file d2 "src/a.mo" "def a : I64 := 1\n";
    let c1 <- Build.checksum_at d1;
    let c2 <- Build.checksum_at d2;
    let c3 <- Build.checksum_at (String.concat d1 "/.");
    let _c1 <- Build.rm_fixture d1;
    let _c2 <- Build.rm_fixture d2;
    return (String.beq c1 c2 && String.beq c1 c3 && Bool.not (String.is_empty c1))
}

/// A missing tree is an error naming it, not the empty digest -- otherwise
/// a deleted dependency checkout would verify against an empty lock entry.
#[test]
def test_checksum_of_a_missing_directory_errors : IO Bool := do {
    let r <- Build.canonical_tree_checksum (Path.path (Build.fixture_root "ck_missing_on_purpose"));
    match r {
        Result.ok _ => return false,
        Result.err m => return (String.starts_with "could not checksum " m)
    }
}

/// `find -type f` would silently drop a symlink, and following one could
/// leave the tree. It is refused by name instead.
#[test]
def test_checksum_rejects_a_symlink_naming_it : IO Bool := do {
    let d <- Build.fresh_fixture "ck_link";
    let _w <- Build.put_file d "src/a.mo" "def a : I64 := 1\n";
    let _s <- Build.put_symlink d "src/b.mo" "a.mo";
    let r <- Build.canonical_tree_checksum (Path.path d);
    let _c <- Build.rm_fixture d;
    match r {
        Result.ok _ => return false,
        Result.err m => return (Build.names_the_link m)
    }
}

/// Reads the message twice, so it cannot be the match binder itself: an
/// unannotated binder is affine and `E` is not known to be `Copy`.
def Build.names_the_link (m : String) : Bool :=
    String.contains m "symbolic link" && String.contains m "src/b.mo"
