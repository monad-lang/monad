/// Tests for `build/src/closure.mo` -- the cache key.
///
/// Two things are being checked, and the second matters more. That the key
/// MOVES when an input moves is the cheap half. That it does NOT move when
/// something irrelevant moves is what makes a cache shareable at all: a key
/// sensitive to a path or a timestamp would miss on every worktree and
/// every checkout, which is a slow cache rather than a wrong one -- but a
/// key that misses everything is indistinguishable from having none.

use std::list {List.contains_by}
use std::process {process_id}
use build::closure {
    Build.closure_digest_with, Build.closure_seed, Build.input_hash,
    Build.toolchain_seed_wanted,
}
use build::hash {Build.probe_digest_tool}
def Build.fix_root (tag : String) : String :=
    String.concat "/tmp/monad_clo_"
        (String.concat (I64.to_string process_id) (String.concat "_" tag))

/// A two-mote fixture: `<root>/a` declaring `<root>/b` as a path
/// dependency, so the walk has an edge to follow.
#[partial]
def Build.two_mote_fixture (tag : String) : IO String := do {
    let d : String := Build.fix_root tag;
    let q : String := Proc.shell_quote d;
    // `let … in` would abort the parse inside a do-block; `:=` with a `;`
    // is the do-block spelling.
    let script : String := "rm -rf " ++ q ++ " && mkdir -p " ++ q ++ "/a/src " ++ q ++ "/b/src";
    let _r <- Proc.capture "sh" ["-c", script];
    let _m1 <- Build.put d "a/mote.toml" "[mote]\nname = \"a\"\n\n[dependencies.b]\npath = \"../b\"\n";
    let _s1 <- Build.put d "a/src/lib.mo" "def a : I64 := 1\n";
    let _m2 <- Build.put d "b/mote.toml" "[mote]\nname = \"b\"\n";
    let _s2 <- Build.put d "b/src/lib.mo" "def b : I64 := 2\n";
    return d
}

#[partial]
def Build.put (root : String) (rel : String) (content : String) : IO I64 := do {
    let path : String := String.concat root (String.concat "/" rel);
    let script : String := String.concat "printf %s "
        (String.concat (Proc.shell_quote content) (String.concat " > " (Proc.shell_quote path)));
    let r <- Proc.capture "sh" ["-c", script];
    match r { Pair.pair code _o => return code }
}

#[partial]
def Build.rm (d : String) : IO I64 := do {
    let r <- Proc.capture "sh" ["-c", String.concat "rm -rf " (Proc.shell_quote d)];
    match r { Pair.pair code _o => return code }
}

def Build.text (r : Result String String) : String :=
    match r { ok h => h, err _ => "" }

#[partial]
def Build.closure_of (dir : String) : IO (Result String String) := do {
    let t <- Build.probe_digest_tool;
    match t { err m => return (err m), ok tool => Build.closure_digest_with tool dir }
}

// ─── the closure edge is actually followed ───

/// Editing a DEPENDENCY changes the root's closure digest. Without this
/// the walk could be silently digesting only the root and the cache would
/// serve stale results after any dependency edit -- the exact failure the
/// whole key exists to prevent.
#[test]
def test_closure_follows_a_declared_dependency : IO Bool := do {
    let d <- Build.two_mote_fixture "dep";
    let r1 <- Build.closure_of (String.concat d "/a");
    let _e <- Build.put d "b/src/lib.mo" "def b : I64 := 999\n";
    let r2 <- Build.closure_of (String.concat d "/a");
    let _c <- Build.rm d;
    return (Bool.not (String.beq (Build.text r1) (Build.text r2)))
}

#[test]
def test_closure_changes_when_the_root_changes : IO Bool := do {
    let d <- Build.two_mote_fixture "root";
    let r1 <- Build.closure_of (String.concat d "/a");
    let _e <- Build.put d "a/src/lib.mo" "def a : I64 := 42\n";
    let r2 <- Build.closure_of (String.concat d "/a");
    let _c <- Build.rm d;
    return (Bool.not (String.beq (Build.text r1) (Build.text r2)))
}

/// A manifest edit that changes nothing about the SOURCES still moves the
/// key, because `gate_declared_deps` can fail a load on the manifest
/// alone.
#[test]
def test_closure_covers_a_manifest_edit : IO Bool := do {
    let d <- Build.two_mote_fixture "manifest";
    let r1 <- Build.closure_of (String.concat d "/a");
    let _e <- Build.put d "b/mote.toml" "[mote]\nname = \"b\"\nversion = \"9.9.9\"\n";
    let r2 <- Build.closure_of (String.concat d "/a");
    let _c <- Build.rm d;
    return (Bool.not (String.beq (Build.text r1) (Build.text r2)))
}

#[test]
def test_closure_is_stable_across_two_runs : IO Bool := do {
    let d <- Build.two_mote_fixture "stable";
    let r1 <- Build.closure_of (String.concat d "/a");
    let r2 <- Build.closure_of (String.concat d "/a");
    let _c <- Build.rm d;
    return (String.beq (Build.text r1) (Build.text r2))
}

/// Content, not timestamps.
#[test]
def test_closure_ignores_a_touch : IO Bool := do {
    let d <- Build.two_mote_fixture "touch";
    let r1 <- Build.closure_of (String.concat d "/a");
    let _t <- Proc.capture "sh" ["-c", String.concat "touch " (Proc.shell_quote (String.concat d "/b/src/lib.mo"))];
    let r2 <- Build.closure_of (String.concat d "/a");
    let _c <- Build.rm d;
    return (String.beq (Build.text r1) (Build.text r2))
}

/// The same two motes at a different path key identically -- what lets two
/// worktrees at one commit share an entry.
#[test]
def test_closure_is_independent_of_the_path : IO Bool := do {
    let d1 <- Build.two_mote_fixture "pathA";
    let d2 <- Build.two_mote_fixture "pathB";
    let r1 <- Build.closure_of (String.concat d1 "/a");
    let r2 <- Build.closure_of (String.concat d2 "/a");
    let _c1 <- Build.rm d1;
    let _c2 <- Build.rm d2;
    return (String.beq (Build.text r1) (Build.text r2))
}

/// A cyclic closure TERMINATES. `init` declares `std` as a dev-dependency
/// while `std` declares `init`, and `MoteManifest` merges both tables, so
/// this is the shape of the real corpus and not a contrived one. Before
/// the visited set, this did not return.
#[test]
def test_closure_terminates_on_a_cycle : IO Bool := do {
    let d : String := Build.fix_root "cycle";
    let q : String := Proc.shell_quote d;
    let _mk <- Proc.capture "sh" ["-c", "rm -rf " ++ q ++ " && mkdir -p " ++ q ++ "/a/src " ++ q ++ "/b/src"];
    let _m1 <- Build.put d "a/mote.toml" "[mote]\nname = \"a\"\n\n[dependencies.b]\npath = \"../b\"\n";
    let _m2 <- Build.put d "b/mote.toml" "[mote]\nname = \"b\"\n\n[dependencies.a]\npath = \"../a\"\n";
    let _s1 <- Build.put d "a/src/lib.mo" "def a : I64 := 1\n";
    let _s2 <- Build.put d "b/src/lib.mo" "def b : I64 := 2\n";
    let r <- Build.closure_of (String.concat d "/a");
    let _c <- Build.rm d;
    match r { ok h => return (Bool.not (String.is_empty h)), err _ => return false }
}

// ─── what the walk starts from ───

/// The ambient pair the WORKING DIRECTORY offers is part of the key, even
/// for a root that never declared it.
///
/// This is the false hit measured on `examples/`: appending a byte to
/// `std/src/io.mo` moved no key at all, because the walk started from the
/// root directory alone while `resolve_module_file` had already resolved
/// `std` out of the working directory. Conditional on the working
/// directory, because that is what the seed reads -- under a checkout the
/// pair must be seeded, and where there is no `init/src/lib.mo` there is
/// nothing to seed.
#[test]
def test_closure_seed_covers_the_working_directory_ambient_pair : IO Bool := do {
    let d <- Build.two_mote_fixture "ambient";
    let seed <- Build.closure_seed (String.concat d "/a");
    let init_here <- IO.file_exists (Path.path "init/src/lib.mo");
    let std_here <- IO.file_exists (Path.path "std/src/lib.mo");
    let _c <- Build.rm d;
    return (List.contains_by String.beq (String.concat d "/a") seed
        && (if init_here then List.contains_by String.beq "init" seed else true)
        && (if std_here then List.contains_by String.beq "std" seed else true))
}

/// The toolchain root is walked ONLY when the working directory did not
/// answer for the ambient pair, and the polarity here was once inverted in
/// both directions at once: the root was seeded where the local pair
/// exists (re-keying every entry in a dev checkout the night a nightly
/// lands) and skipped where it does not (leaving the `init`/`std` the
/// compile actually read out of the key -- a false hit, the failure this
/// whole file exists to prevent).
///
/// Asserted on the PREDICATE and not through `toolchain_seed`, because the
/// seed's other half reads the environment: with no toolchain configured
/// both polarities return empty, so a test through the seed would have
/// passed while the bug was live.
#[test]
def test_toolchain_root_is_walked_only_without_a_local_pair : IO Bool := do {
    return (Bool.not (Build.toolchain_seed_wanted ["init", "std"])
        && Build.toolchain_seed_wanted ["init"]
        && Build.toolchain_seed_wanted List.empty)
}

// ─── the full input hash ───

def Build.fixture_src (d : String) : String := String.concat d "/a/src/lib.mo"
def Build.fixture_root (d : String) : String := String.concat d "/a"

/// Two files, ONE directory, and no `mote.toml` above either: the
/// script-mode shape, where both files root at the directory they sit in
/// and therefore share a closure digest.
#[partial]
def Build.script_pair_fixture (tag : String) : IO String := do {
    let d : String := Build.fix_root tag;
    let q : String := Proc.shell_quote d;
    let script : String := "rm -rf " ++ q ++ " && mkdir -p " ++ q;
    let _r <- Proc.capture "sh" ["-c", script];
    let _o <- Build.put d "one.mo" "def one : I64 := 111\n";
    let _t <- Build.put d "two.mo" "def two : I64 := 222\n";
    return d
}

#[test]
def test_input_hash_succeeds : IO Bool := do {
    let d <- Build.two_mote_fixture "ih";
    let r <- Build.input_hash (Build.fixture_src d) (Build.fixture_root d) "debug" "x86_64-unknown-linux-gnu";
    let _c <- Build.rm d;
    return (Bool.not (String.is_empty (Build.text r)))
}

/// The profile is part of the key: a debug and a release build of the
/// same sources are different artifacts and must not share an entry.
#[test]
def test_input_hash_separates_profiles : IO Bool := do {
    let d <- Build.two_mote_fixture "prof";
    let a <- Build.input_hash (Build.fixture_src d) (Build.fixture_root d) "debug" "x86_64-unknown-linux-gnu";
    let b <- Build.input_hash (Build.fixture_src d) (Build.fixture_root d) "release" "x86_64-unknown-linux-gnu";
    let _c <- Build.rm d;
    return (Bool.not (String.beq (Build.text a) (Build.text b)))
}

/// So is the triple, which is why it is threaded through before anything
/// varies it -- adding it later would invalidate every entry written
/// without it.
#[test]
def test_input_hash_separates_targets : IO Bool := do {
    let d <- Build.two_mote_fixture "tgt";
    let a <- Build.input_hash (Build.fixture_src d) (Build.fixture_root d) "debug" "x86_64-unknown-linux-gnu";
    let b <- Build.input_hash (Build.fixture_src d) (Build.fixture_root d) "debug" "aarch64-unknown-linux-gnu";
    let _c <- Build.rm d;
    return (Bool.not (String.beq (Build.text a) (Build.text b)))
}

/// Both calls below pass the SAME root string -- the directory the two
/// files live in, which is also each file's mote root -- so the closure
/// digest and every other ingredient agree and the file's own bytes are
/// the only thing left that can separate them.
///
/// This is the shape that served `two.mo` the binary built from `one.mo`:
/// before the file was an ingredient the two keys were equal by
/// construction, and `monad build two.mo` printed `cached` and then ran
/// `one`'s program.
#[test]
def test_input_hash_separates_sibling_scripts : IO Bool := do {
    let d <- Build.script_pair_fixture "sib";
    let a <- Build.input_hash (String.concat d "/one.mo") d "debug" "x86_64-unknown-linux-gnu";
    let b <- Build.input_hash (String.concat d "/two.mo") d "debug" "x86_64-unknown-linux-gnu";
    let _c <- Build.rm d;
    return (Bool.not (String.is_empty (Build.text a))
        && Bool.not (String.is_empty (Build.text b))
        && Bool.not (String.beq (Build.text a) (Build.text b)))
}
