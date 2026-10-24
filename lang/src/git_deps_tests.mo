/// Tests for the reader half of git dependencies: `mote.lock` -> `dep_dirs`.
///
/// The mapping is pure once the lock has been read (`Mote.fill_dep_dirs`),
/// so it is tested without a filesystem here; the end-to-end path -- fetch
/// into a real cache, then resolve the `use` -- is
/// `build/src/fetch_tests.mo`, which is where both halves can be reached.
///
/// These live in their own file for the reason `path_tests.mo` does: a
/// `#[test]` inside a module that `lang/src/lib.mo` re-exports is never
/// attributed to a target module, and the sweep skips it silently.

use std::list {List.length}
use lang::mote {
  Mote.fill_dep_dirs, Mote.git_checkout_dir, Mote.parse_manifest, MoteManifest,
}
use lang::lock {GitPin, Lockfile, LockedGit, LockedMote}

def commit_x : String := "0123456789abcdef0123456789abcdef01234567"
def sum_x : String := "sha256:00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"

def app_text (dep_table : String) : String :=
    "[mote]\nname = \"app\"\nversion = \"0.1.0\"\n\n[dependencies.dep]\n" ++ dep_table

def git_app : Option MoteManifest :=
    Mote.parse_manifest "app" (app_text "git = \"file:///repo\"\ntag = \"v1\"\n")

def git_entry (name : String) (url : String) (subdir : Option String) : LockedMote :=
    let g : LockedGit := { url := url, pin := GitPin.tag "v1", commit := commit_x, subdir := subdir } in
    let m : LockedMote := { name := name, version := "0.1.0", checksum := sum_x, git := Option.some g } in
    m

def lock_of (entries : List LockedMote) : Lockfile :=
    let l : Lockfile := { motes := entries } in
    l

/// The path rule itself: the URL is keyed by sha256, the commit is the
/// leaf, and the root is the cache directory `monad fetch` writes into.
#[test]
def test_checkout_dir_is_keyed_by_the_url : Bool :=
    let p : String := Mote.git_checkout_dir "/h" "file:///repo" commit_x in
    String.starts_with "/h/cache/git/checkouts/" p
        && String.ends_with p ("/" ++ commit_x)
        && Bool.not (String.contains p "repo")

/// The whole reader half: a manifest declaring a git dependency, plus a
/// lock entry for it, gives that dependency a directory.
#[test]
def test_a_locked_git_dependency_becomes_a_directory : Bool :=
    match git_app {
        Option.none => false,
        Option.some m =>
            let filled : MoteManifest := Mote.fill_dep_dirs m (lock_of [git_entry "dep" "file:///repo" Option.none]) "/h" in
            String.beq (dep_dir filled "dep") (Mote.git_checkout_dir "/h" "file:///repo" commit_x)
    }

/// `subdir` selects the mote inside a repository that holds several.
#[test]
def test_a_subdir_entry_resolves_inside_the_checkout : Bool :=
    match git_app {
        Option.none => false,
        Option.some m =>
            let filled : MoteManifest := Mote.fill_dep_dirs m (lock_of [git_entry "dep" "file:///repo" (Option.some "motes/dep")]) "/h" in
            String.beq (dep_dir filled "dep")
                (Mote.git_checkout_dir "/h" "file:///repo" commit_x ++ "/motes/dep")
    }

/// A lock entry for a DIFFERENT repository must not locate this one --
/// resolving the wrong tree silently is the failure the lock exists to
/// prevent.
#[test]
def test_a_url_mismatch_is_not_located : Bool :=
    match git_app {
        Option.none => false,
        Option.some m =>
            let filled : MoteManifest := Mote.fill_dep_dirs m (lock_of [git_entry "dep" "file:///other" Option.none]) "/h" in
            String.is_empty (dep_dir filled "dep")
    }

/// No entry at all is "declared, not located", not an error: the `use`
/// still passes the declaration gate, and `--locked` is what reports the
/// stale lock.
#[test]
def test_an_absent_entry_leaves_the_dependency_unlocated : Bool :=
    match git_app {
        Option.none => false,
        Option.some m =>
            let filled : MoteManifest := Mote.fill_dep_dirs m (lock_of List.empty) "/h" in
            String.is_empty (dep_dir filled "dep")
    }

/// A `path` dependency keeps the manifest's own answer whatever the lock
/// says -- the lock never records path dependencies.
#[test]
def test_a_path_dependency_is_untouched : Bool :=
    // An ABSOLUTE path, because a relative one is joined onto the
    // declaring mote's own directory before it ever reaches the lock.
    match Mote.parse_manifest "app" (app_text "path = \"/tmp/dep\"\n") {
        Option.none => false,
        Option.some m =>
            let filled : MoteManifest := Mote.fill_dep_dirs m (lock_of [git_entry "dep" "file:///repo" Option.none]) "/h" in
            String.beq (dep_dir filled "dep") "/tmp/dep"
    }

/// The entry lookup is by the KEY the importer names, so a lock entry for
/// some other mote neither locates nor hides this one.
#[test]
def test_only_the_matching_entry_locates : Bool :=
    match git_app {
        Option.none => false,
        Option.some m =>
            let filled : MoteManifest :=
                Mote.fill_dep_dirs m (lock_of [git_entry "other" "file:///repo" Option.none]) "/h" in
            let count_before : I64 := List.length m.dep_dirs in
            String.is_empty (dep_dir filled "dep") && I64.beq count_before 1
    }

/// The dependency's directory as the loader would read it, or `""`.
def dep_dir (m : MoteManifest) (name : String) : String :=
    match find_dep m.dep_dirs name {
        Option.some d => d,
        Option.none => "",
    }

def find_dep (entries : List (Pair String String)) (name : String) : Option String :=
    match entries {
        List.empty => Option.none,
        List.cons e rest => match e {
            Pair.pair k v => if String.beq k name then Option.some v else find_dep rest name
        }
    }

/// A registry dependency has no directory until a registry exists, and a
/// git lock entry must not conjure one for it.
#[test]
def test_registry_dependencies_are_never_located : Bool :=
    match Mote.parse_manifest "app" (app_text "version = \">=0.1.0\"\n") {
        Option.none => false,
        Option.some m =>
            let filled : MoteManifest :=
                Mote.fill_dep_dirs m (lock_of [git_entry "dep" "file:///repo" Option.none]) "/h" in
            String.is_empty (dep_dir filled "dep")
    }
