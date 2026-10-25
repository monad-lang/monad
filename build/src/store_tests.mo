/// Tests for `build/src/store.mo` and `build/src/identity.mo`.
///
/// The store half is pure path arithmetic, so it is tested exhaustively
/// and cheaply -- every tier of the target-dir precedence, and the empty
/// -root case that would otherwise silently produce an ABSOLUTE `/target`.
/// The identity half needs a process, so it is tested for the two
/// properties a cache key actually depends on: it is stable, and it is
/// not the path.

use build::store {
  Build.artifact_ir_path, Build.entry_root_named, Build.resolve_target_dir,
  Build.store_path, artifact,
  check,
}
use build::identity {Build.compiler_digest, Build.compiler_exe_path}

// ─── target-dir precedence ───

#[test]
def test_target_dir_flag_wins_over_everything : Bool :=
    String.beq
        (Build.resolve_target_dir "flagdir" (Option.some "envdir") (Option.some "configdir") "root")
        "flagdir"

#[test]
def test_target_dir_env_beats_config : Bool :=
    String.beq
        (Build.resolve_target_dir "" (Option.some "envdir") (Option.some "configdir") "root")
        "envdir"

#[test]
def test_target_dir_config_beats_the_default : Bool :=
    String.beq
        (Build.resolve_target_dir "" Option.none (Option.some "target-monad") "root")
        "target-monad"

#[test]
def test_target_dir_falls_back_to_root_target : Bool :=
    String.beq (Build.resolve_target_dir "" Option.none Option.none "root") "root/target"

/// An empty flag, an empty env value and an empty config value all mean
/// "not set" rather than "set to the empty string" -- otherwise a
/// `MONAD_TARGET_DIR=` in the environment would silently redirect every
/// artifact to the filesystem root.
#[test]
def test_target_dir_treats_empty_values_as_unset : Bool :=
    String.beq (Build.resolve_target_dir "" (Option.some "") (Option.some "") "root") "root/target"

/// The case that produces an ABSOLUTE path if written naively: an empty
/// root must give `target`, never `/target`.
#[test]
def test_target_dir_of_an_empty_root_is_relative : Bool :=
    String.beq (Build.resolve_target_dir "" Option.none Option.none "") "target"

#[test]
def test_target_dir_of_dot_root_is_relative : Bool :=
    String.beq (Build.resolve_target_dir "" Option.none Option.none ".") "target"

// ─── store paths ───

#[test]
def test_store_path_separates_the_two_entry_kinds : Bool :=
    String.beq (Build.store_path "t" Entry.artifact "abc" "cli-0.1.0") "t/store/abc-cli-0.1.0" &&
    String.beq (Build.store_path "t" Entry.check "abc" "") "t/check/abc"

/// The `test` kind is a NAME, not an `Entry` constructor -- adding a third
/// constructor changed the nullary tags enough that `Entry.check` started
/// dispatching to `test` in the self-hosted compiler (2026-10-25). The
/// named root is the whole surface that kind needs.
#[test]
def test_entry_root_named_spells_the_test_kind : Bool :=
    String.beq (Build.entry_root_named "t" "test") "t/test"

/// The hash leads, so the directory sorts by key; the slug is a human
/// convenience and is allowed to be absent.
#[test]
def test_store_path_omits_an_empty_slug_cleanly : Bool :=
    String.beq (Build.store_path "t" Entry.artifact "abc" "") "t/store/abc"

/// The IR lives in the artifact root, named by the key: no slug, no
/// profile, no output name -- the key and the target dir, and nothing a
/// user typed. Its directory moves with the target dir like every other
/// entry's.
///
/// This is what makes a build under `-o a` and one under `-o b`
/// byte-identical, and it is not cosmetic: `llc` records its input's
/// BASENAME in the object it emits, so this name ends up inside the
/// artifact. Two names, two artifacts, one source.
#[test]
def test_artifact_ir_path_is_keyed_inside_the_artifact_root : Bool :=
    String.beq (Build.artifact_ir_path "t" "abc") "t/store/abc.ll" &&
    String.beq (Build.artifact_ir_path "t/monad" "abc") "t/monad/store/abc.ll"

/// Two keys are two files. If this ever collapsed, a rebuild after an edit
/// would compile the OLD IR under the new key -- the worst failure a cache
/// can produce, and a name collision is enough to cause it.
#[test]
def test_artifact_ir_path_moves_with_the_key : Bool :=
    Bool.not (String.beq (Build.artifact_ir_path "t" "abc") (Build.artifact_ir_path "t" "abd"))

// ─── compiler identity ───

/// There is a running binary and we can name it. If this fails on a
/// platform, the cache must turn itself off there -- which is what
/// `Build.compiler_digest` returning `err` makes the caller do.
#[test]
def test_compiler_exe_path_resolves : IO Bool := do {
    let p <- Build.compiler_exe_path;
    match p {
        Option.some s => return (Bool.not (String.is_empty s)),
        Option.none => return false
    }
}

#[test]
def test_compiler_digest_succeeds : IO Bool := do {
    let d <- Build.compiler_digest;
    match d { ok h => return (Bool.not (String.is_empty h)), err _ => return false }
}

/// Stable across calls -- a key that moved between two invocations would
/// make every entry a miss.
#[test]
def test_compiler_digest_is_stable : IO Bool := do {
    let a <- Build.compiler_digest;
    let b <- Build.compiler_digest;
    return (String.beq (Build.digest_text a) (Build.digest_text b))
}

/// NOT the path. The tool reads stdin precisely so the binary's location
/// stays out of its own identity; two checkouts of the same compiler must
/// agree, or no cache entry could ever be shared between worktrees.
#[test]
def test_compiler_digest_is_not_the_path : IO Bool := do {
    let d <- Build.compiler_digest;
    let p <- Build.compiler_exe_path;
    match p {
        Option.none => return false,
        Option.some path => return (Bool.not (String.contains (Build.digest_text d) path))
    }
}

def Build.digest_text (r : Result String String) : String :=
    match r { ok h => h, err _ => "" }
