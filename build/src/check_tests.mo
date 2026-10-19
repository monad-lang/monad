/// Tests for `build/src/check.mo`.
///
/// The split here is the point. The PURE half pins the safety property
/// the whole cache rests on: a key moves when any one of its three
/// ingredients moves, and the plan says nothing at all when it is not
/// asked. The I/O half pins the property a cache most needs and is
/// easiest to get wrong -- that a DAMAGED entry is a MISS and not a
/// wrong answer. A cache that mistakes a truncated entry for a hit
/// reports a clean check that never ran, which is the worst failure this
/// work can produce.
///
/// Fixtures are pid-and-tag-scoped because the corpus sweep runs sharded
/// and a fixed `/tmp` name would collide across concurrent shards.

use std::process {process_id}
use build::check {
  Build.check_block, Build.check_entry_dir, Build.check_entry_read,
  Build.check_entry_write, Build.check_key, Build.check_plan,
  Build.check_plan_active, Build.check_plan_key, Build.check_plan_reason,
  Build.check_plan_root, Build.check_worth_caching, Build.mote_root_of, CheckPlan,
}
use build::store {Build.ensure_dir, Build.write_leaf}

/// A pid-and-tag-scoped fixture root.
def Build.check_fixture_root (tag : String) : String :=
    String.concat "/tmp/monad_check_fix_"
        (String.concat (I64.to_string process_id) (String.concat "_" tag))

/// An empty fixture root, removed first so a rerun starts clean.
#[partial]
def Build.check_fresh_fixture (tag : String) : IO String := do {
    let d : String := Build.check_fixture_root tag;
    let _r <- Proc.capture "sh" ["-c", String.concat "rm -rf " (Proc.shell_quote d)];
    let _m <- Build.ensure_dir (String.concat d "/src");
    return d
}

#[partial]
def Build.check_seed_file (d : String) (rel : String) (content : String) : IO I64 := do {
    let ok <- Build.write_leaf (String.concat d (String.concat "/" rel)) content;
    return (if ok then 0 else 1)
}

#[partial]
def Build.check_drop_fixture (d : String) : IO I64 := do {
    let r <- Proc.capture "sh" ["-c", String.concat "rm -rf " (Proc.shell_quote d)];
    match r { Pair.pair code _out => return code }
}

/// A two-mote fixture: `app` declaring `lib` as a dependency, so the
/// closure walk has a real edge to follow and `Mote.discover` has real
/// manifests to find. Both are ordinary motes -- a `[mote] name` and a
/// declared dependency are all the walk reads.
#[partial]
def Build.check_fresh_dep_fixture (tag : String) : IO String := do {
    let d <- Build.check_fresh_fixture tag;
    let app : String := String.concat d "/app";
    let lib : String := String.concat d "/lib";
    let _m1 <- Build.ensure_dir (String.concat app "/src");
    let _m2 <- Build.ensure_dir (String.concat lib "/src");
    let _t1 <- Build.check_seed_file app "mote.toml" "[mote]\nname = \"app\"\n\n[dependencies.lib]\npath = \"../lib\"\n";
    let _t2 <- Build.check_seed_file lib "mote.toml" "[mote]\nname = \"lib\"\n";
    let _a <- Build.check_seed_file app "src/a.mo" "def a : I64 := 1\n";
    let _b <- Build.check_seed_file app "src/b.mo" "def b : I64 := 2\n";
    let _l <- Build.check_seed_file lib "src/l.mo" "def l : I64 := 1\n";
    return d
}

/// A key as a plain string, `""` for "no key" -- so a test can compare
/// two keys directly, and a separate test asserts that a key happens at
/// all.
def Build.key_or_empty (p : CheckPlan) (f : String) : String :=
    match Build.check_plan_key p f {
        Option.none => "",
        Option.some k => k,
    }

/// A hand-built active plan, so the key-comparison tests need no
/// filesystem and no compiler binary.
def Build.plan_over (keys : List (Pair String String)) : CheckPlan :=
    CheckPlan.active "/somewhere/check" keys

// ─── check_block: what a hit replays, byte for byte ───

#[test]
def test_check_block_of_no_diagnostics_is_ok : Bool :=
    String.beq (Build.check_block "a.mo" List.empty List.empty) "ok    a.mo"

/// The header, then every diagnostic on its own line. `check_block` is
/// `intercalate "\n"`, which is what the loop's old
/// `mapM_ println` printed -- no trailing newline, because `println`
/// supplies that at the call site.
#[test]
def test_check_block_of_diagnostics_is_header_then_lines : Bool :=
    String.beq (Build.check_block "a.mo" ["one", "two"] List.empty) "FAIL  a.mo (2 error(s))\none\ntwo"

#[test]
def test_check_block_of_one_diagnostic_has_no_trailing_newline : Bool :=
    String.beq (Build.check_block "a.mo" ["only"] List.empty) "FAIL  a.mo (1 error(s))\nonly"

/// A clean file with warnings: not `ok` (something is reported), not
/// `FAIL` (nothing failed) -- a third status with the same column shape.
#[test]
def test_check_block_of_warnings_only_is_warn_header_then_lines : Bool :=
    String.beq (Build.check_block "a.mo" List.empty ["w1", "w2"]) "WARN  a.mo (2 warning(s))\nw1\nw2"

/// When both kinds are present the errors own the header -- the file
/// fails -- and the warnings follow the errors, so the failure is read
/// first and the warnings never push it off the first lines.
#[test]
def test_check_block_of_errors_and_warnings_prints_errors_first : Bool :=
    String.beq (Build.check_block "a.mo" ["boom"] ["w"]) "FAIL  a.mo (1 error(s))\nboom\nw"

// ─── check_worth_caching: the "expensive" half of the rule ───

/// One file is the editor loop, whose cost is the closure load and whose
/// key would cost a digest of the compiler binary. Not worth caching.
#[test]
def test_worth_caching_is_false_for_one_file : Bool :=
    Bool.not (Build.check_worth_caching 1)

#[test]
def test_worth_caching_is_false_for_no_files : Bool :=
    Bool.not (Build.check_worth_caching 0)

#[test]
def test_worth_caching_is_true_for_two_files : Bool :=
    Build.check_worth_caching 2

// ─── the plan: silence when not asked, a reason when it could not ───

#[test]
def test_inactive_plan_has_no_root : Bool :=
    String.is_empty (Build.check_plan_root (CheckPlan.inactive ""))

#[test]
def test_inactive_plan_has_no_keys : Bool :=
    match Build.check_plan_key (CheckPlan.inactive "") "a.mo" {
        Option.none => true,
        Option.some _k => false,
    }

/// `""` is "not asked for", which is not the same as a failure and must
/// print nothing -- `--no-cache`, `--verbose` and a single-file run all
/// land here, and the user who asked for those knows why.
#[test]
def test_inactive_plan_by_request_reports_nothing : Bool :=
    String.is_empty (Build.check_plan_reason (CheckPlan.inactive ""))

/// A non-empty reason means the cache wanted to run and could not. That
/// is the one case worth a line, because a silently disabled cache on
/// the machine that needed it is invisible otherwise.
#[test]
def test_inactive_plan_with_a_reason_reports_it : Bool :=
    String.beq (Build.check_plan_reason (CheckPlan.inactive "no digest tool")) "no digest tool"

#[test]
def test_active_plan_has_nothing_to_report : Bool :=
    String.is_empty (Build.check_plan_reason (Build.plan_over List.empty))

#[test]
def test_active_plan_is_active : Bool :=
    Build.check_plan_active (Build.plan_over List.empty)

#[test]
def test_inactive_plan_is_not_active : Bool :=
    Bool.not (Build.check_plan_active (CheckPlan.inactive ""))

#[test]
def test_active_plan_has_its_root : Bool :=
    String.beq (Build.check_plan_root (Build.plan_over List.empty)) "/somewhere/check"

// ─── key lookup ───

#[test]
def test_plan_key_finds_a_file : Bool :=
    String.beq (Build.key_or_empty (Build.plan_over [Pair.pair "a.mo" "k1"]) "a.mo") "k1"

/// A file with no key is checked normally and simply not recorded. That
/// is the safe direction: a missing key costs a check, which is what was
/// going to happen anyway.
#[test]
def test_plan_key_misses_an_unknown_file : Bool :=
    String.is_empty (Build.key_or_empty (Build.plan_over [Pair.pair "a.mo" "k1"]) "b.mo")

#[test]
def test_plan_key_finds_the_last_of_many : Bool :=
    String.beq (Build.key_or_empty (Build.plan_over [Pair.pair "a.mo" "k1", Pair.pair "b.mo" "k2"]) "b.mo") "k2"

/// A file appearing twice keeps its FIRST key, which is the one recorded
/// the first time it was checked in this run. `plan_keys` only ever emits
/// one entry per file, so this is a guard on a case that should not arise
/// rather than a behaviour anything depends on.
#[test]
def test_plan_key_of_a_duplicate_takes_the_first : Bool :=
    String.beq (Build.key_or_empty (Build.plan_over [Pair.pair "a.mo" "k1", Pair.pair "a.mo" "k2"]) "a.mo") "k1"

// ─── the key moves when its ingredients move ───

/// The three ingredients are the file's bytes, its mote's closure, and
/// the compiler. Each must be able to move the key on its own -- these
/// three tests are the whole safety argument for `check_key`, stated as
/// three facts rather than as prose.
#[test]
def test_key_moves_with_the_file : Bool :=
    Bool.not (String.beq (Build.check_key "f1" "c" "x") (Build.check_key "f2" "c" "x"))

#[test]
def test_key_moves_with_the_closure : Bool :=
    Bool.not (String.beq (Build.check_key "f" "c1" "x") (Build.check_key "f" "c2" "x"))

/// The one that matters most in THIS repository: an uncommitted `lang/`
/// edit rebuilds the compiler with an unchanged `build_commit`, so
/// `build_commit` cannot be the ingredient here. It is the digest of the
/// running binary instead, and a digest that did not move would serve
/// stale results exactly during the development loop.
#[test]
def test_key_moves_with_the_compiler : Bool :=
    Bool.not (String.beq (Build.check_key "f" "c" "x1") (Build.check_key "f" "c" "x2"))

/// The same inputs give the same key. Without this the cache would miss
/// forever and the tests above would all still pass.
#[test]
def test_key_is_stable_for_the_same_inputs : Bool :=
    String.beq (Build.check_key "f" "c" "x") (Build.check_key "f" "c" "x")

// ─── entry paths ───

#[test]
def test_entry_dir_is_root_slash_key : Bool :=
    String.beq (Build.check_entry_dir "/t/check" "abc") "/t/check/abc"

// ─── the entry: write then read ───

#[test]
def test_entry_round_trips : IO Bool := do {
    let d <- Build.check_fresh_fixture "round";
    let _w <- Build.check_entry_write d "k1" 3 2 "FAIL  a.mo (3 error(s))\nx\ny\nz";
    let r <- Build.check_entry_read d "k1";
    let _c <- Build.check_drop_fixture d;
    match r {
        Option.none => return false,
        Option.some p => match p {
            Pair.pair tally block =>
                return (tally.errors == 3) && (tally.warnings == 2) && String.beq block "FAIL  a.mo (3 error(s))\nx\ny\nz",
        }
    }
}

/// A zero-error entry is the common case (a clean corpus run) and must
/// round-trip like any other: `0` is a count, not an absence.
#[test]
def test_entry_round_trips_a_zero_error_result : IO Bool := do {
    let d <- Build.check_fresh_fixture "zero";
    let _w <- Build.check_entry_write d "k0" 0 0 "ok    a.mo";
    let r <- Build.check_entry_read d "k0";
    let _c <- Build.check_drop_fixture d;
    match r {
        Option.none => return false,
        Option.some p => match p {
            Pair.pair tally block => return (tally.errors == 0) && String.beq block "ok    a.mo",
        }
    }
}

/// An `ok` block is one line with no `\n` in it, and a `FAIL` block is
/// many -- neither shape may acquire a trailing newline in the store, or
/// a replay would differ from the miss it is replacing.
#[test]
def test_entry_round_trips_a_multiline_block : IO Bool := do {
    let d <- Build.check_fresh_fixture "multi";
    let block : String := "FAIL  a.mo (2 error(s))\nfirst error\nsecond error";
    let _w <- Build.check_entry_write d "km" 2 0 block;
    let r <- Build.check_entry_read d "km";
    let _c <- Build.check_drop_fixture d;
    match r {
        Option.none => return false,
        Option.some p => match p { Pair.pair tally b => return (tally.errors == 2) && String.beq b block },
    }
}

/// An entry written before warnings existed has no `warnings` leaf. It
/// must stay a HIT -- the checker that wrote it could not produce
/// warning text -- and replay an honest zero warning count.
#[test]
def test_entry_without_a_warnings_leaf_is_a_hit_with_zero_warnings : IO Bool := do {
    let d <- Build.check_fresh_fixture "oldfmt";
    let dir : String := Build.check_entry_dir d "k";
    let _m <- Build.ensure_dir dir;
    let _w1 <- Build.write_leaf (String.concat dir "/errors") "0";
    let _w2 <- Build.write_leaf (String.concat dir "/out") "ok    a.mo";
    let r <- Build.check_entry_read d "k";
    let _c <- Build.check_drop_fixture d;
    match r {
        Option.none => return false,
        Option.some p => match p {
            Pair.pair tally block => return (tally.errors == 0) && (tally.warnings == 0) && String.beq block "ok    a.mo",
        }
    }
}

#[test]
def test_entry_read_of_a_missing_key_is_none : IO Bool := do {
    let d <- Build.check_fresh_fixture "missing";
    let r <- Build.check_entry_read d "never-written";
    let _c <- Build.check_drop_fixture d;
    match r { Option.none => return true, Option.some _p => return false }
}

// ─── the entry: every way it can be damaged is a MISS ───
//
// A miss costs a check, which is what was going to happen anyway; a hit
// is only ever a saving. That asymmetry is what makes a damaged entry
// harmless rather than poisonous.

/// `errors` is written FIRST, so this (a count with no output) should not
/// arise -- and if it does, it must not be read as a hit with an empty
/// block, which would print nothing where diagnostics belong.
#[test]
def test_entry_read_without_the_output_is_none : IO Bool := do {
    let d <- Build.check_fresh_fixture "noout";
    let dir : String := Build.check_entry_dir d "k";
    let _m <- Build.ensure_dir dir;
    let _w <- Build.write_leaf (String.concat dir "/errors") "1";
    let r <- Build.check_entry_read d "k";
    let _c <- Build.check_drop_fixture d;
    match r { Option.none => return true, Option.some _p => return false }
}

/// The mirror: output with no count. It cannot be replayed, because the
/// summary line needs the number and there is nothing to re-derive it
/// from -- and reporting the block with a count of zero would understate
/// the errors.
#[test]
def test_entry_read_without_the_count_is_none : IO Bool := do {
    let d <- Build.check_fresh_fixture "nocount";
    let dir : String := Build.check_entry_dir d "k";
    let _m <- Build.ensure_dir dir;
    let _w <- Build.write_leaf (String.concat dir "/out") "FAIL  a.mo (1 error(s))\nboom";
    let r <- Build.check_entry_read d "k";
    let _c <- Build.check_drop_fixture d;
    match r { Option.none => return true, Option.some _p => return false }
}

/// A count that is not a number is a miss, not an error. `parse_i64`
/// answers `none` at the first non-digit, so a half-written or truncated
/// count file lands here rather than becoming a bogus total.
#[test]
def test_entry_read_of_a_corrupt_count_is_none : IO Bool := do {
    let d <- Build.check_fresh_fixture "corrupt";
    let dir : String := Build.check_entry_dir d "k";
    let _m <- Build.ensure_dir dir;
    let _w1 <- Build.write_leaf (String.concat dir "/errors") "3x";
    let _w2 <- Build.write_leaf (String.concat dir "/out") "ok    a.mo";
    let r <- Build.check_entry_read d "k";
    let _c <- Build.check_drop_fixture d;
    match r { Option.none => return true, Option.some _p => return false }
}

/// An empty count file is the truncated case, and `parse_i64 ""` is
/// `none` too -- checked separately because it is the one a partial write
/// actually produces.
#[test]
def test_entry_read_of_an_empty_count_is_none : IO Bool := do {
    let d <- Build.check_fresh_fixture "emptycount";
    let dir : String := Build.check_entry_dir d "k";
    let _m <- Build.ensure_dir dir;
    let _w1 <- Build.write_leaf (String.concat dir "/errors") "";
    let _w2 <- Build.write_leaf (String.concat dir "/out") "ok    a.mo";
    let r <- Build.check_entry_read d "k";
    let _c <- Build.check_drop_fixture d;
    match r { Option.none => return true, Option.some _p => return false }
}

/// A key that is a prefix of a real one must not find the real one. The
/// store is a directory per key, so this is really a test that nothing
/// does a prefix match -- cheap to state, and it is the shape a
/// mis-implemented lookup takes.
#[test]
def test_entry_read_does_not_prefix_match : IO Bool := do {
    let d <- Build.check_fresh_fixture "prefix";
    let _w <- Build.check_entry_write d "abcdef" 1 0 "FAIL  a.mo (1 error(s))\nboom";
    let r <- Build.check_entry_read d "abc";
    let _c <- Build.check_drop_fixture d;
    match r { Option.none => return true, Option.some _p => return false }
}

// ─── the plan, end to end over a real fixture tree ───

/// Not asked for: no digest tool is probed and no compiler is identified,
/// which is why this is the cheap case and why the tests below are the
/// only ones that touch the real binary.
#[test]
def test_check_plan_off_when_not_requested : IO Bool := do {
    let p <- Build.check_plan ["a.mo", "b.mo"] "target" false;
    return (Bool.not (Build.check_plan_active p)) && String.is_empty (Build.check_plan_reason p)
}

#[test]
def test_check_plan_off_for_a_single_file : IO Bool := do {
    let p <- Build.check_plan ["a.mo"] "target" true;
    return (Bool.not (Build.check_plan_active p)) && String.is_empty (Build.check_plan_reason p)
}

/// The one test that runs the whole plan for real: two files in a
/// fixture moteless directory, so `mote_root_of` takes its fallback to
/// the source directory and the two share one tree digest.
///
/// Three properties in one, because each `check_plan` digests the running
/// compiler binary and this is the expensive call:
///   * the plan is active and rooted at `<target>/check`
///   * every file gets a key, and two files get DIFFERENT keys
///   * a second run over unchanged files reproduces them exactly --
///     without which the cache would miss forever and every other test
///     here would still pass
#[test]
def test_check_plan_keys_every_file_and_is_stable : IO Bool := do {
    let d <- Build.check_fresh_fixture "plan";
    let _w1 <- Build.check_seed_file d "src/a.mo" "def a : I64 := 1\n";
    let _w2 <- Build.check_seed_file d "src/b.mo" "def b : I64 := 2\n";
    let fa : String := String.concat d "/src/a.mo";
    let fb : String := String.concat d "/src/b.mo";
    let p1 <- Build.check_plan [fa, fb] (String.concat d "/target") true;
    let p2 <- Build.check_plan [fa, fb] (String.concat d "/target") true;
    let ka1 : String := Build.key_or_empty p1 fa;
    let kb1 : String := Build.key_or_empty p1 fb;
    let ka2 : String := Build.key_or_empty p2 fa;
    let _c <- Build.check_drop_fixture d;
    return Build.check_plan_active p1
        && Build.check_plan_active p2
        && String.beq (Build.check_plan_root p1) (String.concat d "/target/check")
        && Bool.not (String.is_empty ka1)
        && Bool.not (String.is_empty kb1)
        && Bool.not (String.beq ka1 kb1)
        && String.beq ka1 ka2
}

/// **The safety property this cache is most likely to get wrong.**
///
/// `check_deps = false` means a file is typechecked against its closure's
/// SIGNATURES, so a change inside a declared dependency can flip whether
/// the file checks while every byte of the file and of its own mote stays
/// put. A key built on the mote's own tree alone therefore serves a
/// stale answer for exactly that edit -- and the edit is an ordinary one
/// (widening a function's type in `std`), not an exotic one.
///
/// The target file here is deliberately NOT rewritten: only `lib/src/l.mo`
/// moves.
#[test]
def test_key_moves_when_a_declared_dependency_changes : IO Bool := do {
    let d <- Build.check_fresh_dep_fixture "dep";
    let fa : String := String.concat d "/app/src/a.mo";
    let fb : String := String.concat d "/app/src/b.mo";
    let target : String := String.concat d "/target";
    let p1 <- Build.check_plan [fa, fb] target true;
    let k1 : String := Build.key_or_empty p1 fa;
    let _w <- Build.check_seed_file d "lib/src/l.mo" "def l : I64 := 2\n";
    let p2 <- Build.check_plan [fa, fb] target true;
    let k2 : String := Build.key_or_empty p2 fa;
    let _c <- Build.check_drop_fixture d;
    return Bool.not (String.is_empty k1)
        && Bool.not (String.is_empty k2)
        && Bool.not (String.beq k1 k2)
}

/// The converse, and the reason the walk is not simply widened to the
/// whole repository: a change OUTSIDE the declared closure must NOT move
/// the key, or every edit anywhere would invalidate everything. `other`
/// is a sibling mote that `app` does not declare.
#[test]
def test_key_ignores_a_mote_the_target_does_not_declare : IO Bool := do {
    let d <- Build.check_fresh_dep_fixture "undeclared";
    let fa : String := String.concat d "/app/src/a.mo";
    let fb : String := String.concat d "/app/src/b.mo";
    let target : String := String.concat d "/target";
    let p1 <- Build.check_plan [fa, fb] target true;
    let k1 : String := Build.key_or_empty p1 fa;
    let other : String := String.concat d "/other";
    let _m <- Build.ensure_dir (String.concat other "/src");
    let _t <- Build.check_seed_file other "mote.toml" "[mote]\nname = \"other\"\n";
    let _o <- Build.check_seed_file other "src/o.mo" "def o : I64 := 9\n";
    let p2 <- Build.check_plan [fa, fb] target true;
    let k2 : String := Build.key_or_empty p2 fa;
    let _c <- Build.check_drop_fixture d;
    return Bool.not (String.is_empty k1) && String.beq k1 k2
}

/// The working directory comes back under ONE name, because two names was
/// two behaviors for one build.
///
/// `Mote.discover` reports a manifest's directory relative to where the
/// walk started, so a mote rooted at the working directory gives `""` for
/// `src/a.mo` and `"."` for the same tree spelled `./src/a.mo`. The empty
/// one used to be skipped by `Build.plan_roots` as "outside any mote", so
/// `monad check src/a.mo src/b.mo` wrote **no** check entries while
/// `monad check ./src/a.mo ./src/b.mo` wrote two -- measured, a fresh store
/// per spelling, in a mote whose `mote.toml` sits in the working directory.
/// Declining to cache is not wrong; declining for one spelling of one build
/// and not the other is a cache that misses work nothing changed, and the
/// plain spelling is the one a user types.
///
/// `"."` is asserted and not merely equality: two spellings that were BOTH
/// `""` would satisfy an equality check and prove nothing -- the same trap
/// `hash_tests.mo`'s empty-root test guards against.
#[test]
def test_mote_root_normalizes_the_working_directory : IO Bool := do {
    let a <- Build.mote_root_of "main.mo";
    let b <- Build.mote_root_of "./main.mo";
    return String.beq "." a && String.beq a b
}
