/// Tests for `build/src/manage.mo`.
///
/// Two halves, and the split is the point.
///
/// The PURE half pins the naming and verdict rules: what counts as an
/// entry's name, what counts as a key, what counts as an output directory,
/// and what each kind's completeness rule says. Those are the rules `ls`
/// and `verify` read and `clean` and `gc` act on, so a mistake in one is a
/// mistake in all four verbs.
///
/// The I/O half pins the two properties that make these verbs safe to run
/// on a store someone actually cares about:
///
///   * **`clean` cannot reach an entry.** It removes the complement of the
///     four kind directories, and the test that matters is that a store
///     survives it -- `store` and `check` are still there afterwards while
///     the profile directories are not.
///   * **`gc` refuses rather than guessing.** An incomplete reachable set
///     is not a smaller set, it is the whole store: the failure mode is
///     deletion, and no fallback is acceptable. Two tests pin it from both
///     ends -- a named-nothing run removes nothing, and a run that DID
///     derive a set still spares the live entry in it.
///
/// Fixtures are pid-and-tag-scoped because the corpus sweep runs sharded
/// and a fixed `/tmp` name would collide across concurrent shards.

use std::list {List.filter, List.intercalate, List.length}
use std::process {process_id}
use lang::module {extract_directory}
use build::check {
  Build.check_plan, Build.check_plan_active, Build.check_plan_all,
  Build.check_plan_key, Build.mote_root_of, CheckPlan,
}
use build::closure {Build.artifact_key, Build.input_hash}
use build::store {
  Build.artifact_ir_path, Build.ensure_dir, Build.entry_root_dir, Build.write_leaf,
  Build.store_path, artifact, check,
}
use build::manage {
  Build.artifact_keys, Build.artifact_name_key, Build.artifact_state,
  Build.check_state, Build.clean_run, Build.droppable_name, Build.entry_views,
  Build.gc_run, Build.is_key, Build.is_output_dir, Build.profile_names,
  Build.strip_ir_suffix, Build.unreachable, Build.view_detail,
  Build.view_is_artifact, Build.view_key, Build.view_kind, Build.view_not_ok,
  EntryView,
}

/// Two names of the only shape an entry may have -- 64 lowercase hex
/// characters -- written out rather than hashed, so a test failure reads
/// as itself rather than as "the digest moved".
def Build.manage_key_a : String :=
    "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"

def Build.manage_key_b : String :=
    "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210"

/// The triple a fixture keys under. Only ever hashed, so its value is the
/// test's to choose.
def Build.manage_triple : String := "test-triple"

// ─── fixtures ───

/// A pid-and-tag-scoped fixture root, removed first so a rerun starts
/// clean.
#[partial]
def Build.manage_fresh_fixture (tag : String) : IO String := do {
    let d : String := String.concat "/tmp/monad_manage_fix_"
        (String.concat (I64.to_string process_id) (String.concat "_" tag));
    let _r <- Proc.capture "sh" ["-c", String.concat "rm -rf " (Proc.shell_quote d)];
    let _m <- Build.ensure_dir (String.concat d "/src");
    return d
}

/// A fixture rooted at a real MOTE: a manifest and two sources, so the
/// files named to `gc` resolve to a root whose closure digest is a
/// meaningful one rather than the fixture directory itself.
#[partial]
def Build.manage_mote_fixture (tag : String) : IO String := do {
    let d <- Build.manage_fresh_fixture tag;
    let _t <- Build.manage_seed (String.concat d "/mote.toml") "[mote]\nname = \"fixture\"\n";
    let _a <- Build.manage_seed (String.concat d "/src/a.mo") "def a : I64 := 1\n";
    let _b <- Build.manage_seed (String.concat d "/src/b.mo") "def b : I64 := 2\n";
    return d
}

/// Write one file, making the directories above it.
#[partial]
def Build.manage_seed (path : String) (content : String) : IO I64 := do {
    let _m <- Build.ensure_dir (extract_directory path);
    let ok <- Build.write_leaf path content;
    return (if ok then 0 else 1)
}

#[partial]
def Build.manage_drop_fixture (d : String) : IO I64 := do {
    let r <- Proc.capture "sh" ["-c", String.concat "rm -rf " (Proc.shell_quote d)];
    match r { Pair.pair code _out => return code }
}

#[partial]
def Build.manage_present (path : String) : IO Bool :=
    IO.file_exists (Path.path path)

#[partial]
def Build.manage_is_dir (path : String) : IO Bool :=
    IO.is_dir (Path.path path)

/// An artifact's binary path, through the real naming layer rather than a
/// hand-spelled `store/...` -- a test that hard-codes the layout would keep
/// passing after the layout moved.
def Build.manage_bin (target : String) (key : String) : String :=
    Build.store_path target Entry.artifact key ""

def Build.manage_ir (target : String) (key : String) : String :=
    Build.artifact_ir_path target key

def Build.manage_check_dir (target : String) (key : String) : String :=
    String.concat (Build.entry_root_dir target Entry.check) (String.concat "/" key)

/// The key an `input_hash` gave, as a String, or `""` when it declined.
/// The `is_key` assertions below are what turn a decline into a failure
/// rather than into a key of length zero.
def Build.manage_hash (r : Result String String) : String :=
    match r { ok h => h, err _ => "" }

/// The key a plan gives one file, as a String. `""` when the plan is
/// inactive -- which the caller must treat as "no key", not as a key of
/// length zero, since a fixture named `check/` is not a thing.
def Build.manage_key_or_empty (p : CheckPlan) (file : String) : String :=
    match Build.check_plan_key p file {
        Option.none => "",
        Option.some k => k
    }

// ─── what a key is ───

#[test]
def test_is_key_accepts_64_lowercase_hex : Bool :=
    Build.is_key Build.manage_key_a && Build.is_key Build.manage_key_b

/// 63 and 65, so the length rule is pinned on both sides of itself rather
/// than at one.
#[test]
def test_is_key_rejects_a_short_name : Bool :=
    Bool.not (Build.is_key (String.slice Build.manage_key_a 0 63))

#[test]
def test_is_key_rejects_a_long_name : Bool :=
    Bool.not (Build.is_key (String.concat Build.manage_key_a "0"))

/// Uppercase is the case that matters: a key is a lowercase hex digest, and
/// a name that differs only in case is a DIFFERENT name -- so accepting it
/// would let `gc` see two entries where the store has one, and `ls` list
/// one that no lookup can reach.
#[test]
def test_is_key_rejects_uppercase_hex : Bool :=
    Bool.not (Build.is_key (String.concat Build.manage_key_a "A"))
        && Bool.not (Build.is_key "ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789")

/// The legacy entry name -- `<hash>-<basename of -o>` -- is not a key, and
/// that is what makes it invisible to `ls` and reclaimable by `gc`.
#[test]
def test_is_key_rejects_a_legacy_slug : Bool :=
    Bool.not (Build.is_key (String.concat Build.manage_key_a "-monad"))

// ─── the two questions a store name can be asked ───

#[test]
def test_artifact_name_key_strips_the_ir_companion : Bool :=
    match Build.artifact_name_key (String.concat Build.manage_key_a ".ll") {
        Option.none => false,
        Option.some k => String.beq k Build.manage_key_a
    }

#[test]
def test_artifact_name_key_reads_a_bare_key : Bool :=
    match Build.artifact_name_key Build.manage_key_a {
        Option.none => false,
        Option.some k => String.beq k Build.manage_key_a
    }

#[test]
def test_artifact_name_key_rejects_a_legacy_slug : Bool :=
    match Build.artifact_name_key (String.concat Build.manage_key_a "-monad") {
        Option.none => true,
        Option.some _k => false
    }

/// The other question -- "what would removing this remove?" -- and the one
/// `gc` has to ask. Written as its own test because the two disagree on
/// exactly one input, the legacy slug, and that disagreement is the
/// difference between a `gc` that reclaims orphans and one that spares
/// every one of them while reporting them as unreachable.
#[test]
def test_droppable_name_strips_the_ir_companion : Bool :=
    String.beq (Build.droppable_name (String.concat Build.manage_key_a ".ll")) Build.manage_key_a

/// The suffix strip itself, asserted on the LENGTH rather than through
/// `is_key`.
///
/// `String.slice` takes a length, not an end index, so the length here is
/// the suffix's own 3 and not "the string's minus the two dots and letters
/// you can see" -- and the first cut of this code wrote `- 2`, which kept
/// the dot and made every `.ll` name a 65-character non-key. Through
/// `is_key` that failure is indistinguishable from "the name is not an
/// entry", which is the answer `store ls` prints and the reason this test
/// reports the exact string instead.
#[test]
def test_strip_ir_suffix_removes_exactly_the_suffix : Bool :=
    String.beq (Build.strip_ir_suffix (String.concat Build.manage_key_a ".ll")) Build.manage_key_a
        && String.beq (Build.strip_ir_suffix "ab.ll") "ab"
        && String.beq (Build.strip_ir_suffix "ab") "ab"
        && String.beq (Build.strip_ir_suffix ".ll") ""

/// A `.ll` in the middle or absent entirely is not a suffix -- `ends_with`
/// and not `contains`, so a name carrying `.ll` anywhere else is left whole
/// rather than truncated into something no lookup can reach.
#[test]
def test_strip_ir_suffix_is_a_suffix_test_not_a_search : Bool :=
    String.beq (Build.strip_ir_suffix "a.ll.b") "a.ll.b"

/// A lone IR whose binary is gone: normalizing it to the key is what makes
/// `remove_entry` take the `.ll` with it instead of looking for a
/// `<key>.ll.ll` that never existed.
#[test]
def test_droppable_name_of_a_lone_ir_is_the_key : Bool :=
    String.beq (Build.droppable_name (String.concat Build.manage_key_a ".ll")) Build.manage_key_a

#[test]
def test_droppable_name_keeps_a_legacy_slug : Bool :=
    String.beq (Build.droppable_name (String.concat Build.manage_key_a "-monad"))
        (String.concat Build.manage_key_a "-monad")

#[test]
def test_droppable_name_keeps_a_bare_key : Bool :=
    String.beq (Build.droppable_name Build.manage_key_a) Build.manage_key_a

// ─── what clean may remove ───

/// The four kind directories, as a set -- and the reason `clean` is defined
/// by exclusion from it rather than by a list of profile names.
#[test]
def test_no_kind_directory_is_an_output_directory : Bool :=
    Bool.not (Build.is_output_dir "store")
        && Bool.not (Build.is_output_dir "check")
        && Bool.not (Build.is_output_dir "test")
        && Bool.not (Build.is_output_dir "db")

#[test]
def test_a_profile_directory_is_an_output_directory : Bool :=
    Build.is_output_dir "debug" && Build.is_output_dir "release" && Build.is_output_dir "whatever-comes-next"

/// An empty name is not a directory at all. It cannot arrive from
/// `IO.list_dir`, and excluding it here is what keeps a caller that
/// synthesizes a name from handing `clean` a `rm -rf <target>/`.
#[test]
def test_an_empty_name_is_not_an_output_directory : Bool :=
    Bool.not (Build.is_output_dir "")

// ─── the keys gc derives ───

/// One per profile, per triple named: a build in either profile writes an
/// entry, so both have to be in the reachable set or the other profile's
/// entry looks unreachable.
#[test]
def test_artifact_keys_are_one_per_profile : Bool :=
    I64.beq (List.length (Build.artifact_keys "f" "c" "k" [Build.manage_triple])) 2

/// Whether a key list is exactly the build side's formula, profile for
/// profile. Hoisted out of the test because it is a match over two lists at
/// once and the inner one has to sit in a `do` block -- the shape
/// `Build.plan_keys` uses for the same reason.
#[partial]
def Build.manage_keys_agree (ks : List String) (ps : List String) : IO Bool := do {
    match ks {
        List.empty => return List.is_empty ps,
        List.cons k rest => match ps {
            List.empty => return false,
            List.cons p prest => do {
                let ok : Bool := String.beq k (Build.artifact_key { file_digest := "f",
                        closure := "c", compiler := "k", profile := p,
                        triple := Build.manage_triple });
                if ok then Build.manage_keys_agree rest prest else return false
            }
        }
    }
}

/// The one that matters: `gc`'s keys and `build`'s key are the SAME
/// formula, so this is the test that would fail if `Build.artifact_keys`
/// and `Build.artifact_key` ever drifted apart -- which is the failure that
/// makes a `gc` delete live artifacts.
#[test]
def test_artifact_keys_match_the_build_side : IO Bool := do {
    let ks : List String := Build.artifact_keys "f" "c" "k" [Build.manage_triple];
    let same <- Build.manage_keys_agree ks Build.profile_names;
    return same && I64.beq (List.length ks) 2
}

#[test]
def test_unreachable_drops_only_what_is_not_kept : Bool :=
    String.beq (List.intercalate "," (Build.unreachable ["a", "b"] ["a", "b", "c", "d"])) "c,d"

#[test]
def test_unreachable_covers_everything_when_nothing_is_kept : Bool :=
    String.beq (List.intercalate "," (Build.unreachable List.empty ["x", "y"])) "x,y"

#[test]
def test_unreachable_of_an_empty_store_is_empty : Bool :=
    List.is_empty (Build.unreachable ["a"] List.empty)

// ─── what an entry's verdict says ───

#[test]
def test_artifact_state_accepts_a_complete_pair : Bool :=
    match Build.artifact_state true true 100 {
        Pair.pair ok _d => ok
    }

#[test]
def test_artifact_state_rejects_a_missing_ir : Bool :=
    match Build.artifact_state true false 100 {
        Pair.pair ok d => Bool.not ok && String.beq d "missing its IR (an artifact is a pair)"
    }

#[test]
def test_artifact_state_rejects_a_missing_binary : Bool :=
    match Build.artifact_state false true 100 {
        Pair.pair ok _d => Bool.not ok
    }

/// Zero bytes is a damaged artifact, not a small one -- which is why the
/// size rule is `> 0` and not merely "the file is there".
#[test]
def test_artifact_state_rejects_an_empty_pair : Bool :=
    match Build.artifact_state true true 0 {
        Pair.pair ok d => Bool.not ok && String.beq d "empty"
    }

#[test]
def test_check_state_accepts_a_complete_entry : Bool :=
    match Build.check_state true true true {
        Pair.pair ok _d => ok
    }

#[test]
def test_check_state_rejects_a_missing_out : Bool :=
    match Build.check_state false true true {
        Pair.pair ok _d => Bool.not ok
    }

/// The rule the READER applies, which is why `verify` can promise that a
/// good entry is one a hit can replay: `check_entry_read` refuses an entry
/// whose count does not parse, so anything less would let `verify` call an
/// unservable entry good.
#[test]
def test_check_state_rejects_a_count_that_is_not_a_number : Bool :=
    match Build.check_state true true false {
        Pair.pair ok d => Bool.not ok && String.beq d "errors is not a number"
    }

// ─── ls and verify: reading a store ───

/// One entry, not two: `<key>` and `<key>.ll` are one artifact, and a
/// listing that printed them separately would report a store of twice the
/// size it has.
#[test]
def test_entry_views_reads_an_artifact_pair_as_one_entry : IO Bool := do {
    let d <- Build.manage_fresh_fixture "pair";
    let target : String := String.concat d "/target";
    let _b <- Build.manage_seed (Build.manage_bin target Build.manage_key_a) "bin";
    let _i <- Build.manage_seed (Build.manage_ir target Build.manage_key_a) "ir";
    let views <- Build.entry_views target;
    let arts : List EntryView := List.filter Build.view_is_artifact views;
    let _x <- Build.manage_drop_fixture d;
    match arts {
        List.cons v rest =>
            return (List.is_empty rest
                && String.beq (Build.view_key v) Build.manage_key_a
                && Bool.not (Build.view_not_ok v)
                && String.beq (Build.view_detail v) "bin+ir"),
        List.empty => return false
    }
}

/// A binary with no IR is INCOMPLETE, not an artifact. It is also exactly
/// what a half-written entry looks like, which is why the pair is checked
/// as a pair.
#[test]
def test_entry_views_flags_an_artifact_without_its_ir : IO Bool := do {
    let d <- Build.manage_fresh_fixture "noir";
    let target : String := String.concat d "/target";
    let _b <- Build.manage_seed (Build.manage_bin target Build.manage_key_a) "bin";
    let views <- Build.entry_views target;
    let _x <- Build.manage_drop_fixture d;
    match views {
        List.cons v _ => return Build.view_not_ok v,
        List.empty => return false
    }
}

#[test]
def test_entry_views_reads_a_check_entry : IO Bool := do {
    let d <- Build.manage_fresh_fixture "chk";
    let target : String := String.concat d "/target";
    let dir : String := Build.manage_check_dir target Build.manage_key_a;
    let _o <- Build.manage_seed (String.concat dir "/out") "ok    a.mo";
    let _e <- Build.manage_seed (String.concat dir "/errors") "0";
    let views <- Build.entry_views target;
    let _x <- Build.manage_drop_fixture d;
    match views {
        List.cons v rest =>
            return (List.is_empty rest
                && String.beq (Build.view_kind v) "check"
                && Bool.not (Build.view_not_ok v)),
        List.empty => return false
    }
}

/// The damaged case, and the one `verify` exists for: a count that is not a
/// number is a `none` from `check_entry_read`, i.e. a miss, so `verify` must
/// say so and exit non-zero rather than list it as an entry.
#[test]
def test_entry_views_flags_a_check_entry_with_a_corrupt_count : IO Bool := do {
    let d <- Build.manage_fresh_fixture "chkbad";
    let target : String := String.concat d "/target";
    let dir : String := Build.manage_check_dir target Build.manage_key_a;
    let _o <- Build.manage_seed (String.concat dir "/out") "ok    a.mo";
    let _e <- Build.manage_seed (String.concat dir "/errors") "not-a-number";
    let views <- Build.entry_views target;
    let _x <- Build.manage_drop_fixture d;
    match views {
        List.cons v _ =>
            return (Build.view_not_ok v && String.beq (Build.view_detail v) "errors is not a number"),
        List.empty => return false
    }
}

/// A legacy slug is not an entry, so `ls` does not list it -- which is the
/// right answer to "what is in the store" and the wrong answer to "what
/// should be reclaimed". `gc` is where the second question is asked.
#[test]
def test_entry_views_ignores_a_legacy_slug : IO Bool := do {
    let d <- Build.manage_fresh_fixture "slug";
    let target : String := String.concat d "/target";
    let _s <- Build.manage_seed (Build.manage_bin target (String.concat Build.manage_key_a "-monad")) "bin";
    let views <- Build.entry_views target;
    let _x <- Build.manage_drop_fixture d;
    return (List.is_empty views)
}

// ─── clean: cannot reach an entry ───

/// **The property that makes `clean` safe to run.** The profile
/// directories go; `store/` and `check/` and everything inside them stay.
#[test]
def test_clean_keeps_the_store : IO Bool := do {
    let d <- Build.manage_fresh_fixture "clean_keep";
    let target : String := String.concat d "/target";
    let _a <- Build.ensure_dir (String.concat target "/debug");
    let _b <- Build.ensure_dir (String.concat target "/release");
    let _c <- Build.ensure_dir (String.concat target "/store");
    let _e <- Build.ensure_dir (String.concat target "/check");
    let _f <- Build.manage_seed (Build.manage_bin target Build.manage_key_a) "bin";
    let rc <- Build.clean_run target false;
    let debug_gone <- Build.manage_is_dir (String.concat target "/debug");
    let release_gone <- Build.manage_is_dir (String.concat target "/release");
    let bin_kept <- Build.manage_present (Build.manage_bin target Build.manage_key_a);
    let check_kept <- Build.manage_is_dir (String.concat target "/check");
    let _x <- Build.manage_drop_fixture d;
    return I64.beq rc 0
        && Bool.not debug_gone
        && Bool.not release_gone
        && bin_kept
        && check_kept
}

/// The converse of the same rule, so the test above is not passing because
/// `clean` does nothing at all: an output directory really does go.
#[test]
def test_clean_removes_an_output_directory : IO Bool := do {
    let d <- Build.manage_fresh_fixture "clean_rm";
    let target : String := String.concat d "/target";
    let _a <- Build.ensure_dir (String.concat target "/debug");
    let rc <- Build.clean_run target false;
    let gone <- Build.manage_is_dir (String.concat target "/debug");
    let _x <- Build.manage_drop_fixture d;
    return I64.beq rc 0 && Bool.not gone
}

/// A store that was never written is not a failure -- there is nothing to
/// clean and nothing went wrong.
#[test]
def test_clean_of_a_missing_root_succeeds : IO Bool := do {
    let d <- Build.manage_fresh_fixture "clean_none";
    let target : String := String.concat d "/no-such-target";
    let rc <- Build.clean_run target false;
    let all_rc <- Build.clean_run target true;
    let _x <- Build.manage_drop_fixture d;
    return I64.beq rc 0 && I64.beq all_rc 0
}

/// `--all` is the other verb: the store goes too, which is the only honest
/// meaning it can have while there is no global store to keep across it.
#[test]
def test_clean_all_removes_the_store : IO Bool := do {
    let d <- Build.manage_fresh_fixture "clean_all";
    let target : String := String.concat d "/target";
    let _b <- Build.manage_seed (Build.manage_bin target Build.manage_key_a) "bin";
    let rc <- Build.clean_run target true;
    let gone <- Build.manage_is_dir target;
    let bin_gone <- Build.manage_present (Build.manage_bin target Build.manage_key_a);
    let _x <- Build.manage_drop_fixture d;
    return I64.beq rc 0 && Bool.not gone && Bool.not bin_gone
}

// ─── gc: refuses rather than guesses ───

/// **The safety property, in its bluntest form.** Nothing was named, so no
/// key could be derived, so nothing may be removed -- not even though the
/// reachable set is trivially known to be empty. `--apply` is passed
/// deliberately: the refusal has to win over the instruction to act.
#[test]
def test_gc_refuses_when_no_files_were_named : IO Bool := do {
    let d <- Build.manage_fresh_fixture "gc_none";
    let target : String := String.concat d "/target";
    let _b <- Build.manage_seed (Build.manage_bin target Build.manage_key_a) "bin";
    let rc <- Build.gc_run List.empty target [Build.manage_triple] true;
    let kept <- Build.manage_present (Build.manage_bin target Build.manage_key_a);
    let _x <- Build.manage_drop_fixture d;
    return I64.beq rc 1 && kept
}

/// Dry run is the default for a reason: the counts are worth reading before
/// they are acted on, and acting anyway is the one thing a dry run must not
/// do.
#[test]
def test_gc_dry_run_removes_nothing : IO Bool := do {
    let d <- Build.manage_mote_fixture "gc_dry";
    let target : String := String.concat d "/target";
    let files : List String := [String.concat d "/src/a.mo", String.concat d "/src/b.mo"];
    let _b <- Build.manage_seed (Build.manage_bin target Build.manage_key_a) "bin";
    let _i <- Build.manage_seed (Build.manage_ir target Build.manage_key_a) "ir";
    let rc <- Build.gc_run files target [Build.manage_triple] false;
    let bin_kept <- Build.manage_present (Build.manage_bin target Build.manage_key_a);
    let ir_kept <- Build.manage_present (Build.manage_ir target Build.manage_key_a);
    let _x <- Build.manage_drop_fixture d;
    return I64.beq rc 0 && bin_kept && ir_kept
}

/// The other end of the refusal: a run that DID derive a set still spares
/// the entry in it. The key is the one `check_plan` gives the fixture's own
/// file, i.e. exactly the key a `monad check` of that file would write and
/// later read -- so this test fails if `gc` deletes live check entries,
/// which is the failure that would silently turn every check into a miss.
#[test]
def test_gc_spares_a_reachable_check_entry : IO Bool := do {
    let d <- Build.manage_mote_fixture "gc_spare";
    let target : String := String.concat d "/target";
    let fa : String := String.concat d "/src/a.mo";
    let fb : String := String.concat d "/src/b.mo";
    let files : List String := [fa, fb];
    let plan <- Build.check_plan files target true;
    let live : String := Build.manage_key_or_empty plan fa;
    let dir : String := Build.manage_check_dir target live;
    let _o <- Build.manage_seed (String.concat dir "/out") "ok    a.mo";
    let _e <- Build.manage_seed (String.concat dir "/errors") "0";
    let rc <- Build.gc_run files target [Build.manage_triple] true;
    let kept <- Build.manage_is_dir dir;
    let _x <- Build.manage_drop_fixture d;
    return I64.beq rc 0 && Build.is_key live && kept
}

/// **Every artifact of one mote, not just the one whose key was asked
/// for.**
///
/// The artifact-side twin of the test above, and the one that catches the
/// collision it was written for: `src/a.mo` and `src/b.mo` share a mote,
/// so they share a root AND a closure digest, and a reachable set built
/// from roots rather than files holds one key where the build side wrote
/// two. The entries are named by `Build.input_hash` -- the formula
/// `build_cached` itself calls -- so a `gc` that derives anything else
/// removes both, and both `is_key` checks fail alongside.
#[test]
def test_gc_spares_every_artifact_of_one_mote : IO Bool := do {
    let d <- Build.manage_mote_fixture "gc_art";
    let target : String := String.concat d "/target";
    let fa : String := String.concat d "/src/a.mo";
    let fb : String := String.concat d "/src/b.mo";
    let files : List String := [fa, fb];
    let root <- Build.mote_root_of fa;
    let ra <- Build.input_hash fa root "debug" Build.manage_triple;
    let rb <- Build.input_hash fb root "debug" Build.manage_triple;
    let ka : String := Build.manage_hash ra;
    let kb : String := Build.manage_hash rb;
    let _sa <- Build.manage_seed (Build.manage_bin target ka) "a";
    let _sb <- Build.manage_seed (Build.manage_bin target kb) "b";
    let rc <- Build.gc_run files target [Build.manage_triple] true;
    let kept_a <- Build.manage_present (Build.manage_bin target ka);
    let kept_b <- Build.manage_present (Build.manage_bin target kb);
    let _x <- Build.manage_drop_fixture d;
    return Build.is_key ka && Build.is_key kb
        && Bool.not (String.beq ka kb)
        && I64.beq rc 0
        && kept_a && kept_b
}

/// **One named file is a plan, not a degenerate case.**
///
/// `check_plan` refuses to plan a single file, because for `check` a
/// one-file run in an editor loop costs less than the fork its key needs.
/// `gc` caches nothing, so that floor buys it nothing -- and routed through
/// `check_plan` it made `monad gc src/one.mo` plan nothing, see an inactive
/// plan and refuse, i.e. a `gc` that could only reclaim from a run naming
/// two or more files. Every test here used to name two, which is exactly
/// why they did not catch it: this one names one, and asserts the plan was
/// derived rather than refused.
#[test]
def test_gc_plans_a_single_named_file : IO Bool := do {
    let d <- Build.manage_mote_fixture "gc_one";
    let target : String := String.concat d "/target";
    let files : List String := [String.concat d "/src/a.mo"];
    let plan <- Build.check_plan_all files target;
    let live : String := Build.manage_key_or_empty plan (String.concat d "/src/a.mo");
    let dir : String := Build.manage_check_dir target live;
    let _o <- Build.manage_seed (String.concat dir "/out") "ok    a.mo";
    let _e <- Build.manage_seed (String.concat dir "/errors") "0";
    let rc <- Build.gc_run files target [Build.manage_triple] true;
    let kept <- Build.manage_is_dir dir;
    let _x <- Build.manage_drop_fixture d;
    return (Build.check_plan_active plan)
        && Build.is_key live
        && I64.beq rc 0
        && kept
}

/// And the half that reclaims: an entry nothing in the named set can reach
/// goes, which is the orphan the plan's own gate left 184 of.
#[test]
def test_gc_removes_an_unreachable_check_entry : IO Bool := do {
    let d <- Build.manage_mote_fixture "gc_drop";
    let target : String := String.concat d "/target";
    let files : List String := [String.concat d "/src/a.mo", String.concat d "/src/b.mo"];
    let dir : String := Build.manage_check_dir target Build.manage_key_a;
    let _o <- Build.manage_seed (String.concat dir "/out") "ok    a.mo";
    let _e <- Build.manage_seed (String.concat dir "/errors") "0";
    let rc <- Build.gc_run files target [Build.manage_triple] true;
    let gone <- Build.manage_present (String.concat dir "/out");
    let _x <- Build.manage_drop_fixture d;
    return I64.beq rc 0 && Bool.not gone
}

/// **The orphan a key test alone would have spared forever.** A legacy slug
/// is not a key, so `gc` asked as "is this an entry?" would report it as
/// unreachable and then not remove it. Both of its files go -- which also
/// pins that the pair is reclaimed together at this spelling too.
#[test]
def test_gc_removes_a_legacy_slug_entry : IO Bool := do {
    let d <- Build.manage_mote_fixture "gc_slug";
    let target : String := String.concat d "/target";
    let files : List String := [String.concat d "/src/a.mo", String.concat d "/src/b.mo"];
    let slug : String := String.concat Build.manage_key_a "-monad";
    let _b <- Build.manage_seed (Build.manage_bin target slug) "bin";
    let _i <- Build.manage_seed (Build.manage_ir target slug) "ir";
    let rc <- Build.gc_run files target [Build.manage_triple] true;
    let bin_gone <- Build.manage_present (Build.manage_bin target slug);
    let ir_gone <- Build.manage_present (Build.manage_ir target slug);
    let _x <- Build.manage_drop_fixture d;
    return I64.beq rc 0 && Bool.not bin_gone && Bool.not ir_gone
}

/// A lone IR -- its binary already gone -- is reclaimed as the pair's key,
/// so the `.ll` goes rather than being left behind for a `<key>.ll.ll` that
/// never existed.
#[test]
def test_gc_removes_an_orphaned_ir : IO Bool := do {
    let d <- Build.manage_mote_fixture "gc_orphan";
    let target : String := String.concat d "/target";
    let files : List String := [String.concat d "/src/a.mo", String.concat d "/src/b.mo"];
    let _i <- Build.manage_seed (Build.manage_ir target Build.manage_key_a) "ir";
    let rc <- Build.gc_run files target [Build.manage_triple] true;
    let ir_gone <- Build.manage_present (Build.manage_ir target Build.manage_key_a);
    let _x <- Build.manage_drop_fixture d;
    return I64.beq rc 0 && Bool.not ir_gone
}

/// **`gc` spares an artifact built for another target.**
///
/// A build keys with the target it was given, so a reachable set holding only
/// the host's own triple reports every cross-built artifact as unreachable and
/// removes it -- which is what one `triple` parameter could not express.
#[test]
def test_gc_spares_another_targets_artifact : IO Bool := do {
    let d <- Build.manage_mote_fixture "gc_cross";
    let target : String := String.concat d "/target";
    let fa : String := String.concat d "/src/a.mo";
    let fb : String := String.concat d "/src/b.mo";
    let files : List String := [fa, fb];
    let root <- Build.mote_root_of fa;
    let cross : String := "aarch64-unknown-linux-gnu";
    let rh <- Build.input_hash fa root "debug" cross;
    let kh : String := Build.manage_hash rh;
    let _sh <- Build.manage_seed (Build.manage_bin target kh) "arm";
    let rc <- Build.gc_run files target [cross] true;
    let kept <- Build.manage_present (Build.manage_bin target kh);
    let _x <- Build.manage_drop_fixture d;
    return Build.is_key kh && I64.beq rc 0 && kept
}

/// The other half, and the one that proves the set is READ rather than
/// ignored: the same artifact goes when its triple is not in it.
#[test]
def test_gc_collects_a_triple_absent_from_the_set : IO Bool := do {
    let d <- Build.manage_mote_fixture "gc_crossgone";
    let target : String := String.concat d "/target";
    let fa : String := String.concat d "/src/a.mo";
    let fb : String := String.concat d "/src/b.mo";
    let files : List String := [fa, fb];
    let root <- Build.mote_root_of fa;
    let cross : String := "aarch64-unknown-linux-gnu";
    let rh <- Build.input_hash fa root "debug" cross;
    let kh : String := Build.manage_hash rh;
    let _sh <- Build.manage_seed (Build.manage_bin target kh) "arm";
    let rc <- Build.gc_run files target ["x86_64-unknown-linux-gnu"] true;
    let gone <- Build.manage_present (Build.manage_bin target kh);
    let _x <- Build.manage_drop_fixture d;
    return Build.is_key kh && I64.beq rc 0 && Bool.not gone
}
