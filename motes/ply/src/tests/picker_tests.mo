// Phase 5's file-picker gate: a fixture listing, ranked, with an exact-prefix
// match first (code-editor.md's Phase 5 gate, literally: "A picker test on a
// fixture directory ranks an exact-prefix match first").
//
// THE RANKING IS THE WHOLE FEATURE, so the tiers are pinned one at a time --
// a name prefix beats a path prefix, a path prefix beats a containment, a
// containment beats a subsequence -- and then the gate fixture does it end to
// end. A picker whose order is wrong does not fail loudly; it opens the wrong
// file, which is why every tier is a test.
//
// THE LISTING ITSELF IS NOT TESTED HERE. `IO.list_dir` is `std`'s and its own
// suite covers it; what this module owns is the PURE half (rank, window,
// resolve), so the fixtures are literal path lists.

use lib::picker {Picker.rank, Picker.score, Picker.tier_name_prefix,
    Picker.tier_path_prefix, Picker.tier_contains, Picker.tier_subsequence,
    Picker.window_offset, Picker.clamp_selected, Picker.take_from, Picker.nth,
    Picker.resolve}
use std::list {List.intercalate}

// ── Fixtures ─────────────────────────────────────────────────────────────

/// A small repository-ish listing, in `IO.list_dir`'s sorted order.
def pk_files : List String :=
    ["motes/ply/src/main.mo", "motes/ply/src/model.mo", "motes/ply/src/view.mo",
        "motes/ply/mote.toml", "motes/regex/src/main.mo", "README.md"]

/// The first ranked entry, or `<none>`.
def pk_first (files : List String) (want : String) : String :=
    match Picker.rank files want {
        List.cons one _ => one,
        List.empty => "<none>"
    }

/// The whole ranked list, joined -- so a test can assert the ORDER, not just
/// the head.
def pk_all (files : List String) (want : String) : String :=
    List.intercalate "," (Picker.rank files want)

/// A candidate's tier, or -1 for a non-match.
def pk_tier (path : String) (want : String) : I64 :=
    match Picker.score path want {
        Option.none => 0 - 1,
        Option.some s => pk_fst s
    }

def pk_fst (p : Pair I64 I64) : I64 :=
    match p {
        Pair.pair tier _ => tier
    }

// ── The tiers ────────────────────────────────────────────────────────────

/// TIER 1: the file's own NAME starts with the filter. "main" is a name
/// prefix on both `main.mo`s, and beats nothing else here -- but the tier is
/// what the score says.
#[test]
def test_name_prefix_is_the_best_tier : Bool :=
    I64.beq (pk_tier "motes/ply/src/main.mo" "main") Picker.tier_name_prefix
        && I64.beq (pk_tier "main.mo" "main") Picker.tier_name_prefix

/// TIER 2: the filter is a prefix of the PAGE PATH but not of the name.
#[test]
def test_path_prefix_is_the_second_tier : Bool :=
    I64.beq (pk_tier "motes/ply/src/main.mo" "motes/ply") Picker.tier_path_prefix

/// TIER 3: the path merely CONTAINS it.
#[test]
def test_contains_is_the_third_tier : Bool :=
    I64.beq (pk_tier "motes/ply/src/main.mo" "src") Picker.tier_contains

/// TIER 4: the filter is a SUBSEQUENCE of the path -- "mplw" reaches
/// "motes/ply/src/view.mo" without any three of those letters being adjacent.
#[test]
def test_subsequence_is_the_fuzzy_tier : Bool :=
    I64.beq (pk_tier "motes/ply/src/view.mo" "mplw") Picker.tier_subsequence

/// A path that matches nowhere is `none` -- not the worst tier, which would
/// put it in the list.
#[test]
def test_non_match_has_no_tier : Bool :=
    I64.beq (pk_tier "motes/ply/src/main.mo" "zzz") (0 - 1)

/// THE ORDER OF THE TESTS IS THE RANKING: a path that is BOTH a name prefix
/// and a containment keeps the name prefix. "motes/ply/src/main.mo" contains
/// "main" twice and starts its name with it.
#[test]
def test_better_tier_wins_over_later_ones : Bool :=
    I64.beq (pk_tier "motes/ply/src/main.mo" "main") Picker.tier_name_prefix

/// Case does not matter: "MAIN" ranks like "main".
#[test]
def test_filter_is_case_insensitive : Bool :=
    String.beq (pk_first pk_files "MAIN") (pk_first pk_files "main")

// ── The gate: an exact prefix ranks first ────────────────────────────────

/// THE PHASE 5 GATE. "model" is a name prefix on exactly one file, so the
/// ranked head is that file -- and no earlier-looking candidate (a path that
/// merely contains the letters) can outrank it.
#[test]
def test_exact_prefix_ranks_first : Bool :=
    String.beq (pk_first pk_files "model") "motes/ply/src/model.mo"

/// Inside one tier, the SHORTER path comes first: among the two name-prefix
/// matches for "main", the repo-root one is shorter than the ply source one.
#[test]
def test_shorter_path_wins_inside_a_tier : Bool :=
    let files : List String := ["motes/ply/src/main.mo", "main.mo"] in
    String.beq (pk_first files "main") "main.mo"

/// The gate's ranking, whole: "ply" is a path prefix on four files, so they
/// all come before `README.md` -- which does not match at all -- and the
/// order inside the tier is by LENGTH, so `mote.toml` (shortest) is first.
#[test]
def test_gate_ranking_order : Bool :=
    String.beq (pk_all pk_files "ply")
        "motes/ply/mote.toml,motes/ply/src/main.mo,motes/ply/src/view.mo,motes/ply/src/model.mo"

/// A filter that matches nothing ranks nothing -- the picker is empty, not
/// full of noise.
#[test]
def test_no_match_ranks_nothing : Bool :=
    I64.beq (List.length (Picker.rank pk_files "zzzz")) 0

/// An EMPTY filter keeps every candidate: `/`-style pickers open showing the
/// whole listing, and an empty filter is not a filter.
#[test]
def test_empty_filter_keeps_everything : Bool :=
    I64.beq (List.length (Picker.rank pk_files "")) (List.length pk_files)

/// Equal scores keep the LISTING's order, so the list does not shuffle
/// between keystrokes. Both `main.mo`s score the same tier and the same
/// length, and the listing has ply's before regex's.
#[test]
def test_equal_scores_keep_listing_order : Bool :=
    let files : List String := ["a/main.mo", "b/main.mo"] in
    String.beq (pk_all files "main") "a/main.mo,b/main.mo"

// ── The window ───────────────────────────────────────────────────────────

/// A highlight inside the first page needs no scroll.
#[test]
def test_window_at_the_top : Bool :=
    I64.beq (Picker.window_offset 2 5 20) 0

/// A highlight past the window scrolls the least needed to show it.
#[test]
def test_window_scrolls_down : Bool :=
    I64.beq (Picker.window_offset 7 5 20) 3

/// A highlight on the last row scrolls to the last page, never past it.
#[test]
def test_window_at_the_bottom : Bool :=
    I64.beq (Picker.window_offset 19 5 20) 15

/// A list shorter than the window does not scroll at all.
#[test]
def test_window_shorter_than_height : Bool :=
    I64.beq (Picker.window_offset 2 10 3) 0

/// The clamp keeps a selection legal after the filter shrank the list: 9
/// rows became 3, so the highlight is 2 -- and 0 rows means row 0.
#[test]
def test_clamp_after_the_list_shrank : Bool :=
    I64.beq (Picker.clamp_selected 9 3) 2
        && I64.beq (Picker.clamp_selected 9 0) 0
        && I64.beq (Picker.clamp_selected (-4) 3) 0

/// The window's rows: `take_from` cuts the visible slice.
#[test]
def test_take_from_cuts_the_window : Bool :=
    String.beq (List.intercalate "," (Picker.take_from 1 2 ["a", "b", "c", "d"])) "b,c"

/// `nth` finds the highlighted row, and `none` past the end.
#[test]
def test_nth_finds_the_row : Bool :=
    match Picker.nth 1 ["a", "b"] {
        Option.some got => String.beq got "b",
        Option.none => false
    }
        && pk_no_nth (Picker.nth 5 ["a", "b"])

def pk_no_nth (r : Option String) : Bool :=
    match r {
        Option.some _ => false,
        Option.none => true
    }

// ── Resolving the chosen path ────────────────────────────────────────────

/// A `""` directory is the process's cwd, so the candidate IS the path.
#[test]
def test_resolve_in_the_cwd_is_the_candidate : Bool :=
    String.beq (Picker.resolve "" "main.mo") "main.mo"

/// A listing taken in a directory resolves against it.
#[test]
def test_resolve_joins_the_directory : Bool :=
    String.beq (Picker.resolve "src" "main.mo") "src/main.mo"

/// An ABSOLUTE candidate wins over the directory -- `IO.list_dir "/"` answers
/// `/a`, and joining it again would move it.
#[test]
def test_resolve_keeps_an_absolute_candidate : Bool :=
    String.beq (Picker.resolve "src" "/abs/main.mo") "/abs/main.mo"
