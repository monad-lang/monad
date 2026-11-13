// Ply's file picker: ranking a directory listing against what was typed
// (code-editor.md Phase 5, the second item).
//
// THE LISTING IS IO AND LIVES ELSEWHERE. `Space f` issues a `Cmd.perform`
// that calls `IO.list_dir` and answers `EditorMsg.picker_files`; the pure
// update folds it onto the state (`EditorState.with_picker_files`). This
// module is the PURE half: given the candidates and the filter, which ones
// survive and in what order. That split is the same one `save_result` uses
// and for the same reason -- `Cmd.perform`'s action cannot see the state.
//
// RANKING, IN THE ORDER THE PLAN ASKS FOR: an EXACT PREFIX match first.
// Four tiers, best first:
//
//   1. the file's OWN NAME starts with the filter ("main" -> "main.mo");
//   2. the relative path starts with it ("motes/ply" -> "motes/ply/src/...");
//   3. the path CONTAINS it ("src" -> "motes/ply/src/main.mo");
//   4. the filter is a SUBSEQUENCE of the path ("mpl" -> "motes/ply/..."),
//      which is the fuzzy tier -- the one that makes a picker worth having.
//
// Inside a tier, shorter paths come first: a filter is a way of saying
// "the one I mean", and among two matches the shorter name is more often
// the one meant. Equal scores then keep the listing's own order, through an
// INDEX TIEBREAK carried in the score (`Picker.combine`) rather than through
// the sort's stability -- `List.sort_by` claims stability but reverses equal
// elements, so an answer that relied on it would shuffle between keystrokes,
// which is the one thing a fuzzy list must never do.
//
// A MISSING MATCH IS DROPPED, not ranked last: a picker listing every file
// in the tree with the non-matches at the bottom is a worse answer than a
// short list, because the arrow keys then have to travel through them.
//
// LITERAL, CASE-INSENSITIVE, AND ON BYTES. Case folding is
// `String.to_lowercase`, which is what a user expects of a file filter.
// The walk is over bytes (`String.to_list`), so a multi-byte character is
// compared byte-wise -- consistent, and never a boundary question, because
// a filter typed one character at a time is a byte sequence either way.

use init::shared {Shared}
use std::list {List.sort_by}
use std::path {raw_path_join}

// ── The tiers ────────────────────────────────────────────────────────────

/// The best tier: the file's own name starts with the filter.
pub def Picker.tier_name_prefix : I64 := 0

/// The relative path starts with the filter.
pub def Picker.tier_path_prefix : I64 := 1

/// The path contains the filter.
pub def Picker.tier_contains : I64 := 2

/// The filter is a subsequence of the path.
pub def Picker.tier_subsequence : I64 := 3

// ── Matching ─────────────────────────────────────────────────────────────

/// Is `needle` a subsequence of `hay`? (Every byte of `needle` appears in
/// `hay`, in order, not necessarily adjacently.) This is the fuzzy tier.
#[terminating]
def is_subsequence (hay : List U8) (needle : List U8) : Bool :=
    match needle {
        List.empty => true,
        List.cons n nrest =>
            match hay {
                List.empty => false,
                List.cons h hrest =>
                    if U8.beq n h
                    then is_subsequence hrest nrest
                    else is_subsequence hrest (List.cons n nrest)
            }
    }

/// The file's own name from a relative path: everything after the last
/// `/`. A path with no `/` is its own name, which is the whole point.
def base_name (path : String) : String :=
    let at : I64 := String.find_last path "/" in
    if at < 0 then path else String.drop (at + 1) path

/// The rank tier `path` earns for `want` (both already lowercased), or
/// `none` when the path does not match at all.
///
/// THE ORDER OF THE TESTS IS THE RANKING. Each arm returns as soon as it
/// matches, so the first (best) tier a path qualifies for is the one it
/// gets -- a name prefix is never demoted to "contains" just because it
/// also contains the filter further along.
def rank_tier (path : String) (want : String) : Option I64 :=
    if String.is_empty want
    then Option.some Picker.tier_name_prefix
    else if String.starts_with want (base_name path)
    then Option.some Picker.tier_name_prefix
    else if String.starts_with want path
    then Option.some Picker.tier_path_prefix
    else if String.contains path want
    then Option.some Picker.tier_contains
    else if is_subsequence (String.to_list path) (String.to_list want)
    then Option.some Picker.tier_subsequence
    else Option.none

/// One candidate's score: `(tier, length)`, lower is better. `none` is a
/// non-match. The length is the TIEBREAK inside a tier.
pub def Picker.score (path : String) (want : String) : Option (Pair I64 I64) :=
    match rank_tier (String.to_lowercase path) (String.to_lowercase want) {
        Option.none => Option.none,
        Option.some tier => Option.some (Pair.pair tier (String.length path))
    }

// ── Ranking a listing ────────────────────────────────────────────────────

/// Every candidate that matches, best first. The one entry point the update
/// and the view both call, so the list a user sees and the list `Enter`
/// accepts are the same list by construction.
pub def Picker.rank (files : List String) (want : String) : List String :=
    // The filter is lowercased ONCE and shared into the scan: the affine
    // rule's own remedy, and the reason the scan is not a per-row
    // `String.to_lowercase`.
    let want_lc : String := String.to_lowercase want in
    let hits : List (Pair I64 String) := Picker.rank_go files want_lc 0 List.empty in
    Picker.ordered hits

/// The matching candidates as `(score, path)` pairs, in listing order.
///
/// `at` IS THE CANDIDATE'S INDEX IN THE LISTING, and it is threaded into the
/// score (`Picker.combine`) rather than left to the sort's stability. That is
/// deliberate: `std`'s `List.sort_by` documents itself as stable but orders
/// EQUAL elements in reverse (`tests/picker_tests.mo`'s
/// `test_equal_scores_keep_listing_order` pins the behaviour a picker needs),
/// so relying on it would make two equally-ranked files swap places on every
/// keystroke -- the one thing a fuzzy list must never do. An explicit index
/// tiebreak is a total order, so no stability is needed at all.
#[terminating]
def Picker.rank_go (files : List String) (want : String) (at : I64)
    (acc : List (Pair I64 String)) : List (Pair I64 String) :=
    match files {
        List.empty => List.reverse acc,
        List.cons one rest =>
            match Picker.score one want {
                Option.none => Picker.rank_go rest want (at + 1) acc,
                Option.some s =>
                    match s {
                        Pair.pair tier len =>
                            Picker.rank_go rest want (at + 1)
                                (List.cons (Pair.pair (Picker.combine tier len at) one) acc)
                    }
            }
    }

/// One comparable number from a score's three parts, best first: the tier,
/// then the path's length, then the LISTING INDEX -- so a shorter path always
/// wins inside a tier, and two candidates that agree on both keep the order
/// the directory listed them in.
///
/// The scales are the widest any listing can reach rather than the widest a
/// filesystem allows: a listing beyond a million entries, or a path beyond a
/// thousand bytes, is not a picker's problem, and `Picker.rank`'s callers
/// pass a listing `IO.list_dir` produced. Ties on all three are the same
/// path twice, which the sort may order either way.
pub def Picker.combine (tier : I64) (len : I64) (at : I64) : I64 :=
    tier * 1073741824 + len * 1048576 + at

/// Sort the scored candidates ascending and drop the scores, leaving the
/// paths. The score is a TOTAL order (`Picker.combine`), so no element
/// compares equal to another and the sort's stability cannot matter.
def Picker.ordered (hits : List (Pair I64 String)) : List String :=
    let sorted : List (Pair I64 String) := List.sort_by ply_pair_lt hits in
    Picker.paths_of sorted

/// Score order: strictly less. `Picker.combine` makes the score a total
/// order, so no two distinct candidates compare equal and the sort needs no
/// stability guarantee (`List.sort_by` has none in practice -- see
/// `Picker.rank_go`).
def ply_pair_lt (a : Pair I64 String) (b : Pair I64 String) : Bool :=
    match a {
        Pair.pair ka _ =>
            match b {
                Pair.pair kb _ => ka < kb
            }
    }

/// The second component of each pair, in order.
#[terminating]
def Picker.paths_of (hits : List (Pair I64 String)) : List String :=
    match hits {
        List.empty => List.empty,
        List.cons one rest =>
            match one {
                Pair.pair _ path => List.cons path (Picker.paths_of rest)
            }
    }

// ── The chosen candidate's path ──────────────────────────────────────────

/// The path `Enter` opens for `rel` -- a candidate from the listing --
/// relative to the directory the listing was taken in. A `dir` of `""` is
/// the process's own cwd, which is how the editor starts and why the answer
/// is then the candidate unchanged.
///
/// AN ABSOLUTE CANDIDATE WINS OVER `dir`: `raw_path_join` returns an
/// absolute second argument unchanged, which is what `IO.list_dir "/"`
/// needs (`/a` must not become `.//a`).
pub def Picker.resolve (dir : String) (rel : String) : String :=
    if String.is_empty dir then rel else raw_path_join dir rel

// ── The window ───────────────────────────────────────────────────────────

/// The first row of a `height`-row window over `count` rows with row
/// `selected` highlighted -- the least scroll that keeps the selection
/// visible. The same rule `tui`'s `ListState` applies (`list_scroll_to`),
/// restated here because the mode stores only `selected`: a stored offset
/// would be a second truth about the window, and a resize can strand one.
pub def Picker.window_offset (selected : I64) (height : I64) (count : I64) : I64 :=
    let h : I64 := if height < 1 then 1 else height in
    if count < 1
    then 0
    else if selected < 0
    then 0
    else if Bool.not (selected < count)
    then (if count < h then 0 else count - h)
    else if selected < h
    then 0
    else selected - h + 1

/// The highlighted row, clamped into `[0, count)` -- `0` when there is
/// nothing to pick. A filter can shrink the list under a selection that was
/// legal a keystroke ago, so every read goes through here.
pub def Picker.clamp_selected (selected : I64) (count : I64) : I64 :=
    if count < 1
    then 0
    else if selected < 0
    then 0
    else if Bool.not (selected < count)
    then count - 1
    else selected

/// The `height` rows of `rows` starting at `first`.
#[terminating]
pub def Picker.take_from (first : I64) (height : I64) (rows : List String) : List String :=
    let dropped : List String := Picker.drop_rows (if first < 0 then 0 else first) rows in
    Picker.take_rows height dropped

#[terminating]
def Picker.drop_rows (n : I64) (rows : List String) : List String :=
    if n < 1
    then rows
    else match rows {
        // The empty arm answers `List.empty` rather than the binder: the
        // match already consumed the scrutinee, so naming it again would be
        // a second read (the affine rule's own complaint).
        List.empty => List.empty,
        List.cons _ rest => Picker.drop_rows (n - 1) rest
    }

#[terminating]
def Picker.take_rows (n : I64) (rows : List String) : List String :=
    if n < 1
    then List.empty
    else match rows {
        List.empty => List.empty,
        List.cons one rest => List.cons one (Picker.take_rows (n - 1) rest)
    }

/// The `n`th row, or `none`.
#[terminating]
pub def Picker.nth (n : I64) (rows : List String) : Option String :=
    match rows {
        List.empty => Option.none,
        List.cons one rest =>
            if n < 1 then Option.some one else Picker.nth (n - 1) rest
    }
