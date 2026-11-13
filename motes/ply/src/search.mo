// Ply's `/` search: finding the next match and turning it into a selection
// (code-editor.md Phase 5, the third item).
//
// WHY THIS IS ITS OWN MODULE: `commands.mo` is the update -- dispatch, the
// registry, the mode switches. Finding a match is a scan over the rope plus
// the wrap-around rule, which is the kind of thing worth reading (and
// testing) without a registry in the way. The regex mote does the matching;
// this module owns WHAT a search means.
//
// A SEARCH SELECTS, exactly as a motion does (the plan's §4 note: "the
// motion *selects*"). `/foo` does not just move the caret -- it puts a
// selection on the match, so the very next key acts on it (`/foo` then `d`
// deletes the match). That is the selection-first contract, and it is why
// this returns a `Selections` rather than an offset.
//
// LITERAL, NOT REGEX, AND THAT IS A DECISION. The regex mote exists (Phase
// 4 landed: `Regex.new`, `find_all`, `find_at`), and `select_regex` (`s`)
// uses it. `/` stays a PLAIN SUBSTRING search because that is what every
// modal editor's `/` does by default -- vim's `/` is a regex only because
// vim has `nomagic` and `\V`; Helix's `/` is literal. A user typing `/a.b`
// expects to find "a.b". Making `/` regex would silently change what a
// query means, and a literal search is the one whose failure mode
// ("no match") is not surprising. `s` is the way to ask for a pattern.
//
// NO IO HERE, and no `EditorState`: the module takes a rope, a search
// origin and a query, so a test drives the whole wrap rule with string
// fixtures and the `monad_eval` interpreter can run it.

use init::shared {Shared}
use lib::types {Rope, Selection, Selections}
use lib::rope {Rope.line_start, Rope.line_of, Rope.line_content_end,
    Rope.end_offset, Rope.slice}

// ── Finding ──────────────────────────────────────────────────────────────

/// The byte offset of the first match of `query` at or after `from`, or
/// `none`. A query is never matched from inside a multi-byte character:
/// `String.byte_index_of` walks by character (`init/src/string.mo`), so a
/// needle made of whole characters can only be found at a boundary.
///
/// AN EMPTY QUERY HAS NO MATCH. `String.byte_index_of ""` answers `some 0`
/// (an empty needle matches everywhere), which as a search would mean
/// "Enter jumps to the top of the file and `n` never moves" -- a silent
/// no-op that reads like a hang. The caller refuses the empty query long
/// before here (`run_search`), and the guard is repeated so this def's
/// answer is its own.
pub def Search.find_from (text : String) (query : String) (from : I64) : Option I64 :=
    if String.is_empty query
    then Option.none
    else if Bool.not (from < String.length text)
    then Option.none
    else match String.byte_index_of (String.drop from text) query {
        Option.none => Option.none,
        Option.some rel => Option.some (from + rel)
    }

/// The offset of the match to select for a search started at `origin` going
/// `forward`, WRAPPING once at the end. A forward search looks at or after
/// `origin`; a backward one looks for the LAST match before it. Failing
/// either, it wraps to the other end -- the rule every editor keeps, because
/// a search that refused to wrap makes `n` at the last match feel broken.
///
/// `origin` IS EXCLUSIVE FOR A BACKWARD SEARCH. `n` after a match must find
/// the one before it, not the same span again; the caret is on the match's
/// head, which for a forward search is its end, so "before" must mean
/// strictly before the match's START. `Search.step`'s caller passes the
/// selection's start for exactly this reason.
pub def Search.next_match (text : String) (query : String) (origin : I64) (forward : Bool)
    : Option I64 :=
    let from : I64 := if origin < 0 then 0 else origin in
    if forward
    then match Search.find_from text query from {
        Option.some at => Option.some at,
        Option.none => ply_wrap_forward text query
    }
    else match Search.last_before text query from {
        Option.some at => Option.some at,
        Option.none => ply_wrap_backward text query
    }

/// The first match in the whole text -- the wrap destination of a forward
/// search that ran off the end.
def ply_wrap_forward (text : String) (query : String) : Option I64 :=
    Search.find_from text query 0

/// The LAST match in the whole text -- the wrap destination of a backward
/// search that ran off the start.
def ply_wrap_backward (text : String) (query : String) : Option I64 :=
    Search.last_before text query (String.length text)

/// The offset of the last match of `query` that STARTS strictly before
/// `before`, or `none`.
///
/// One forward pass carrying the best hit so far. `String.d`rop is O(1) (an
/// interior pointer) and the scan is per character, so a 1 MiB buffer pays
/// its bytes once -- the same cost as the forward direction, which is what a
/// `N` at the top of a file should cost.
#[terminating]
def Search.last_before (text : String) (query : String) (before : I64) : Option I64 :=
    if String.is_empty query
    then Option.none
    else ply_last_go text query 0 before Option.none

/// The scan behind `last_before`. `at` is an absolute offset in `text`; each
/// step re-slices the tail, so no offset arithmetic crosses a character
/// boundary unnoticed.
#[terminating]
def ply_last_go (text : String) (query : String) (at : I64) (before : I64)
    (best : Option I64) : Option I64 :=
    if Bool.not (at < before)
    then best
    else if Bool.not (at < String.length text)
    then best
    else match String.byte_index_of (String.drop at text) query {
        Option.none => best,
        Option.some rel =>
            let hit : I64 := at + rel in
            if Bool.not (hit < before)
            then best
            else ply_last_go text query (hit + 1) before (Option.some hit)
    }

// ── Turning a match into a selection ─────────────────────────────────────

/// One selection over `[start, start + len)` -- the match, select-then-act.
/// The anchor is the start and the head the end, so the selection reads
/// left-to-right and `d` deletes it.
pub def Search.selection_at (start : I64) (len : I64) : Selections :=
    let one : Selection := { anchor := start, head := start + len } in
    { ranges := List.cons one List.empty, primary := 0 }

// ── The line-aware query the picker's ranking also wants ─────────────────

/// The text of the line `off` sits on, WITHOUT its terminator. The search's
/// status line reports the line number, and the picker's fuzzy ranking does
/// not need this at all -- it is here because "the line containing an
/// offset" is the one geometry both the search and `goto` want, and two
/// copies of it would drift.
pub def Search.line_text_of (rope : Rope) (off : I64) : String :=
    let line : I64 := Rope.line_of rope off in
    let ls : I64 := Rope.line_start rope line in
    Rope.slice rope ls (Rope.line_content_end rope line - ls)

/// The number of the line `off` sits on, 1-based for display.
pub def Search.line_number_of (rope : Rope) (off : I64) : I64 :=
    Rope.line_of rope off + 1

/// The buffer's whole text, for a scan. Kept here (rather than reaching into
/// `model.mo`) so the search stays a function of a rope, and shared through
/// one handle where the caller reads it twice -- `commands.mo`'s job.
pub def Search.text_of (rope : Shared Rope) : String :=
    Rope.slice (Shared.get rope) 0 (Rope.end_offset (Shared.get rope))
