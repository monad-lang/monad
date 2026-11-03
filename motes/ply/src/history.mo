// Ply's undo history: a tree of revisions, not a stack.
//
// UNDO IS SNAPSHOT MOVEMENT, NOT INVERSE CHANGES (the plan's Decision 2):
// every `Revision` holds a pointer to the whole-text rope its transaction
// produced, so undo and redo only move `History.current` -- there is no
// inverse edit to compute and none to get wrong. The `Change` list rides
// along anyway because two consumers need deltas and not snapshots: LSP
// `didChange` (Phase 6) and the MCP edit log (Phase 7).
//
// A BRANCH STAYS REACHABLE (the Phase 1 gate's undo/redo case): committing
// after an undo does not delete the undone child -- `revisions` is a map
// keyed by id, so the old branch is still there and `History.goto` walks to
// it. That is the whole reason the history is a tree keyed by id and not a
// list: `undo; edit` forks the tree, and a list would have thrown the
// other fork away.
//
// `time_ms` is a stamp for the later earlier/later traversal (Helix's
// `earlier`/`later`); Phase 1 commits 0 for every revision because the
// pure core has no clock -- the TUI (Phase 4) stamps transactions as they
// arrive, and the comparison this field feeds is not exercised until then.
//
// AFFINE DISCIPLINE: a `History` holds a `BTreeMap`, so it is deliberately
// not `Copy` (the absent-list doctrine), and no def below may touch the
// record twice. Every def matches the record into its fields ONCE and
// passes those fields to a helper -- the same discipline `selection.mo`
// records. The one exception is `commit`, which threads four fields; its
// helper takes exactly those four, so the record is read once there too.

use init::shared {Shared}
use std::map {Map, BTreeMap}
use lib::types {Rope, Selections, Change, Revision, History}
use lib::selection {Selections.cursor}

/// An empty history: no revisions at all. `History.current` and
/// `History.saved` name none (`-1` is not a revision id: ids are `0..`), and
/// the first `commit` creates revision 0.
pub def History.empty : History :=
    { revisions := BTreeMap.empty,
      current := 0 - 1,
      next_id := 0,
      saved := 0 - 1 }

/// The current revision, if the history has one. `History.empty` has none;
/// every history with a commit always does.
pub def History.current_revision (h : History) : Option Revision :=
    match h {
        { revisions, current, .. } => Map.lookup current revisions
    }

/// The text at the current revision -- the whole rope, since a revision IS
/// a whole-text snapshot. An empty history answers the empty rope.
pub def History.current_rope (h : History) : Rope :=
    match History.current_revision h {
        Option.some rev => rev.rope,
        Option.none => Rope.leaf ""
    }

/// The selections at the current revision, for restoring after an undo.
pub def History.current_selections (h : History) : Selections :=
    match History.current_revision h {
        Option.some rev => rev.selections,
        Option.none => Selections.cursor 0
    }

/// Commit one transaction's result: a new revision whose parent is the
/// current one, and `current` moved to it. The caller (a transaction)
/// supplies the rope and selections AFTER the changes and the change list
/// that produced them, so the history never edits -- it only records.
///
/// A commit after an undo FORKS rather than overwrites: the undone child
/// keeps its id and stays in `revisions` (see the module header). That is
/// this function's whole contract with `History.goto`.
///
/// Returns the grown history and the new revision's id, so a caller that
/// wants the id (the MCP server reporting a new version) does not have to
/// read it back out.
pub def History.commit (h : History) (rope : Rope) (selections : Selections)
    (changes : List Change) (time_ms : I64) : Pair History I64 :=
    match h {
        { revisions, current, next_id, saved } =>
            History.commit_grown revisions current next_id saved rope selections changes time_ms
    }

/// The grown history: insert the new revision, move `current` to it, bump
/// `next_id`, keep `saved` (a commit does not save).
def History.commit_grown (revisions : BTreeMap I64 Revision) (current : I64) (next_id : I64)
    (saved : I64) (rope : Rope) (selections : Selections) (changes : List Change) (time_ms : I64)
    : Pair History I64 :=
    let rev : Revision :=
        { parent := current,
          rope := rope,
          selections := selections,
          changes := changes,
          time_ms := time_ms } in
    let grown : History :=
        { revisions := Map.insert next_id rev revisions,
          current := next_id,
          next_id := next_id + 1,
          saved := saved } in
    Pair.pair grown next_id

/// Step to the current revision's parent: `u`. `Option.none` when there is
/// nothing to undo -- the current revision is the root, or the history is
/// empty -- and that is a value the caller reports, not an error.
pub def History.undo (h : History) : Option History :=
    match h {
        { revisions, current, next_id, saved } =>
            History.undo_from revisions current next_id saved
    }

/// The undo step, with every field bound once: look up the current
/// revision, then move to its parent unless that parent is the sentinel
/// (a root's parent is itself -- `commit` stores `current` as the parent of
/// revision 0, which is `-1` for the empty history's first commit, i.e.
/// "no parent" -- and `-1 == current` would mean undoing an empty history,
/// which is the `none` case).
def History.undo_from (revisions : BTreeMap I64 Revision) (current : I64) (next_id : I64)
    (saved : I64) : Option History :=
    // The map is read twice (lookup, then the rebuilt history), so it is
    // shared -- the affine rule's own remedy, and the honest one for a
    // persistent tree both sides only read.
    let shared : Shared (BTreeMap I64 Revision) := Shared.of revisions in
    match Map.lookup current (Shared.get shared) {
        Option.some rev =>
            match rev {
                { parent, .. } =>
                    if I64.beq parent (0 - 1)
                    then Option.none
                    else Option.some
                        { revisions := Shared.get shared,
                          current := parent,
                          next_id := next_id,
                          saved := saved }
            },
        Option.none => Option.none
    }

/// Step forward: `U`. From a revision reached by undo, the forward
/// direction is ambiguous once a branch exists, so this takes the NEWEST
/// child of `current` -- the largest id among revisions whose parent is the
/// current one, which is the branch the user was most recently on.
/// `Option.none` at a leaf (nothing to redo).
pub def History.redo (h : History) : Option History :=
    match h {
        { revisions, current, next_id, saved } =>
            History.redo_scan (BTreeMap.to_list revisions) current (0 - 1) revisions next_id saved
    }

/// The scan: `entries` in ascending id order (that is `BTreeMap.to_list`'s
/// order), so the LAST child found is the newest. `best` starts at the
/// sentinel `-1`, which no real id equals; `next_id`/`saved` ride along so
/// the rebuilt history keeps them.
#[terminating]
def History.redo_scan (entries : List (Pair I64 Revision)) (cur : I64) (best : I64)
    (revisions : BTreeMap I64 Revision) (next_id : I64) (saved : I64) : Option History :=
    match entries {
        List.empty =>
            if I64.beq best (0 - 1)
            then Option.none
            else Option.some { revisions := revisions, current := best, next_id := next_id, saved := saved },
        List.cons e rest =>
            match e {
                Pair.pair id rev =>
                    if I64.beq rev.parent cur
                    then History.redo_scan rest cur id revisions next_id saved
                    else History.redo_scan rest cur best revisions next_id saved
            }
    }

/// Move to a named revision: the exact navigation a branch jump needs, and
/// the undo/redo movements are its special cases. `Option.none` when `id`
/// is not in the history (a caller cannot invent an id the map does not
/// hold, but `goto` is total anyway: a history API is editor-facing input).
pub def History.goto (h : History) (id : I64) : Option History :=
    match h {
        { revisions, next_id, saved, .. } =>
            match Map.lookup id revisions {
                Option.some _ =>
                    Option.some { revisions := revisions, current := id, next_id := next_id, saved := saved },
                Option.none => Option.none
            }
    }

/// Mark the current revision as the saved one: the dirty flag is
/// `current != saved` (Phase 4's `Space w` and `:q` refusal).
pub def History.mark_saved (h : History) : History :=
    match h {
        { revisions, current, next_id, .. } =>
            { revisions := revisions, current := current, next_id := next_id, saved := current }
    }
