// Ply's transactions: how a `List Change` becomes a new document.
//
// A TRANSACTION IS THE ONE EDITING FUNNEL (the plan's §1 note): every
// editing surface -- keystrokes, the TUI's commands, LSP edits, an agent's
// MCP `buffer_apply` -- goes through this module, so the invariant holds
// wherever an edit came from:
//
//   * changes are validated BEFORE anything moves: sorted by `start`,
//     non-overlapping, inside the text, and every offset lands on a UTF-8
//     character boundary;
//   * a rejected transaction leaves the document UNTOUCHED (the plan's
//     UTF-8-offsets risk: an agent's `Change` may carry an offset inside a
//     multi-byte sequence, and producing invalid text is the failure mode
//     this rejects instead);
//   * one transaction bumps `Document.version` exactly once, commits ONE
//     history revision, and maps every selection through every change.
//
// THE ORDER IS RIGHT-TO-LEFT (highest `stop` first): every change's
// offsets are in the OLD text's coordinates, so applying the LAST change
// first leaves the earlier changes' coordinates valid -- the same reason
// `selection.mo`'s mapping folds left-to-right over the same list. Both
// sides consume one sorted list and agree by construction.

use init::shared {Shared}
use lib::types {Rope, Selections, Change, History}
use lib::rope {Rope.replace, Rope.bytes, Rope.char_start}
use lib::selection {Selections.map_through_changes}
use lib::model {Document}
use lib::history {History.commit}
use lib::instances {}

/// Why a transaction was rejected -- a value, not a string, so the TUI can
/// word it and the MCP server can encode it without parsing its own
/// messages.
pub type Rejection {
    /// `start` outside `[0, bytes]`.
    out_of_bounds (start : I64),
    /// `stop` before `start`.
    inverted (start : I64) (stop : I64),
    /// A later change begins before an earlier one ends: unsorted or
    /// overlapping. Both changes are named.
    overlap (first : I64) (second : I64),
    /// An offset lands inside a multi-byte UTF-8 sequence. The offending
    /// offset is named.
    splits_char (off : I64)
}

/// Apply a whole transaction. `Result Rejection Document`: the document
/// out is a NEW value (rope, selections, history, version all moved), and
/// the document in is untouched by a rejection -- the caller's `Result.err`
/// handling is the whole story, there is no cleanup to do.
///
/// Validating FIRST and applying after is what makes "untouched on
/// rejection" free: a half-applied edit list would need an undo to roll
/// back, and the check costs one pass that the apply pass needs anyway.
pub def Transaction.apply (doc : Document) (changes : List Change) : Result Rejection Document :=
    // Both reads -- the rope the validate pass checks and the document the
    // apply pass consumes -- share one handle; the document is an immutable
    // record over persistent structures, so a borrow is the honest share.
    let shared : Shared Document := Shared.of doc in
    let view : Document := Shared.get shared in
    let shared_changes : Shared (List Change) := Shared.of changes in
    match view {
        { rope, .. } =>
            match Transaction.validate rope (Shared.get shared_changes) {
                Result.err why => Result.err why,
                Result.ok _ =>
                    Result.ok (Transaction.apply_validated view (Shared.get shared_changes))
            }
    }

/// Validate the change list against the rope: every offset inside the
/// text, every pair ordered and disjoint, every offset on a character
/// boundary. One left-to-right pass carrying the previous change's
/// `stop`; `Result.ok unit` means the list is applyable as-is.
pub def Transaction.validate (rope : Rope) (changes : List Change) : Result Rejection Unit :=
    Transaction.validate_go rope changes (0 - 1)

#[terminating]
def Transaction.validate_go (rope : Rope) (changes : List Change) (prev_stop : I64)
    : Result Rejection Unit :=
    match changes {
        List.empty => Result.ok unit,
        List.cons ch rest =>
            if Bool.not (Transaction.bounded rope ch)
            then Result.err (Rejection.out_of_bounds ch.start)
            // Adjacency is LEGAL: half-open ranges that touch
            // (`prev_stop == ch.start`) share no byte, so the rejection is
            // only when the later change starts strictly before the earlier
            // one ends.
            else if ch.start < prev_stop
            then Result.err (Rejection.overlap prev_stop ch.start)
            else if Bool.not (Rope.char_start rope ch.start)
            then Result.err (Rejection.splits_char ch.start)
            else if Bool.not (Rope.char_start rope ch.stop)
            then Result.err (Rejection.splits_char ch.stop)
            else Transaction.validate_go rope rest ch.stop
    }

/// Both ends of the change exist and are ordered: `0 <= start <= stop <=
/// bytes`. Written with `Bool.not`/`I64.lt` because `<=` is not bound. An
/// inverted change (`stop < start`) fails this, and the validate pass
/// reports it as `out_of_bounds` -- the one rejection the MCP surface has
/// to word, since a client computing offsets wrong is exactly the client
/// that needs the number back.
def Transaction.bounded (rope : Rope) (ch : Change) : Bool :=
    Bool.not (ch.start < 0)
        && Bool.not (Rope.bytes rope < ch.stop)
        && Bool.not (ch.stop < ch.start)

/// The apply pass, for a list `validate` accepted. Applies right-to-left
/// (highest offsets first), maps every selection through the whole list,
/// commits exactly one revision, bumps the version exactly once.
def Transaction.apply_validated (doc : Document) (changes : List Change) : Document :=
    match doc {
        { path, rope, selections, history, language, version } =>
            Transaction.apply_fields path rope selections history language version changes
    }

/// The apply, with every field bound once by the caller's pattern.
def Transaction.apply_fields (path : Option String) (rope : Rope) (selections : Selections)
    (history : History) (language : String) (version : I64) (changes : List Change) : Document :=
    // Three reads of the change list (rope, selections, history) share one
    // handle -- the same reasoning as `Transaction.apply`'s doc share.
    let shared_changes : Shared (List Change) := Shared.of changes in
    let new_rope : Rope := Transaction.apply_changes rope (Shared.get shared_changes) in
    let new_selections : Selections :=
        Selections.map_through_changes selections (Shared.get shared_changes) in
    Transaction.apply_commit path language version new_rope new_selections history (Shared.get shared_changes)

/// The commit step, split out so `new_selections` is bound once by the
/// caller's `let` and read once here.
def Transaction.apply_commit (path : Option String) (language : String) (version : I64)
    (rope : Rope) (selections : Selections) (history : History) (changes : List Change) : Document :=
    let shared_sel : Shared Selections := Shared.of selections in
    match History.commit history rope (Shared.get shared_sel) changes 0 {
        Pair.pair grown _ =>
            { path := path,
              rope := rope,
              selections := Shared.get shared_sel,
              history := grown,
              language := language,
              version := version + 1 }
    }

/// Apply every change to the rope, highest-offset change first.
#[terminating]
def Transaction.apply_changes (rope : Rope) (changes : List Change) : Rope :=
    match changes {
        List.empty => rope,
        List.cons ch rest =>
            let later := Transaction.apply_changes rope rest in
            Rope.replace later ch.start ch.stop ch.text
    }
