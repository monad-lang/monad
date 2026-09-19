// Pins on the sort/universe rules (`type_check_sort_full`,
// lang/src/typecheck/infer.mo).
//
// These are REGRESSION PINS, not proofs of soundness. Each one pins a
// rule the checker is supposed to implement, on the exact term shape
// that reaches that rule -- so if the rule is loosened or the term shape
// drifts out from under it, the pin fails and says so. What they cannot
// do is establish that the checker is sound; only the negative pin below
// is a genuine soundness claim, and it is genuine precisely because it
// asserts a REFUSAL.
//
// `Sort n : Sort m` holds exactly when `n < m`. There is no `Sort n :
// Sort n` -- that is Type-in-Type -- and no `Sort n : Sort m` for
// `n > m`. Cumulativity (the `≤` in `Sort n ≤ Sort m` for `n ≤ m`) is a
// CONVERSION rule, applied by `unify` when comparing two types, and is
// deliberately NOT what these pins test: `type_check_sort_full` answers
// "is this sort a valid inhabitant of that sort", a strictly lower
// relation.

use lib::checker::harness {accepted, rejected}

// --- The soundness pin ---

/// `Type : Type` must be refused. This is the one pin here that is a
/// soundness claim rather than a characterization: accepting it makes
/// the checker inconsistent via Girard's paradox.
///
/// It was ACCEPTED before, by an `I64.beq expected_level level` arm in
/// `type_check_sort_full` ahead of the strict comparison. `Sort 1` has
/// to be built as a `Term` rather than written in source, because in
/// source it lowers to an application of the `Sort` global (see the
/// harness's own note on reachability) -- which is exactly why this pin
/// is term-level.
#[test]
def sort_is_not_its_own_type : Bool :=
    rejected (Term.type_ 1) (Term.type_ 1)

/// The same hole one level down: `Prop : Prop` must be refused too.
/// A fix that special-cased level 1 rather than correcting the relation
/// would pass the pin above and fail this one.
#[test]
def prop_is_not_its_own_type : Bool :=
    rejected (Term.type_ 0) (Term.type_ 0)

// --- The hierarchy is inhabited strictly upward ---

/// `Prop : Type`.
#[test]
def prop_inhabits_type : Bool :=
    accepted (Term.type_ 0) (Term.type_ 1)

/// `Type : Sort 2`.
#[test]
def type_inhabits_sort_2 : Bool :=
    accepted (Term.type_ 1) (Term.type_ 2)

/// Strictness: a sort does not inhabit the level directly below it.
/// Together with the two pins above this pins the relation at three
/// consecutive levels, so neither `n < m` being relaxed to `n <= m` nor
/// to `n <= m + 1` survives.
#[test]
def sort_2_does_not_inhabit_type : Bool :=
    rejected (Term.type_ 2) (Term.type_ 1)

// --- Inferring a sort's own type ---

/// Checked against no expectation at all, `Prop` infers `Type` --
/// `type_check_sort_full`'s `Term.hole` arm, `Sort (level + 1)`.
#[test]
def prop_infers_type_unprompted : Bool :=
    accepted (Term.type_ 0) Term.hole

/// And `Type` infers `Sort 2`, the same arm one level up. Pinned
/// separately because the arm's `+ 1` is the whole of the rule: an
/// off-by-one there is invisible to the accept/reject pins above (which
/// pass a concrete expectation) and only shows when nothing is expected.
#[test]
def type_infers_sort_2_unprompted : Bool :=
    accepted (Term.type_ 1) Term.hole
