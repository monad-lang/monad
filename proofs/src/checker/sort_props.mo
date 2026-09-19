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

// --- The second spelling: `Term.sort (SortLevel ...)` ---
//
// Every pin above writes a sort as `Term.type_ n`, the concrete-level
// spelling the checker itself builds. `Term.sort` carries the same level
// as structure (`concrete`/`var`/`max`/`succ`), and the rules must agree
// across the two -- `sort_level_of` is the one helper that absorbs the
// difference, so a pin below that fails is that helper, not the sort rule.
//
// The second spelling is reachable from source only once the parser lowers
// a concrete level to it (deferred: the grammar still emits `Term.type_`,
// so these are hand-built terms, exactly as the pins above are). Pinning
// it NOW is the point: `level_const`/`level_lt` are exercised by the sweep
// the moment the lowering flips, and a wrong `succ` there would otherwise
// be found by a corpus-wide red sweep instead of by a named pin.

/// `Prop : Type` in the structured spelling -- the same claim as
/// `prop_inhabits_type`, reached through `level_lt (concrete 0)`.
#[test]
def sort_spelling_is_a_valid_inhabitant : Bool :=
    accepted (Term.sort (SortLevel.concrete 0)) (Term.type_ 1)

/// The soundness pin again, one level up and in the structured spelling:
/// `Sort 1 : Sort 1` must be refused, and it must be refused by the level
/// relation rather than by a spelling mismatch between the two sides.
#[test]
def sort_spelling_is_not_its_own_type : Bool :=
    rejected (Term.sort (SortLevel.concrete 1)) (Term.sort (SortLevel.concrete 1))

/// The EXPECTED side in the structured spelling -- the one direction the
/// pre-W1.1 checker could not have done, because it matched the expected
/// term directly (`Term.type_ expected_level`) and so had no way to read
/// a structured expectation at all. Reading both sides through
/// `sort_level_of` is what makes the spellings interchangeable.
///
/// The claim is checked rather than asserted: making `sort_level_of`
/// answer `Option.none` for a `Term.sort` input -- i.e. dropping exactly
/// the expected-side absorption -- fails THIS pin and no other one in
/// this file (11/12). So the pin is sensitive to that rule alone and
/// cannot be passing through some unrelated path.
#[test]
def type_spelling_is_accepted_at_a_sort_spelling_expectation : Bool :=
    accepted (Term.type_ 1) (Term.sort (SortLevel.concrete 2))

/// A level that is not a literal still compares: `succ (concrete 0)` IS
/// `concrete 1`, so `Type : Sort 2` holds through it. Pins `level_const`'s
/// `succ` evaluation -- an unresolved level deliberately has no `I64`, and
/// this is the case that shows the evaluated one does. The expectation is
/// written in the OTHER spelling on purpose: a `succ` level against a
/// `Term.sort` expectation would leave this pin passing even if the
/// absorption were one-directional.
#[test]
def sort_spelling_evaluates_a_succ_level : Bool :=
    accepted (Term.sort (SortLevel.succ (SortLevel.concrete 0))) (Term.type_ 2)

/// With nothing expected, a structured sort must reach the rule's
/// `Term.hole` arm rather than be checked against some invented
/// expectation. It is a real pin on the ARM ORDER, not just on the level:
/// were `sort_level_of (Term.hole)` ever to answer `some (concrete 0)`
/// instead of `Option.none`, this exact term would be compared against
/// `Prop` and refused, and the pin would fail. `Sort 1 : Sort 2` in the
/// structured spelling is the same claim as `type_inhabits_sort_2`, so the
/// two spellings are pinned at the same level.
#[test]
def sort_spelling_is_accepted_with_no_expectation : Bool :=
    accepted (Term.sort (SortLevel.concrete 1)) Term.hole
