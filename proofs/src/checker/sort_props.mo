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

use lib::checker::harness {accepted, rejected, infers_sort_at}

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
    rejected (Term.sort (SortLevel.concrete 1)) (Term.sort (SortLevel.concrete 1))

/// The same hole one level down: `Prop : Prop` must be refused too.
/// A fix that special-cased level 1 rather than correcting the relation
/// would pass the pin above and fail this one.
#[test]
def prop_is_not_its_own_type : Bool :=
    rejected (Term.sort (SortLevel.concrete 0)) (Term.sort (SortLevel.concrete 0))

// --- The hierarchy is inhabited strictly upward ---

/// `Prop : Type`.
#[test]
def prop_inhabits_type : Bool :=
    accepted (Term.sort (SortLevel.concrete 0)) (Term.sort (SortLevel.concrete 1))

/// `Type : Sort 2`.
#[test]
def type_inhabits_sort_2 : Bool :=
    accepted (Term.sort (SortLevel.concrete 1)) (Term.sort (SortLevel.concrete 2))

/// Strictness: a sort does not inhabit the level directly below it.
/// Together with the two pins above this pins the relation at three
/// consecutive levels, so neither `n < m` being relaxed to `n <= m` nor
/// to `n <= m + 1` survives.
#[test]
def sort_2_does_not_inhabit_type : Bool :=
    rejected (Term.sort (SortLevel.concrete 2)) (Term.sort (SortLevel.concrete 1))

// --- Inferring a sort's own type ---

/// Checked against no expectation at all, `Prop` infers `Type` --
/// `type_check_sort_full`'s `Term.hole` arm, `Sort (level + 1)`.
#[test]
def prop_infers_type_unprompted : Bool :=
    accepted (Term.sort (SortLevel.concrete 0)) Term.hole

/// And `Type` infers `Sort 2`, the same arm one level up. Pinned
/// separately because the arm's `+ 1` is the whole of the rule: an
/// off-by-one there is invisible to the accept/reject pins above (which
/// pass a concrete expectation) and only shows when nothing is expected.
#[test]
def type_infers_sort_2_unprompted : Bool :=
    accepted (Term.sort (SortLevel.concrete 1)) Term.hole

// --- Sort levels: structure rather than a bare numeral ---
//
// A sort carries its level as STRUCTURE (`concrete`/`var`/`max`/`succ`),
// and the rules must handle every shape, not just a numeral.
// `sort_level_of` is what lets a shape-inspecting site read the level and
// `level_const` is what folds a computed one, so a pin below that fails is
// one of those two rather than the sort rule itself.
//
// The grammar lowers a source `Type`/`Sort n`/`Sort u` to this shape
// already, so these are reachable from source and exercised by the sweep
// -- but pinning them by hand is still the point: a wrong `succ` in
// `type_check_sort_full`, or a dropped arm in `sort_level_of`, would
// otherwise be found by a corpus-wide red sweep instead of by a named pin.

/// `Prop : Type` at explicit levels -- the same claim as
/// `prop_inhabits_type`, reached through `level_lt (concrete 0)`.
#[test]
def sort_spelling_is_a_valid_inhabitant : Bool :=
    accepted (Term.sort (SortLevel.concrete 0)) (Term.sort (SortLevel.concrete 1))

/// The soundness pin again, one level up: `Sort 1 : Sort 1` must be
/// refused, and it must be refused by the LEVEL relation rather than by the
/// two sides failing to match structurally.
#[test]
def sort_spelling_is_not_its_own_type : Bool :=
    rejected (Term.sort (SortLevel.concrete 1)) (Term.sort (SortLevel.concrete 1))

/// The EXPECTED side -- the direction a checker that matched the expected
/// term directly, numeral only, cannot do at all. Reading both sides
/// through `sort_level_of` is what makes a computed expectation readable.
///
/// The claim is checked rather than asserted: making `sort_level_of`
/// answer `Option.none` for a `Term.sort` input -- i.e. dropping exactly
/// that absorption -- fails THIS pin and no other one in this file
/// (11/12). So the pin is sensitive to that rule alone and
/// cannot be passing through some unrelated path.
#[test]
def type_spelling_is_accepted_at_a_sort_spelling_expectation : Bool :=
    accepted (Term.sort (SortLevel.concrete 1)) (Term.sort (SortLevel.concrete 2))

/// A level that is not a literal still compares: `succ (concrete 0)` IS
/// `concrete 1`, so `Type : Sort 2` holds through it. Pins `level_const`'s
/// `succ` evaluation -- an unresolved level deliberately has no `I64`, and
/// this is the case that shows the evaluated one does.
#[test]
def sort_spelling_evaluates_a_succ_level : Bool :=
    accepted (Term.sort (SortLevel.succ (SortLevel.concrete 0))) (Term.sort (SortLevel.concrete 2))

/// With nothing expected, a sort must reach the rule's `Term.hole` arm
/// rather than be checked against some invented expectation. It is a real
/// pin on the ARM ORDER, not just on the level: were `sort_level_of
/// (Term.hole)` ever to answer `some (concrete 0)` instead of
/// `Option.none`, this exact term would be compared against `Prop` and
/// refused, and the pin would fail. This is the same claim as
/// `type_inhabits_sort_2`.
#[test]
def sort_spelling_is_accepted_with_no_expectation : Bool :=
    accepted (Term.sort (SortLevel.concrete 1)) Term.hole

// --- The universe of a Pi/Forall is the MAX of its components ---
//
// These pin W1.2. They cannot be written with `accepted`: `type_check`'s
// `Term.pi`/`Term.forall` arms ignore the expectation completely and answer
// the universe they computed, so every well-formed Pi is accepted against
// EVERY expectation and no accept/reject pair can tell a `max` from a flat,
// numeral-only universe. They read the inferred type instead, through the
// harness's `inferred_sort_level`.
//
// Every level below is one higher than the level its component is written
// at, and that is the rule rather than an off-by-one: a component's
// contribution is the sort of its TYPE, and `Sort n : Sort (n+1)`. So
// `Type` (written at level 1) contributes 2, `Sort 3` contributes 4, and
// the Pi over both lives at 4.

/// The codomain decides when it is the higher one: `(Type) -> Sort 3`
/// lives at 4, not at the domain's 2.
#[test]
def pi_universe_is_the_max_of_its_parts : Bool :=
    infers_sort_at (Term.pi (Term.sort (SortLevel.concrete 1)) (Term.sort (SortLevel.concrete 3))) 4

/// The domain decides when IT is the higher one -- the mirror image, so
/// neither "always the first" nor "always the second" survives both pins.
/// `(Sort 3) -> Sort 2`: the domain contributes 4, the codomain 3.
#[test]
def pi_universe_is_the_max_not_the_last_part : Bool :=
    infers_sort_at (Term.pi (Term.sort (SortLevel.concrete 3)) (Term.sort (SortLevel.concrete 2))) 4

/// `Forall` is the same rule, pinned separately because it is a separate
/// arm -- a `max` added to one arm and not the other is exactly the shape
/// of half-fix this file exists to catch.
#[test]
def forall_universe_is_the_max_of_its_parts : Bool :=
    infers_sort_at (Term.forall (DebugName.named (Identifier.id "a")) (Term.sort (SortLevel.concrete 1)) (Term.sort (SortLevel.concrete 3))) 4

/// A component that is not a known sort contributes a flat 1, which is
/// what both arms answered unconditionally before W1.2. This is the pin
/// that says the `max` did not quietly become "the sort of anything,
/// defaulting to 0" -- a hole at both ends must still land at 1.
#[test]
def pi_universe_defaults_an_unknown_component_to_1 : Bool :=
    infers_sort_at (Term.pi Term.hole Term.hole) 1

/// `Prop` at both ends: both components contribute 1 (`Prop : Type`), so
/// the Pi is at 1 -- the level W1.2 must NOT move, since every `Pi` in the
/// corpus today has components at exactly this level.
#[test]
def pi_universe_of_prop_components_stays_at_1 : Bool :=
    infers_sort_at (Term.pi (Term.sort (SortLevel.concrete 0)) (Term.sort (SortLevel.concrete 0))) 1
