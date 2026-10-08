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

use lang::src::types {concrete, hole, id, named, pi, sort, succ}
use lib::checker::harness {accepted, rejected, infers_sort_at}
use lang::module {try_parse_decls}
use lang::scope {build_scope_from_decls}
use lang::typecheck::infer {empty_local_types, empty_locals, type_check}
use lang::types {
  ModulePath, Scope, ScopeData, binder_anon, binder_binder, cub, cub_interval, level_const,
  sentinel,
}

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

// --- The universe of a Pi chain is the MAX of its components ---
//
// These pin W1.2. They cannot be written with `accepted`: `type_check`'s
// `Term.pi` arm ignores the expectation completely and answers
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
    infers_sort_at (Term.pi binder_anon (Term.sort (SortLevel.concrete 1)) (Term.sort (SortLevel.concrete 3))) 4

/// The domain decides when IT is the higher one -- the mirror image, so
/// neither "always the first" nor "always the second" survives both pins.
/// `(Sort 3) -> Sort 2`: the domain contributes 4, the codomain 3.
#[test]
def pi_universe_is_the_max_not_the_last_part : Bool :=
    infers_sort_at (Term.pi binder_anon (Term.sort (SortLevel.concrete 3)) (Term.sort (SortLevel.concrete 2))) 4

/// `Forall` is the same rule, pinned separately because it is a separate
/// arm -- a `max` added to one arm and not the other is exactly the shape
/// of half-fix this file exists to catch.
#[test]
/// A quantifier binder (`binder`), not an arrow: R2b folded `Term.forall`
/// into `Term.pi`, and this pin is what says the universe rule did not move
/// with the constructor.
def quantifier_universe_is_the_max_of_its_parts : Bool :=
    infers_sort_at (Term.pi (binder_binder (Identifier.id "a")) (Term.sort (SortLevel.concrete 1)) (Term.sort (SortLevel.concrete 3))) 4

/// A component that is not a known sort contributes a flat 1, which is
/// what both arms answered unconditionally before W1.2. This is the pin
/// that says the `max` did not quietly become "the sort of anything,
/// defaulting to 0" -- a hole at both ends must still land at 1.
#[test]
def pi_universe_defaults_an_unknown_component_to_1 : Bool :=
    infers_sort_at (Term.pi binder_anon Term.hole Term.hole) 1

/// `Prop` at both ends: both components contribute 1 (`Prop : Type`), so
/// the Pi is at 1 -- the level W1.2 must NOT move, since every `Pi` in the
/// corpus today has components at exactly this level.
#[test]
def pi_universe_of_prop_components_stays_at_1 : Bool :=
    infers_sort_at (Term.pi binder_anon (Term.sort (SortLevel.concrete 0)) (Term.sort (SortLevel.concrete 0))) 1

// --- The interval is a primitive kind, not a universe resident ---
//
// Stage 1 step 4: `Π(i : I) A` with `A : Prop` must stay in `Prop`. The
// interval's checker-reported type is `Sort 1` (`I : Type`, matching the
// declared signature in the prelude's `with Cubical` block), and `level_of_type`
// defaults a non-sort to `concrete 1`, so without `pi_domain_level`'s
// bare-interval arm every `I -> A` lands one universe too high -- a
// `Prop`-valued path family bumped out of `Prop`, and Stage 2's
// `PathP : (A : I -> Sort l) -> A i0 -> A i1 -> Sort l` unstateable at
// `l = 0`. A dimension binder contributes nothing to the universe level,
// which is the formation rule CCHM gives `PathP`.
//
// The DISCRIMINATING codomain is not a written sort. A codomain `Prop`
// has type `Sort 1` and contributes 1, so `I -> Prop` infers `Sort 1`
// under both the fixed and the unfixed rule and cannot tell them apart
// (the two pins further down hold that line instead). A def `A : Prop`
// contributes 0 -- its type IS `Sort 0` -- which is what makes
// `Π(i : I) A` the pin that can fail. That needs a def in the scope, so
// these pins cannot run against the builtins-only `proof_scope` the
// harness's `infers_sort_at` uses, and build the same two-declaration
// scope `lang/src/tests`'s cubical pins are built from instead.

def interval_kind_path : ModulePath :=
    ModulePath.mp (List.cons (Identifier.id "proofs_sort_interval") List.empty)

def interval_kind_source : String :=
    String.concat "#[cubical \"interval\"] def I : Type\n"
    "def A : Prop\n"

/// A parse failure yields an empty scope, which makes every pin below
/// fail rather than silently pass against a scope with nothing bound.
def interval_kind_scope : Scope :=
    let sd : ScopeData :=
        match try_parse_decls interval_kind_source {
            Option.some decl_list => build_scope_from_decls interval_kind_path decl_list,
            Option.none => build_scope_from_decls interval_kind_path List.empty,
        } in
    {
        module_id := interval_kind_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

/// A free (global) reference by name -- the same helper idiom
/// `lang/src/tests`'s whnf tests use.
def kind_var (nm : String) : Term := Term.var sentinel (DebugName.named (Identifier.id nm))

/// `inferred_sort_level` above, against `interval_kind_scope` instead of
/// `proof_scope` -- the universe rule under test needs a def in the
/// scope, which `proof_scope` cannot hold. Nothing else differs, and
/// the folding through `level_const` is copied for the same reason its
/// own doc comment gives: the Pi arm answers a `max`, not a `concrete`.
def inferred_sort_level_in_kind_scope (term : Term) : Option I64 :=
    match type_check term Term.hole interval_kind_scope empty_local_types empty_locals {
        ok tt =>
            match tt.typ {
                Term.sort level => level_const level,
                _ => Option.none,
            },
        err _ => Option.none,
    }

/// Does the checker infer `term`'s type in `interval_kind_scope` to be
/// the sort at concrete level `n`?
def infers_sort_at_in_kind_scope (term : Term) (n : I64) : Bool :=
    match inferred_sort_level_in_kind_scope term {
        Option.some m => I64.beq m n,
        Option.none => false,
    }

/// THE pin: a Prop-valued family over the interval stays in `Prop`. This
/// is the one that fails when the bare-interval arm is removed -- it
/// infers `Sort 1` and with it every `Prop`-valued path family.
#[test]
def pi_over_the_interval_and_a_prop_variable_stays_in_prop : Bool :=
    infers_sort_at_in_kind_scope (Term.pi binder_anon cub_interval (kind_var "A")) 0

/// The same domain by bare NAME reference -- the shape a SOURCE
/// `(i : I) -> A` lowers to, where the domain only becomes the cubical
/// term inside `type_check` itself (the Stage 1 step 3 rewrite). Pinned
/// separately because probing the raw domain instead of the checked one
/// would pass every hand-built pin above and silently miss the route
/// actual source takes.
#[test]
def pi_over_the_interval_by_reference_stays_in_prop : Bool :=
    infers_sort_at_in_kind_scope (Term.pi binder_anon (kind_var "I") (kind_var "A")) 0

/// The codomain's written `Prop` contributes 1 (`Prop : Type`), so even
/// with the domain contributing 0 the Pi stays at 1 -- the pin that says
/// the interval arm did not quietly zero every Pi it touches.
#[test]
def pi_over_the_interval_and_a_written_prop_stays_at_1 : Bool :=
    infers_sort_at_in_kind_scope (Term.pi binder_anon cub_interval (Term.sort (SortLevel.concrete 0))) 1

/// The control on the OTHER side: a written `Prop` domain contributes 1
/// even against a 0-contributing codomain, so the 0 above is the
/// interval's alone and not something any small codomain drags in.
#[test]
def pi_over_prop_and_a_prop_variable_stays_at_1 : Bool :=
    infers_sort_at_in_kind_scope (Term.pi binder_anon (Term.sort (SortLevel.concrete 0)) (kind_var "A")) 1

/// Interval-VALUED is not the interval: a dimension in domain position
/// keeps the ordinary `level_of_type` answer (its type is `I`, not a
/// sort, so the default 1), which is the arm testing bare-interval-ness
/// rather than interval-typedness.
#[test]
def pi_over_a_dimension_stays_at_1 : Bool :=
    infers_sort_at_in_kind_scope (Term.pi binder_anon (cub CubicalPrim.i0 List.empty) (kind_var "A")) 1
