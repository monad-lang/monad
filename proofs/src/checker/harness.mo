// The checker self-verification harness.
//
// TERM-LEVEL, on purpose. `accepted`/`rejected` take hand-built `Term`s
// and run `type_check` on them directly, so a pin names exactly the one
// rule it tests. The more legible source-level form ("does this snippet
// typecheck?") is a strictly weaker instrument for a LEAF rule: `Sort 1`
// in source lowers to an application of the `Sort` global and is checked
// by `type_check_app`, so a source-level pin for the sort-universe rule
// passes on both the fixed and the broken checker. A source-level
// harness lands alongside this one for the pins that genuinely are
// whole-module properties.
//
// NO NEW EXPORTS FROM `lang`. Everything used here is already `pub`:
// `type_check` (lang/src/typecheck/infer.mo), `empty_local_types` and
// `empty_locals` (same file), `build_scope_from_decls` (lang/src/scope.mo),
// and `Scope`/`ScopeData`/`Term`/`ModulePath`/`Identifier`
// (lang/src/types.mo). Keeping that surface at zero is a constraint of
// this mote rather than a happy accident -- `lang`'s own test files reach
// the same internals through the intra-mote `lib::` path, which a
// separate mote cannot use.
//
// What this harness therefore CANNOT reach, and the pins it implies:
//   - `TypeError` (lang/src/types.mo) is not `pub`, so pins assert
//     accept/reject, never a specific error variant.
//   - `DebugName` was not `pub` at first, which is why the earliest pins
//     built no binder at all. It was widened deliberately (W1.2) so the
//     `Forall` universe arm could be pinned: `type_check_pi` and
//     `type_check_forall` are separate arms, and a `max` added to one and
//     not the other is precisely the half-fix a pin has to catch.
//   - `level_const` was the second widening (W1.4), and the reason is the
//     same shape of argument: a sort's level is often a COMPUTED `max`, so
//     a reader that matches only the concrete shape answers "not a sort"
//     for exactly the `Pi`/`Forall` universes this harness exists to pin.
//     Folding through `level_const` is what makes those pins mean anything.
//     Two exports widened so far, each forced by one pin that cannot be
//     written otherwise.
//   - `Similar` (a class) is not `pub`, so no pin compares two arbitrary
//     inferred types. What a pin CAN do is read a concrete sort level out
//     of an inferred type (`inferred_sort_level`, pattern-matching the
//     `pub` `Term` constructors); where a rule cannot be observed that
//     way, the pin asserts through a `check` that only succeeds at the
//     right answer.
// None of these is a reason to widen `lang`'s exports yet. If a pin
// genuinely needs one, widen it deliberately, one name at a time.

use lang::scope {build_scope_from_decls}
use lang::typecheck::infer {empty_local_types, empty_locals, type_check}
use lang::types {ModulePath, Scope, ScopeData, Term, level_const}

// A scope with the builtins only (`add_builtins` registers `Type`,
// `Prop`, `Sort`, `Pred`), which is all a leaf-rule pin needs: none of
// them refers to a user inductive.
//
// Built through `build_scope_from_decls` rather than with a hand-written
// `ScopeData`, and bound to its own def rather than inlined into the
// record literal -- the same shape `lang`'s own test scopes use.
def proof_synthetic_path : ModulePath :=
    ModulePath.mp (List.cons (Identifier.id "proofs_synthetic") List.empty)

def proof_scope_data : ScopeData := build_scope_from_decls proof_synthetic_path List.empty

def proof_scope : Scope := {
    module_id := proof_synthetic_path,
    scope := proof_scope_data,
    parent := Option.none,
}

/// Does `term` typecheck against `expected_type`, per the checker's own
/// `type_check`? `expected_type` is the TYPE the term is checked
/// against, so `accepted (Term.type_ 0) (Term.type_ 1)` asks
/// "`Prop : Type`?" and `rejected (Term.type_ 1) (Term.type_ 1)` asks
/// "is `Type : Type`?" (no).
def accepted (term : Term) (expected_type : Term) : Bool :=
    match type_check term expected_type proof_scope empty_local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

/// The negation of `accepted`, named for what a pin usually means: the
/// checker must REFUSE this.
def rejected (term : Term) (expected_type : Term) : Bool := not (accepted term expected_type)

/// The concrete sort level the checker INFERS for `term`, or `Option.none`
/// when it infers something that is not a concrete sort (including an
/// error, and including a level that is not a literal -- a `Term.sort`
/// whose level is a variable has no `I64` to report, and `level_const` is
/// not `pub` here to ask more precisely).
///
/// This exists because `accepted` structurally cannot see a `Pi`'s or a
/// `Forall`'s universe: `type_check`'s `Term.pi`/`Term.forall` arms ignore
/// the expectation and answer the universe they computed, so EVERY
/// expectation is accepted for a well-formed Pi and an accept/reject pin
/// over one cannot discriminate at all. Reading the inferred type is the
/// only observable route, and the `Term` constructors are `pub`, so no new
/// export is needed for it.
def inferred_sort_level (term : Term) : Option I64 :=
    match type_check term Term.hole proof_scope empty_local_types empty_locals {
        ok tt => match tt.typ {
            Term.type_ n => Option.some n,
            _ => Option.none,
        },
        err _ => Option.none,
    }

/// Does the checker infer `term`'s type to be the sort at concrete level
/// `n`? The readable form of `inferred_sort_level` for a pin.
def infers_sort_at (term : Term) (n : I64) : Bool :=
    match inferred_sort_level term {
        Option.some m => I64.beq m n,
        Option.none => false,
    }
