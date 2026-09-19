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
//   - `DebugName` is not `pub`, so no pin here builds a lambda or a
//     binder -- sort and leaf-rule pins only.
//   - `Similar` (a class) is not `pub`, so no pin inspects an inferred
//     type directly; where a rule must be observed, the pin asserts
//     through a `check` that only succeeds at the right answer.
// None of these is a reason to widen `lang`'s exports yet. If a pin
// genuinely needs one, widen it deliberately, one name at a time.

use lang::scope {build_scope_from_decls}
use lang::typecheck::infer {empty_local_types, empty_locals, type_check}
use lang::types {ModulePath, Scope, ScopeData, Term}

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
