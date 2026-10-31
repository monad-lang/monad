// Dependent-elimination theorems that are WRITABLE now that `match` elaborates
// to an `Elim` with a derived motive (`core-term-simplification.md` R3c).
//
// These are the end-to-end proof that a source `match` reaches
// `type_check_elim`: each result type is a TYPE-LEVEL function of the
// scrutinee (`F b`, `E n n`), so the legacy non-dependent rule rejects the
// arms (their types differ per constructor) and only the dependent rule
// accepts them by refining the scrutinee. A swapped arm is REJECTED (measured:
// `error: type mismatch: expected ((fn (_ : Bool) => F b) true), found (F
// false)`), so the rule is not vacuous.
//
// Two surface requirements are load-bearing today:
//
// * The type function is an EXPLICIT parameter (`(F : Bool -> Type)`). An
//   IMPLICIT higher-kinded parameter is skolemized as `Sort 0` during
//   elaboration, so applying it is untyped and the motive fails the "function
//   into a sort" check.
// * Constructor arguments inside those parameter types are spelled BARE
//   (`F true`, `E x x`'s `reflf zero`), not `Bool.true`/`Nat.zero`: the motive
//   applies the RESOLVED constructor's own bare name, and the checker's
//   unification compares constructor references by spelling.
//
// Measured limits on what is NOT yet writable (2026-10-31):
//
// * `Sigma.snd` (`B (Sigma.fst p)`) needs the constructor's own field type
//   `snd : B fst` substituted with the earlier field binding. The checker
//   leaves that `fst` as a free name -- the field-dependent gap
//   `implementations/field-pattern-type-args-not-substituted.md` records for
//   `Vec` -- so the minor's inferred type disagrees with the refined motive.
// * Recursive induction (`s k (rec k)`) uses the predecessor twice; `Nat` is
//   not `Copy`, so the always-on affine rule rejects it (proofs/ has no
//   `[affine]` exception).
// * A constructor referenced in an arm BODY is qualified by `qualify_modules`
//   (`Nat.succ`), while a derived motive applies the resolved constructor's
//   bare name (`succ`); the two do not unify. `bool_elim` sidesteps this
//   because its constructor references sit in the SIGNATURE's parameter types,
//   which qualification does not rewrite. A `Nat` case split into an equality
//   family hits it in its arms.
// * A type-level IF/MATCH used directly as a result type has no kind the
//   checker can report, so the motive-sort check fails. A local type function
//   avoids that.
//
// Nothing here executes the eliminator: its type argument cannot be supplied
// with the surface syntax (implicit arguments are inferred, and higher-order
// inference is not implemented). The theorems are VERIFIED by the checker,
// which is the property this step delivers.

/// The proof-relevant eliminator for `Bool` into an arbitrary type family:
/// the `true` arm has type `F true`, the `false` arm `F false`, and the result
/// is `F b`.
pub def bool_elim (F : Bool -> Type) (t : F true) (f : F false) (b : Bool) : F b :=
    match b {
        Bool.true => t,
        Bool.false => f,
    }

// ─── Presence pin (the def above is the deliverable) ────────────────────

/// The module loads and its theorems are checked even though no test can
/// instantiate their type arguments.
#[test]
def test_dependent_elim_theorems_load : Bool := true
