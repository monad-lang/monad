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
// One surface requirement is load-bearing today: the type function must be an
// EXPLICIT parameter (`(F : Bool -> Type)`, `(E : Nat -> Nat -> Type)`). An
// IMPLICIT higher-kinded parameter is skolemized as `Sort 0` during
// elaboration, so applying it is untyped and the motive fails the "function
// into a sort" check. Qualified constructor spellings (`Bool.true`,
// `Nat.succ`) now work: the Elim minor comparison normalizes them (and the
// checker's `Term.con` form) to the free-var application a derived motive
// builds.
//
// Measured limits on what is NOT yet writable (2026-11-01):
//
// * `Sigma.snd` (`B (Sigma.fst p)`) needs the constructor's own field type
//   `snd : B fst` substituted with the earlier field binding. The checker
//   leaves that `fst` as a free name -- the field-dependent gap
//   `implementations/field-pattern-type-args-not-substituted.md` records for
//   `Vec` -- so the minor's inferred type disagrees with the refined motive.
// * Recursive induction (`s k (rec k)`) uses the predecessor twice; `Nat` is
//   not `Copy`, so the always-on affine rule rejects it (proofs/ has no
//   `[affine]` exception).
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
pub def bool_elim (F : Bool -> Type) (t : F Bool.true) (f : F Bool.false) (b : Bool) : F b :=
    match b {
        Bool.true => t,
        Bool.false => f,
    }

/// A case split over `Nat` into an arbitrary two-place type family, with the
/// constructor references spelled QUALIFIED (`Nat.zero`, `Nat.succ`) as an
/// ordinary body is. The motive supplies the bare resolved spelling, so this
/// only checks once the rule canonicalizes constructor references.
pub def nat_case_refl (E : Nat -> Nat -> Type) (reflf : (x : Nat) -> E x x) (n : Nat) : E n n :=
    match n {
        Nat.zero => reflf Nat.zero,
        Nat.succ k => reflf (Nat.succ k),
    }

// ─── Presence pin (the def above is the deliverable) ────────────────────

/// The module loads and its theorems are checked even though no test can
/// instantiate their type arguments.
#[test]
def test_dependent_elim_theorems_load : Bool := true
