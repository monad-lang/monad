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
// * A FIELD-PATTERN arm (`{ fst, snd } => snd`) stays on the non-dependent
//   path: the dependent fallback uses the RAW cases, and only
//   `type_check_field_pattern_case` resolves those (see
//   `dependent_match_gate_ok`).
// * Recursive induction (`s k (rec k)`) uses the predecessor twice; `Nat` is
//   not `Copy`, so the always-on affine rule rejects it (proofs/ has no
//   `[affine]` exception).
// * A type-level IF/MATCH used directly as a result type has no kind the
//   checker can report, so the motive-sort check fails. A local type function
//   avoids that.
//
// These theorems are VERIFIED by the checker. They can also be CALLED now
// when the type argument is EXPLICIT (`sigma_snd I64 (fn (a : I64) => I64)
// (Sigma.dpair 1 2)`): a type NAME in value position compiles to an inert
// sort value in both backends. See `dependent_runtime.mo` for the
// compile-and-run tier. Still missing: IMPLICIT type arguments (higher-order
// inference is not implemented) and a type application used as a value.

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

/// `Sigma.snd`, the second projection -- the shape `plans/type-system/
/// sigma-types.md` names as the dependent-elimination target. `dpair`'s
/// second field is DECLARED in terms of the first (`snd : B fst`), so the
/// arm's `b` is typed `B a`; the refined motive puts `Sigma.fst (dpair a b)`
/// in the result type, and delta + iota reduce that to `a`.
pub def sigma_snd (A : Type) (B : A -> Type) (p : Sigma A B) : B (Sigma.fst p) :=
    match p {
        Sigma.dpair a b => b,
    }

/// A case split over `Sigma` into an arbitrary family: the arm receives the
/// constructor under the refinement, and the result is `C p`.
pub def sigma_case (A : Type) (B : A -> Type) (C : (p : Sigma A B) -> Type)
    (f : (a : A) -> (b : B a) -> C (Sigma.dpair a b))
    (p : Sigma A B) : C p :=
    match p {
        Sigma.dpair a b => f a b,
    }

// ─── Presence pin (the defs above are the deliverable) ──────────────────

/// The module loads and its theorems are checked even though no test can
/// instantiate their type arguments.
#[test]
def test_dependent_elim_theorems_load : Bool := true
