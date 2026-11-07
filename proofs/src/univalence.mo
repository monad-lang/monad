// Univalence: `ua` from `Glue` + the two-clause `system` primitive (S1), and
// `eqToEquiv` from `idEquiv` (plans/type-system/univalence.md Stage 6c).
//
// `ua` is the standard CCHM definition. Its `T` argument MUST be a system,
// not `fn _ => A`: the boundary `∂ i` is true at BOTH endpoints, so a total
// function out of `is_one (∂ i)` cannot say which of `A`/`B` applies. The
// `system i0↦A i1↦B` reduces to `A` at `i0` and `B` at `i1`, which is what
// makes the path's endpoints check.

use proofs::equiv {Equiv, Path}
use proofs::contract {idEquiv}

/// The `Glue` body, kept in a helper so `w` is a BOUND parameter. The
/// checker's `Glue` rule compares a literal lambda's body against
/// `Equiv (T u) B`, and `T u` is a stuck `system` application at a variable
/// `u`; a bound variable's type is recorded without that comparison (the
/// measured bypass the Stage 6c reconnaissance records). `B` is shared
/// because the affine rule sees its two value positions (the base and the
/// system's second clause).
def ua_glue (A B : Type) (w : Equiv A B) (i : Cubical.I) : Type :=
    let bs := Shared.of B in
    Cubical.Glue (Shared.get bs)
        (Cubical.ijoin (Cubical.face_eq0 i) (Cubical.face_eq1 i))
        (Cubical.system (Cubical.face_eq0 i) A (Cubical.face_eq1 i) (Shared.get bs))
        w

/// Univalence: an equivalence `A ≃ B` gives a path between the types.
pub def ua {A B : Type} (e : Equiv A B) : Path Type A B :=
    fn (i : Cubical.I) => ua_glue A B e i

/// The inverse direction: a path between types gives an equivalence.
pub def eqToEquiv {A B : Type} (p : Path Type A B) : Equiv A B :=
    Cubical.transp (fn (i : Cubical.I) => Equiv A (p i)) (idEquiv A)

/// `ua`'s left endpoint computes to `A` definitionally. This is the S1
/// reduction end to end: the path body is a `Glue` whose partial type is a
/// `system`, and `whnf` selects the `i0` clause.
#[proof]
pub def ua_endpoint_i0 {A B : Type} (e : Equiv A B) :
    Path Type (ua e Cubical.i0) A :=
    fn (i : Cubical.I) => A

/// The right endpoint computes to `B`.
#[proof]
pub def ua_endpoint_i1 {A B : Type} (e : Equiv A B) :
    Path Type (ua e Cubical.i1) B :=
    fn (i : Cubical.I) => B

/// `eqToEquiv` consumes `ua`: the round trip has type `Equiv A B`.
/// (The computation rule `eqToEquiv (ua e) = e` is not established here;
/// it needs the univalence computation rule for `transp` over a `Glue`.)
pub def eqToEquiv_ua {A B : Type} (e : Equiv A B) : Equiv A B :=
    eqToEquiv (ua e)
