// Equivalence and contractibility (univalence.md Stage 6a).
//
// All five are ordinary library defs -- no new `CubicalPrim` tag -- because
// the standard HoTT statements are pure `Sigma`/`Pi`/`Path` compositions and
// none of them ever unfolds `Path`'s own body; only its signature is needed.
// `Path` itself carries the body `Cubical.PathP (fn _ => A) a b`, which is
// what `type_check_bound_var`'s depth shift (PR #129) unblocked.

pub def Path (A : Type) (a : A) (b : A) : Type :=
    Cubical.PathP (fn _ => A) a b

/// `isContr A` -- a point of `A` with every point equal to it.
pub def isContr (A : Type) : Type :=
    Sigma A (fn center => ((x : A) -> Path A x center))

/// The homotopy fiber of `f` over `b`: a preimage together with a path from
/// its image to `b`.
pub def fiber (A : Type) (B : Type) (f : A -> B) (b : B) : Type :=
    Sigma A (fn a => Path B (f a) b)

/// `isEquiv f` -- every fiber is contractible.
pub def isEquiv (A : Type) (B : Type) (f : A -> B) : Type :=
    (b : B) -> isContr (fiber A B f b)

/// An equivalence is a map with a proof that it is one.
pub def Equiv (A : Type) (B : Type) : Type :=
    Sigma (A -> B) (fn f => isEquiv A B f)
