// Equivalence and contractibility (univalence.md Stage 6a).
//
// Ordinary library defs -- no new `CubicalPrim` tag -- because the standard
// HoTT statements are pure `Sigma`/`Pi`/`Path` compositions and none of them
// ever unfolds `Path`'s own body; only its signature is needed. `Path`
// itself carries the body `Cubical.PathP (fn _ => A) a b`.
//
// Universe-polymorphic like `Sigma`: each def takes its own level(s), so the
// same statements serve `Prop`- and `Type`-level carriers. `#[proof]` on each
// because `init` is compiler-source surface and the Rust host cannot type a
// cubical `Path`; the attribute is what makes the host skip the body, exactly
// as `proofs/`'s declaration-only host policy does for that mote. The
// self-hosted checker still checks every body.

#[proof]
pub def Path {u : Universe} (A : Sort u) (a : A) (b : A) : Sort u :=
    Cubical.PathP (fn _ => A) a b

/// A proof is `Copy`: a path never reaches run time (the compiled form of a
/// `Path` is erased -- there is nothing to own), so sharing one costs nothing
/// and two uses cannot double-free. Without it the affine rule rejects the
/// ordinary cubical proofs that mention the same path twice -- a contraction's
/// `pair_path p (fn i j => p (ijoin i j))`, a `path_pair` whose two components
/// depend on the same path.
///
/// It is a LIBRARY instance rather than a kernel rule about `Path`, for the
/// same reason `Copy Cubical.I` is: `Copy` is an ordinary class, and a proof
/// type is whatever the library says it is. Note this licenses duplicating a
/// PROOF, not the data a proof is about (`b : A` in `Sigma.dpair b (refl b)` is
/// still affine unless `A` has its own instance).
pub instance {u : Universe} {A : Sort u} {a : A} {b : A} Copy (Path A a b) {
    def copy (p : Path A a b) : Pair (Path A a b) (Path A a b) := Pair.pair p p
}

/// `isContr A` -- a point of `A` with every point equal to it.
#[proof]
pub def isContr {u : Universe} (A : Sort u) : Sort u :=
    Sigma A (fn center => ((x : A) -> Path A x center))

/// The homotopy fiber of `f` over `b`: a preimage together with a path from
/// its image to `b`.
#[proof]
pub def fiber {u : Universe} {v : Universe} (A : Sort u) (B : Sort v)
    (f : A -> B) (b : B) : Sort (max u v) :=
    Sigma A (fn a => Path B (f a) b)

/// `isEquiv f` -- every fiber is contractible.
#[proof]
pub def isEquiv {u : Universe} {v : Universe} (A : Sort u) (B : Sort v)
    (f : A -> B) : Sort (max u v) :=
    (b : B) -> isContr (fiber A B f b)

/// An equivalence is a map with a proof that it is one.
#[proof]
pub def Equiv {u : Universe} {v : Universe} (A : Sort u) (B : Sort v) : Sort (max u v) :=
    Sigma (A -> B) (fn f => isEquiv A B f)
