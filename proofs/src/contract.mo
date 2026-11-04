// Contractibility of the identity's fibers, and `idEquiv` (univalence.md S2).
//
// This module exists because it needs BOTH halves: `Path`/`refl`/`path_pair`
// (`paths.mo`) and `fiber`/`isContr`/`Equiv` (`equiv.mo`) -- and `equiv.mo`
// cannot import `paths.mo`, because `paths.mo` imports `equiv.mo` for `Path`.
//
// Two checker rules had to land for this to check at all (measured 2026-11-04/05):
//
//   - The dependent-match gate now reduces the scrutinee type before reading
//     its spine. A `match` on `x : fiber A A (fn x => x) b` -- a DEF-spelled
//     type -- used to flatten to four spine args while `Sigma` declares two, so
//     the refinement declined and the contraction's `PathP` family never got
//     solved.
//   - A `#[proof]` def's body may use any binder freely: its result is erased,
//     so the center's `Sigma.dpair b (refl b)` duplicates `b : A` for free.
//     No `Copy` instance can license that for a type variable `A`.
use proofs::equiv {Equiv, Path, fiber, isContr}
use proofs::paths {refl, path_pair}

/// One contraction step: `pair_path` with the dependent family written out.
///
/// The declared type spells `Sigma A (fn a => Path A a b)` rather than
/// `fiber A A (fn x => x) b` on purpose. With the def-unfolding in the expected
/// type, `path_pair`'s implicit `B` is solved to the identity instead of
/// `fn a => Path A a b` (measured 2026-11-05); the two types are convertible,
/// so callers still pass `fiber ...` values.
pub def fiber_step {A : Type} (b : A) (a : A) (p : Path A a b) :
    Path (Sigma A (fn a => Path A a b)) (Sigma.dpair a p) (Sigma.dpair b (refl b)) :=
    path_pair p (fn (i : Cubical.I) => fn (j : Cubical.I) => p (Cubical.ijoin i j))

/// The fiber of the identity over `b` is contractible: center `(b, refl b)`.
#[proof]
pub def fiber_id_contr {A : Type} (b : A) : isContr (fiber A A (fn x => x) b) :=
    Sigma.dpair (Sigma.dpair b (refl b))
        (fn (x : fiber A A (fn x => x) b) =>
            match x { Sigma.dpair a p => fiber_step b a p })

/// The identity map is an equivalence -- what `eqToEquiv` transports along
/// (`univalence.md` Stage 6c).
pub def idEquiv {A : Type} : Equiv A A :=
    Sigma.dpair (fn x => x) (fn b => fiber_id_contr b)
