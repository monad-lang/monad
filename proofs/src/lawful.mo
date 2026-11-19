// `LawfulMonad`: a class whose instances must PROVE the three monad laws.
//
// The class lives in `proofs/` because the laws are `Path` equalities and
// `init/` may not import `proofs/`. Its result sort is `Prop` (the class-head
// Sort clause): the laws are propositions.
//
// The operations are EXPLICIT class parameters, and their type arguments are
// EXPLICIT Pi binders. Both are forced by measurement:
//
//   * the self-hosted checker does not reduce a class-METHOD call in a type,
//     so `Path (Id B) (Monad.bind (Monad.pure a) f) (f a)` can never convert
//     to `Path (Id B) (f a) (f a)` and its law is unprovable;
//   * an implicit binder inside a class parameter's type (`bind : {A : Type}
//     -> ...`) is not parseable (the class head fails to parse), so the
//     operations take `(A : Type)` explicitly.
//
// Right identity and associativity case-split on `Id`'s single constructor.
// A direct `match m { … }` checks the arm body against a derived motive the
// checker leaves unreduced (`Id.bind … (id a) …` never converts), so the
// proofs go through an EXPLICIT eliminator with a named family -- the same
// recipe `proofs/src/nat.mo` documents.
use proofs::equiv {Path}
use proofs::paths {refl, ap}
use proofs::list {list_elim}

/// A monad whose operations satisfy the three laws. `bind`/`pure` are the
/// instance's own operations, passed explicitly.
pub class [Monad M] LawfulMonad (M : Type -> Type)
    (bind : (A : Type) -> (B : Type) -> (a : M A) -> (f : A -> M B) -> M B)
    (pure : (A : Type) -> (a : A) -> M A) : Prop {
    /// `bind (pure a) f = f a`.
    def left_identity (a : A) (f : A -> M B) :
        Path (M B) (bind A B (pure A a) f) (f a)

    /// `bind m pure = m`.
    def right_identity (m : M A) :
        Path (M A) (bind A A m (pure A)) m

    /// `bind (bind m f) g = bind m (fn x => bind (f x) g)`.
    def associative (m : M A) (f : A -> M B) (g : B -> M C) :
        Path (M C) (bind B C (bind A B m f) g)
            (bind A C m (fn x => bind B C (f x) g))
}

/// The identity monad's `pure`, as a named def so the laws can reduce it.
pub def Id.pure (A : Type) (a : A) : Id A := Id.id a

/// The identity monad's `bind`, as a named def so the laws can reduce it.
pub def Id.bind (A : Type) (B : Type) (m : Id A) (f : A -> Id B) : Id B :=
    match m { Id.id a => f a }

/// `Id`'s explicit eliminator: an arbitrary family over `Id A`, supplied by
/// its value at the single constructor. Mirrors `nat_elim`/`list_elim`.
pub def Id.elim {A : Type} (P : Id A -> Type) (h : (a : A) -> P (Id.id a))
    (m : Id A) : P m :=
    match m { Id.id a => h a }

/// The right-identity family (`#[proof]`: it mentions `m` twice).
#[proof]
pub def Id.right_fam {A : Type} (m : Id A) : Type :=
    Path (Id A) (Id.bind A A m (Id.pure A)) m

/// The associativity family (`#[proof]`: it mentions `m`/`g` twice).
#[proof]
pub def Id.assoc_fam {A B C : Type} (f : A -> Id B) (g : B -> Id C) (m : Id A) : Type :=
    Path (Id C) (Id.bind B C (Id.bind A B m f) g)
        (Id.bind A C m (fn x => Id.bind B C (f x) g))

/// Associativity for `Id`, through the eliminator. `#[proof]` licenses
/// reading `f`/`g` twice (family + step).
#[proof]
pub def Id.assoc {A B C : Type} (m : Id A) (f : A -> Id B) (g : B -> Id C) :
    Path (Id C) (Id.bind B C (Id.bind A B m f) g)
        (Id.bind A C m (fn x => Id.bind B C (f x) g)) :=
    Id.elim (Id.assoc_fam f g) (fn a => refl (Id.bind B C (f a) g)) m

/// `Id` is a lawful monad for its own `bind`/`pure`. The instance's method
/// bodies are the checked proofs (the self-hosted checker verifies them).
pub instance LawfulMonad Id Id.bind Id.pure {
    /// `bind (pure a) f` reduces to `f a`.
    def left_identity (a : A) (f : A -> Id B) :
        Path (Id B) (Id.bind A B (Id.pure A a) f) (f a) :=
        refl (f a)

    /// Match the single constructor; both sides reduce to `id a`.
    def right_identity (m : Id A) :
        Path (Id A) (Id.bind A A m (Id.pure A)) m :=
        Id.elim Id.right_fam (fn a => refl (Id.id a)) m

    /// Match the single constructor; both sides reduce to `bind (f a) g`.
    /// The proof is `Id.assoc`: conversion does not see through a
    /// `let fs := Shared.of f`, so the family must name `f`/`g` directly.
    def associative (m : Id A) (f : A -> Id B) (g : B -> Id C) :
        Path (Id C) (Id.bind B C (Id.bind A B m f) g)
            (Id.bind A C m (fn x => Id.bind B C (f x) g)) :=
        Id.assoc m f g
}

/// `Option`'s `pure` with an explicit type argument, the shape the class's
/// operation parameter takes.
pub def option_pure (A : Type) (a : A) : Option A := Option.some a

/// `Option`'s `bind` with explicit type arguments.
pub def option_bind (A : Type) (B : Type) (m : Option A) (f : A -> Option B) : Option B :=
    match m {
        Option.some a => f a,
        Option.none => Option.none,
    }

/// `Option`'s explicit eliminator.
pub def Option.elim {A : Type} (P : Option A -> Type) (hs : (a : A) -> P (Option.some a))
    (hn : P Option.none) (m : Option A) : P m :=
    match m {
        Option.some a => hs a,
        Option.none => hn,
    }

#[proof]
pub def option_right_fam {A : Type} (m : Option A) : Type :=
    Path (Option A) (option_bind A A m (option_pure A)) m

#[proof]
pub def option_assoc_fam {A B C : Type} (f : A -> Option B) (g : B -> Option C) (m : Option A) : Type :=
    Path (Option C) (option_bind B C (option_bind A B m f) g)
        (option_bind A C m (fn x => option_bind B C (f x) g))

#[proof]
pub def option_assoc {A B C : Type} (m : Option A) (f : A -> Option B) (g : B -> Option C) :
    Path (Option C) (option_bind B C (option_bind A B m f) g)
        (option_bind A C m (fn x => option_bind B C (f x) g)) :=
    Option.elim (option_assoc_fam f g) (fn a => refl (option_bind B C (f a) g))
        (refl Option.none) m

/// `Option` is a lawful monad. Each law splits on the constructor; `none`
/// short-circuits both sides to `none`.
pub instance LawfulMonad Option option_bind option_pure {
    def left_identity (a : A) (f : A -> Option B) :
        Path (Option B) (option_bind A B (option_pure A a) f) (f a) :=
        refl (f a)

    def right_identity (m : Option A) :
        Path (Option A) (option_bind A A m (option_pure A)) m :=
        Option.elim option_right_fam (fn a => refl (Option.some a)) (refl Option.none) m

    def associative (m : Option A) (f : A -> Option B) (g : B -> Option C) :
        Path (Option C) (option_bind B C (option_bind A B m f) g)
            (option_bind A C m (fn x => option_bind B C (f x) g)) :=
        option_assoc m f g
}

/// `List`'s `pure` with an explicit type argument.
pub def list_pure (A : Type) (a : A) : List A := List.cons a List.empty

/// `List`'s `bind` with explicit type arguments (`List.flat_map`'s body).
pub def list_bind (A : Type) (B : Type) (m : List A) (f : A -> List B) : List B :=
    match m {
        List.empty => List.empty,
        List.cons x t => List.append (f x) (list_bind A B t f),
    }

/// `xs ++ bind [] f = xs`: `append_nil` with the tail left as `bind [] f`.
#[proof]
pub def list_left_fam {A B : Type} (f : A -> List B) (xs : List B) : Type :=
    Path (List B) (List.append xs (list_bind A B List.empty f)) xs

/// Left identity for `List`: `bind [a] f = f a ++ bind [] f`, which is `f a`
/// by induction on `f a`. Stated through `list_left_fam` rather than
/// `append_nil (f a)`: conversion does not see `f a ++ bind [] f` and
/// `f a ++ []` as equal, because `whnf` unfolds `List.append` to a match
/// stuck on `f a` and the stuck arms are then compared without reduction (a
/// known conversion limitation; `plans/type-system/std-monad-instances-and-laws.md`).
#[proof]
pub def list_left_identity {A B : Type} (a : A) (f : A -> List B) :
    Path (List B) (list_bind A B (list_pure A a) f) (f a) :=
    list_elim (list_left_fam f) (refl List.empty)
        (fn x t ih => ap (fn tl => List.cons x tl) ih) (f a)

#[proof]
pub def list_right_fam {A : Type} (m : List A) : Type :=
    Path (List A) (list_bind A A m (list_pure A)) m

/// Right identity for `List`, by induction: `bind (x :: t) pure` reduces to
/// `x :: bind t pure`.
#[proof]
pub def list_right_identity {A : Type} (m : List A) :
    Path (List A) (list_bind A A m (list_pure A)) m :=
    list_elim list_right_fam (refl List.empty)
        (fn x t ih => ap (fn tl => List.cons x tl) ih) m

// No `LawfulMonad List` instance yet: associativity needs
// `bind g (xs ++ ys) = bind g xs ++ bind g ys` and `append_assoc` chained in
// one step, i.e. path composition (`trans`), which `proofs/` does not have
// (univalence plan, comp/trans/J).
