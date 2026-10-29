/// Optics: Lenses, Prisms, and combinators
/// Structural encoding — lenses as getter+setter pairs, prisms as match+construct.

// --- Lens ---

/// A lens focuses on a part A within a whole S.
pub type Lens S A {
    mkLens (view : S -> A) (set : A -> S -> S)
}

/// Create a lens from explicit getter and setter functions.
def lens (get : S -> A) (put : A -> S -> S) : Lens S A :=
    Lens.mkLens get put

/// Extract the focused value from a structure.
pub def view (ln : Lens S A) (s : S) : A :=
    match ln { mkLens v _ => v s }

/// Replace the focused value within a structure.
pub def set (ln : Lens S A) (a : A) (s : S) : S :=
    match ln { mkLens _ st => st a s }

/// Modify the focused value within a structure.
///
/// `[Copy S]` because a lens reads the focus AND rebuilds the whole, so the
/// structure is mentioned twice. That is a real second ownership need, not
/// a borrow: the rebuilt value is a new `S`. (Reaching for `[Copy S]` is
/// honest where `Copy (Lens S A)` would not be — a lens is a pair of
/// closures, and function values are deliberately never `Copy`.)
pub def over [Copy S] (ln : Lens S A) (g : A -> A) (s : S) : S :=
    // `s` is used twice because a lens reads the focus and rebuilds the
    // whole; `[Copy S]` is the declared permission for that duplication
    // (and the affine rule reads it). The checker does not yet ENFORCE a
    // def-level constraint at call sites -- a language-wide gap tracked in
    // `plans/type-system/quantitative-types.md` -- so a caller with no
    // `Copy S` instance is accepted today.
    match ln { mkLens v st => st (g (v s)) s }

// --- Prism ---

/// A prism focuses on one variant of a sum type.
type Prism S A {
    mkPrism (preview : S -> Option A) (review : A -> S)
}

/// Try to extract a value through a prism (may fail).
def preview (p : Prism S A) (s : S) : Option A :=
    match p { mkPrism prev _ => prev s }

/// Construct a value through a prism.
def review (p : Prism S A) (a : A) : S :=
    match p { mkPrism _ rev => rev a }

/// Modify a value through a prism (no-op if prism doesn't match).
def over_prism [Copy S] (p : Prism S A) (g : A -> A) (s : S) : S :=
    match p {
        mkPrism prev rev =>
            match prev s {
                none => s,
                some a => rev (g a)
            }
    }

/// Set a value through a prism (no-op if prism doesn't match).
def set_prism [Copy S] (p : Prism S A) (a : A) (s : S) : S :=
    over_prism p (fn _ => a) s
