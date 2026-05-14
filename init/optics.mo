/// Optics: Lenses, Prisms, and combinators
/// Structural encoding — lenses as getter+setter pairs, prisms as match+construct.

// --- Lens ---

/// A lens focuses on a part A within a whole S.
type Lens S A {
    mkLens (view : S -> A) (set : A -> S -> S)
}

/// Create a lens from explicit getter and setter functions.
def lens (get : S -> A) (put : A -> S -> S) : Lens S A :=
    Lens.mkLens get put

/// Extract the focused value from a structure.
def view (ln : Lens S A) (s : S) : A :=
    match ln { mkLens v _ => v s }

/// Replace the focused value within a structure.
def set (ln : Lens S A) (a : A) (s : S) : S :=
    match ln { mkLens _ st => st a s }

/// Modify the focused value within a structure.
def over (ln : Lens S A) (g : A -> A) (s : S) : S :=
    let a := view ln s in
    set ln (g a) s

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
def over_prism (p : Prism S A) (g : A -> A) (s : S) : S :=
    match preview p s {
        none => s,
        some a => review p (g a)
    }

/// Set a value through a prism (no-op if prism doesn't match).
def set_prism (p : Prism S A) (a : A) (s : S) : S :=
    over_prism p (fn _ => a) s
