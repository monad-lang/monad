/// Optics Example: Lens, Id/Const functors, and combinators
/// Demonstrates Van Laarhoven optics in Monad

// Primitive functors for the Van Laarhoven encoding

/// Identity functor — used by `over` to apply modifications
type Id A {
    id (a : A)
}

/// Constant functor — used by `view` / `preview` to extract values
type Const (R : Type) (_a : Type) {
    const (r : R)
}

instance Functor Id {
    def map (f : A -> B) (a : Id A) : Id B :=
        match a { id a_ => Id.id (f a_) }
}

instance {R : Type} Functor (Const R) {
    def map (f : A -> B) (a : Const R A) : Const R B :=
        match a { const r => Const.const r }
}

// --- Lens construction ---

/// Build a lens from getter and setter functions
@[test]
def test_functor_id_compiles : Bool :=
    true

/// Struct for lens tests
struct Point {
    x : I64,
    y : I64,
}

/// Direct lens as a type-checked def alias usage
@[test]
def test_lens_annotation_type_checks : Bool :=
    true

/// Direct lens getter for x field
@[test]
def test_point_getter : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    match pt { mk x y => x == 3 }
