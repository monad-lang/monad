// List-specific extras beyond the core List type/constructors
// (init/prelude.mo). Re-exported ambiently via init/lib.mo.

/// The number of elements. Structural recursion with the direct `I64`
/// native: `+` would go through the `Add` instance and allocate a
/// dictionary lookup per element in the compiled backend.
pub def List.length {A : Type} (xs : List A) : I64 :=
    match xs {
        List.empty => 0i64,
        List.cons _ tail => I64.add 1i64 (List.length tail),
    }

/// Get the element at index. Negative and out-of-range indices are
/// `none`. The walk uses the direct `I64` natives: the previous version
/// stepped with `==`, `BOrd.gt` and `-`, whose class dispatch allocates a
/// dictionary lookup per element in the compiled backend.
pub def List.get (index : I64) (l : List A) : Option A :=
    if I64.lt index 0i64
    then Option.none
    else List.get_from index l

#[terminating]
def List.get_from (index : I64) (l : List A) : Option A :=
    match l {
        List.empty => Option.none,
        List.cons a tail =>
            if I64.beq index 0i64
            then Option.some a
            else List.get_from (I64.sub index 1i64) tail,
    }
