// List-specific extras beyond the core List type/constructors
// (init/prelude.mo). Re-exported ambiently via init/lib.mo.

/// The number of elements. The accumulator keeps the self-call in tail
/// position, so codegen's rewrite (`codegen/src/tco.mo`) turns the walk into
/// a loop; `I64.add 1 (length tail)` recursed once per element and overflowed
/// the stack on a long list -- `motes/moon`'s ETag hashes a whole file with
/// `Sha256.pad`, and a multi-MB static asset crashed the trellis server. The
/// direct `I64` native is deliberate: `+` would go through the `Add` instance
/// and allocate a dictionary lookup per element in the compiled backend.
def List.length_go {A : Type} (xs : List A) (n : I64) : I64 :=
    match xs {
        List.empty => n,
        List.cons _ tail => List.length_go tail (I64.add n 1i64),
    }

pub def List.length {A : Type} (xs : List A) : I64 := List.length_go xs 0i64

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
