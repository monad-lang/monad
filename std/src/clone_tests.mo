/// `Clone` in the presence of mutable state.
///
/// A pure `clone` cannot allocate a fresh cell, so an instance for a type
/// that holds a `Ref` has to decide: share it, or do nothing. This test pins
/// the shared behaviour, which is why `Ref` itself has no `Clone` instance —
/// a caller who wants a fresh cell says so at the type.
///
/// (Independence of cloned *pure* storage is guaranteed by construction but
/// unobservable without a mutable cell, so it is documented in
/// `init/src/clone.mo` rather than asserted here.)
use init::shared {Shared}
use std::ref {Ref}

struct Cell {
    value : Ref I64
}

instance Clone Cell {
    def clone (c : Shared Cell) : Cell :=
        let shared : Cell := Shared.get c in
        let out : Cell := { value := shared.value } in
        out
}

#[test]
def test_clone_of_mutable_state_shares_the_cell : IO Bool := do {
    let r <- Ref.new 1;
    let c : Cell := { value := r };
    let d : Cell := Clone.clone (Shared.of c);
    let dv : Ref I64 := d.value;
    let cv : Ref I64 := c.value;
    let _ <- Ref.set dv 2;
    let v <- Ref.get cv;
    return (I64.beq v 2)
}
