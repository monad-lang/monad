/// Constant-time byte equality.
///
/// Equal-length inputs compare EVERY byte, accumulating with `Bool.and`,
/// so no comparison short-circuits on the first difference. A length
/// mismatch shows up when the shorter input runs out and is reported
/// without examining the longer one -- the lengths are public values, not
/// secrets. Timing is data-independent to the extent the backend's
/// `U8.beq` and `Bool.and` are branch-free, which is what this shape can
/// promise in a managed language.

pub def Ct.eq (a : List U8) (b : List U8) : Bool :=
  Ct.eq_go a b true

#[terminating]
def Ct.eq_go (a : List U8) (b : List U8) (same : Bool) : Bool :=
  match a {
    List.empty => match b {
      List.empty => same,
      List.cons _ _ => false
    },
    List.cons x xs => match b {
      List.empty => false,
      List.cons y ys => Ct.eq_go xs ys (Bool.and same (U8.beq x y))
    }
  }
