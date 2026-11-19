/// The `Option`/`List` Functor/Applicative/Monad instances and the `Nat`
/// `Mul`/`BOrd`/`ToString` instances. Instance resolution is a run-time step,
/// so each instance is EXECUTED here, not merely checked.
use std::test {}

def half (n : I64) : Option I64 :=
    if I64.rem n 2 == 0 then Option.some (n / 2) else Option.none

def opt_eq (a : Option I64) (b : I64) : Bool :=
    match a {
        Option.some x => x == b,
        Option.none => false
    }

def opt_none (a : Option I64) : Bool := Option.is_none a

#[test]
def test_option_functor_map : Bool :=
    opt_eq (Functor.map (fn (x : I64) => x + 1) (Option.some 41)) 42
        && opt_none (Functor.map (fn (x : I64) => x + 1) Option.none)

#[test]
def test_option_applicative : Bool :=
    let f : Option (I64 -> I64) := Applicative.pure (fn (x : I64) => x * 2) in
    let g : Option (I64 -> I64) := Option.none in
    opt_eq (Applicative.apply f (Option.some 21)) 42
        && opt_none (Applicative.apply g (Option.some 21))

#[test]
def test_option_bind_short_circuits : Bool :=
    opt_eq (Monad.bind (Option.some 8) half) 4
        && opt_none (Monad.bind (Option.some 7) half)
        && opt_none (Monad.bind Option.none half)

def quarter (n : I64) : Option I64 := do {
    let h <- half n;
    let q <- half h;
    return q
}

#[test]
def test_option_do_block : Bool :=
    opt_eq (quarter 20) 5 && opt_none (quarter 6)

def list_eq (a : List I64) (b : List I64) : Bool :=
    match a {
        List.empty => List.is_empty b,
        List.cons x xs => match b {
            List.empty => false,
            List.cons y ys => (x == y) && list_eq xs ys
        }
    }

#[test]
def test_list_flat_map : Bool :=
    list_eq (List.flat_map (fn (x : I64) => [x, x * 10]) [1, 2]) [1, 10, 2, 20]

#[test]
def test_list_applicative_is_cartesian : Bool :=
    let fs : List (I64 -> I64) := [fn (x : I64) => x + 1, fn (x : I64) => x * 10] in
    list_eq (Applicative.apply fs [1, 2]) [2, 3, 10, 20]
        && list_eq (Applicative.pure 7) [7]

#[test]
def test_list_bind : Bool :=
    list_eq (Monad.bind [1, 2, 3] (fn (x : I64) => [x, x])) [1, 1, 2, 2, 3, 3]
        && list_eq (Monad.bind [1, 2] (fn (x : I64) => List.empty)) List.empty

def pairs_sum (xs : List I64) (ys : List I64) : List I64 := do {
    let x <- xs;
    let y <- ys;
    return x + y
}

#[test]
def test_list_do_block : Bool :=
    list_eq (pairs_sum [1, 2] [10, 20]) [11, 21, 12, 22]

def two : Nat := Nat.succ (Nat.succ Nat.zero)
def three : Nat := Nat.succ two

#[test]
def test_nat_mul_instance : Bool :=
    Nat.eq (two * three) (Nat.succ (Nat.succ (Nat.succ three)))
        && Nat.eq (Nat.zero * three) Nat.zero

#[test]
def test_nat_order : Bool :=
    Nat.lt two three && Bool.not (Nat.lt three two) && Bool.not (Nat.lt two two)
        && Nat.le two two && Bool.not (Nat.le three two)

#[test]
def test_nat_bord_instance : Bool :=
    (two < three) && (three > two) && (two <= two) && (two >= two)
        && Bool.not (three < two) && Bool.not (two >= three)

#[test]
def test_nat_to_string_instance : Bool :=
    ToString.to_string three == "3" && ToString.to_string Nat.zero == "0"
