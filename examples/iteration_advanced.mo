use init.foldable {Foldable}

def multiply (x : I64) (y : I64) : I64 := x * y

def sum (t : List I64) : I64 :=
  Foldable.foldr (fn x acc => x + acc) 0 t

def product (t : List I64) : I64 :=
  Foldable.foldr multiply 1 t

def length (t : List A) : I64 :=
  Foldable.foldr (fn _ acc => acc + 1) 0 t

def reverse (t : List A) : List A :=
  (Foldable.foldl (fn acc x => List.cons x acc) [] t : List A)

#[test]
def test_sum : Bool := sum [1, 2, 3, 4] == 10

#[test]
def test_product : Bool := product [2, 3, 4] == 24

#[test]
def test_length : Bool := length [1, 2, 3] == 3

#[test]
def test_reverse : Bool :=
  let rev : List I64 := reverse [1, 2, 3] in
  match rev {
    cons h _ => h == 3,
    empty => false
  }

#[test]
def test_any : Bool :=
  let f := fn (x : I64) => x == 3 in
  let t : List I64 := [1, 2, 3] in
  Foldable.foldr (fn x acc => f x || acc) false t

#[test]
def test_all : Bool :=
  let f := fn (x : I64) => x == x in
  let t : List I64 := [1, 2, 3] in
  Foldable.foldr (fn x acc => f x && acc) true t
